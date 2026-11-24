/**
 * finalsay core: the decision procedure, classification with the trifecta
 * rule, and a gate that tracks exposure per context and writes a trace the Lean
 * reference can audit (`finalsay audit TRACE --config CONFIG`).
 *
 * No pi imports, so it runs under plain Node for the tests.
 */

export type Tier = "reversible" | "compensatable" | "irreversible";
export type Decision = "allow" | "ask" | "deny";

export interface Exposure {
  sawPrivate: boolean;
  sawUntrusted: boolean;
}

export interface Request {
  principal: string;
  agent: string;
  action: string;
  resource: string;
  tier: Tier;
  approved: boolean;
  tainted: boolean;
  amount: number;
}

export type Cond =
  | { op: "always" }
  | { op: "actionIs"; action: string }
  | { op: "actionPrefix"; prefix: string }
  | { op: "tierIs"; tier: Tier }
  | { op: "tainted" }
  | { op: "amountAtMost"; amount: number }
  | { op: "and"; args: [Cond, Cond] }
  | { op: "not"; arg: Cond };

export interface Rule {
  name: string;
  effect: "allow" | "deny";
  when: Cond;
}

export interface Entry {
  action: string;
  tier: Tier;
  compensation?: string | null;
  observable?: boolean;
  readsPrivate?: boolean;
  readsUntrusted?: boolean;
}

export interface TierMap {
  entries: Entry[];
  trustHints?: boolean;
}

/** Reclassify file writes by where they land. Matched against the normalized path. */
export interface PathRule {
  tools: string[];
  /** Matches if any path segment equals this (e.g. ".git"). */
  segment?: string;
  /** Matches if the file name equals this (e.g. ".envrc"). */
  basename?: string;
  action: string;
}

export interface Config {
  tierMap: TierMap;
  policy: Rule[];
  /** Tool name → action name. Unmapped tools use their own name (and are unknown). */
  actions?: Record<string, string>;
  pathRules?: PathRule[];
  /** Action for a path-ruled tool writing outside the project root (default
   *  "file.write.outside"; unmapped actions are irreversible). The checkpoint only
   *  covers the project, so nothing outside it can be undone. */
  outsideAction?: string;
  /** Action for a path-ruled tool writing inside a git repo nested in the project
   *  (default "file.write.nested-repo"): the checkpoint stores nested repos as a
   *  pointer, not their files, so it can't restore them. */
  nestedRepoAction?: string;
}

/** Which action a path rule assigns, given an already-normalized (lowercased) path. */
export function pathAction(rules: PathRule[], toolName: string, normalized: string): string | undefined {
  const segs = normalized.split(/[\\/]+/).filter(Boolean);
  const name = segs[segs.length - 1] ?? "";
  for (const r of rules) {
    if (!r.tools.includes(toolName)) continue;
    if (r.segment && segs.includes(r.segment.toLowerCase())) return r.action;
    if (r.basename && name === r.basename.toLowerCase()) return r.action;
  }
  return undefined;
}

/* ── Decision procedure ─────────────────────────────────────────────── */

export function cond(c: Cond, r: Request): boolean {
  switch (c.op) {
    case "always": return true;
    case "actionIs": return r.action === c.action;
    case "actionPrefix": return r.action.startsWith(c.prefix);
    case "tierIs": return r.tier === c.tier;
    case "tainted": return r.tainted;
    case "amountAtMost": return r.amount <= c.amount;
    case "and": return cond(c.args[0], r) && cond(c.args[1], r);
    case "not": return !cond(c.arg, r);
  }
  throw new Error(`unknown op ${(c as { op: string }).op}`); // fail closed
}

function firstMatch(p: Rule[], effect: "allow" | "deny", r: Request): Rule | undefined {
  return p.find((rule) => rule.effect === effect && cond(rule.when, r));
}

export function evaluate(p: Rule[], r: Request): { decision: Decision; rule: string | null } {
  const deny = firstMatch(p, "deny", r);
  if (deny) return { decision: "deny", rule: deny.name };       // 1. deny wins
  if (r.approved) return { decision: "allow", rule: null };     // approved by an authority
  if (r.tier === "irreversible") return { decision: "ask", rule: null }; // 2. irreversible asks
  const allow = firstMatch(p, "allow", r);
  if (allow) return { decision: "allow", rule: allow.name };
  return { decision: "ask", rule: null };                       // 3. no rule asks
}

/* ── Classification ─────────────────────────────────────────────────── */

function lookup(m: TierMap, action: string): Entry | undefined {
  return m.entries.find((e) => e.action === action);
}

export function effectiveTier(m: TierMap, action: string, hint: Tier | null): Tier {
  const e = lookup(m, action);
  if (e) return e.tier === "compensatable" && !e.compensation ? "irreversible" : e.tier; // 4. owner wins
  if (m.trustHints) return hint === "reversible" ? "reversible" : "irreversible";
  return "irreversible";                                        // unknown is irreversible
}

export const observable = (m: TierMap, a: string) => lookup(m, a)?.observable ?? true;
export const readsPrivate = (m: TierMap, a: string) => lookup(m, a)?.readsPrivate ?? false;
export const readsUntrusted = (m: TierMap, a: string) => lookup(m, a)?.readsUntrusted ?? false;

export function sessionTier(m: TierMap, action: string, hint: Tier | null, x: Exposure): Tier {
  if (x.sawPrivate && x.sawUntrusted && observable(m, action)) return "irreversible"; // 4c. trifecta
  return effectiveTier(m, action, hint);
}

/* ── The gate: contexts, exposure, trace ────────────────────────────── */

const NONE: Exposure = { sawPrivate: false, sawUntrusted: false };
const join = (a: Exposure, b: Exposure): Exposure => ({
  sawPrivate: a.sawPrivate || b.sawPrivate,
  sawUntrusted: a.sawUntrusted || b.sawUntrusted,
});

export interface ToolCall {
  toolName: string;
  toolCallId: string;
  /** Set by the harness (not the script) for calls a code-mode script made. */
  parentToolCallId?: string;
  input: Record<string, unknown>;
}

export interface ToolResult {
  toolName: string;
  toolCallId: string;
  parentToolCallId?: string;
  content: { type: string; text?: string }[];
}

export interface Approver {
  /** False in headless modes: an `ask` is then refused. */
  hasUI: boolean;
  confirm(title: string, message: string): Promise<boolean>;
}

/** Trace events, in the JSON shape the Lean reference derives. */
export type TraceEvent =
  | { call: { c: Record<string, unknown> } }
  | { handoff: { src: string; dst: string; schema: "freeText" | { structured: { bits: number } }; bytes: number } };

/** How the gate sees paths (see paths.ts `makePaths`). `normalize` gives the
 *  lowercased real path to classify; `resolve` gives the real path, which the gate
 *  writes back into the call so the tool opens what was classified; `inside` says
 *  whether a path is in the project (else `outsideAction`); `nestedRepo` whether it
 *  is in a git repo nested inside the project, which the checkpoint can't restore
 *  (else `nestedRepoAction`). */
export interface Paths {
  normalize: (path: string) => string;
  resolve?: (path: string) => string;
  inside?: (path: string) => boolean;
  nestedRepo?: (path: string) => boolean;
}

export class Gate {
  private env = new Map<string, Exposure>();
  /** Code-mode calls that were allowed: call id → (parent context, run context). */
  private runs = new Map<string, { parent: string; run: string }>();

  private cfg: Config;
  private sink: (e: TraceEvent) => void;
  private who: { principal: string; agent: string };
  private hintOf: (toolName: string) => Tier | null;
  private paths: Paths;

  constructor(
    cfg: Config,
    sink: (e: TraceEvent) => void,
    who = { principal: "user:me", agent: "pi" },
    hintOf: (toolName: string) => Tier | null = () => null,
    paths: Paths = { normalize: (p) => p.toLowerCase() },
  ) {
    this.cfg = cfg;
    this.sink = sink;
    this.who = who;
    this.hintOf = hintOf;
    this.paths = paths;
  }

  exposure(ctx: string): Exposure {
    return this.env.get(ctx) ?? NONE;
  }

  /** Top-level calls run in `main`; calls a script made run in that script's context. */
  contextOf(parentToolCallId?: string): string {
    if (!parentToolCallId) return "main";
    return runName(parentToolCallId.split("/")[0]);
  }

  actionOf(toolName: string, input: Record<string, unknown> = {}): string {
    if (this.cfg.pathRules && typeof input.path === "string") {
      const norm = this.paths.normalize(input.path);
      const a = pathAction(this.cfg.pathRules, toolName, norm);
      if (a) return a;
      const ruled = this.cfg.pathRules.some((r) => r.tools.includes(toolName));
      if (ruled && this.paths.inside && !this.paths.inside(input.path)) {
        return this.cfg.outsideAction ?? "file.write.outside";
      }
      if (ruled && this.paths.nestedRepo?.(input.path)) {
        return this.cfg.nestedRepoAction ?? "file.write.nested-repo";
      }
    }
    return this.cfg.actions?.[toolName] ?? toolName;
  }

  private handoff(src: string, dst: string, bytes: number) {
    // Free text carries every label; a structured schema would clear `untrusted`.
    this.env.set(dst, join(this.exposure(dst), this.exposure(src)));
    this.sink({ handoff: { src, dst, schema: "freeText", bytes } });
  }

  /** Decide a tool call. Returns a block result, or undefined to let it run. */
  async onToolCall(ev: ToolCall, ui: Approver): Promise<{ block: true; reason: string } | undefined> {
    const { tierMap, policy } = this.cfg;
    const ctx = this.contextOf(ev.parentToolCallId);
    const x = this.exposure(ctx);
    const action = this.actionOf(ev.toolName, ev.input);
    // Pin the path: the tool opens the real path that was classified.
    if (this.paths.resolve && typeof ev.input.path === "string") {
      ev.input.path = this.paths.resolve(ev.input.path);
    }
    const hint = tierMap.trustHints ? this.hintOf(ev.toolName) : null;
    const amount = Number.isInteger(ev.input.amount) && (ev.input.amount as number) >= 0 ? (ev.input.amount as number) : 0;
    const req: Request = {
      ...this.who, action, resource: ctx,
      tier: sessionTier(tierMap, action, hint, x),
      approved: false, tainted: x.sawUntrusted, amount,
    };

    const first = evaluate(policy, req);
    let approved = false;
    let res = first;
    if (first.decision === "ask" && ui.hasUI) {
      const why = req.tier === "irreversible" && effectiveTier(tierMap, action, hint) !== "irreversible"
        ? "\n\nEscalated: this context holds private data and untrusted input, and this action is observable."
        : "";
      approved = await ui.confirm(`Allow ${action}? [${req.tier}]`,
        `${ev.toolName} ${JSON.stringify(ev.input).slice(0, 400)}${why}`);
      if (approved) res = evaluate(policy, { ...req, approved: true });
    }

    const ran = res.decision === "allow";
    const obs = observable(tierMap, action);
    const brought: Exposure = ran
      ? { sawPrivate: readsPrivate(tierMap, action), sawUntrusted: readsUntrusted(tierMap, action) }
      : NONE;
    this.sink({ call: { c: {
      ctx, hint, request: req, exposure: x, approved,
      decision: res.decision, rule: res.rule, ran, observable: obs,
      bytesOut: ran && obs ? JSON.stringify(ev.input).length : 0, brought,
    } } });
    if (!ran) {
      const reason = res.decision === "deny"
        ? `finalsay: denied by rule '${res.rule}'`
        : ui.hasUI ? `finalsay: ${action} was not approved`
        : `finalsay: ${action} needs approval and there is no one to ask`;
      return { block: true, reason };
    }

    // Labels attach at decision time: results of parallel calls can arrive in any order.
    this.env.set(ctx, join(x, brought));
    if (ev.toolName === "codemode") {
      const run = runName(ev.toolCallId);
      this.runs.set(ev.toolCallId, { parent: ctx, run });
      this.handoff(ctx, run, JSON.stringify(ev.input).length); // the code carries its writer's labels
    }
    return undefined;
  }

  /** A code-mode script finished: its output flows back to the context that ran it. */
  onToolResult(ev: ToolResult) {
    const r = this.runs.get(ev.toolCallId);
    if (!r) return;
    this.runs.delete(ev.toolCallId);
    const bytes = ev.content.reduce((n, c) => n + (c.text?.length ?? 0), 0);
    this.handoff(r.run, r.parent, bytes);
  }
}

function runName(id: string): string {
  return "run_" + id.replace(/[^A-Za-z0-9_]/g, "_");
}
