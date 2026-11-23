# finalsay for pi

A [pi](https://pi.dev) extension that implements the model. Every tool call, including calls made by `codemode` scripts, is classified, escalated by the trifecta rule, and decided:
- `allow` runs it;
- `ask` goes to you through `ctx.ui.confirm` (in headless modes it's refused);
- `deny` blocks it.

The trace it writes is audited by the Lean reference.

## Why pi fits

Pi provides the mechanisms; this extension supplies the policy.

| Pi provides | The model uses it as |
|---|---|
| `tool_call` handlers that can block; a handler that throws blocks too | the decision point, failing closed |
| `tool_result` handlers | where code-mode output flows back |
| `codemode` scripts in QuickJS with no file, network, or timer access; only `tools.*` | a sandboxed run = its own **context** |
| `parentToolCallId` on calls a script makes, **assigned by pi** | which run a call belongs to, decided by the harness, not the code |
| No built-in boundary; [docs](https://pi.dev) say isolate pi from outside | the boundary is `srt`/a container; the policy doesn't pretend to be one |

What pi doesn't have, and this adds:
- a principle for who decides: reversibility tiers, with the owner's tier map beating tool hints;
- information-flow labels (private, untrusted) and the trifecta rule;
- a complete, replayable trace with a channel report.

## Run it

```sh
pi -e ./examples/pi/finalsay        # from the repo root
```

Then try: *"Read my inbox and deal with anything urgent."* The toy inbox holds a planted instruction to forward the Q4 plan. The toy tools (`inbox_read`, `email_draft`, `email_send`, `calendar_create`) touch nothing real. `/policy` shows the config path, the trace file, and the main context's exposure.

Audit a session afterwards:

```sh
./.lake/build/bin/finalsay audit .finalsay/trace-<time>.jsonl \
  --config examples/pi/finalsay/config.json
```

## Test it (no model, no pi)

```sh
cd examples/pi/finalsay && npm test
```

- `test/fixtures.test.ts`: the TypeScript core against the Lean fixtures (600/600 decision and classification cases; malformed input is pi's job, since a crashing handler blocks).
- `test/paths.test.ts`: path classification on a real repo, including case variants and symlinks into `.git`.
- `test/session.test.ts`: a simulated session fed through the gate exactly as pi's events would be. The trace it writes passes `finalsay audit --config`, and a tampered copy fails.

The simulated session:

```
RUN   [main] read
RUN   [main] calendar_create
RUN   [main] codemode
RUN   [run_t3] inbox_read
BLOCK [run_t3] email_send  (finalsay: denied by rule 'no-outbound-when-tainted')
BLOCK [run_t3] calendar_create  (finalsay: calendar.create was not approved)
BLOCK [main] email_send  (finalsay: denied by rule 'no-outbound-when-tainted')
RUN   [main] calendar_create        ← asked [irreversible, escalated], approved
RUN   [main] write
BLOCK [main] bash  (finalsay: shell.exec was not approved)
```

The script's inbox read labels its run; the script's output flows back as free text, so `main` inherits both labels; every observable action after that needs you.

## Choices worth knowing

- **Labels attach when a call is decided**, from the config's `readsPrivate` / `readsUntrusted`, not from inspecting results. Scripts can run calls in parallel, so results arrive in any order; decision order is the order that's well defined. This is also more cautious: you can't know a page is safe before reading it.
- **Config never comes from the project folder** (`$FINALSAY_CONFIG`, then `~/.pi/agent/finalsay.json`, then the bundled one). A repository must not be able to loosen its own policy.
- **`bash` is classified reversible only under the hardened sandbox *and* an outside checkpoint** (next section). It stays *observable*, because allowlisted network domains are channels. Without both, delete the `shell.exec` entry so `bash` falls back to unknown, which is irreversible.
- **File writes are classified by where they land.** `write`/`edit` into `.git` is `file.write.vcs` (it can destroy the undo). Into files something outside the sandbox runs later — CI (`.github`), git/editor config (`.husky`, `.vscode`, `.pre-commit-config.yaml`, `.gitmodules`), shell startup (`.envrc`), and **any agent's project config dir** (`.pi`, `.codex`, `.cursor`, `.agents`, `.claude`, `.opencode`) — it's `file.write.exec`, an edge to your full permissions. Both are irreversible, so they ask.

  **The principle, not the list:** *a write is reversible only if nothing outside the sandbox will later execute the file; when you can't tell, treat it as irreversible.* The list is a pragmatic approximation of that rule. Two details matter: matching is by **resolved path segment at any depth**, so a *nested* `sub/.codex/config.toml` is caught, not just `<root>/.codex`; and paths are resolved, symlinks followed, and case-folded first, so `.GIT` and symlinks into `.git` don't slip past. The honest limit: a name list is a treadmill — every new tool invents a new config dir — which is why the `file.write.*` tiers exist to carry the *principle*, and why an unknown write defaults to irreversible rather than reversible. `test/paths.test.ts` checks all of these.

## Sandbox and checkpoints

"Reversible" needs two things this extension can't provide itself:

1. **`srt` with `srt-settings.json`.** Use it with pi's sandbox example extension, or wrap all of pi with `srt -s examples/pi/srt-settings.json pi …`. On top of pi's defaults it adds:
   - deny `.git` entirely: otherwise sandboxed code can rewrite history;
   - deny `.github`, `.husky`, `.pi` (so the sandbox can't rewrite its own config), and `.envrc`;
   - no network.

2. **A checkpoint outside the project.** `checkpoint.sh save` before a session, and `checkpoint.sh restore REV` to undo. The store lives outside the sandbox's write area, so the code it protects against can't touch it.

Build and test commands on agent-edited files (`make`, `npm test`, `lake build`) belong inside the sandbox too: those files are writable by design.
- **The trace is written by the extension, inside pi's process.** That's fine for a demo and for catching mistakes. Against a hostile agent, the trace has to be written by something outside the boundary (see the gate design in the main README).
