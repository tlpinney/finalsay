# Let reversibility decide who decides

*A holistic, slightly informal account of authority for AI agents.*

Travis Pinney · November 2026

---

## TL;DR

AI agents now do things that matter: send email, move money, push code, write files that other programs run later. 2026 produced a burst of good work on governing that: compensability tiers, commit-time authorization, effect closure at provider boundaries, transactional runtimes, barrier semantics for approval gates, authority conservation across forking agents. Each is a real piece. None of them says why the pieces belong together.

Here's the one idea I think ties them together:

> **An effect is reversible relative to a boundary if the information needed to undo it stays inside the boundary. Reversibility decides who may authorize an effect, and the point where it crosses the boundary is where that decision has to be made.**

Reversible things are the agent's call. Compensatable things are policy's call. Irreversible things need a human with authority, at the moment the effect crosses the boundary. From that one definition you get the three tiers, the commit point, why compensation isn't undo (there's a small information-theoretic result here), why writing a file that something runs later is irreversible, and why enforcement splits into an inner semantic gate and an outer OS floor.

Then I read six recent systems through that lens. It explains *where* each one puts its check. What it doesn't explain is what each one adds: what makes an approval *valid* at that point (current, bound to the exact effect, from someone with authority, conserved across forks, held across concurrent branches, drained after revocation). Put all of those at the one point the principle picks, and you get a single coherent system. This repo states it, proves its end-to-end guarantees in Lean, and checks an independent implementation against 1,217 exported cases, with mutation testing to show the corpus actually notices when a guarantee breaks.

---

## 1. Who decides?

An agent that can act in the world holds authority. Every deployment has to answer *who decides*: when can the agent just go, when does a rule decide, and when does a person have to? The usual answers are "trust the model", "allowlist some tools", or "put a prompt in front of anything that looks scary". None of those says what makes an action scary, so none of them tells you where the line goes.

The recent literature has made real progress on pieces of this:

- **Tallam** names a point of no return and sorts actions into compensable, partially compensable, and non-compensable [[Tallam 2026]](#ref-tallam).
- **Cordon** wraps an agent task in a semantic transaction: local effects stay reversible, external ones wait in an outbox until a commit-time check [[Chen et al. 2026]](#ref-cordon).
- **Santos-Grueiro** shows authorization has to be checked at the atomic commit point of the exact effect [[Santos-Grueiro 2026a]](#ref-santos-commit), and that it isn't over until in-flight work can no longer reach a rejected effect [[Santos-Grueiro 2026b]](#ref-santos-closure).
- **Khan** measures approval gates in six agent frameworks that pause one branch while a sibling's effect lands anyway [[Khan 2026]](#ref-khan).
- **Zhu and Wang** show forking agents have to *reallocate* authority, not copy it [[Zhu & Wang 2026]](#ref-zhu).

Each paper has a piece, and each piece stands on its own justification. What I want to do here is explain the field: say what each of these is really doing, why the pieces fit, and what the whole looks like once you put them in one place.

What's in here:

1. **The framework** (§2). Reversibility relative to a boundary as the one organizing idea, plus an honest statement of what it *doesn't* decide.
2. **The field through that lens** (§3). Six 2026 systems, credited for what each one actually contributes.
3. **A holistic picture** (§4). The field as one stack, and one system where every validity condition is a clause of one commit-time check.
4. **A machine-checked composition** (§5). Lean 4 proofs for all policies and all interleavings, 1,217 conformance cases, and mutation testing.
5. **Run-later writes** (§6). Why files that something executes later are the sneakiest irreversible effect, and the two-layer defense the framework prescribes.

---

## 2. The framework

### Reversibility is relative to a boundary

The same `DELETE` is reversible on a snapshotted database and irreversible on one with no backup. Reversibility isn't a property of an action. It's a property of an action *relative to a boundary*: the part of the world whose history you control.

> **Definition.** An effect is *reversible* with respect to a boundary iff the information needed to restore the prior state is retained inside the boundary, and *irreversible* iff that information has crossed it.

This is the classic idea from reversible computing, plus a boundary. A computation is invertible exactly when it erases no information, and you can make any computation invertible by keeping its history [[Landauer 1961]](#ref-landauer), [[Bennett 1973]](#ref-bennett). The boundary is just the edge of the history you keep. A draft email is reversible because its history is yours. Once you hit send, undoing it would need information that now lives in someone else's inbox.

Someone outside *seeing* the effect is the commonest way information crosses, but it's not the definition. An effect can be past the point of no return before anyone looks, say once a provider has durably accepted a message it hasn't delivered yet. The real test is: *can you still prevent or invert this from inside the boundary?*

### Who decides: three tiers

Most real agent actions are neither cleanly reversible nor hopelessly final. A refund can't undo a charge, but it can counteract it. A cancellation can't unsend an invite, but it can withdraw it. That's the database world's saga [[Garcia-Molina & Salem 1987]](#ref-sagas): if you can't roll back, define a compensating action. So, three classes:

| Class | Meaning | Who decides | Mode |
|---|---|---|---|
| Reversible | Prior state restorable, no trace | The agent | Act, log, allow appeal |
| Compensatable | Can't undo, but a declared action counteracts it | Policy | Act within policy; outside it, escalate |
| Irreversible | No restoration, no adequate compensation | A human with authority | Decide before, or grant in advance |

The reasoning is short. A decision carries authority to the extent it can't be undone. If an effect can be reversed, the agent's judgment can be reviewed and fixed afterwards, so the agent can decide. If it can't, the decision is final when it's made, so it has to be made by whoever is entitled to make final decisions about that thing. The line isn't human vs. model. It's reversible vs. irreversible. Better models earn more room *inside* the reversible tier. They don't earn authority over the irreversible one.

### Where: the commit point

If finality is what demands authority, the decision belongs exactly where an effect becomes final: where it crosses the boundary. Push that point as late as you can, make everything before it reversible (sandbox, dry run, staging, two-phase commit), and put the strictest decider right there. Two-phase commit turns into separation of duties: the agent prepares, the authority commits.

Actions also move between tiers. Sandboxing and staging turn irreversible actions into compensatable or reversible ones by moving the boundary. **You shrink the human tier by engineering reversibility, not by trusting smarter models.**

### What falls out

A bunch of things people usually argue separately turn out to be consequences of the definition.

**Compensation isn't restoration.** A compensating action gets back a targeted *quantity*, not the *state*, because the record of both the effect and its compensation sticks around.

> **Theorem (compensation is not restoration).** In an append-only ledger, applying a compensating action after an effect restores the targeted quantity (say, the balance) but strictly increases the audit residue (the ledger length). The resulting state differs from the pre-effect state.

The residue is Bennett's history tape: to invert, you have to keep the record, and the record is the cost. It's Landauer's principle showing up in business logic. (In Lean: `compensation_leaves_residue`.)

**The case nobody anticipated escalates.** If you can't show the information stays inside, assume it crossed. So an action that no rule covers and no tier map classifies is irreversible by default, and goes to a human.

**Run-later writes are irreversible.** A write is only reversible if nothing outside the boundary will later interpret it. Config that another program executes on its next start (git hooks, CI workflows, editor tasks, any agent's project config) carries the effect across the boundary at a time the writer doesn't control. More in §6.

**Enforce where effects cross.** A guard on a command's *text* sees intent, not effect, and indirection gets around it. The boundary is actually crossed in the operating system, so the floor belongs there: an outer OS sandbox that sees every write from every tool. But an OS sandbox can only allow or deny, so the decisions that need tool semantics (ask a human, track taint, know a compensation exists) belong in an inner gate on typed tool calls. Each one covers what the other can't.

**Information leaks through permitted actions.** An allowed action can still carry information out in its content, its timing, or just the fact that it happened. Private data, untrusted input, and a way to communicate out is Simon Willison's "lethal trifecta" [[Willison 2025]](#ref-willison-trifecta). If you classify by who can *observe* the effect, it becomes a tier question: in a session that has seen both private data and untrusted input, every externally observable action is irreversible. And between contexts, a *structured* result (a boolean, an enum) can't carry instructions, so it stops untrusted taint where free text wouldn't. That's the idea behind the Dual LLM pattern [[Willison 2023]](#ref-willison-dual) and CaMeL [[Debenedetti et al. 2025]](#ref-camel).

### Why it's succinct, and what it doesn't do

Every element of the framework follows from the one definition:

| Element | Follows because |
|---|---|
| Three tiers | They're degrees of how much undo-information stays inside; authority tracks finality. |
| Commit point | The crossing is the only place a decision becomes final, so that's where the decider goes. |
| Unknown is irreversible | Without evidence the information stays inside, assume it crossed. |
| Compensation ≠ undo | Compensation adds history instead of removing it. |
| Run-later writes | A later interpreter outside the boundary is a crossing the writer doesn't schedule. |
| Inner/outer enforcement | Enforce where effects cross (outer); decide with semantics where calls are legible (inner). |
| Trifecta / covert channels | Observation is a crossing; under exposure, observable actions are irreversible. |
| Sandbox, staging, 2PC | These move the boundary, and so move actions down a tier. |

Succinct can be a warning sign, though. A framework can stay elegant just because it hasn't met the details that force complexity. So here's exactly what the principle decides and what it doesn't.

It decides *where* authority has to be exercised and *who* has to exercise it. It does **not** decide whether a particular "yes" is valid. An irreversible action with an approval attached passes the tier rule even if that approval was revoked an hour ago, was for a different amount, came from someone with no authority over the resource, got copied into five forked sub-agents, or was granted while a sibling branch had already acted. Those are a second, orthogonal axis: the classic conditions on a valid authorization [[Saltzer & Schroeder 1975]](#ref-saltzer). The principle doesn't derive them. It tells you where they all have to be checked. And it turns out that second axis is exactly where the recent work has concentrated.

---

## 3. The field through the lens

I read six 2026 systems in full and asked two questions of each: what does the framework say it's doing, and what does it add that the framework doesn't derive?

| System | Where it checks (framework reading) | What it adds (validity axis) | Evidence |
|---|---|---|---|
| Tallam [[ref]](#ref-tallam) | MP5, "externally observable, side-effecting, or otherwise difficult to compensate"; three compensability classes | Capability attenuation along delegation; scoped approval | Argued; reference policy core |
| Cordon [[ref]](#ref-cordon) | Shadow state keeps local effects reversible; outbox holds external ones that "may cross an irreversible boundary" | Lineage from secrets/untrusted input to sinks; transaction-scoped approval | Prototype; 45 workflows |
| Santos-Grueiro, commit-time [[ref]](#ref-santos-commit) | The commit boundary, "the last point where the system can withhold" the effect | Approval current at commit and bound to the exact effect | Lean (139 theorems); measured |
| Santos-Grueiro, effect closure [[ref]](#ref-santos-closure) | The effect frontier, which "may precede return, declared completion, or visibility" | Drain in-flight work after revocation; idempotent binding | Lean; Kafka/NATS/K8s |
| Khan [[ref]](#ref-khan) | Execution = the commit point past which a tool can't revoke | Barrier semantics: a hold covers the whole run; at-most-once; cancel fences | 1,200 live runs; Verus, TLA+ |
| Zhu & Wang [[ref]](#ref-zhu) | (Orthogonal: reversal is out of scope) | Authority conserved, not copied, across forks | Prose proofs; checked corpus |

**Tallam: the tiers, without the reason.** The five-plane architecture puts its action-commit mediation point where a call becomes "externally observable, side-effecting, or otherwise difficult to compensate," and sorts actions into compensable, partially compensable, and non-compensable, with the last needing explicit authorization. In framework terms, that's the commit point and the three tiers. The paper gives the taxonomy a paragraph, with "does an inverse exist" as its only criterion; the definition above supplies the *why*. Tallam's own contribution is elsewhere: capability attenuation along delegation chains (each delegate's capability is a subset of its delegator's), time-bounded capabilities, and approvals bound to capabilities instead of action signatures.

**Cordon: the boundary, actually built.** Cordon makes each agent task a semantic transaction. Local mutations go to shadow state and can be rolled back; external effects wait in an outbox "because their release may cross an irreversible boundary"; commit validates the composed flow first. That's the framework's boundary built in software, right down to treating the final answer to the user as a gated external effect. Beyond reversibility, it adds flow rules: secret-derived data can't reach an unauthorized sink, untrusted input can't justify a sensitive write, and an approval binds to one transaction.

**Santos-Grueiro: the check at the crossing, and how long it lasts.** Commit-time authorization needs a complete, current justification for the exact effect at its atomic commit point, "the last point where the system can withhold it." The framework explains why the check goes there. It doesn't explain the rest, and the paper's evidence shows the rest matters: 12 of its 17 advisories involve no intervening change at all. They're failures of *binding*, not timing. Effect closure pushes this past the commit: authorization ends only when issuance stops *and* nothing in flight can still reach a rejected effect. Its line that "later abort, compensation, or reconciliation cannot erase a violation; prevention must act before" the frontier is the commit point and the residue theorem in one sentence. And its frontier, which can come before visibility, is why my definition talks about preventability instead of observation.

**Khan: the hold has to cover the whole run.** Khan measures approval gates in six agent frameworks and finds that a pause only holds the branch that asked: 215 of 1,200 live-model runs leak a sibling's effect while the human is still deciding. The framework explains the scope ("irreversible or externally committed" actions, executed at the point the tool can no longer revoke them) but says nothing about concurrency. Khan adds barrier semantics (no gated effect of a paused run executes; rejected effects never execute; each executes at most once; cancellation fences late work) and a verified out-of-process gate.

**Zhu and Wang: conservation.** For self-modifying agent populations, treating each fork as a fresh copy of its parent's grant "silently multiplies budgets, concurrency slots, approval weight, and effect combinations." Their principle: "a fork reallocates existing authority instead of copying it." Reversal is out of scope. This is the cleanest example of a property that lives purely on the second axis: the tiers assume one agent, and nothing about reversibility says an approval can't be duplicated across children.

**What the lens shows.** Every system puts its check where the framework says it has to go, at the boundary crossing, even though each calls that point something different (mediation point, outbox, commit boundary, frontier, admission point). Each then adds one or two validity conditions, justified on their own terms. None of them combines currency, binding, approver authority, attenuation, conservation, the run barrier, and drain at one point, and none gives compensation a formal account as non-restoration. That's the gap the next two sections fill.

---

## 4. One picture

### The field as a stack

Put the pieces together and agent authority looks like a stack of five layers. Each answers one question, and each line of recent work has concentrated on one or two of them. Seen this way, the systems above aren't competing designs. They're contributions to different layers of the same structure.

| Layer | Question | Where the field's work sits |
|---|---|---|
| 1. Boundary engineering | How much can we make reversible? | Sandboxes, shadow state and outboxes [[Cordon]](#ref-cordon), staging, two-phase commit; the outer OS floor here |
| 2. Classification | Which tier is this effect in? | Compensability classes [[Tallam]](#ref-tallam); the tier map, run-later rule, and trifecta rule here |
| 3. The commit point | Where must the decision be made? | Mediation point [[Tallam]](#ref-tallam), commit boundary [[Santos-Grueiro a]](#ref-santos-commit), effect frontier [[Santos-Grueiro b]](#ref-santos-closure), admission [[Khan]](#ref-khan) |
| 4. Validity at the point | Is this particular "yes" valid? | Currency, binding [[Santos-Grueiro a]](#ref-santos-commit); attenuation [[Tallam]](#ref-tallam); conservation [[Zhu & Wang]](#ref-zhu); barrier [[Khan]](#ref-khan); information flow [[Cordon]](#ref-cordon) |
| 5. After the point | What happens once it's crossed? | Drain and bind [[Santos-Grueiro b]](#ref-santos-closure); compensation and its residue; audit |

The claim is that these layers are one design problem. Layer 1 decides how much of the world the agent can change freely. Layer 2 says which effects are left. Layer 3 puts the decision where each of those effects becomes final. Layer 4 makes sure the decision taken there is a real one, and layer 5 makes sure it stays in force. The framework explains why they're stacked in that order: each one is about where the information needed to undo an effect lives.

### One check at one point

Once the framework fixes *where* (the crossing) and *who* (by tier), all the validity conditions from §3 can be checked there, in one place. Here's the path an effect takes:

```
 agent proposes effect e in run r
   |
   v
 policy + tier ------- deny --------> dropped
   |  allow            | ask
   v                   v
 run barrier: while an effect of r awaits a human, r is held  [Khan]
   |  released
   v
 ONE commit-time check, judged on the state at this moment:
   - policy decision for e (tier rule: irreversible needs approval)
   - approval bound to exactly e, unexpired, unrevoked, unused  [Santos-Grueiro]
   - approver holds authority over e via an attenuated chain    [Tallam]
   - proposing agent's budget covers e (forks split, not copy)  [Zhu & Wang]
   |  pass: consume approval, spend budget, write audit record
   v
 provider: carrier tagged {approval, delegation chain}
   - revoking any tag fences the carrier in flight              [Santos-Grueiro]
   - each idempotency key lands once, despite redelivery
   v
 effect lands
```

Each bracketed condition comes from the cited work. The framework supplies the single point where all of them get checked.

That's where the framework earns its keep. Each prior system enforces its condition at its own point, under its own model. Here there's one point, and every condition is a clause of one check, so they can't disagree about when an effect became final. Two small design choices make it work:

1. *Every* effect leaving the barrier goes through the same check, including siblings released after a decision. Nothing gets waved through because it was allowed earlier.
2. The carrier handed to the provider is tagged with the approval it used *and* the delegation chain behind the approver's authority. Revoking any of them, even a delegation two levels up, drains the effect, even if it's already in flight.

For every policy and every interleaving of proposals, decisions, grants, revocations, delegations, forks, clock ticks, deliveries, and redeliveries, the composed system guarantees:

1. every effect that lands traces to an audit record of a passed check;
2. an irreversible effect that lands was backed, at commit, by an approval covering exactly it, unexpired, unrevoked, from someone holding authority over it within the root's scope, and its carrier names that approval and chain;
3. once an approval or a delegation is revoked, nothing it backed lands, whether in flight, redelivered, or attempted later;
4. each effect lands at most once; rejected effects never leave the barrier; a cancelled run commits nothing further;
5. while a run is waiting on a human, only a decision on that run commits anything of it;
6. each single-use approval backs at most one commit, and the total committed amount never exceeds the root budget, however agents fork;
7. nobody ever holds authority the root didn't have.

One last property shows the layers agree: in every reachable state, a commit that passed the check is never refused at the provider. So the provider's own refusal is defense in depth, not a second, possibly conflicting, decision.

---

## 5. Proving it

The framework, each component, and the composed system are specified and proved in Lean 4 (the `FinalSay/` folder). It's small on purpose: a reference semantics, not an implementation. Every theorem holds for *all* policies and all operation sequences, and depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No `sorry`.

| Module | Headline theorems | Property (source) |
|---|---|---|
| `Core`, `Invariants` | `deny_wins`, `irreversible_needs_approval`, `no_rule_asks`, `unknown_is_irreversible`, `trifecta_needs_approval`, `malformed_never_allowed` | Tier rule, exceptions escalate, fail closed (this work) |
| `World` | `compensation_leaves_residue`, `compensation_is_not_undo` | Residue (this work) |
| `Authority` | `irreversible_commit_exact_current`, `revocation_is_effective`, `single_use_at_most_once`, `decision_before_commit_goes_stale` | Currency, binding [[Santos-Grueiro a]](#ref-santos-commit) |
| `Conservation` | `budget_conserved`, `grant_used_at_most_once`, `copy_on_fork_overspends` | Conservation [[Zhu & Wang]](#ref-zhu) |
| `Delegation` | `no_amplification`, `links_attenuated`, `revocation_cascades`, `irreversible_commit_authorized` | Attenuation [[Tallam]](#ref-tallam) |
| `Barrier` | `barrier`, `rejected_never_lands`, `lands_at_most_once`, `cancel_fences_run`, `per_branch_pause_leaks` | Barrier semantics [[Khan]](#ref-khan) |
| `Frontier` | `revocation_drains`, `key_lands_at_most_once`, `in_flight_outlives_revocation` | Drain, bind [[Santos-Grueiro b]](#ref-santos-closure) |
| `System` | `run_sim`, `landed_was_committed`, `irreversible_landed_authorized`, `delegation_revocation_drains_system`, `barrier_system`, `committed_within_budget`, `committed_never_refused_at_dispatch` | Composition (this work) |

**Composition by simulation.** The composed system holds each component's state and only changes it through that component's own transition function. `run_sim` proves that in any run, each component's state is a run of its own model, so every component theorem holds inside the system unchanged. The end-to-end results then only need a bit of glue: an invariant tying landed carriers to audit records, records to the state they were judged in, and spent budget to the committed total.

**Counterexamples.** Each component also proves, by computation, that the obvious weaker design fails:

- a decision taken before revocation allows what the commit-time check refuses;
- copy-on-fork spends twice the grant;
- a per-branch pause lands a sibling mid-decision;
- refusing new dispatches lets in-flight work land after revocation;
- without binding to the key, redelivery lands twice;
- an approval from a sub-agent with no authority passes the currency check on its own.

**Conformance and mutation testing.** Lean exports 1,217 cases with expected outcomes: 602 for the decision core, and 615 traces of the composed system (15 named scenarios plus 600 from a fixed seed). An independent, standard-library-only Python implementation, written from the spec, reproduces all of them (`examples/python/`).

But a passing corpus tells you nothing until you've seen it fail. So I broke one guarantee at a time in the Python implementation and counted how many cases noticed:

| Broken guarantee | Failing | Broken guarantee | Failing |
|---|---|---|---|
| Approver authority | 336 | Fork conservation | 91 |
| Provider fence | 205 | Idempotency bind | 84 |
| Revocation cascade | 107 | Single use | 24 |
| Run barrier | 99 | Provider refusal (equivalent) | 0 |
| Attenuation | 93 | | |

The first corpus, built from single random operations, missed the revocation cascade completely and only caught a missing provider fence in 3 cases. Multi-step flows almost never assemble by chance. After adding targeted flows, every non-equivalent mutant gets caught. The one equivalent mutant is the provider ignoring revoked tags, which `committed_never_refused_at_dispatch` proves can't change any outcome.

**What's mine and what isn't.** The validity properties come from the cited work, and several are already machine-checked there (in Lean [[Santos-Grueiro a]](#ref-santos-commit); in Verus and TLA+ [[Khan]](#ref-khan)). I re-model them small only so I can compose them. What I'm adding is the organizing principle, the residue theorem, putting every condition at one point, and a mechanized check that they compose.

---

## 6. Run-later writes

The framework predicts something specific: a write is irreversible when something outside the boundary will later execute it. This is worth dwelling on, because it's the effect that's easiest to miss.

Coding agents typically run model-chosen shell commands inside an OS sandbox (Seatbelt on macOS, bubblewrap and seccomp on Linux): writes confined to the workspace, no network by default, a few paths held read-only. The question is *which* paths. Plenty of files in a workspace are executed later by something that isn't sandboxed:

- git hooks and `.git/config` (`core.fsmonitor`, aliases), which run on your next `git commit` or `git status`;
- CI workflows, editor tasks, `.envrc`, pre-commit configs;
- any agent's own project config dir (`.codex`, `.cursor`, `.agents`, `.claude`, `.pi`, `.opencode`, …), which may define hooks or MCP servers that start next session.

A sandboxed write to any of those is a crossing the writer doesn't schedule. It looks local and reversible, but the effect lands later, on the host, with your full permissions. This class is well known: Git itself fixed a version of it in 2014, where a `.Git/config` path got past Git's own `.git` checks on case-insensitive filesystems [[CVE-2014-9390]](#ref-cve2014), and agent sandboxes have shipped fixes for git-hook and git-config routes since.

Two mistakes keep producing it, and both are boundary mistakes:

1. **The protected set is drawn too small.** Protecting `<root>/.codex` instead of *any* `.codex` means a nested one is, by the sandbox's own policy, a permitted write.
2. **Protection is matched against the name, not the file.** Policies are written in names ("deny writes to `.git`"), but the filesystem decides which file a name refers to. On the default macOS and Windows filesystems, `.git/config`, `.Git/config` and `.GIT/config` are the same file, and a symlink can make `notes/hooks` mean `.git/hooks`. So a guard that blocks any path containing `.git/` lets `.GIT/hooks/pre-commit`, `./.Git/hooks/pre-commit` and a symlink into `.git` straight through, and each lands in the real hooks folder. The rule was right; what it got applied to wasn't. The component that resolves the name is the one actually deciding, so enforce there (a kernel sandbox checks the file a path resolves to, and none of those spellings get past it). If a check has to work on strings, resolve first: make the path absolute, follow symlinks, fold case, then match whole path segments. And treat a name you can't resolve with certainty like any other unanticipated case: escalate it.

It's worth looking at where vendors draw their own line. When a sandbox failed to protect a file it promised to protect, like git hooks or a git config key that runs on the next `git status`, that was treated as a real bug and fixed. But public bug-bounty scope rules also say an attack is out of scope if it "depends on the client processing a repository or other file", or needs to get past a "trust this project" prompt, or only uses "actions allowed by the active configuration." In other words, the authority boundary is the one-time trust prompt, and what a trusted project contains is accepted risk.

Both halves are coherent. A sandbox's guarantee is exactly the set of things it commits to defending, so "is this a bug?" becomes "did the boundary claim to cover this?" That's the same move as the rest of this write-up: *reversible relative to what boundary* is itself a decision, made the moment a system declares a trust boundary. It's also why a reversibility-based layer is still useful: it re-examines, at each write, a trust that was granted once and never revisited. The dangerous gap usually isn't what the boundary blocks loudly. It's what's on the far side of a prompt the user clicked through months ago.

**The fix the framework prescribes.** Classify run-later writes as irreversible, and enforce where effects cross:

- **Outer floor (OS sandbox).** Deny them at any depth and by resolved name. In `srt` [[Anthropic srt]](#ref-srt) that means depth-independent globs like `**/.git`, `**/.codex`, … instead of root-relative names. This covers the shell, which no tool-level gate can see. In this repo the outer policy is *generated by Lean* (`FinalSay/SrtConfig.lean` → `experiments/wrapper/srt-outer.json`), with proofs that it denies exactly the writes the model classifies as irreversible, at any depth and in any letter case.
- **Inner gate (typed tools).** Classify the same writes as irreversible and *ask* instead of refusing. The pi extension in `examples/pi/` does this, normalizing paths first (absolute, symlinks followed, case-folded, whole-segment match). That matters because the outer layer is blunt: it would also deny a legitimate edit to `.cursor/rules`.

Configured this way, the outer layer denies nested run-later config at any depth, the version-control directory everywhere, and case variants, including through the shell, while ordinary source writes stay allowed. One outer policy wraps different agents without changes. The inner gate catches the same writes when they come through a typed file tool, and asks a human instead of just saying no.

---

## 7. Related work

§3 covers the six systems closest to this. Beyond them:

- Prompt-injection defenses by design: the lethal trifecta [[Willison 2025]](#ref-willison-trifecta) names the condition the trifecta rule escalates on; the Dual LLM pattern [[Willison 2023]](#ref-willison-dual) and CaMeL [[Debenedetti et al. 2025]](#ref-camel) separate what untrusted data can influence, which is what the trace's structured handoffs do.
- Out-of-process enforcement on the only action path shows up in Dobrin and Chmiel's safety kernel [[Dobrin & Chmiel 2026]](#ref-dobrin) and in action-boundary governance with trusted provenance [[Mazzocchetti 2026]](#ref-mazzocchetti).
- The validity conditions I compose come from classic protection principles: complete mediation, least privilege, fail-safe defaults, and separation of privilege [[Saltzer & Schroeder 1975]](#ref-saltzer).
- Compensation as a defined counteraction is the saga pattern [[Garcia-Molina & Salem 1987]](#ref-sagas). The residue result gives it an information-theoretic reading via Landauer and Bennett [[Landauer 1961]](#ref-landauer), [[Bennett 1973]](#ref-bennett), which I haven't seen elsewhere in this literature. Cordon's post-rollback residual-deltas metric [[Chen et al. 2026]](#ref-cordon) measures local rollback, not compensation, and makes no formal claim.

---

## 8. Limitations

- The framework decides *where* and *who*. It doesn't derive the validity conditions, and I'm not claiming it does. Its succinctness is a claim about organization, not completeness.
- The Lean models are small. Approvals live in a shared store instead of being held by individual agents. The drain results assume the mediator can reach the provider's queue.
- The inner gate is only as good as its tier map, and the run-later name list is a treadmill (every new tool invents a new config dir). The backstop is the default: *unknown is irreversible*.
- I read six systems closely. The literature is moving fast, and the gaps I name are relative to those six.

---

## 9. Wrapping up

Recent work on agent authority has produced the right pieces without a reason for them to fit together. One definition supplies it: an effect is reversible if the information to undo it stays inside a boundary you control. That decides who may authorize an effect and where the decision has to be made, and from it you get the tiers, the commit point, the residue of compensation, and how to treat run-later writes. What it *doesn't* decide, whether a given "yes" is valid, is exactly what the field has been working out. Once the principle fixes the point, those conditions compose into one check with guarantees you can prove.

The bigger picture is a single stack where boundary engineering, classification, the commit point, the validity of the decision made there, and what happens after are all one design problem, organized by where the information needed to undo an effect lives.

---

## References

<a id="ref-bennett"></a>**Bennett 1973.** Charles H. Bennett. *Logical Reversibility of Computation.* IBM Journal of Research and Development 17(6):525–532, 1973.

<a id="ref-cordon"></a>**Chen et al. 2026.** Zheng Chen, Hanqing Liu, Duling Xu, Dong Dong, Jialin Li, Bangzheng Pu, Jidong Zhai. *Cordon: Semantic Transactions for Tool-Using LLM Agents.* [arXiv:2606.17573](https://arxiv.org/abs/2606.17573), 2026.

<a id="ref-cve2014"></a>**CVE-2014-9390.** Git case-insensitive `.Git` path handling. [nvd.nist.gov/vuln/detail/CVE-2014-9390](https://nvd.nist.gov/vuln/detail/CVE-2014-9390), 2014.

<a id="ref-camel"></a>**Debenedetti et al. 2025.** Edoardo Debenedetti, Ilia Shumailov, Tianqi Fan, Jamie Hayes, Nicholas Carlini, Daniel Fabian, Christoph Kern, Chongyang Shi, Andreas Terzis, Florian Tramèr. *Defeating Prompt Injections by Design* (CaMeL). [arXiv:2503.18813](https://arxiv.org/abs/2503.18813), 2025.

<a id="ref-dobrin"></a>**Dobrin & Chmiel 2026.** Seth Dobrin, Łukasz Chmiel. *The Unfireable Safety Kernel: Execution-Time AI Alignment for AI Agents and Other Escapable AI Systems.* [arXiv:2606.26057](https://arxiv.org/abs/2606.26057), 2026.

<a id="ref-sagas"></a>**Garcia-Molina & Salem 1987.** Hector Garcia-Molina, Kenneth Salem. *Sagas.* Proceedings of the 1987 ACM SIGMOD International Conference on Management of Data, 249–259, 1987.

<a id="ref-khan"></a>**Khan 2026.** Sajjad Khan. *Stop Means Stop: Measuring and Repairing the Enforcement Gap in Agent-Framework Control Primitives.* [arXiv:2607.14166](https://arxiv.org/abs/2607.14166), 2026.

<a id="ref-landauer"></a>**Landauer 1961.** Rolf Landauer. *Irreversibility and Heat Generation in the Computing Process.* IBM Journal of Research and Development 5(3):183–191, 1961.

<a id="ref-mazzocchetti"></a>**Mazzocchetti 2026.** Adam Mazzocchetti. *Runtime Governance for Agentic AI: Action-Boundary Control with Trusted Provenance and Fail-Closed Execution.* [arXiv:2608.16891](https://arxiv.org/abs/2608.16891), 2026.

<a id="ref-saltzer"></a>**Saltzer & Schroeder 1975.** Jerome H. Saltzer, Michael D. Schroeder. *The Protection of Information in Computer Systems.* Proceedings of the IEEE 63(9):1278–1308, 1975.

<a id="ref-santos-commit"></a>**Santos-Grueiro 2026a.** Igor Santos-Grueiro. *Temporary Authority, Permanent Effects: Commit-Time Authorization for LLM Agents.* [arXiv:2607.10487](https://arxiv.org/abs/2607.10487), 2026.

<a id="ref-santos-closure"></a>**Santos-Grueiro 2026b.** Igor Santos-Grueiro. *When Does Authorization End? Effect Closure at Provider Boundaries.* [arXiv:2609.02866](https://arxiv.org/abs/2609.02866), 2026.

<a id="ref-srt"></a>**Anthropic srt.** Anthropic. *Sandbox Runtime (srt).* [github.com/anthropics/sandbox-runtime](https://github.com/anthropics/sandbox-runtime), 2026.

<a id="ref-tallam"></a>**Tallam 2026.** Krti Tallam. *A Five-Plane Reference Architecture for Runtime Governance of Production AI Agents.* [arXiv:2606.12320](https://arxiv.org/abs/2606.12320), 2026.

<a id="ref-zhu"></a>**Zhu & Wang 2026.** Genliang Zhu, Chu Wang. *Authorization for Self-Modifying AI Agent Populations: Conserving Authority across Replacement, Forking, and Rollback.* [arXiv:2610.00347](https://arxiv.org/abs/2610.00347), 2026.

<a id="ref-willison-dual"></a>**Willison 2023.** Simon Willison. *The Dual LLM pattern for building AI assistants that can resist prompt injection.* [simonwillison.net/2023/Apr/25/dual-llm-pattern](https://simonwillison.net/2023/Apr/25/dual-llm-pattern/), April 2023.

<a id="ref-willison-trifecta"></a>**Willison 2025.** Simon Willison. *The lethal trifecta for AI agents: private data, untrusted content, and external communication.* [simonwillison.net/2025/Jun/16/the-lethal-trifecta](https://simonwillison.net/2025/Jun/16/the-lethal-trifecta/), June 2025.
