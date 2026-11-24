# Let reversibility decide who decides

*A working paper on authority for AI agents, written informally.*

Travis Pinney · November 2026

---

## TL;DR

AI agents now do things that matter: send email, move money, push code, write files that other programs run later. 2026 produced a burst of good work on governing that: compensability classes, commit-time authorization, effect closure at provider boundaries, transactional runtimes, barrier semantics for approval gates, authority conservation across forking agents, and, most recently, reversibility classes that gate actions. Each is a real piece.

This paper argues that one question organizes them:

> **Can you still prevent this effect, or put things back, from inside a boundary you control?**

If you can, the effect is reversible relative to that boundary and the agent can be left to decide; you can review and undo afterwards. If you can't, the decision is final the moment it's made, so it has to be made by someone entitled to make final decisions, at the point where the effect crosses the boundary.

**Others already use irreversibility this way.** Magentic-UI's action guard sends actions a developer marks as irreversible to the user for approval, runs ones marked never irreversible automatically, and has an LLM judge decide the cases in between. Tallam sorts actions into compensability classes, Cordon holds external effects in an outbox until commit, and Waghmare & Sufi define reversibility classes that gate actions.

**What's here:**

1. **A boundary-relative, preventability-based definition** (§2), stated once, with what it decides and what it doesn't.
2. **A reading of recent work as one stack** (§4). The definition explains *where* each system puts its check. What each one adds is a condition for an approval to be *valid* at that point.
3. **A small Lean 4 model** (§6) that puts six of those conditions at one commit point and proves they compose, with tiers assigned by the owner and approvals bound to a single effect. It comes with an independent implementation and mutation-tested fixtures. It proves the authorization machinery *given* the owner's classification, not the classification itself.
4. **Run-later writes as a worked case** (§7): files that something outside the sandbox executes later, and a two-layer defense.

There is no attack benchmark or user study here. §9 says what evaluation would have to show.

---

## 1. Who decides?

An agent that can act in the world holds authority, so every deployment has to answer *who decides*. When can the agent just go, when does a rule decide, and when does a person have to?

Deployed systems answer with a mix of mechanisms:
- permission modes (ask for everything, auto-accept edits, bypass);
- per-tool allowlists and deny lists;
- approval prompts on tools marked dangerous;
- OS sandboxes for shell commands;
- a one-time "trust this project" prompt.

Recent research systems add commit-time checks, transactional outboxes, and reversibility classes.

These work, but they're usually justified case by case: this tool is dangerous, that directory is sensitive. The question this paper asks is whether one reason can say, for a new action nobody has listed yet, which side of the line it falls on, and why the line is there.

The 2026 pieces this builds on:

- **Tallam** names a point of no return and sorts actions into compensable, partially compensable, and non-compensable [[Tallam 2026]](#ref-tallam).
- **Cordon** wraps an agent task in a semantic transaction: local effects stay reversible, external ones wait in an outbox until a commit-time check of the composed flow [[Chen et al. 2026]](#ref-cordon).
- **Santos-Grueiro** shows authorization has to be checked at the atomic commit point of the exact effect [[Santos-Grueiro 2026a]](#ref-santos-commit). It isn't over until in-flight work can no longer reach a rejected effect [[Santos-Grueiro 2026b]](#ref-santos-closure).
- **Khan** tests control primitives in six agent frameworks; in the five that ship a pre-execution approval gate, a pause holds only the branch that asked, so a sibling's effect lands anyway [[Khan 2026]](#ref-khan).
- **Zhu and Wang** mediate registered protected effects through an external protocol with atomic commits, and show that when agents fork, authority has to be *reallocated*, not copied [[Zhu & Wang 2026a]](#ref-zhu). Their follow-up makes revocation quiesce across delegation and provider boundaries [[Zhu & Wang 2026b]](#ref-zhu-revocation).
- **Waghmare and Sufi**, concurrently, define a five-level reversibility vocabulary and a session guard that raises calls to the top level when needed [[Waghmare & Sufi 2026]](#ref-waghmare).

---

## 2. The lens

### One definition

The same `DELETE` is reversible on a snapshotted database and irreversible on one with no backup. So reversibility isn't a property of an action alone. It's a property of an action *relative to a boundary*: the part of the world whose state and history you control.

> **Definition.** An effect is *reversible* relative to a boundary *B* if, acting only inside *B*, you can still either prevent it or restore the state that matters to what it was, **before anything outside *B* that you don't control acts on it**. Otherwise it is *irreversible* relative to *B*.

Four notes on reading it:

- **Prevent or restore.** An email in your drafts folder is reversible: you can still not send it. A sent email isn't: you can't prevent delivery any more, and you can't restore the recipient's inbox. An effect can also be past the point of no return before anyone sees it. Once a provider has durably accepted a message it hasn't delivered yet, you've lost the ability to prevent it, though nobody has observed anything. That's why the test is about control, not observation. Santos-Grueiro's effect frontier, which "may precede return, declared completion, or visibility" [[Santos-Grueiro 2026b]](#ref-santos-closure), makes the same point.
- **"Before anything outside acts on it."** The timing clause is what makes a planted git hook irreversible even though you could, in principle, delete it tomorrow. The hook fires on your next `git commit`, and nobody schedules that around the agent's writes. Being able to restore a file later doesn't help once something outside the boundary has already run it. What matters is whether the undo can happen first.
- **"The state that matters."** Undoing a file edit from a checkpoint leaves a log entry saying you did. That doesn't make the edit irreversible: the audit log isn't part of the state anyone depends on. Which state matters is part of drawing the boundary.
- **The information intuition.** A useful way to think about it comes from reversible computing. A computation can be inverted exactly when it doesn't erase information, and you can make any computation invertible by keeping a record of its history and later running it backwards [[Landauer 1961]](#ref-landauer), [[Bennett 1973]](#ref-bennett). Keeping the information needed to undo an effect inside the boundary is *necessary* for reversibility. It isn't sufficient: you also need the control to use it. The definition above is the control version.

**Who draws the boundary.** Choosing *B*, and the tier map that follows from it, is itself an act of authority. It belongs to the owner of the resources, not to the agent. A boundary the agent can redraw (by editing the sandbox config, the tier map, or the trust list) isn't one. Much of §7 is about exactly that.

### Who decides: tiers

Most real agent actions are neither cleanly reversible nor hopelessly final. A refund can't undo a charge, but it can counteract it; a cancellation can't unsend an invite, but it can withdraw it. That's the saga pattern from databases [[Garcia-Molina & Salem 1987]](#ref-sagas): when you can't roll back, you define a compensating action. So there are three classes, ordered by how much of the decision is still open afterwards:

| Class | Meaning | Who decides | Mode |
|---|---|---|---|
| Reversible | Can be prevented or restored from inside the boundary | The agent | Act, log, allow appeal |
| Compensatable | Can't be undone, but a declared action counteracts it, with a bounded, known cost | Policy | Act within policy limits; outside them, escalate |
| Irreversible | No restoration, no adequate compensation | A human with authority | Decide before, or grant in advance |

The reasoning for the two ends is short. A decision carries authority to the extent it can't be undone. If an effect can be reversed, the agent's judgement can be reviewed and fixed afterwards, so the agent may decide. If it can't, the decision is final when made, so it has to be made by whoever is entitled to make final decisions about that resource.

The middle tier needs one more assumption, and it's worth being explicit. Compensation is an argument for *policy* deciding only when the harm is bounded and priced in advance: a refund up to some amount, an invite that can be cancelled before the meeting. That is what lets a rule, written ahead of time, stand in for a person. "Compensatable" without a declared compensation is treated as irreversible. The bound is the policy's job: a rule can cap an amount per action (`amountAtMost`), and in the composed system the root budget caps the total. The model doesn't check that every compensatable action has a bound.

Two honest caveats:
- **Finality triggers escalation, but it doesn't settle everything.** A reversible action can still be catastrophic while it lasts, and an irreversible one can be trivial (an unobservable log line). Magnitude and observability matter too; the tiers are where the conversation starts.
- **In the Lean model the rule is binary.** The fixed decision procedure requires approval for irreversible effects and lets policy rules decide everything else; "reversible is the agent's call" is a policy rule the owner writes (`reversible-ok`). The three tiers describe how the owner is expected to write policy, not three code paths.

### Where: the commit point

If finality is what demands authority, the decision belongs where the effect becomes final: where it crosses the boundary. Push that point as late as you can, make everything before it reversible (sandbox, dry run, staging, two-phase commit), and put the strictest decider there. Two-phase commit becomes separation of duties: the agent prepares, the authority commits.

Actions also move between tiers. Sandboxing and staging turn irreversible actions into compensatable or reversible ones by moving the boundary. **You shrink the human tier by engineering reversibility, not by trusting smarter models.**

### What the lens suggests

These aren't derivations. Each needs an extra assumption, listed in the right-hand column. But they all fall out of asking the one question.

| Consequence | Why, through the lens | Also needs |
|---|---|---|
| Commit point | The crossing is where a decision becomes final, so that's where the decider goes | Complete mediation at the crossing |
| Unknown is irreversible | Without evidence that you can still prevent or restore, assume you can't | Fail-safe defaults |
| Compensation ≠ undo | Compensation counteracts a quantity; the effect and its counteraction both remain | A notion of which state matters |
| Run-later writes | A later interpreter outside the boundary is a crossing the writer doesn't schedule | Knowing what runs which files |
| Inner/outer enforcement | Enforce where effects actually cross (OS); decide with semantics where calls are legible (gate) | A sandbox that enforces on resolved names |
| Observable actions under exposure | Observation is one way information crosses; once a session holds private data and untrusted input, anything observable may carry it out | A confidentiality goal; labels on what was read |
| Sandbox, staging, 2PC | They move the boundary, and so move actions down a tier | That the staging area is really inside the boundary |

**Compensation isn't restoration.** A compensating action restores a targeted quantity, not the state. The ledger in this repo's toy world makes the point concrete: refund then charge back, and the balance returns but the statement now has two more lines (`compensation_leaves_residue` in Lean). Taken alone that's an illustration, not a deep result: in an append-only ledger, nothing appended can remove what's already there. The formal treatment of compensation as something weaker than undo goes back to Korth, Levy and Silberschatz [[Korth et al. 1990]](#ref-korth). The lens adds only why it matters for authority: a compensating action doesn't make the original decision reviewable, so it doesn't by itself license leaving that decision to the agent.

**Observable actions under exposure.** Private data, untrusted input, and a way to communicate out is Simon Willison's "lethal trifecta" [[Willison 2025]](#ref-willison-trifecta). Meta's "Agents Rule of Two" turns it into a design rule: within a session an agent should have at most two of untrustworthy input, access to sensitive systems or private data, and the ability to change state or communicate externally, and otherwise needs supervision [[Meta 2025]](#ref-rule-of-two). Here "observable" means an outward channel: someone outside can see that the action happened or what it carried. That's a different sense from the observation in the definition's first note. Through the lens, information leaving through such a channel can't be brought back, so it's a crossing. Requiring untrusted input as well as private data before escalating isn't something the lens implies; it's a threat-model choice taken from the trifecta. With that choice, once a session has seen both, every observable action is treated as irreversible and needs approval. Between contexts, a *structured* result (a boolean, an enum) can't carry instructions, so it stops untrusted taint where free text wouldn't. That's the idea behind the Dual LLM pattern [[Willison 2023]](#ref-willison-dual) and CaMeL [[Debenedetti et al. 2025]](#ref-camel).

### What the lens doesn't decide

The lens decides *where* authority has to be exercised and *who* has to exercise it. It does **not** decide whether a particular "yes" is valid. An irreversible action with an approval attached passes the tier rule even if that approval:
- was revoked an hour ago;
- was for a different amount, or a different request that looks the same;
- came from someone with no authority over the resource;
- got copied into five forked sub-agents;
- was granted while a sibling branch had already acted.

Those form a second, orthogonal axis: the classic conditions on a valid authorization [[Saltzer & Schroeder 1975]](#ref-saltzer). The lens doesn't derive them. It tells you where they all have to be checked. That second axis is where most recent work has concentrated.

---

## 3. Threat model and what's trusted

**Adversary.** Any of:
- the model, steered by prompt injection;
- a malicious repository or document the agent reads;
- a malicious sub-agent.

The adversary can propose any tool call with any arguments, including a claimed tier and paths spelled any way the tool accepts. In the sandbox it can run any shell command.

**Trusted (the TCB).**
- **The gate:** the decision procedure and commit-time check, the approval store, and the delegation record. These run outside the agent's reach.
- **The owner:** writes the policy and the tier map, draws the boundary, and is the root of delegation. Only authenticated principals grant approvals, delegate, or revoke; agents only propose.
- **The OS sandbox:** enforces deny rules against the file a path resolves to, at any depth, as configured.
- **Provider mediation:** the mediator can drop in-flight carriers at the provider, which is what makes revocation drain.
- **Atomicity:** each operation (propose, approve, commit, dispatch) happens atomically.
- **The trace writer:** for audit to mean anything against a hostile agent, it sits outside the sandbox.
- **Human approvers:** they decide honestly on what they are shown.

**Non-goals.**
- Closing covert channels; they're counted, not closed.
- Approver deception and approval fatigue; see §9.
- Kernel or sandbox bugs.
- Correctness of the tier map itself. A mislabeled action is the owner's error, and the defaults (unknown is irreversible, observable unless declared otherwise) only limit the damage.

**Which guarantee needs what.** Every row also assumes atomic operations and a gate and approval store outside the agent's reach.

| Guarantee | Further assumptions it rests on |
|---|---|
| Every landed effect traces to a passed check (§6, item 1) | Provider mediation is complete: nothing reaches the provider except through the gate |
| Irreversible effects that land were approved for that effect (item 2) | Only authenticated principals approve; the gate, not the agent, assigns effect ids. (The owner's tier map being right affects what "irreversible" covers, not whether the guarantee holds.) |
| Revocation drains in-flight work (item 3) | Provider mediation is complete |
| At most once; rejected never lands; cancel fences (item 4) | The gate, not the agent, decides which run a call belongs to |
| A held run commits nothing while waiting (item 5) | Same |
| Single use, and spending within the root budget (item 6) | The gate assigns each effect to the agent that proposed it |
| No authority beyond the root's (item 7) | Only authenticated principals delegate |
| Run-later writes are blocked or asked (§7) | Sandbox enforces on resolved names; the run-later list covers what actually runs later |
| Logged decisions are consistent with the config and replay | Trace written outside the sandbox, append-only. The audit catches inconsistent entries, not deleted or consistently rewritten ones |

---

## 4. Recent work through the lens

I read six 2026 systems in full and asked two questions of each: what does the lens say it's doing, and what does it add that the lens doesn't derive? Five put an explicit check at a point of no return for agent actions; Zhu and Wang's conservation paper is included for what it adds to the validity axis. The claims in this section are about these six; §8 positions against the rest.

| System | Where it checks (lens reading) | What it adds (validity axis) | Evidence |
|---|---|---|---|
| Tallam [[ref]](#ref-tallam) | MP5, "externally observable, side-effecting, or otherwise difficult to compensate"; three compensability classes | Capability attenuation along delegation; scoped approval | Argued; reference policy core |
| Cordon [[ref]](#ref-cordon) | Shadow state keeps local effects reversible; outbox holds external ones that "may cross an irreversible boundary" | Lineage from secrets/untrusted input to sinks; transaction-scoped approval; one validity check of the composed flow at commit | Prototype; 45 workflows |
| Santos-Grueiro, commit-time [[ref]](#ref-santos-commit) | The commit boundary, "the last point where the system can withhold" the effect | Approval current at commit and bound to the exact effect | Lean (139 theorems); measured |
| Santos-Grueiro, effect closure [[ref]](#ref-santos-closure) | The effect frontier, which "may precede return, declared completion, or visibility" | Drain in-flight work after revocation; idempotent binding | Lean; Kafka/NATS/K8s |
| Khan [[ref]](#ref-khan) | Execution, the point past which a tool can't revoke | Barrier semantics: a hold covers the whole run; at-most-once; cancel fences | 1,200 live runs; Verus, TLA+ |
| Zhu & Wang [[ref]](#ref-zhu) | An external protocol's atomic commit for registered protected effects | Authority conserved, not copied, across forks, replacement and rollback | Prose proofs; checked corpus |

**Tallam: compensability classes at a mediation point.** The five-plane architecture puts its action-commit mediation point where a call becomes "externally observable, side-effecting, or otherwise difficult to compensate," and sorts actions into compensable, partially compensable, and non-compensable, with the last needing explicit authorization. That's the commit point and the tiers. The taxonomy gets a paragraph, with whether an inverse operation can restore the external state as its criterion. Tallam's main contributions are elsewhere:
- capability attenuation along delegation chains, where each delegate's capability is a subset of its delegator's;
- time-bounded capabilities;
- approvals bound to capabilities rather than action signatures.

**Cordon: the boundary, built, and checked in one place.** Cordon makes each agent task a semantic transaction:
- local mutations go to shadow state and can be rolled back;
- external effects wait in an outbox "because their release may cross an irreversible boundary";
- commit validates the composed flow first.

This is the closest prior system to the picture in §5. It builds the boundary in software, down to classifying the final output to the user as an effect object, and it checks its conditions together, at one commit. Its conditions are flow rules: secret-derived data can't reach an unauthorized sink, untrusted input can't justify a sensitive write, and an approval binds to one transaction. Authority is scoped per transaction; it doesn't model concurrency between branches, conservation across forks, delegation chains or attenuation, or what happens after commit at the provider.

**Santos-Grueiro: the check at the crossing, and how long it lasts.** Commit-time authorization needs a complete, current justification for the exact effect at its atomic commit point, "the last point where the system can withhold it." The lens explains why the check goes there. It doesn't explain the rest, and the paper's evidence shows the rest matters: 12 of its 17 advisories involve no intervening change at all. They're failures of *binding*, not timing.

Effect closure pushes this past the commit: authorization ends only when issuance stops *and* nothing in flight can still reach a rejected effect. Its line that "later abort, compensation, or reconciliation cannot erase a violation; prevention must act before" the frontier is the commit point and the compensation point together, in one sentence.

**Khan: the hold has to cover the whole run.** Khan tests control primitives in six agent frameworks. In the five that ship a pre-execution approval gate, a pause only holds the branch that asked: 215 of 1,200 live-model runs leak a sibling's effect while the human is still deciding. The lens explains the scope ("irreversible or externally committed" actions, executed at the point the tool can no longer revoke them) but says nothing about concurrency. Khan adds barrier semantics and a verified out-of-process gate:
- no gated effect of a paused run executes;
- rejected effects never execute;
- each effect executes at most once;
- cancellation fences late work.

**Zhu and Wang: conservation.** Their protocol mediates registered protected effects with atomic commits. For self-modifying agent populations, treating each fork as a fresh copy of its parent's grant "silently multiplies budgets, concurrency slots, approval weight, and effect combinations." Their principle: "a fork reallocates existing authority instead of copying it." Their rollback is rollback of the agents themselves, not of effects in the world. This is the cleanest property on the second axis alone: the tiers assume one agent, and nothing about reversibility says an approval can't be duplicated across children. Their follow-up on revocation [[Zhu & Wang 2026b]](#ref-zhu-revocation) composes delegation root cuts with provider-frontier certificates, which overlaps the delegation-drain result in §6.

**What the lens shows.** Each puts its check at the boundary crossing, though each calls it something different (mediation point, outbox, commit boundary, frontier, admission point, protocol commit). Each then adds one or two validity conditions, justified on their own terms. Cordon checks its conditions together at one point.

---

## 5. One picture

### The field as a stack

Put the pieces together and agent authority looks like a stack of five layers. Each answers one question, and each line of work has concentrated on one or two. Seen this way, the systems above aren't competing designs; they're contributions to different layers.

| Layer | Question | Where the work sits |
|---|---|---|
| 1. Boundary engineering | How much can we make reversible? | Sandboxes, shadow state and outboxes [[Cordon]](#ref-cordon), undo and damage confinement [[GoEX]](#ref-goex), pre-destructive snapshots [[Parallax]](#ref-parallax), staging, two-phase commit; the outer OS floor here |
| 2. Classification | Which tier is this effect in? | Compensability classes [[Tallam]](#ref-tallam); reversibility classes [[Waghmare & Sufi]](#ref-waghmare); the tier map, run-later rule, and exposure rule here |
| 3. The commit point | Where must the decision be made? | Mediation point [[Tallam]](#ref-tallam), commit boundary [[Santos-Grueiro a]](#ref-santos-commit), effect frontier [[Santos-Grueiro b]](#ref-santos-closure), admission [[Khan]](#ref-khan) |
| 4. Validity at the point | Is this particular "yes" valid? | Currency and binding [[Santos-Grueiro a]](#ref-santos-commit), [[Kodathala et al.]](#ref-approve-what); attenuation [[Tallam]](#ref-tallam); conservation [[Zhu & Wang a]](#ref-zhu); barrier [[Khan]](#ref-khan); information flow [[Cordon]](#ref-cordon), [[FIDES]](#ref-fides); privilege policies [[Progent]](#ref-progent) |
| 5. After the point | What happens once it's crossed? | Drain and bind [[Santos-Grueiro b]](#ref-santos-closure), [[Zhu & Wang b]](#ref-zhu-revocation); deciding whether saved state can be resumed [[Zhang & Liu 2026]](#ref-recoverability); compensation; audit |

Layer 1 decides how much of the world the agent can change freely. Layer 2 says which effects are left. Layer 3 puts the decision where each of those becomes final. Layer 4 makes sure the decision taken there is a real one, and layer 5 makes sure it stays in force. The lens suggests the order for layers 1 to 3: each is about where the ability to prevent or restore an effect is lost.

### Checks at one point

Once *where* (the crossing) and *who* (by tier) are fixed, the validity conditions can all be checked there. Here's the path an effect takes in the model:

```
 agent proposes effect e in run r (any claimed tier is ignored)
   |
   v
 gate binds e to its proposal's id, classifies it from the owner's tier map
   |
   v
 policy + tier ------- deny --------> dropped
   |  allow            | ask
   v                   v
 run barrier: while an effect of r awaits a human, r is held  [Khan]
   |  released
   v
 ONE commit-time check, judged on the state at this moment:
   - policy decision for e (irreversible needs an approval)
   - approval granted for e itself, unexpired, unrevoked, unused  [Santos-Grueiro]
   - approver holds authority over e via an attenuated chain      [Tallam]
   - proposing agent's budget covers e (forks split, not copy)    [Zhu & Wang]
   |  pass: consume approval, spend budget, write audit record
   v
 provider: carrier tagged {approval, delegation chain}
   - revoking any tag fences the carrier in flight                [Santos-Grueiro]
   - each idempotency key lands once, despite redelivery
   v
 effect lands
```

Each bracketed condition comes from the cited work. There are really two enforcement sites:
- **the commit-time check**, where every condition is a clause of one predicate;
- **the frontier fence at the provider**, which drains in-flight work after a revocation.

The fence is load-bearing: remove it, and revoked work that was already dispatched still lands. Only the provider's own refusal to *dispatch* under a revoked tag is redundant, as §6 shows.

Three choices make the composition work:
1. **Every effect leaving the barrier goes through the same check,** including siblings released after a decision. Nothing is waved through because it was allowed earlier.
2. **The tier and the approval binding are the gate's, not the proposer's.** The gate classifies from the owner's map and binds the request to its proposal's effect id, and an approval is granted for one effect id. (In the model the id arrives with the proposal; the threat model assumes the gate, not the agent, assigns it.) So an identical-looking request, say from a forked sub-agent, can't consume it. This is the binding problem Santos-Grueiro's advisories show, and the one Kodathala et al. address with effect descriptors [[Kodathala et al. 2026]](#ref-approve-what).
3. **The carrier is tagged** with the approval it used *and* the delegation chain behind the approver's authority. Revoking any of them, even a delegation two levels up, drains the effect, even in flight.

**What this does and doesn't cover.** The decision core (§6) also has the exposure rule and the trace. The composed system does *not* include them: its classification is the owner's static tier map, without session exposure. Information flow sits in layer 4 because systems like Cordon and FIDES put it there, not because this model checks it.

---

## 6. The Lean model

Each component and the composed system are specified and proved in Lean 4 (the `FinalSay/` folder); the lens itself is not. It's small on purpose: a reference semantics, not an implementation.

**What is and isn't formalized.**
- **Not formalized: the definition in §2.** The model has no notion of a boundary or of what can be prevented or restored. Tiers are a label the owner supplies.
- **Proved: the authorization machinery, given those labels.** If the owner's map says irreversible, then everything below holds, whatever the agent claims.
- **The theorems hold for every policy in the rule language and every sequence of atomic operations.** They depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorry`.
- **Operations aren't authenticated in the model.** Any operation can be issued. The guarantees are meaningful under the threat model's assumption that only authenticated principals issue grants, delegations and revocations, and agents only propose.

| Module | Headline theorems | Property (source) |
|---|---|---|
| `Core`, `Invariants` | `deny_wins`, `irreversible_needs_approval`, `no_rule_asks`, `unknown_is_irreversible`, `malformed_never_allowed` | Fixed decision order no policy rule can override; fail closed |
| `Invariants` | `trifecta_needs_approval` | The exposure rule, after Willison's trifecta [[Willison 2025]](#ref-willison-trifecta) |
| `World` | `compensation_leaves_residue`, `compensation_is_not_undo` | Illustration of compensation ≠ undo |
| `Authority` | `irreversible_commit_exact_current`, `revocation_is_effective`, `single_use_at_most_once`, `decision_before_commit_goes_stale` | Currency, binding [[Santos-Grueiro a]](#ref-santos-commit) |
| `Conservation` | `budget_conserved`, `grant_used_at_most_once`, `copy_on_fork_overspends` | Conservation [[Zhu & Wang a]](#ref-zhu) |
| `Delegation` | `no_amplification`, `links_attenuated`, `revocation_cascades`, `irreversible_commit_authorized` | Attenuation [[Tallam]](#ref-tallam) |
| `Barrier` | `barrier`, `rejected_never_lands`, `lands_at_most_once`, `cancel_fences_run`, `per_branch_pause_leaks` | Barrier semantics [[Khan]](#ref-khan) |
| `Frontier` | `revocation_drains`, `key_lands_at_most_once`, `in_flight_outlives_revocation` | Drain, bind [[Santos-Grueiro b]](#ref-santos-closure) |
| `System` | `run_sim`, `landed_was_committed`, `irreversible_landed_authorized`, `landed_classified_and_bound`, `delegation_revocation_drains_system`, `barrier_system`, `committed_within_budget`, `committed_never_refused_at_dispatch` | The composition |

For every policy and every sequence of proposals, decisions, grants, revocations, delegations, forks, clock ticks, deliveries, and redeliveries, the composed system guarantees:

1. every effect that lands traces to an audit record of a passed check;
2. an irreversible effect that lands (irreversible by the *owner's* classification, whatever the proposer claimed) was backed, at commit, by an approval granted for that effect id, unexpired, unrevoked, from someone holding authority over it within the root's scope, and its carrier names that approval and chain;
3. once an approval or a delegation is revoked, nothing it backed lands, whether in flight, redelivered, or attempted later;
4. each effect lands at most once; rejected effects never leave the barrier; a cancelled run commits nothing further;
5. while a run is waiting on a human, only a decision on that run commits anything of it;
6. each single-use approval backs at most one commit, and the total committed amount never exceeds the root budget, however agents fork;
7. nobody ever holds authority the root didn't have.

**Composition by simulation.** The composed system holds each component's state and changes it only through that component's own transition function. `run_sim` proves that in any run, the gate, delegation record, provider, and agent population are each a run of their own model, so their theorems hold inside the system unchanged. The approval store isn't in the simulation relation: its properties (single use, revocation) are re-proved at system level. The end-to-end results need a little glue: an invariant tying landed carriers to audit records, records to the state they were judged in, proposals and records to the owner's classification and their own effect id, and spent budget to the committed total.

**Counterexamples.** Each component also proves, by computation, that the obvious weaker design fails:

- a decision taken before revocation allows what the commit-time check refuses;
- copy-on-fork spends twice the grant;
- a per-branch pause lands a sibling mid-decision;
- refusing new dispatches lets in-flight work land after revocation;
- without binding to the key, redelivery lands twice;
- an approval from a sub-agent with no authority passes the currency check on its own;
- a proposer claiming "reversible" for a refund, under a policy that allows anything reversible, gets nothing landed without approval (`spoofed_tier_ignored`);
- an approval granted for one refund isn't consumed by an identical second one (`approval_not_captured`).

**Conformance and mutation testing.** Lean exports 1,219 cases with expected outcomes:
- 602 for the decision core;
- 617 traces of the composed system: 17 named scenarios plus 600 from a fixed seed, some of which propose with the wrong tier.

A second, standard-library-only Python implementation reproduces all of them (`examples/python/`). Two caveats on what that shows:
- I wrote it from the spec myself, so it isn't independent in the strong sense.
- The fixtures come from Lean's executable definitions, so agreement shows the two implementations match those definitions. It doesn't check the theorems.

A passing corpus tells you nothing until you've seen it fail. So I broke one guarantee at a time in the Python implementation and counted the cases that noticed:

| Broken guarantee | Failing | Broken guarantee | Failing |
|---|---|---|---|
| Approver authority | 216 | Approval not bound to the effect | 82 |
| Provider fence | 194 | Attenuation | 77 |
| Run barrier | 129 | Fork conservation | 71 |
| Revocation cascade | 82 | Idempotency bind | 66 |
| Proposer's claimed tier trusted | 59 | Single use | 9 |
| Expiry ignored | 1 | Provider refusal at dispatch (equivalent) | 0 |

These are hand-picked mutants, one per guarantee, not a systematic mutation of every clause. Expiry is caught by a single case, so that part of the corpus is thin.

The one mutant that fails no cases is the provider ignoring revoked tags at dispatch. The commit-time check has already refused anything a revoked approval or delegation backed: `committed_never_refused_at_dispatch` shows that the refusal never fires in any reachable commit. That theorem doesn't yet state the stronger claim that the two designs are observationally equivalent.

Several of these properties are already machine-checked in the work they come from: in Lean [[Santos-Grueiro a]](#ref-santos-commit), and in Verus and TLA+ [[Khan]](#ref-khan). The models here are small so they can be composed.

---

## 7. Run-later writes

The lens predicts something specific, through the definition's timing clause: a write is irreversible when something outside the boundary will execute it before you can undo it. This is worth dwelling on, because it's the effect that's easiest to miss.

Coding agents typically run model-chosen shell commands inside an OS sandbox (Seatbelt on macOS, bubblewrap and seccomp on Linux). Writes are confined to the workspace, there's no network by default, and a few paths are held read-only. The question is *which* paths. Plenty of files in a workspace are executed later by something that isn't sandboxed:

- git hooks and `.git/config` (`core.fsmonitor`, aliases), which run on your next `git commit` or `git status`;
- CI workflows, editor tasks, `.envrc`, pre-commit configs;
- any agent's own project config dir (`.codex`, `.cursor`, `.agents`, `.claude`, `.pi`, `.opencode`, …), which may define hooks or MCP servers that start next session;
- and, less obviously, ordinary source: Makefiles, `package.json` scripts, test files, anything in `node_modules/.bin`.

A sandboxed write to any of those is a crossing the writer doesn't schedule: a checkpoint could restore the file, but only after the hook or the CI job has already run it. It looks local and reversible, but the effect lands later, on the host, with your full permissions. This class is well known. Git itself fixed a version of it in 2014: a `.Git/config` path got past Git's own `.git` checks on case-insensitive filesystems [[CVE-2014-9390]](#ref-cve2014). Agent sandboxes have shipped fixes for git-hook and git-config routes since.

Two mistakes keep producing it, and both are boundary mistakes.

1. **The protected set is drawn too small.** Protecting `<root>/.codex` instead of *any* `.codex` means a nested one is, by the sandbox's own policy, a permitted write.
2. **Protection is matched against the name, not the file.** Policies are written in names ("deny writes to `.git`"), but the filesystem decides which file a name refers to.
   - On the default macOS and Windows filesystems, `.git/config`, `.Git/config` and `.GIT/config` are the same file.
   - A symlink can make `notes/hooks` mean `.git/hooks`.
   - Tools add their own spellings: pi strips a leading `@` and expands `~`.
   - So a guard that blocks any path containing `.git/` lets `.GIT/hooks/pre-commit`, a symlink into `.git`, or `@.git/hooks/pre-commit` straight through.

   The rule was right; what it got applied to wasn't. The component that resolves the name is the one actually deciding, so enforce there. A kernel sandbox checks the file a path resolves to. If a check has to work on strings, resolve the name exactly as the tool will: make it absolute, follow symlinks, fold case, match whole path segments. Then make the tool open exactly the path you checked. Treat a name you can't resolve with certainty like any other unanticipated case, and escalate it.

It's worth looking at where vendors draw their own line. When a sandbox failed to protect a file it promised to protect, that was treated as a real bug and fixed. Examples are git hooks, or a git config key that runs on the next `git status`.

But public bug-bounty scope rules also say an attack is out of scope if it:
- "depends on the client processing a repository or other file";
- needs to get past a "trust this project" prompt;
- or only uses "actions allowed by the active configuration."

The authority boundary, in other words, is the one-time trust prompt, and what a trusted project contains is accepted risk. Both halves are coherent: a sandbox's guarantee is exactly the set of things it commits to defending. That's the same move as the rest of this paper. *Reversible relative to what boundary* is itself a decision, made the moment a system declares a trust boundary. A reversibility-based layer re-examines, at each write, a trust that was granted once and never revisited.

**The defense the lens suggests.** Classify run-later writes as irreversible, and enforce where effects cross:

- **Outer floor (OS sandbox).** Deny run-later names at any depth and by resolved name. In `srt` [[Anthropic srt]](#ref-srt) that means depth-independent globs like `**/.git`, `**/.codex`, … instead of root-relative names. This covers the shell, which no tool-level gate can see.
  - The policy in `experiments/wrapper/` is generated from a list in Lean (`FinalSay/SrtConfig.lean`). The Lean proofs show the rendered globs implement the same segment predicate as the list, at any depth and under ASCII case folding. That's correctness of the generator, not of the list or of `srt`. Writes are allowed only inside the project, not in `/tmp`, which the checkpoint doesn't cover.
  - Whether `srt` enforces globs that way is a trusted assumption, checked by `experiments/wrapper/probe.sh`. For every listed name, it writes at the root, two levels down, and in upper case, then checks `/tmp`, `$HOME` and an ordinary write. On macOS all 42 probes of the generated policy behave as expected, and all 54 of the pi example's config. It hasn't been run on Linux, or with real agents under the policy.
- **Inner gate (typed tools).** Classify the same writes as irreversible and *ask* instead of refusing. That matters because the outer layer is blunt: it would also deny a legitimate edit to `.cursor/rules`. The pi extension in `examples/pi/` does this:
  - it resolves paths exactly as pi does, then follows symlinks, folds case and matches whole segments;
  - it pins the tool call to the real path it classified, which covers pi's own path rewriting. A symlink created in the not-yet-existing part of the path between decision and write is still a race, which the OS sandbox covers;
  - it treats writes outside the project, and inside git repos nested in it (which the checkpoint can't restore), as irreversible.

  It implements the decision core (invariants 1–5), not the composed system.

**Limits of the run-later list.** It under-approximates the principle, and it's a treadmill: every new tool invents a new config dir. The pi gate treats a write inside the project to a name not on the list as reversible, because a checkpoint can undo it. By the timing clause, that holds only if nothing outside the sandbox runs the file first. The checkpoint can restore a `.cursor` file just as well as a source file. The difference is when the trigger fires: agent config runs at the next session start, git hooks on the next commit, and source files whenever someone builds. Source files, Makefiles and test files are reversible only if whatever runs them runs inside the sandbox too, or after a checkpointed review. That holds in the setup described in `examples/pi/`, not in general.

---

## 8. Related work

§4 covers the six systems closest to this. Beyond them:

**Reversibility and approval, directly.**
- **Waghmare and Sufi** (concurrent) define a declared five-level reversibility vocabulary (R0 to R4) for agent actions. Their session guard raises an egress-capable call to R4 once the session has read data, unless every destination is allow-listed. It gated the relevant action in all 29 attributable attack runs while adding nine approval points across 1,209 benign runs [[Waghmare & Sufi 2026]](#ref-waghmare).
- **GoEX** argues for "an intuitive undo feature" and "damage confinement" for LLM-generated actions, with validation after the fact rather than review before [[Patil et al. 2024]](#ref-goex). Through the lens, it moves the boundary (layer 1) so more actions become reversible.
- **Parallax** captures pre-destructive state for rollback when an automated validator fails [[Fokou 2026]](#ref-parallax): layer 1.
- **Recoverability as a system primitive** makes reuse of saved agent state an explicit decision for long-horizon agents, and holds back continuation while effects are unresolved [[Zhang & Liu 2026]](#ref-recoverability): closer to layer 5.
- **Magentic-UI** is the clearest deployed instance of reversibility deciding who approves [[Mozannar et al. 2025]](#ref-magentic). Its action guard (§6.4) exists "to ensure that any irreversible or potentially harmful agent actions are reviewed by the human user before being executed". The developer marks each action type as always, maybe, or never irreversible. "Always" goes to the user, "never" runs automatically, and an LLM judge decides whether a "maybe" needs approval. In terms of the stack in §5, that's layer 2, with a human at the irreversible end.

**What an approval binds to.** "Approve What, Exactly?" argues that an approval must "name exactly what it approves." The gateway renders the approval from a canonical effect descriptor and executes only the stored call [[Kodathala et al. 2026]](#ref-approve-what). That's the effect binding in §5, built and rendered for a human.

**Revocation and authority across agents.** Zhu and Wang's work on revocation for long-running agents composes delegation root cuts with provider-frontier certificates [[Zhu & Wang 2026b]](#ref-zhu-revocation). The delegation drain in §6 is a small instance of the same idea.

**Agent security by design.**
- The lethal trifecta [[Willison 2025]](#ref-willison-trifecta) names the condition the exposure rule escalates on, and the Agents Rule of Two [[Meta 2025]](#ref-rule-of-two) makes it a design rule. Waghmare and Sufi's session guard is a working instance of the same escalation. The exposure rule here is the same idea applied per action: under all three, observable actions need a human.
- The Dual LLM pattern [[Willison 2023]](#ref-willison-dual) and CaMeL [[Debenedetti et al. 2025]](#ref-camel) separate what untrusted data can influence, which is what the trace's structured handoffs do.
- FIDES tracks confidentiality and integrity labels in a planner and enforces policy deterministically [[Costa et al. 2025]](#ref-fides).
- Progent expresses privilege as symbolic rules over tool names and arguments [[Shi et al. 2025]](#ref-progent).
- IsolateGPT isolates execution between LLM apps [[Wu et al. 2025]](#ref-isolategpt).
- Zhou and Zhang survey access control for agents [[Zhou & Zhang 2026]](#ref-access-survey).

In terms of the stack, these sit in layers 2 and 4: they decide what is allowed.

**Out-of-process enforcement.** Enforcement on the only action path appears in Dobrin and Chmiel's safety kernel [[Dobrin & Chmiel 2026]](#ref-dobrin) and in action-boundary governance with trusted provenance [[Mazzocchetti 2026]](#ref-mazzocchetti).

**Classic sources.** The validity conditions here are old ideas applied to agents:
- complete mediation, least privilege, fail-safe defaults and separation of privilege [[Saltzer & Schroeder 1975]](#ref-saltzer);
- capabilities and their attenuation [[Dennis & Van Horn 1966]](#ref-dennis), [[Birgisson et al. 2014]](#ref-macaroons);
- cascading revocation in database authorization [[Griffiths & Wade 1976]](#ref-griffiths), [[Fagin 1978]](#ref-fagin);
- time-of-check-to-time-of-use races [[Bishop & Dilger 1996]](#ref-bishop).

Compensation as a defined counteraction is the saga pattern [[Garcia-Molina & Salem 1987]](#ref-sagas), with a formal treatment by Korth, Levy and Silberschatz [[Korth et al. 1990]](#ref-korth).

---

## 9. Limitations, and what an evaluation would need

**Limitations.**
- **The lens decides where and who, not validity.** It doesn't derive the validity conditions; it places them.
- **The central definition isn't formalized.** The Lean model takes tiers as owner-supplied labels. A stronger version would define a boundary over a state model, prove that a given tier map is sound for its tools, and connect the two.
- **The Lean models are small.**
  - Approvals live in one shared store, not with individual agents.
  - The drain results assume the mediator can reach the provider's queue.
  - Operations are atomic and their sources aren't authenticated in the model.
  - The composed system doesn't include the exposure rule.
- **The examples aren't hardened products.** The pi gate writes its trace inside its own process, the approval prompt shows a truncated view of the call, and labels for the exposure rule exist only for the toy tools.
- **The literature moves fast.** The comparison in §4 is with six systems read closely; §8 is broader but not exhaustive.

**What an evaluation would need to show.** This is a working paper; a systems version would need at least:
- **Attack resistance.** An injection benchmark (AgentDojo or similar) and a suite of run-later-write attacks, run with and without the inner gate and the outer sandbox. The suite should include the path spellings above.
- **Cost to the user.** Approval prompts per task and task completion, especially once the exposure rule escalates everything observable. Approval fatigue is the obvious way this design fails in practice: a human who approves everything is not an authority.
- **False denials.** Legitimate edits the outer deny list blocks.
- **Overhead** of the gate and the commit-time check.
- **Portability.** The outer policy running more than one real agent, with each agent's network needs recorded, on macOS and Linux.

---

## 10. Wrapping up

Recent work on agent authority has produced most of the right pieces. One question organizes them: can you still prevent this effect, or put things back, from inside a boundary you control? That decides who may authorize an effect and where the decision has to be made. From it you can read the tiers, the commit point, why compensation isn't undo, and why files that run later are a crossing.

What it doesn't decide is whether a given "yes" is valid: current, bound to this effect, from someone with authority, not copied, not overtaken by a sibling, drained when withdrawn. That's what the field has been working out. Once the lens fixes the point, those conditions can be checked together, and a small model shows they compose.

The bigger picture is a single stack: boundary engineering, classification, the commit point, the validity of the decision made there, and what happens after. It is one design problem, organized by where the ability to undo an effect is lost.

---

## References

<a id="ref-bennett"></a>**Bennett 1973.** Charles H. Bennett. *Logical Reversibility of Computation.* IBM Journal of Research and Development 17(6):525–532, 1973.

<a id="ref-macaroons"></a>**Birgisson et al. 2014.** Arnar Birgisson, Joe Gibbs Politz, Úlfar Erlingsson, Ankur Taly, Michael Vrable, Mark Lentczner. *Macaroons: Cookies with Contextual Caveats for Decentralized Authorization in the Cloud.* NDSS 2014.

<a id="ref-bishop"></a>**Bishop & Dilger 1996.** Matt Bishop, Michael Dilger. *Checking for Race Conditions in File Accesses.* Computing Systems 9(2):131–152, 1996.

<a id="ref-cordon"></a>**Chen et al. 2026.** Zheng Chen, Hanqing Liu, Duling Xu, Dong Dong, Jialin Li, Bangzheng Pu, Jidong Zhai. *Cordon: Semantic Transactions for Tool-Using LLM Agents.* [arXiv:2606.17573](https://arxiv.org/abs/2606.17573), 2026.

<a id="ref-fides"></a>**Costa et al. 2025.** Manuel Costa, Boris Köpf, Aashish Kolluri, Andrew Paverd, Mark Russinovich, Ahmed Salem, Shruti Tople, Lukas Wutschitz, Santiago Zanella-Béguelin. *Securing AI Agents with Information-Flow Control* (FIDES). [arXiv:2505.23643](https://arxiv.org/abs/2505.23643), 2025.

<a id="ref-cve2014"></a>**CVE-2014-9390.** Git case-insensitive `.Git` path handling. [nvd.nist.gov/vuln/detail/CVE-2014-9390](https://nvd.nist.gov/vuln/detail/CVE-2014-9390), 2014.

<a id="ref-camel"></a>**Debenedetti et al. 2025.** Edoardo Debenedetti, Ilia Shumailov, Tianqi Fan, Jamie Hayes, Nicholas Carlini, Daniel Fabian, Christoph Kern, Chongyang Shi, Andreas Terzis, Florian Tramèr. *Defeating Prompt Injections by Design* (CaMeL). [arXiv:2503.18813](https://arxiv.org/abs/2503.18813), 2025.

<a id="ref-dennis"></a>**Dennis & Van Horn 1966.** Jack B. Dennis, Earl C. Van Horn. *Programming Semantics for Multiprogrammed Computations.* Communications of the ACM 9(3):143–155, 1966.

<a id="ref-dobrin"></a>**Dobrin & Chmiel 2026.** Seth Dobrin, Łukasz Chmiel. *The Unfireable Safety Kernel: Execution-Time AI Alignment for AI Agents and Other Escapable AI Systems.* [arXiv:2606.26057](https://arxiv.org/abs/2606.26057), 2026.

<a id="ref-fagin"></a>**Fagin 1978.** Ronald Fagin. *On an Authorization Mechanism.* ACM Transactions on Database Systems 3(3):310–319, 1978.

<a id="ref-parallax"></a>**Fokou 2026.** Joel Fokou. *Parallax: Why AI Agents That Think Must Never Act.* [arXiv:2604.12986](https://arxiv.org/abs/2604.12986), 2026.

<a id="ref-sagas"></a>**Garcia-Molina & Salem 1987.** Hector Garcia-Molina, Kenneth Salem. *Sagas.* Proceedings of the 1987 ACM SIGMOD International Conference on Management of Data, 249–259, 1987.

<a id="ref-griffiths"></a>**Griffiths & Wade 1976.** Patricia P. Griffiths, Bradford W. Wade. *An Authorization Mechanism for a Relational Database System.* ACM Transactions on Database Systems 1(3):242–255, 1976.

<a id="ref-khan"></a>**Khan 2026.** Sajjad Khan. *Stop Means Stop: Measuring and Repairing the Enforcement Gap in Agent-Framework Control Primitives.* [arXiv:2607.14166](https://arxiv.org/abs/2607.14166), 2026.

<a id="ref-approve-what"></a>**Kodathala et al. 2026.** Sai Varun Kodathala, Prashanth Pollishetty, Jaylen Cargill. *Approve What, Exactly? Effect Binding and Trusted Rendering for Agent Step-Up Authorization.* [arXiv:2610.21063](https://arxiv.org/abs/2610.21063), 2026.

<a id="ref-korth"></a>**Korth et al. 1990.** Henry F. Korth, Eliezer Levy, Abraham Silberschatz. *A Formal Approach to Recovery by Compensating Transactions.* Proceedings of the 16th VLDB Conference, 95–106, 1990.

<a id="ref-landauer"></a>**Landauer 1961.** Rolf Landauer. *Irreversibility and Heat Generation in the Computing Process.* IBM Journal of Research and Development 5(3):183–191, 1961.

<a id="ref-mazzocchetti"></a>**Mazzocchetti 2026.** Adam Mazzocchetti. *Runtime Governance for Agentic AI: Action-Boundary Control with Trusted Provenance and Fail-Closed Execution.* [arXiv:2608.16891](https://arxiv.org/abs/2608.16891), 2026.

<a id="ref-rule-of-two"></a>**Meta 2025.** Meta. *Agents Rule of Two: A Practical Approach to AI Agent Security.* [ai.meta.com/blog/practical-ai-agent-security](https://ai.meta.com/blog/practical-ai-agent-security/), October 2025.

<a id="ref-magentic"></a>**Mozannar et al. 2025.** Hussein Mozannar, Gagan Bansal, Cheng Tan, Adam Fourney, Victor Dibia, Jingya Chen, Jack Gerrits, Tyler Payne, Matheus Kunzler Maldaner, Madeleine Grunde-McLaughlin, Eric Zhu, Griffin Bassman, Jacob Alber, Peter Chang, Ricky Loynd, Friederike Niedtner, Ece Kamar, Maya Murad, Rafah Hosn, Saleema Amershi. *Magentic-UI: Towards Human-in-the-loop Agentic Systems.* [arXiv:2507.22358](https://arxiv.org/abs/2507.22358), 2025.

<a id="ref-goex"></a>**Patil et al. 2024.** Shishir G. Patil, Tianjun Zhang, Vivian Fang, Noppapon C., Roy Huang, Aaron Hao, Martin Casado, Joseph E. Gonzalez, Raluca Ada Popa, Ion Stoica. *GoEX: Perspectives and Designs Towards a Runtime for Autonomous LLM Applications.* [arXiv:2404.06921](https://arxiv.org/abs/2404.06921), 2024.

<a id="ref-saltzer"></a>**Saltzer & Schroeder 1975.** Jerome H. Saltzer, Michael D. Schroeder. *The Protection of Information in Computer Systems.* Proceedings of the IEEE 63(9):1278–1308, 1975.

<a id="ref-santos-commit"></a>**Santos-Grueiro 2026a.** Igor Santos-Grueiro. *Temporary Authority, Permanent Effects: Commit-Time Authorization for LLM Agents.* [arXiv:2607.10487](https://arxiv.org/abs/2607.10487), 2026.

<a id="ref-santos-closure"></a>**Santos-Grueiro 2026b.** Igor Santos-Grueiro. *When Does Authorization End? Effect Closure at Provider Boundaries.* [arXiv:2609.02866](https://arxiv.org/abs/2609.02866), 2026.

<a id="ref-progent"></a>**Shi et al. 2025.** Tianneng Shi, Jingxuan He, Zhun Wang, Hongwei Li, Linyu Wu, Wenbo Guo, Dawn Song. *Progent: Securing AI Agents with Privilege Control.* [arXiv:2504.11703](https://arxiv.org/abs/2504.11703), 2025.

<a id="ref-srt"></a>**Anthropic srt.** Anthropic. *Sandbox Runtime (srt).* [github.com/anthropics/sandbox-runtime](https://github.com/anthropics/sandbox-runtime), 2026.

<a id="ref-tallam"></a>**Tallam 2026.** Krti Tallam. *A Five-Plane Reference Architecture for Runtime Governance of Production AI Agents.* [arXiv:2606.12320](https://arxiv.org/abs/2606.12320), 2026.

<a id="ref-waghmare"></a>**Waghmare & Sufi 2026.** Deepak Waghmare, Shaad Sufi. *Can You Undo It? Reversibility Classes for AI Agent Actions.* [arXiv:2611.22075](https://arxiv.org/abs/2611.22075), 2026.

<a id="ref-willison-dual"></a>**Willison 2023.** Simon Willison. *The Dual LLM pattern for building AI assistants that can resist prompt injection.* [simonwillison.net/2023/Apr/25/dual-llm-pattern](https://simonwillison.net/2023/Apr/25/dual-llm-pattern/), April 2023.

<a id="ref-willison-trifecta"></a>**Willison 2025.** Simon Willison. *The lethal trifecta for AI agents: private data, untrusted content, and external communication.* [simonwillison.net/2025/Jun/16/the-lethal-trifecta](https://simonwillison.net/2025/Jun/16/the-lethal-trifecta/), June 2025.

<a id="ref-isolategpt"></a>**Wu et al. 2025.** Yuhao Wu, Franziska Roesner, Tadayoshi Kohno, Ning Zhang, Umar Iqbal. *IsolateGPT: An Execution Isolation Architecture for LLM-Based Agentic Systems.* NDSS 2025. [arXiv:2403.04960](https://arxiv.org/abs/2403.04960).

<a id="ref-recoverability"></a>**Zhang & Liu 2026.** Zhihui Zhang, Wei Liu. *Recoverability as a System Primitive for Long-Horizon AI Agents.* [arXiv:2609.13672](https://arxiv.org/abs/2609.13672), 2026.

<a id="ref-access-survey"></a>**Zhou & Zhang 2026.** Chijin Zhou, Quan Zhang. *Rethinking Access Control for AI Agents: Recent Advances and Open Challenges.* [arXiv:2611.06764](https://arxiv.org/abs/2611.06764), 2026.

<a id="ref-zhu"></a>**Zhu & Wang 2026a.** Genliang Zhu, Chu Wang. *Authorization for Self-Modifying AI Agent Populations: Conserving Authority across Replacement, Forking, and Rollback.* [arXiv:2610.00347](https://arxiv.org/abs/2610.00347), 2026.

<a id="ref-zhu-revocation"></a>**Zhu & Wang 2026b.** Genliang Zhu, Chu Wang. *Authorization Revocation for Long-Running AI Agents: Root-Scoped Quiescence under Delegation and Asynchronous Execution.* [arXiv:2609.21284](https://arxiv.org/abs/2609.21284), 2026.
