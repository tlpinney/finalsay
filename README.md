# finalsay

A small, engine-agnostic governance model for AI agent tool calls, built around one idea:

> **Let reversibility decide who decides.**

A decision carries real authority only if it can't be undone. So instead of asking "how much do we trust the model?", ask "can this action be undone?" and divide authority accordingly:

| Tier | Meaning | Who decides |
|---|---|---|
| **Reversible** | The exact prior state can be restored, with no trace (a file under git, a draft) | The agent |
| **Compensatable** | Can't be undone, but a declared compensating action counteracts it, leaving a trace (a refund, a calendar invite) | Policy |
| **Irreversible** | No restoration, no adequate compensation (a sent email, a leaked secret) | A human with authority |

This repo is a **toy reference implementation in [Lean 4](https://lean-lang.org/)**: the model, proofs that its rules hold for *every* policy, a small simulated agent, and conformance fixtures so the same model can be implemented in Cedar, OPA, or anything else.

The longer write-up, with how this relates to recent work on agent authority, is in [`paper.md`](paper.md).

## The model

Every tool call becomes a **request** (action, resource, tier, approval, context) and gets exactly one of three **decisions**: `allow`, `ask` (escalate to a human with authority), or `deny`.

The decision procedure:
1. Any matching **deny** rule → `deny`
2. **Approved** by someone with authority → `allow`
3. **Irreversible** without approval → `ask`
4. Any matching **allow** rule → `allow`
5. Otherwise → `ask`

### Invariants

Five rules every implementation must keep. In Lean they're proved for all policies (`FinalSay/Invariants.lean`):

1. **Deny wins:** a matching deny rule always produces `deny`, even over an approval.
2. **Irreversible needs approval:** an irreversible action without approval is never `allow`.
3. **No rule, ask:** if no rule applies and nothing was approved, the answer is `ask`. Nothing is allowed by default; `allow` only ever comes from an approval or a matching allow rule.
4. **The owner classifies:** the owner's tier map beats any tool's self-declared hints; unknown actions are irreversible unless the owner opts in to trusting hints; "compensatable" only counts if a compensation is declared. And the **trifecta rule** (below): once a session holds private data *and* untrusted input, every observable action is classified irreversible.
5. **Fail closed:** a request that can't be parsed is never `allow` (`ask` when a human is present, `deny` when none is).

**What these don't cover, and two more that do.** Reversibility decides *where* authority is exercised and *who* exercises it, not whether a given approval is valid. On its own, invariant 2 is satisfied by an approval that is stale or that covers a different effect. Two further invariants close that gap in the model:

6. **Exact and current at commit** (`FinalSay/Authority.lean`): approvals are data bound to one exact effect (action, resource, amount), with an expiry, revocation and single use. The gate re-derives approval from its own store at commit time and ignores whatever the request claims. Proved for every policy and every sequence of grants, revocations, clock ticks and commits:
   - an irreversible commit has an approval covering exactly that effect, unexpired, unrevoked and unused (`irreversible_commit_exact_current`);
   - every logged effect is bound to the approval it consumed (`run_log_ok`);
   - after `revoke id`, no later effect uses `id` (`revocation_is_effective`);
   - a single-use approval backs at most one effect (`single_use_at_most_once`);
   - a decision taken before a revocation would allow what the commit-time check refuses (`decision_before_commit_goes_stale`), which is why the check sits at commit.
7. **Forking moves authority, never copies it** (`FinalSay/Conservation.lean`): a population of agents holds budgets and single-use grants. Fork gives the child a share and the parent keeps the rest. Proved for every sequence of forks, spends and uses:
   - budget held + spent is constant (`budget_conserved`), so the population never spends more than the root was granted (`spent_le_root`);
   - grants held + used is a permutation of the starting grants (`grants_conserved`), so each grant is used at most once across all agents (`grant_used_at_most_once`);
   - copy-on-fork, the naive alternative, spends twice the grant (`copy_on_fork_overspends`).

8. **The approver must hold authority** (`FinalSay/Delegation.lean`): authority starts at a root (the resource owner) and is delegated as scoped links (actions, resources, amount limit, expiry). A link can only be issued within the issuer's own scope, and revoking a link kills everything delegated beneath it. Proved for every sequence of delegations and revocations:
   - nobody holds authority the root didn't have (`no_amplification`);
   - every link is within its parent's scope and was issued by the parent's holder (`links_attenuated`);
   - revocation cascades down the chain and stays in force (`revocation_cascades`);
   - an irreversible commit's approval is exact, current, and from someone holding authority over that effect (`irreversible_commit_authorized`);
   - a sub-agent's approval of exactly the right effect passes invariant 6 alone and is refused here (`unauthorized_approver_refused`).
9. **An `ask` holds the whole run** (`FinalSay/Barrier.lean`): while one effect of a run waits for a human, the run's other effects are held, not released. Proved for every sequence of submissions, decisions and cancellations:
   - while a run has an effect awaiting a decision, nothing of it lands except through a decision on that run (`barrier`);
   - a rejected effect never lands (`rejected_never_lands`);
   - each effect lands at most once (`lands_at_most_once`);
   - after cancel, nothing of the run lands, including late submissions (`cancel_fences_run`);
   - pausing only the branch that asked lets a sibling land mid-decision (`per_branch_pause_leaks`).
10. **Revocation drains in-flight work** (`FinalSay/Frontier.lean`): a commit hands a carrier to a provider, which lands it later and may redeliver it. On revocation the mediator drops in-flight carriers of that grant, and it lands each idempotency key once. Proved for every sequence of dispatches, deliveries, retries and revocations:
    - once a grant is revoked, nothing it authorized lands again, whether in flight, redelivered or new (`revocation_drains`);
    - each key lands at most once (`key_lands_at_most_once`);
    - refusing new dispatches alone isn't enough: an in-flight carrier lands after revocation (`in_flight_outlives_revocation`);
    - without binding to the key, a retry lands twice (`redelivery_duplicates`).

### All of it together (`FinalSay/System.lean`)

One system holds a delegation org, an approval store, the run gate, a provider, and an agent population with budgets. An effect is proposed. The policy decides: deny drops it; allow submits it to the gate; ask submits it as needing approval, which holds its whole run. Whatever the gate releases passes **one commit-time check**: policy, an exact/current/unused approval from someone with authority, and the agent's budget. A passing check consumes the approval, spends the budget, hands a carrier to the provider, and writes an audit record of the state it was judged in.

Each component changes only through its own step function (`run_sim`), so every component theorem holds inside the system. On top of that, for every policy and every sequence of operations from a fresh system:
- every effect that lands traces to an audit record of a passed commit-time check (`landed_was_committed`);
- an irreversible effect that lands was backed, at commit, by an approval covering exactly it, unexpired, unrevoked, from someone holding authority over it within the root's scope; and the carrier names that approval (`irreversible_landed_authorized`);
- after an approval is revoked, nothing it backed lands, in flight or redelivered (`revocation_drains_system`);
- each effect lands at most once (`lands_once_system`) and leaves the gate at most once (`released_once_system`); rejected effects never leave (`rejected_never_released_system`);
- while a run waits on a human, only a decision on that run commits anything of it (`barrier_system`);
- the total committed amount never exceeds the root budget, however agents fork (`committed_within_budget`);
- nobody holds authority the root lacked (`no_amplification_system`);
- after a delegation is revoked, nothing lands whose approver's authority ran through it, because carriers are tagged with the approval and its whole delegation chain (`delegation_revocation_drains_system`, `not_on_chain`);
- after a run is cancelled, nothing of it is committed (`cancel_fences_system`);
- each single-use approval backs at most one commit (`single_use_system`);
- and the pipeline isn't vacuous: a concrete run holds a sibling behind an ask, then lands both after approval (`pipeline_lands`); another lands a manager-approved refund, or drains it if the manager's delegation is revoked first (`delegation_drain_example`).

**Where these come from.** The individual properties aren't new. Commit-time authorization and effect closure come from Santos-Grueiro (also machine-checked, in Lean). Barrier semantics come from Khan (verified in Verus and TLA+). Attenuation comes from Tallam, and conservation from Zhu & Wang. What this repo adds:
- placing all of them at the one point reversibility selects (the commit/frontier);
- a checked model showing they compose in one system.

**Honest limits.**
- Budgets are conserved across forks. Approvals, though, live in one shared store rather than being held by individual agents.
- The fence assumes the mediator can drop carriers at the provider (complete mediation).
- These are small models. They are not a verified implementation. Related work: commit-time authorization and effect closure (Santos-Grueiro), conservation under forking (Zhu & Wang), attenuation (Tallam), barrier leaks (Khan). For the trace: the lethal trifecta (Willison), the Dual LLM pattern (Willison) and CaMeL (Debenedetti et al.) for endorsing structured results, and Cordon (Chen et al.) for flow labels.

### The trifecta rule

A leak needs three things in one session: **private data**, **untrusted input**, and **a way to communicate outward**. This is Simon Willison's [lethal trifecta](https://simonwillison.net/2025/Jun/16/the-lethal-trifecta/). A policy gate can't close every outward channel, because a *permitted* action can still carry information in its content, its timing, or the fact that it happened at all. So the rule doesn't try to read content; it counts channels:

- Each tier map entry says whether the action is **observable** (can someone outside see that it happened, or what it contained?) and whether it **reads private data**. Unknown actions are observable.
- Once a session has seen both private data and untrusted input, every observable action is classified **irreversible**, since information that has crossed the boundary can't be taken back. Invariant 2 then means it's never allowed without approval.
- Unobservable work (notes, drafts) is unaffected, so the agent can keep working locally.

Proved in `FinalSay/Invariants.lean`: the rule escalates observable actions (`trifecta_escalates`, `trifecta_needs_approval`), changes nothing without the full trifecta or for unobservable actions (`no_trifecta_unchanged`, `unobservable_unchanged`), and only ever escalates (`trifecta_only_escalates`).

Approval is a weak defence here: a person approving a message checks what it says, not what might be encoded in it. Prefer deny rules, narrow parameters, or delayed release for sessions in this state.

### The trace is a flow graph

Taint tracking is reachability in a data-flow graph. Every tool call and every handoff is recorded in a trace (`FinalSay/Trace.lean`), and exposure is computed by walking it:

- **A context is one node.** A model can be influenced by anything in its context, so inside one context everything flows to everything. Session-level flags are exact there, not an approximation.
- **Contexts connect only through handoffs**, such as a sub-agent returning a result. That's the only place the graph gets finer, so **context boundaries set how precise the graph can be**.
- **Handoffs treat the two labels differently.** A *structured* result (a boolean, an enum) can't carry instructions, so it clears *untrusted*. *Private* always carries through, because even one bit can carry private information; releasing private data takes a decision, not a schema.

Proved: exposure only grows (`step_monotone`); private always propagates and structured results clear untrusted (`handoff_keeps_private`, `structured_endorses`); and for **every script**, the harness's exposure equals the trace's and no observable call runs unapproved in a context holding private data and untrusted input (`run_safe`).

Covert channels can't be closed, but every use of one can be **counted, attributed, and replayed**:

- `finalsay trace split F` writes the trace as JSON lines.
- `finalsay audit F` replays every decision against the owner's config, recomputes exposure from the graph, and prints a **channel report**: every observable call that ran in a context holding labels, with an upper bound on bytes sent. Any mismatch is a finding; an unreadable trace fails.
- `finalsay graph split` prints the graph as Mermaid.

Scenario 2 puts the inbox in a quarantined `reader` context:

```
ALLOW notes.write [reversible] allowed by rule 'reversible-ok'
ALLOW [reader] inbox.read [reversible] allowed by rule 'reversible-ok'
      (private data entered reader)
      (untrusted content entered reader)
  ↳   reader → main (structured, 1 bit)
ALLOW calendar.create_event [compensatable] allowed by rule 'calendar-ok'
  ↳   reader → main (free text, 120 bytes)
ASK   calendar.create_event [irreversible] irreversible action: needs approval from someone with authority → human declined
      (escalated: this context holds private data and untrusted input, and this is observable)

── Channel report ──
  [main] calendar.create_event: 15 bytes out, context held [private]
```

The 1-bit answer leaves the main context able to act; the free-text summary doesn't. The first invite is allowed but still reported, because the main context held private data when it went out.

### Code mode and sandboxes

A sandboxed run is just another context. Nothing inside it is traced; everything that **crosses its edges** is:

| Edge | In the model | Recorded by, in a real system |
|---|---|---|
| The code going in | handoff from the writing context (free text, so it carries that context's labels) | the launcher hashes the script |
| Calls the code makes | governed calls in the run's context | the gate |
| Output coming back | handoff to the model (structured, or free text) | the launcher captures stdout |
| Files that outlive the run | handoff to `workspace` | a before/after snapshot diff, which is also what makes the run reversible |

Scenario 3 (`finalsay trace code F`, `finalsay graph code`):

```
  ↳   main → run1 (free text, 240 bytes)
ALLOW [run1] inbox.read [reversible] allowed by rule 'reversible-ok'
      (private data entered run1)
      (untrusted content entered run1)
  ↳   run1 → workspace (free text, 512 bytes, carries +private +untrusted)
  ↳   run1 → main (structured, 1 bit, carries +private)
ALLOW calendar.create_event [compensatable] allowed by rule 'calendar-ok'
  ↳   main → run2 (free text, 180 bytes, carries +private)
ALLOW [run2] inbox.read [reversible] allowed by rule 'reversible-ok'
      (untrusted content entered run2)
  ↳   run2 → main (free text, 300 bytes, carries +private +untrusted)
ASK   calendar.create_event [irreversible] … → human declined
```

Run 2 holds private data before it reads anything: the code main wrote carried it in. The `workspace` ends up with private data and untrusted input, so whatever later pushes or syncs those files is a channel too.

Two things a real gate must get right that the toy takes for granted: the gate, not the code, decides which run a call belongs to (one socket per run, identified by the connection); and the trace is written by the gate, outside the sandbox, append-only. OS-level tracing (`eslogger` on macOS, eBPF or gVisor on Linux) can check that the sandbox actually held. Treat its denials as detection, not decisions: honest code told "no network" doesn't keep trying.

### Why compensation isn't undo

The toy world makes the difference precise (`FinalSay/World.lean`, `FinalSay/Agent.lean`). Proved:
- A refund followed by its compensating charge restores the **balance**, but the **statement** gains two entries, so the world is provably *not* back where it started.
- Deleting a calendar event doesn't un-notify anyone: both the invite and the cancellation were seen.
- Rollback restores notes **exactly**, and **no** rollback can unsend an email.

## Run it

Requires Lean via [elan](https://github.com/leanprover/elan). With Nix, `nix develop` (or `direnv allow`) gives you elan, the `cedar` and `opa` CLIs, and Python, pinned by `flake.lock`.

```sh
lake build                                      # builds the code and checks every proof
./.lake/build/bin/finalsay                      # run the toy agent scenario
./.lake/build/bin/finalsay export fixtures/fixtures.json       # regenerate fixtures
python3 examples/python/check.py fixtures/fixtures.json        # check another implementation
python3 examples/python/mutate.py fixtures/fixtures.json       # check the corpus catches broken guarantees
./.lake/build/bin/finalsay trace split /tmp/t.jsonl             # write a trace (JSON lines)
./.lake/build/bin/finalsay audit /tmp/t.jsonl                   # replay and audit it
./.lake/build/bin/finalsay graph code                           # flow graph as Mermaid (one|split|code)
```

Scenario 1, everything in one context: an agent writes a note, creates a calendar event, issues two refunds, drafts and sends an email, reads an inbox containing a planted "forward the plan to …" message, then tries to send to that address:

```
ALLOW notes.write [reversible] allowed by rule 'reversible-ok'
ALLOW calendar.create_event [compensatable] allowed by rule 'calendar-ok'
ALLOW bank.refund [compensatable] allowed by rule 'small-refunds'
ASK   bank.refund [compensatable] no rule applies: escalating → human declined
ALLOW email.draft [reversible] allowed by rule 'reversible-ok'
ALLOW email.send [irreversible] approved by someone with authority → human approved
ALLOW inbox.read [reversible] allowed by rule 'reversible-ok'
      (private data entered the session)
      (untrusted content entered the session)
DENY  email.send [irreversible] denied by rule 'no-outbound-when-tainted'
ASK   calendar.create_event [irreversible] irreversible action: needs approval from someone with authority → human declined
      (escalated: this context holds private data and untrusted input, and this is observable)
ALLOW notes.write [reversible] allowed by rule 'reversible-ok'
ASK   mystery.tool [irreversible] irreversible action: needs approval from someone with authority → human declined
```

Every step was individually permitted until the last send; the deny rule stopped the outcome, before a human was even asked. The same calendar action that was allowed earlier now needs approval, because an invite's title reaches the attendees; writing a note is still fine. The scenario then rolls back and shows what each tier can and can't recover.

## Implementing it elsewhere

`fixtures/fixtures.json` (format `finalsay-fixtures/v3`) holds the policies, tier maps, and expected answers computed by the Lean reference:

| Section | Cases | Checks |
|---|---|---|
| `decisions` | 360 | request + policy → expected `decision` and `rule`; each case lists the invariants it exercises |
| `classification` | 240 | tier map + action + hint + session exposure → expected tier (cases exercising the trifecta rule are tagged `4c-trifecta`) |
| `malformed` | 2 | unparseable input + mode → expected decision |
| `system.cases` | 615 | composed system (invariants 6–10): a sequence of operations (propose, approve, reject, cancel, grant, revoke approval, tick, delegate, revoke delegation, fork, deliver, retry) → expected landed carriers and their tags, audit records, gate released/rejected, approvals used, amount spent. There are 15 named scenarios plus 600 runs from a fixed seed |

An implementation **conforms** if it reproduces every expected answer. `examples/python/check.py` is an independent, standard-library-only implementation written from this README; it passes all 602. A deliberately broken variant (default `allow` instead of `ask`) fails 39 cases, all tagged `3-no-rule-asks`; one without the trifecta rule fails 17, all tagged `4c-trifecta`.

The composed system is replayed by `examples/python/composed.py`, a second standard-library implementation; it reproduces all 615 system cases. `examples/python/mutate.py` checks the corpus is strong enough to certify it. It breaks one guarantee at a time and counts the cases that notice:

| Broken guarantee | Failing cases |
|---|---|
| Provider fence | 205 |
| Run barrier (per-branch pause) | 99 |
| Approver authority | 336 |
| Idempotency bind | 84 |
| Revocation cascade | 107 |
| Fork conservation (copy-on-fork) | 91 |
| Single use | 24 |
| Attenuation | 93 |

One mutant is equivalent by design and fails 0 cases: the provider refusing to dispatch under a revoked tag. In the composed system the commit-time check has already refused anything a revoked approval or delegation backed, so the provider's own refusal is defence in depth. That's proved, not just observed: `committed_never_refused_at_dispatch` shows that in every reachable state, a commit's tags are never ones the provider has revoked.

Conditions in policies are a tiny language (`always`, `actionIs`, `actionPrefix`, `tierIs`, `tainted`, `amountAtMost`, `and`, `not`). Mapping them to Cedar `when` clauses or Rego rules is straightforward; the decision procedure above is the part to get exactly right. In Cedar, for example, "no rule applies" shows up as a deny *with no determining policy*, which must be mapped to `ask`.

## Layout

| File | Contents |
|---|---|
| `FinalSay/Core.lean` | Tiers, decisions, requests, policies, `evaluate`, fail-closed `evaluateRaw` |
| `FinalSay/Classify.lean` | Tier maps, effective-tier resolution, and the trifecta rule |
| `FinalSay/Invariants.lean` | Proofs of the five invariants |
| `FinalSay/World.lean` | Toy world, tools, and the compensation theorems |
| `FinalSay/Trace.lean` | The trace as a flow graph: events, handoffs, exposure by reachability, audit, channel report, Mermaid |
| `FinalSay/Agent.lean` | Agent harness with contexts: classify → evaluate → escalate → run → record; `run_safe`; rollback theorems |
| `FinalSay/Demo.lean` | The demo tier map, policy, approver, and starting world |
| `FinalSay/Fixtures.lean` | JSON fixture export |
| `FinalSay/Authority.lean` | Invariant 6: approvals bound to the exact effect, checked at commit; revocation, expiry, single use |
| `FinalSay/Conservation.lean` | Invariant 7: forking moves budget and grants, never copies |
| `FinalSay/Delegation.lean` | Invariant 8: scoped delegation from a root, attenuation, cascading revocation, approver authority |
| `FinalSay/Barrier.lean` | Invariant 9: an `ask` holds the whole run (B1–B4) |
| `FinalSay/Frontier.lean` | Invariant 10: provider boundary; revocation drains in-flight work, idempotency bind |
| `FinalSay/System.lean` | Invariants 6–10 composed into one system, with end-to-end theorems |
| `FinalSay/SystemFixtures.lean` | Composed-system fixtures: named scenarios + seeded random runs |
| `FinalSay/Config.lean` | Reads a tier map and policy from JSON, so any harness's trace can be audited (`audit F --config C`) |
| `examples/python/check.py` | Independent implementation checked against the fixtures |
| `examples/python/composed.py` | Independent implementation of the composed system |
| `examples/python/mutate.py` | Mutation test: does the corpus catch each broken guarantee? |
| `examples/pi/` | A [pi](https://pi.dev) extension implementing the model, including code mode; its traces pass the Lean audit. Also a hardened `srt` config and an outside-the-project checkpoint script |
| `paper.md` | The write-up: the framework, prior work through it, the composed system, and run-later writes |
| `experiments/` | The outer sandbox wrapper (`wrapper/`, generated from the Lean policy) and a checkpoint-restore check |

## Status

A toy, meant to make an idea concrete. Not production code. Real tool interception exists for pi (`examples/pi/`). Not yet included: a Claude Code hook or MCP gateway, Cedar and OPA versions, time windows ("reversible until T"), per-value provenance (the session-level exposure flags are a coarse version), and real enforcement outside the agent's process (a sandbox plus a gate that holds the credentials).

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this work, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
