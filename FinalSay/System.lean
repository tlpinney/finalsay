import FinalSay.Delegation
import FinalSay.Conservation
import FinalSay.Barrier
import FinalSay.Frontier

/-!
# The composed system

Invariants 6–10 were proved as separate models. This module puts them in one
system and proves they hold together.

State: a delegation `Org`, an approval `Store`, a run `Gate`, a `Provider`, an
agent population `Pop` with budgets, the proposals, and an audit log.

The path of an effect:
1. **propose**: the policy is consulted (`commitDecideAuth`). Deny drops it; allow
   submits it to the gate as not needing approval; ask submits it as needing
   approval, which holds its whole run.
2. **approve / reject**: a human decides on a pending effect.
3. Whatever the gate releases goes through **one commit-time check**
   (`commitOne`): the policy again, an approval that is exact, current, unused and
   from someone holding authority over the effect, and the proposing agent's
   budget. If it passes, the approval is consumed, the budget is spent, a carrier
   goes to the provider, and an audit `Record` stores the state it was judged in.
4. **deliver / retry**: the provider lands carriers, possibly redelivering.
5. **revokeApproval** withdraws an approval at the gate and fences it at the
   provider. **delegate** grants scoped authority. **revokeDelegation** revokes a
   link at the org and fences, at the provider, every carrier whose approver's
   authority ran through it. **fork** splits budget.

Carriers are tagged with the approval they used and the delegation chain behind
the approver's authority (`tagsOf`), so revoking any of them drains the carrier.

Each component changes only through its own step function, so every invariant
proved for it holds here (`run_sim`). On top of that, for every policy and every
sequence of operations from a fresh system:

* `landed_was_committed`: every effect that lands traces to an audit record of a
  passed commit-time check.
* `irreversible_landed_authorized`: an irreversible effect that lands was backed,
  at commit, by an approval covering exactly that effect, unexpired, unrevoked,
  from someone holding authority over it, within the root's scope; and the
  carrier names that approval.
* `revocation_drains_system`: after an approval is revoked, nothing it backed
  lands, in flight or redelivered.
* `delegation_revocation_drains_system` (+ `not_on_chain`): after a delegation is
  revoked, nothing lands whose approver's authority ran through it.
* `cancel_fences_system`: after a run is cancelled, nothing of it is committed.
* `single_use_system`: each single-use approval backs at most one commit.
* `lands_once_system`: each effect lands at most once.
* `barrier_system`: while a run waits on a human, no step other than a decision
  on that run commits anything of it.
* `committed_within_budget`: the total amount of all committed effects never
  exceeds the root budget, however agents fork.
* `no_amplification_system`, `released_once_system`, `rejected_never_released_system`.

Related work: each component's property comes from prior work, cited in its own
module: commit-time authorization and effect closure (Santos-Grueiro, arXiv
2607.10487, 2609.02866), barrier semantics (Khan, arXiv 2607.14166), attenuation
(Tallam, arXiv 2606.12320), conservation (Zhu & Wang, arXiv 2610.00347). What this
module adds is checking all of them at one point and proving they compose.
-/

namespace FinalSay

/-- A proposed effect: its id, the proposing agent (index in the population),
and the request. -/
structure Proposal where
  id    : EffId
  agent : Nat
  req   : Request

/-- Audit record of one passed commit-time check, with the state it was judged in. -/
structure Record where
  id    : EffId
  agent : Nat
  req   : Request
  via   : Option Approval
  /-- The delegation chain behind the approver's authority. -/
  chain : List Nat
  store : Store
  org   : Org

/-- Provider tags: approvals and delegation links live in disjoint namespaces. -/
def approvalTag (aid : Nat) : Nat := 2 * aid
def linkTag (lid : Nat) : Nat := 2 * lid + 1

/-- The delegation chain behind `who`'s authority over `t`: empty if the root holds
it directly, otherwise the witnessing link and every link above it (revoking any
of them kills that authority). -/
def Org.chain (o : Org) (who : String) (t : Target) (now : Nat) : List Nat :=
  if who == o.root && o.rootScope.covers t now then []
  else match o.links.find? (fun l => o.live l && l.holder == who && l.scope.covers t now) with
    | some l => l.ancestors ++ [l.id]
    | none => []

/-- What a carrier is tagged with: the approval it used and the delegation chain
behind that approval's authority. -/
def tagsOf : Option Approval → List Nat → List Nat
  | some a, chain => approvalTag a.id :: chain.map linkTag
  | none, _ => []

structure System where
  org   : Org
  store : Store := {}
  gate  : Gate := {}
  prov  : Provider := {}
  pop   : Pop
  props : List Proposal := []
  recs  : List Record := []

def System.chainFor (s : System) (via : Option Approval) (r : Request) : List Nat :=
  match via with
  | some a => s.org.chain a.approver r.target s.store.now
  | none => []

def System.budgetOk (s : System) (i n : Nat) : Bool :=
  match s.pop.agents[i]? with
  | some h => decide (n ≤ h.budget)
  | none => false

/-- The single commit-time check every released effect goes through. -/
def System.commitOne (p : Policy) (s : System) (id : EffId) : System :=
  match s.props.find? (fun q => q.id == id) with
  | none => s
  | some q =>
    if (commitDecideAuth p s.org s.store q.req).decision = .allow ∧
        s.budgetOk q.agent q.req.amount = true then
      { s with
        store := s.store.consume (s.store.pickAuth s.org q.req),
        pop   := s.pop.step (.spend q.agent q.req.amount),
        prov  := s.prov.step (.dispatch id (tagsOf (s.store.pickAuth s.org q.req)
                   (s.chainFor (s.store.pickAuth s.org q.req) q.req))),
        recs  := s.recs ++ [⟨id, q.agent, q.req, s.store.pickAuth s.org q.req,
                   s.chainFor (s.store.pickAuth s.org q.req) q.req, s.store, s.org⟩] }
    else s

/-- Install a new gate state and commit whatever it newly released. -/
def System.withGate (p : Policy) (s : System) (g' : Gate) : System :=
  (g'.released.drop s.gate.released.length).foldl (System.commitOne p) { s with gate := g' }

inductive SOp where
  | propose (q : Proposal)
  | approve (id : EffId)
  | reject (id : EffId)
  | cancel (run : Nat)
  | grant (a : Approval)
  | revokeApproval (aid : Nat)
  | tick
  | delegate (id : Nat) (issuer holder : String) (scope : Scope) (via : Option Nat)
  /-- Revoke a delegation link: at the org and, for everything it backed, at the provider. -/
  | revokeDelegation (lid : Nat)
  | fork (parent : Nat) (child : String) (share : Nat)
  | deliver (key : EffId)
  | retry (key : EffId)

def System.step (p : Policy) (s : System) : SOp → System
  | .propose q =>
    if s.props.any (fun q' => q'.id == q.id) then s
    else
      let s := { s with props := s.props ++ [q] }
      let d := (commitDecideAuth p s.org s.store q.req).decision
      if d = .deny then s
      else s.withGate p (s.gate.step (.submit q.id (d != .allow)))
  | .approve id => s.withGate p (s.gate.step (.decide id true))
  | .reject id => s.withGate p (s.gate.step (.decide id false))
  | .cancel r => { s with gate := s.gate.step (.cancel r) }
  | .grant a => { s with store := { s.store with granted := s.store.granted ++ [a] } }
  | .revokeApproval aid =>
    { s with store := { s.store with revoked := aid :: s.store.revoked },
             prov := s.prov.step (.revoke (approvalTag aid)) }
  | .tick => { s with store := { s.store with now := s.store.now + 1 } }
  | .delegate id iss hol sc via => { s with org := s.org.step (.delegate id iss hol sc via) }
  | .revokeDelegation lid =>
    { s with org := s.org.step (.revoke lid), prov := s.prov.step (.revoke (linkTag lid)) }
  | .fork i c share => { s with pop := s.pop.step (.fork i c share []) }
  | .deliver k => { s with prov := s.prov.step (.deliver k) }
  | .retry k => { s with prov := s.prov.step (.retry k) }

def System.run (p : Policy) (s : System) (ops : List SOp) : System := ops.foldl (System.step p) s

/-- A fresh system: one root principal with a root scope, one root agent. -/
def System.fresh (root : String) (sc : Scope) (agent : Holder) : System :=
  { org := { root, rootScope := sc }, pop := { agents := [agent] } }

theorem System.run_cons (p : Policy) (s : System) (op : SOp) (ops : List SOp) :
    s.run p (op :: ops) = (s.step p op).run p ops := rfl

theorem System.run_append (p : Policy) (s : System) (xs ys : List SOp) :
    s.run p (xs ++ ys) = (s.run p xs).run p ys := by
  simp [System.run, List.foldl_append]

theorem Gate.run_append (g : Gate) (xs ys : List GOp) : g.run (xs ++ ys) = (g.run xs).run ys := by
  simp [Gate.run, List.foldl_append]
theorem Org.run_append (o : Org) (xs ys : List DOp) : o.run (xs ++ ys) = (o.run xs).run ys := by
  simp [Org.run, List.foldl_append]
theorem Provider.run_append (s : Provider) (xs ys : List FOp) :
    s.run (xs ++ ys) = (s.run xs).run ys := by
  simp [Provider.run, List.foldl_append]
theorem Pop.run_append (s : Pop) (xs ys : List PopOp) : s.run (xs ++ ys) = (s.run xs).run ys := by
  simp [Pop.run, List.foldl_append]

/-! ### Each component changes only through its own steps -/

/-- What a step may do to each component. -/
def Sim (s t : System) : Prop :=
  (∃ gs, t.gate = s.gate.run gs) ∧ (∃ os, t.org = s.org.run os) ∧
    (∃ fs, t.prov = s.prov.run fs) ∧ (∃ ps, t.pop = s.pop.run ps)

theorem Sim.refl (s : System) : Sim s s :=
  ⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩

theorem Sim.trans {s t u : System} (h₁ : Sim s t) (h₂ : Sim t u) : Sim s u := by
  obtain ⟨⟨g1, hg1⟩, ⟨o1, ho1⟩, ⟨f1, hf1⟩, ⟨p1, hp1⟩⟩ := h₁
  obtain ⟨⟨g2, hg2⟩, ⟨o2, ho2⟩, ⟨f2, hf2⟩, ⟨p2, hp2⟩⟩ := h₂
  exact ⟨⟨g1 ++ g2, by rw [hg2, hg1, Gate.run_append]⟩, ⟨o1 ++ o2, by rw [ho2, ho1, Org.run_append]⟩,
    ⟨f1 ++ f2, by rw [hf2, hf1, Provider.run_append]⟩, ⟨p1 ++ p2, by rw [hp2, hp1, Pop.run_append]⟩⟩

theorem commitOne_sim (p : Policy) (s : System) (id : EffId) :
    Sim s (s.commitOne p id) ∧ (s.commitOne p id).gate = s.gate ∧
      (s.commitOne p id).org = s.org ∧ (s.commitOne p id).props = s.props := by
  unfold System.commitOne
  split
  · exact ⟨Sim.refl s, rfl, rfl, rfl⟩
  · split
    · exact ⟨⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[.dispatch _ _], rfl⟩, ⟨[.spend _ _], rfl⟩⟩, rfl, rfl, rfl⟩
    · exact ⟨Sim.refl s, rfl, rfl, rfl⟩

theorem foldl_commit_sim (p : Policy) (L : List EffId) : ∀ (s : System),
    Sim s (L.foldl (System.commitOne p) s) ∧ (L.foldl (System.commitOne p) s).gate = s.gate ∧
      (L.foldl (System.commitOne p) s).org = s.org := by
  induction L with
  | nil => intro s; exact ⟨Sim.refl s, rfl, rfl⟩
  | cons id L ih =>
    intro s
    obtain ⟨h1, hg1, ho1, -⟩ := commitOne_sim p s id
    obtain ⟨h2, hg2, ho2⟩ := ih (s.commitOne p id)
    exact ⟨h1.trans h2, hg2.trans hg1, ho2.trans ho1⟩

theorem withGate_sim (p : Policy) (s : System) (op : GOp) :
    Sim s (s.withGate p (s.gate.step op)) := by
  unfold System.withGate
  obtain ⟨h, _, _⟩ := foldl_commit_sim p ((s.gate.step op).released.drop s.gate.released.length)
    { s with gate := s.gate.step op }
  exact Sim.trans (t := { s with gate := s.gate.step op })
    ⟨⟨[op], by simp [Gate.run]⟩, ⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩ h

theorem step_sim (p : Policy) (s : System) (op : SOp) : Sim s (s.step p op) := by
  cases op with
  | propose q =>
    simp only [System.step]
    split
    · exact Sim.refl s
    · split
      · exact Sim.refl _
      · exact withGate_sim p { s with props := s.props ++ [q] } _
  | approve id => exact withGate_sim p s _
  | reject id => exact withGate_sim p s _
  | cancel r => exact ⟨⟨[.cancel r], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩
  | grant a => exact Sim.refl _
  | revokeApproval aid => exact ⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[.revoke _], rfl⟩, ⟨[], rfl⟩⟩
  | tick => exact Sim.refl _
  | delegate id iss hol sc via => exact ⟨⟨[], rfl⟩, ⟨[.delegate id iss hol sc via], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩
  | revokeDelegation lid => exact ⟨⟨[], rfl⟩, ⟨[.revoke lid], rfl⟩, ⟨[.revoke _], rfl⟩, ⟨[], rfl⟩⟩
  | fork i c sh => exact ⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[.fork i c sh []], rfl⟩⟩
  | deliver k => exact ⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[.deliver k], rfl⟩, ⟨[], rfl⟩⟩
  | retry k => exact ⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[.retry k], rfl⟩, ⟨[], rfl⟩⟩

/-- **Simulation:** in any run, the gate, organisation, provider and population are
each a run of their own model, so every theorem proved for them applies. -/
theorem run_sim (p : Policy) (ops : List SOp) : ∀ (s : System), Sim s (s.run p ops) := by
  induction ops with
  | nil => intro s; exact Sim.refl s
  | cons op ops ih => intro s; exact (step_sim p s op).trans (ih _)

/-! ### The audit invariant -/

/-- What every audit record certifies about the moment of commit. -/
def Record.Ok (r : Record) : Prop :=
  r.org.WithinRoot ∧ r.via = r.store.pickAuth r.org r.req ∧
    (∀ a, r.via = some a → a ∈ r.store.granted ∧ a.validFor r.store r.req = true ∧
      r.org.holds a.approver r.req.target r.store.now = true) ∧
    (r.req.tier = .irreversible → r.via.isSome) ∧
    r.chain = (match r.via with
      | some a => r.org.chain a.approver r.req.target r.store.now
      | none => [])

/-- The system invariant tying the components together. -/
def System.Inv (s : System) : Prop :=
  s.org.WithinRoot ∧ (∀ r ∈ s.recs, r.Ok) ∧
    (∀ c ∈ s.prov.inflight ++ s.prov.landed, ∃ r ∈ s.recs, r.id = c.key ∧ c.grants = tagsOf r.via r.chain) ∧
    s.pop.spent = (s.recs.map (fun r => r.req.amount)).sum

/-- Provider carriers come from earlier carriers or from a dispatch. -/
theorem Provider.step_carriers (s : Provider) (op : FOp) (c : Carrier)
    (hc : c ∈ (s.step op).inflight ++ (s.step op).landed) :
    c ∈ s.inflight ++ s.landed ∨ ∃ k g, op = .dispatch k g ∧ c = ⟨k, g⟩ := by
  cases op with
  | dispatch k g =>
    simp only [Provider.step] at hc
    split at hc
    · exact Or.inl hc
    · simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with (hc | hc) | hc
      · exact Or.inl (List.mem_append_left _ hc)
      · exact Or.inr ⟨k, g, rfl, hc⟩
      · exact Or.inl (List.mem_append_right _ hc)
  | deliver k =>
    left
    simp only [Provider.step] at hc
    split at hc
    · next c' hf =>
      split at hc
      · rcases List.mem_append.mp hc with hc | hc
        · exact List.mem_append_left _ (List.erase_subset hc)
        · exact List.mem_append_right _ hc
      · simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | hc | hc
        · exact List.mem_append_left _ (List.erase_subset hc)
        · exact List.mem_append_right _ hc
        · exact hc ▸ List.mem_append_left _ (List.mem_of_find?_eq_some hf)
    · exact hc
  | retry k =>
    left
    simp only [Provider.step] at hc
    split at hc
    · next c' hf =>
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with (hc | hc) | hc
      · exact List.mem_append_left _ hc
      · subst hc
        rcases List.mem_append.mp (List.mem_of_find?_eq_some hf) with h | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ h
      · exact List.mem_append_right _ hc
    · exact hc
  | revoke g =>
    left
    simp only [Provider.step, List.mem_append, List.mem_filter] at hc
    rcases hc with hc | hc
    · exact List.mem_append_left _ hc.1
    · exact List.mem_append_right _ hc

theorem spend_spent (s : System) (i n : Nat) (h : s.budgetOk i n = true) :
    (s.pop.step (.spend i n)).spent = s.pop.spent + n := by
  unfold System.budgetOk at h
  simp only [Pop.step]
  split at h
  · next hh hi =>
    rw [hi]; simp only [decide_eq_true_eq] at h; simp [h]
  · simp at h

theorem fork_spent (pop : Pop) (i : Nat) (c : String) (sh : Nat) :
    (pop.step (.fork i c sh [])).spent = pop.spent := by
  simp only [Pop.step]; split
  · split <;> rfl
  · rfl

theorem commitOne_inv (p : Policy) (s : System) (id : EffId) (h : s.Inv) :
    (s.commitOne p id).Inv ∧ ∃ new, (s.commitOne p id).recs = s.recs ++ new ∧ ∀ r ∈ new, r.id = id := by
  obtain ⟨hw, hok, hlink, hspent⟩ := h
  unfold System.commitOne
  split
  · exact ⟨⟨hw, hok, hlink, hspent⟩, [], by simp, by simp⟩
  · next q hq =>
    split
    · next hc =>
      obtain ⟨hal, hb⟩ := hc
      refine ⟨⟨hw, ?_, ?_, ?_⟩, _, rfl, by simp⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hok r hr
        · simp at hr; subst hr
          refine ⟨hw, rfl, ?_, ?_, rfl⟩
          · intro a ha
            have hmem := List.mem_of_find?_eq_some ha
            have hv := List.find?_some ha
            simp only [Bool.and_eq_true] at hv
            exact ⟨hmem, hv.1, hv.2⟩
          · intro hirr
            cases hp : s.store.pickAuth s.org q.req with
            | none =>
              exact absurd hal (irreversible_needs_approval p { q.req with approved := _ } hirr
                (by simp [hp]))
            | some _ => rfl
      · intro c hc
        rcases Provider.step_carriers _ _ c hc with hc | ⟨k, g, he, hc⟩
        · obtain ⟨r, hr, h1, h2⟩ := hlink c hc
          exact ⟨r, List.mem_append_left _ hr, h1, h2⟩
        · cases he; subst hc
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩
      · rw [spend_spent s _ _ hb, hspent]
        simp
    · exact ⟨⟨hw, hok, hlink, hspent⟩, [], by simp, by simp⟩

theorem foldl_commit_inv (p : Policy) (L : List EffId) : ∀ (s : System), s.Inv →
    (L.foldl (System.commitOne p) s).Inv ∧
      ∃ new, (L.foldl (System.commitOne p) s).recs = s.recs ++ new ∧ ∀ r ∈ new, r.id ∈ L := by
  induction L with
  | nil => intro s h; exact ⟨h, [], by simp, by simp⟩
  | cons id L ih =>
    intro s h
    obtain ⟨h1, n1, e1, hn1⟩ := commitOne_inv p s id h
    obtain ⟨h2, n2, e2, hn2⟩ := ih _ h1
    refine ⟨h2, n1 ++ n2, by simp only [List.foldl_cons]; rw [e2, e1, List.append_assoc], ?_⟩
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (hn1 r hr) ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hn2 r hr)

theorem withGate_inv (p : Policy) (s : System) (g' : Gate) (h : s.Inv) :
    (s.withGate p g').Inv ∧ ∃ new, (s.withGate p g').recs = s.recs ++ new ∧
      ∀ r ∈ new, r.id ∈ g'.released.drop s.gate.released.length := by
  obtain ⟨hw, hok, hlink, hspent⟩ := h
  exact foldl_commit_inv p _ { s with gate := g' } ⟨hw, hok, hlink, hspent⟩

theorem step_inv_sys (p : Policy) (s : System) (op : SOp) (h : s.Inv) : (s.step p op).Inv := by
  obtain ⟨hw, hok, hlink, hspent⟩ := h
  have hcarry : ∀ (fop : FOp), (∀ k g, fop ≠ .dispatch k g) →
      ∀ c ∈ (s.prov.step fop).inflight ++ (s.prov.step fop).landed,
        ∃ r ∈ s.recs, r.id = c.key ∧ c.grants = tagsOf r.via r.chain := by
    intro fop hnd c hc
    rcases Provider.step_carriers _ _ c hc with hc | ⟨k, g, he, _⟩
    · exact hlink c hc
    · exact absurd he (hnd k g)
  cases op with
  | propose q =>
    simp only [System.step]
    split
    · exact ⟨hw, hok, hlink, hspent⟩
    · split
      · exact ⟨hw, hok, hlink, hspent⟩
      · exact (withGate_inv p { s with props := s.props ++ [q] } _ ⟨hw, hok, hlink, hspent⟩).1
  | approve id => exact (withGate_inv p s _ ⟨hw, hok, hlink, hspent⟩).1
  | reject id => exact (withGate_inv p s _ ⟨hw, hok, hlink, hspent⟩).1
  | cancel r => exact ⟨hw, hok, hlink, hspent⟩
  | grant a => exact ⟨hw, hok, hlink, hspent⟩
  | revokeApproval aid => exact ⟨hw, hok, hcarry _ (by intro k g h; cases h), hspent⟩
  | tick => exact ⟨hw, hok, hlink, hspent⟩
  | delegate id iss hol sc via => exact ⟨s.org.step_withinRoot _ hw, hok, hlink, hspent⟩
  | revokeDelegation lid =>
    exact ⟨s.org.step_withinRoot _ hw, hok, hcarry _ (by intro k g h; cases h), hspent⟩
  | fork i c sh => exact ⟨hw, hok, hlink, by show (s.pop.step (.fork i c sh [])).spent = _; rw [fork_spent, hspent]; rfl⟩
  | deliver k => exact ⟨hw, hok, hcarry _ (by intro k g h; cases h), hspent⟩
  | retry k => exact ⟨hw, hok, hcarry _ (by intro k g h; cases h), hspent⟩

theorem run_inv_sys (p : Policy) (ops : List SOp) : ∀ (s : System), s.Inv → (s.run p ops).Inv := by
  induction ops with
  | nil => intro s h; exact h
  | cons op ops ih => intro s h; exact ih _ (step_inv_sys p s op h)

theorem fresh_inv (root : String) (sc : Scope) (agent : Holder) :
    (System.fresh root sc agent).Inv := by
  refine ⟨by simp [Org.WithinRoot, System.fresh], by simp [System.fresh], by simp [System.fresh], ?_⟩
  simp [System.fresh]

/-! ### End-to-end guarantees -/

section
variable (p : Policy) (root : String) (sc : Scope) (agent : Holder) (ops : List SOp)

/-- **Every effect that lands was committed:** it traces to an audit record of a
passed commit-time check, and the carrier names the approval that record used. -/
theorem landed_was_committed :
    ∀ c ∈ ((System.fresh root sc agent).run p ops).prov.landed,
      ∃ r ∈ ((System.fresh root sc agent).run p ops).recs,
        r.id = c.key ∧ c.grants = tagsOf r.via r.chain ∧ r.Ok := by
  intro c hc
  obtain ⟨_, hok, hlink, _⟩ := run_inv_sys p ops _ (fresh_inv root sc agent)
  obtain ⟨r, hr, h1, h2⟩ := hlink c (List.mem_append_right _ hc)
  exact ⟨r, hr, h1, h2, hok r hr⟩

/-- **An irreversible effect that lands was authorized:** at the moment of commit,
an approval covered exactly that effect, had not expired, had not been revoked,
was given by someone holding authority over the effect, within the root's
scope; and the landed carrier is tagged with that approval. -/
theorem irreversible_landed_authorized (c : Carrier)
    (hc : c ∈ ((System.fresh root sc agent).run p ops).prov.landed) :
    ∃ r ∈ ((System.fresh root sc agent).run p ops).recs, r.id = c.key ∧
      (r.req.tier = .irreversible →
        ∃ a, r.via = some a ∧ c.grants = approvalTag a.id :: r.chain.map linkTag ∧
          a.target = r.req.target ∧
          r.store.now < a.expires ∧ a.id ∉ r.store.revoked ∧
          r.org.holds a.approver r.req.target r.store.now = true ∧
          r.org.rootScope.covers r.req.target r.store.now = true) := by
  obtain ⟨r, hr, hid, hg, hw, _, hvia, hirr, _⟩ := landed_was_committed p root sc agent ops c hc
  refine ⟨r, hr, hid, fun ht => ?_⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hirr ht)
  obtain ⟨_, hv, hh⟩ := hvia a ha
  simp only [Approval.validFor, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at hv
  exact ⟨a, ha, by rw [hg, ha]; rfl, hv.1.1.1, hv.1.1.2, hv.1.2, hh,
    holds_within_root r.org hw _ _ _ hh⟩

/-- **Revocation drains, end to end:** once approval `aid` is revoked, nothing it
backed lands again, whether it was in flight, redelivered, or attempted later. -/
theorem revocation_drains_system (pre post : List SOp) (aid : Nat) :
    let mid := (System.fresh root sc agent).run p (pre ++ [.revokeApproval aid])
    ∃ new, ((System.fresh root sc agent).run p (pre ++ .revokeApproval aid :: post)).prov.landed =
        mid.prov.landed ++ new ∧ ∀ c ∈ new, approvalTag aid ∉ c.grants := by
  intro mid
  have e : pre ++ SOp.revokeApproval aid :: post = (pre ++ [.revokeApproval aid]) ++ post := by simp
  rw [e, System.run_append]
  obtain ⟨-, -, ⟨fs, hfs⟩, -⟩ := run_sim p post mid
  rw [hfs]
  obtain ⟨-, -, ⟨fs0, hfs0⟩, -⟩ := run_sim p (pre ++ [.revokeApproval aid]) (System.fresh root sc agent)
  apply drains_from
  · show mid.prov.Drained
    rw [hfs0]; exact run_drained _ _ (by simp [Provider.Drained, System.fresh])
  · show approvalTag aid ∈ mid.prov.revoked
    simp only [mid, System.run_append, System.run, List.foldl_cons, List.foldl_nil, System.step]
    simp [Provider.step]

/-- **Each effect lands at most once**, end to end. -/
theorem lands_once_system :
    (((System.fresh root sc agent).run p ops).prov.landed.map Carrier.key).Nodup := by
  obtain ⟨-, -, ⟨fs, hfs⟩, -⟩ := run_sim p ops (System.fresh root sc agent)
  rw [hfs]; exact key_lands_at_most_once fs

/-- **Each effect leaves the gate at most once.** -/
theorem released_once_system : ((System.fresh root sc agent).run p ops).gate.released.Nodup := by
  obtain ⟨⟨gs, hgs⟩, -⟩ := run_sim p ops (System.fresh root sc agent)
  rw [hgs]; exact lands_at_most_once gs

/-- **A rejected effect never leaves the gate.** -/
theorem rejected_never_released_system (x : EffId)
    (hx : x ∈ ((System.fresh root sc agent).run p ops).gate.rejected) :
    x ∉ ((System.fresh root sc agent).run p ops).gate.released := by
  obtain ⟨⟨gs, hgs⟩, -⟩ := run_sim p ops (System.fresh root sc agent)
  rw [hgs] at hx ⊢; exact rejected_never_lands gs x hx

/-- **The committed total stays within the root budget**, however agents fork. -/
theorem committed_within_budget :
    ((((System.fresh root sc agent).run p ops).recs.map (fun r => r.req.amount)).sum) ≤ agent.budget := by
  obtain ⟨-, -, -, hspent⟩ := run_inv_sys p ops _ (fresh_inv root sc agent)
  obtain ⟨-, -, -, ⟨ps, hps⟩⟩ := run_sim p ops (System.fresh root sc agent)
  rw [← hspent, hps]
  exact spent_le_root agent ps

/-- **No amplification**, end to end: nobody ever holds authority the root lacked. -/
theorem no_amplification_system (who : String) (t : Target) (now : Nat)
    (hh : ((System.fresh root sc agent).run p ops).org.holds who t now = true) :
    sc.covers t now = true := by
  obtain ⟨-, ⟨os, hos⟩, -⟩ := run_sim p ops (System.fresh root sc agent)
  rw [hos] at hh
  exact no_amplification root sc os who t now hh

/-- **Revoking a delegation drains, end to end:** once delegation link `lid` is
revoked, nothing lands whose approver's authority ran through `lid` (directly or
through a link delegated beneath it), whether in flight, redelivered or later. -/
theorem delegation_revocation_drains_system (pre post : List SOp) (lid : Nat) :
    let mid := (System.fresh root sc agent).run p (pre ++ [.revokeDelegation lid])
    ∃ new, ((System.fresh root sc agent).run p (pre ++ .revokeDelegation lid :: post)).prov.landed =
        mid.prov.landed ++ new ∧ ∀ c ∈ new, linkTag lid ∉ c.grants := by
  intro mid
  have e : pre ++ SOp.revokeDelegation lid :: post = (pre ++ [.revokeDelegation lid]) ++ post := by
    simp
  rw [e, System.run_append]
  obtain ⟨-, -, ⟨fs, hfs⟩, -⟩ := run_sim p post mid
  rw [hfs]
  obtain ⟨-, -, ⟨fs0, hfs0⟩, -⟩ :=
    run_sim p (pre ++ [.revokeDelegation lid]) (System.fresh root sc agent)
  apply drains_from
  · show mid.prov.Drained
    rw [hfs0]; exact run_drained _ _ (by simp [Provider.Drained, System.fresh])
  · show linkTag lid ∈ mid.prov.revoked
    simp only [mid, System.run_append, System.run, List.foldl_cons, List.foldl_nil, System.step]
    simp [Provider.step]

/-- What the tag means: if a carrier lacks `linkTag lid` and its record used an
approval, then `lid` is not on that approval's authority chain. -/
theorem not_on_chain (r : Record) (c : Carrier) (a : Approval) (lid : Nat)
    (hg : c.grants = tagsOf r.via r.chain) (ha : r.via = some a) (hn : linkTag lid ∉ c.grants) :
    lid ∉ r.chain := by
  intro hl
  apply hn
  rw [hg, ha]
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem hl)

end

/-- **The barrier, end to end:** while run `r` has an effect awaiting a human, a
step that is not a decision on run `r` commits nothing of run `r`. -/
theorem barrier_system (p : Policy) (s : System) (op : SOp) (r : Nat) (hinv : s.Inv)
    (hb : s.gate.blocked r = true)
    (hop : ∀ id, (op = .approve id ∨ op = .reject id) → id.1 ≠ r) :
    ∃ new, (s.step p op).recs = s.recs ++ new ∧ ∀ x ∈ new, x.id.1 ≠ r := by
  have viaGate : ∀ (s' : System) (gop : GOp), s'.Inv → s'.gate.blocked r = true →
      (∀ id ap, gop = .decide id ap → id.1 ≠ r) →
      ∃ new, (s'.withGate p (s'.gate.step gop)).recs = s'.recs ++ new ∧ ∀ x ∈ new, x.id.1 ≠ r := by
    intro s' gop hi hb' hg
    obtain ⟨n, hn, hnr⟩ := barrier s'.gate gop r hb' hg
    obtain ⟨-, new, hnew, hids⟩ := withGate_inv p s' (s'.gate.step gop) hi
    refine ⟨new, hnew, fun x hx => ?_⟩
    have := hids x hx
    rw [hn, List.drop_left] at this
    exact hnr _ this
  cases op with
  | propose q =>
    simp only [System.step]
    split
    · exact ⟨[], by simp, by simp⟩
    · split
      · exact ⟨[], by simp, by simp⟩
      · obtain ⟨hw, hok, hlink, hspent⟩ := hinv
        exact viaGate { s with props := s.props ++ [q] } _ ⟨hw, hok, hlink, hspent⟩ hb
          (by intro id ap h; cases h)
  | approve id =>
    exact viaGate s _ hinv hb (by intro id' ap h; cases h; exact hop id (Or.inl rfl))
  | reject id =>
    exact viaGate s _ hinv hb (by intro id' ap h; cases h; exact hop id (Or.inr rfl))
  | cancel _ => exact ⟨[], by simp [System.step], by simp⟩
  | grant _ => exact ⟨[], by simp [System.step], by simp⟩
  | revokeApproval _ => exact ⟨[], by simp [System.step], by simp⟩
  | tick => exact ⟨[], by simp [System.step], by simp⟩
  | delegate _ _ _ _ _ => exact ⟨[], by simp [System.step], by simp⟩
  | revokeDelegation _ => exact ⟨[], by simp [System.step], by simp⟩
  | fork _ _ _ => exact ⟨[], by simp [System.step], by simp⟩
  | deliver _ => exact ⟨[], by simp [System.step], by simp⟩
  | retry _ => exact ⟨[], by simp [System.step], by simp⟩

/-- Every reachable state satisfies the invariant (so `barrier_system` applies at
every step of every run from a fresh system). -/
theorem reachable_inv (p : Policy) (root : String) (sc : Scope) (agent : Holder) (ops : List SOp) :
    ((System.fresh root sc agent).run p ops).Inv :=
  run_inv_sys p ops _ (fresh_inv root sc agent)

/-! ### Cancellation fences, end to end -/

/-- A step commits only effects the gate releases in that step, and the gate's
release obeys its fence: nothing of a cancelled run. -/
theorem step_fenced_sys (p : Policy) (s : System) (op : SOp) (hi : s.Inv) (hf : s.gate.Fenced) :
    ∃ new, (s.step p op).recs = s.recs ++ new ∧ ∀ x ∈ new, x.id.1 ∉ s.gate.cancelled := by
  have viaGate : ∀ (s' : System) (gop : GOp), s'.Inv → s'.gate.Fenced →
      ∃ new, (s'.withGate p (s'.gate.step gop)).recs = s'.recs ++ new ∧
        ∀ x ∈ new, x.id.1 ∉ s'.gate.cancelled := by
    intro s' gop hi' hf'
    obtain ⟨-, n, hn, hnc⟩ := step_fenced s'.gate gop hf'
    obtain ⟨-, new, hnew, hids⟩ := withGate_inv p s' (s'.gate.step gop) hi'
    refine ⟨new, hnew, fun x hx => ?_⟩
    have := hids x hx
    rw [hn, List.drop_left] at this
    exact hnc _ this
  cases op with
  | propose q =>
    simp only [System.step]
    split
    · exact ⟨[], by simp, by simp⟩
    · split
      · exact ⟨[], by simp, by simp⟩
      · obtain ⟨hw, hok, hlink, hspent⟩ := hi
        exact viaGate { s with props := s.props ++ [q] } _ ⟨hw, hok, hlink, hspent⟩ hf
  | approve id => exact viaGate s _ hi hf
  | reject id => exact viaGate s _ hi hf
  | _ => exact ⟨[], by simp [System.step], by simp⟩

theorem cancel_from (p : Policy) (r : Nat) (post : List SOp) : ∀ (s : System), s.Inv →
    s.gate.Fenced → r ∈ s.gate.cancelled →
    ∃ new, (s.run p post).recs = s.recs ++ new ∧ ∀ x ∈ new, x.id.1 ≠ r := by
  induction post with
  | nil => intro s _ _ _; exact ⟨[], by simp [System.run], by simp⟩
  | cons op ops ih =>
    intro s hi hf hr
    obtain ⟨n1, h1, hn1⟩ := step_fenced_sys p s op hi hf
    obtain ⟨⟨gs, hgs⟩, -⟩ := step_sim p s op
    have hf' : (s.step p op).gate.Fenced := by rw [hgs]; exact run_fenced gs _ hf
    have hr' : r ∈ (s.step p op).gate.cancelled := by rw [hgs]; exact (run_grows gs _).2.2 r hr
    obtain ⟨n2, h2, hn2⟩ := ih _ (step_inv_sys p s op hi) hf' hr'
    refine ⟨n1 ++ n2, by rw [System.run_cons, h2, h1, List.append_assoc], ?_⟩
    intro x hx hxr
    rcases List.mem_append.mp hx with hx | hx
    · exact hn1 x hx (hxr ▸ hr)
    · exact hn2 x hx hxr

/-- **B4, end to end:** after run `r` is cancelled, nothing of `r` is committed
again, including effects that were waiting and effects a late branch proposes. -/
theorem cancel_fences_system (p : Policy) (root : String) (sc : Scope) (agent : Holder)
    (pre post : List SOp) (r : Nat) :
    let mid := (System.fresh root sc agent).run p (pre ++ [.cancel r])
    ∃ new, ((System.fresh root sc agent).run p (pre ++ .cancel r :: post)).recs =
        mid.recs ++ new ∧ ∀ x ∈ new, x.id.1 ≠ r := by
  intro mid
  have e : pre ++ SOp.cancel r :: post = (pre ++ [.cancel r]) ++ post := by simp
  rw [e, System.run_append]
  obtain ⟨⟨gs, hgs⟩, -⟩ := run_sim p (pre ++ [.cancel r]) (System.fresh root sc agent)
  apply cancel_from
  · exact reachable_inv p root sc agent _
  · show mid.gate.Fenced
    rw [hgs]; exact run_fenced gs _ (by simp [Gate.Fenced, System.fresh])
  · show r ∈ mid.gate.cancelled
    simp only [mid, System.run_append, System.run, List.foldl_cons, List.foldl_nil, System.step]
    simp [Gate.step]

/-! ### Single-use approvals, end to end -/

/-- Ids of single-use approvals consumed by the audit log. -/
def oneShotRecs (recs : List Record) : List Nat :=
  recs.filterMap fun r => match r.via with
    | some a => if a.oneShot then some a.id else none
    | none => none

def System.Once (s : System) : Prop :=
  (oneShotRecs s.recs).Nodup ∧ ∀ i ∈ oneShotRecs s.recs, i ∈ s.store.used

theorem pickAuth_unused {s : Store} {o : Org} {r : Request} {a : Approval}
    (h : s.pickAuth o r = some a) : a.oneShot = true → a.id ∉ s.used := by
  have hv := List.find?_some h
  simp only [Approval.validFor, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, Bool.and_eq_false_iff] at hv
  intro ho
  rcases hv.1.2 with h1 | h1
  · simp [ho] at h1
  · simpa using h1

theorem oneShotRecs_append (l₁ l₂ : List Record) :
    oneShotRecs (l₁ ++ l₂) = oneShotRecs l₁ ++ oneShotRecs l₂ := by
  simp [oneShotRecs, List.filterMap_append]

theorem oneShotRecs_none (r : Record) (h : r.via = none) : oneShotRecs [r] = [] := by
  simp [oneShotRecs, h]

theorem oneShotRecs_some (r : Record) (a : Approval) (h : r.via = some a) :
    oneShotRecs [r] = if a.oneShot then [a.id] else [] := by
  cases ho : a.oneShot <;> simp [oneShotRecs, h, ho]

theorem commitOne_once (p : Policy) (s : System) (id : EffId) (h : s.Once) :
    (s.commitOne p id).Once := by
  obtain ⟨hnd, hused⟩ := h
  unfold System.commitOne
  split
  · exact ⟨hnd, hused⟩
  · split
    · unfold System.Once
      simp only [oneShotRecs_append]
      cases hp : s.store.pickAuth s.org _ with
      | none =>
        rw [oneShotRecs_none _ rfl, List.append_nil]
        exact ⟨hnd, fun i hi => by simpa [Store.consume] using hused i hi⟩
      | some a =>
        have hnu := pickAuth_unused hp
        rw [oneShotRecs_some _ a rfl]
        cases ho : a.oneShot
        · simp only [Bool.false_eq_true, ite_false, List.append_nil]
          exact ⟨hnd, fun i hi => by simp [Store.consume, hused i hi]⟩
        · simp only [ite_true]
          refine ⟨?_, ?_⟩
          · rw [List.nodup_append]
            refine ⟨hnd, by simp, ?_⟩
            intro x hx y hy hxy
            simp at hy; subst hy; subst hxy
            exact hnu ho (hused _ hx)
          · intro i hi
            simp only [List.mem_append, List.mem_singleton] at hi
            rcases hi with hi | hi
            · simp [Store.consume, hused i hi]
            · simp [Store.consume, hi]
    · exact ⟨hnd, hused⟩

theorem foldl_commit_once (p : Policy) (L : List EffId) : ∀ (s : System), s.Once →
    (L.foldl (System.commitOne p) s).Once := by
  induction L with
  | nil => intro s h; exact h
  | cons id L ih => intro s h; exact ih _ (commitOne_once p s id h)

theorem step_once_sys (p : Policy) (s : System) (op : SOp) (h : s.Once) : (s.step p op).Once := by
  obtain ⟨hnd, hused⟩ := h
  cases op with
  | propose q =>
    simp only [System.step]
    split
    · exact ⟨hnd, hused⟩
    · split
      · exact ⟨hnd, hused⟩
      · exact foldl_commit_once p _ _ ⟨hnd, hused⟩
  | approve id => exact foldl_commit_once p _ _ ⟨hnd, hused⟩
  | reject id => exact foldl_commit_once p _ _ ⟨hnd, hused⟩
  | _ => exact ⟨hnd, hused⟩

/-- **Each single-use approval backs at most one committed effect**, end to end. -/
theorem single_use_system (p : Policy) (root : String) (sc : Scope) (agent : Holder)
    (ops : List SOp) : (oneShotRecs ((System.fresh root sc agent).run p ops).recs).Nodup := by
  suffices ∀ s : System, s.Once → (s.run p ops).Once from
    (this _ ⟨by simp [oneShotRecs, System.fresh], by simp [oneShotRecs, System.fresh]⟩).1
  induction ops with
  | nil => intro s h; exact h
  | cons op ops ih => intro s h; exact ih _ (step_once_sys p s op h)

/-! ### The gate and the provider agree -/

/-- Every tag the provider has revoked comes from a revoked approval or delegation. -/
def System.Sync (s : System) : Prop :=
  ∀ g ∈ s.prov.revoked, (∃ aid ∈ s.store.revoked, g = approvalTag aid) ∨
    (∃ lid ∈ s.org.revoked, g = linkTag lid)

theorem chain_live (o : Org) (who : String) (t : Target) (now : Nat) (l : Nat)
    (hl : l ∈ o.chain who t now) : l ∉ o.revoked := by
  unfold Org.chain at hl
  split at hl
  · simp at hl
  · split at hl
    · next w hw =>
      have hv := List.find?_some hw
      simp only [Bool.and_eq_true] at hv
      have hlive := hv.1.1
      simp only [Org.live, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not, List.all_eq_true] at hlive
      rcases List.mem_append.mp hl with hl | hl
      · have := hlive.2 l hl; simpa using this
      · simp at hl; subst hl; exact hlive.1
    · simp at hl

/-- **No committed effect is refused at the provider:** in a synchronised state,
none of the tags a commit dispatches has been revoked, so the provider's own
check at dispatch never fires. (This is why removing it is an equivalent mutant.) -/
theorem dispatch_tags_live (s : System) (hs : s.Sync) (r : Request) :
    ∀ g ∈ tagsOf (s.store.pickAuth s.org r) (s.chainFor (s.store.pickAuth s.org r) r),
      g ∉ s.prov.revoked := by
  intro g hg hrev
  cases hp : s.store.pickAuth s.org r with
  | none => simp [hp, tagsOf] at hg
  | some a =>
    have hv := (List.find?_some hp)
    simp only [Bool.and_eq_true, Approval.validFor, decide_eq_true_eq, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hv
    have hnr : a.id ∉ s.store.revoked := hv.1.1.2
    simp only [hp, tagsOf, System.chainFor, List.mem_cons, List.mem_map] at hg
    rcases hs g hrev with ⟨aid, haid, hga⟩ | ⟨lid, hlid, hgl⟩
    · rcases hg with hg | ⟨l, _, hgl'⟩
      · have : aid = a.id := by simp [approvalTag] at hg hga; omega
        exact hnr (this ▸ haid)
      · simp [approvalTag, linkTag] at hga hgl'; omega
    · rcases hg with hg | ⟨l, hl, hgl'⟩
      · simp [approvalTag, linkTag] at hg hgl; omega
      · have : l = lid := by simp [linkTag] at hgl hgl'; omega
        exact chain_live s.org _ _ _ l hl (this ▸ hlid)

theorem Provider.dispatch_revoked (pv : Provider) (k : EffId) (gs : List Nat) :
    (pv.step (.dispatch k gs)).revoked = pv.revoked := by
  simp only [Provider.step]; split <;> rfl

theorem Provider.nonrevoke_revoked (pv : Provider) (op : FOp) (h : ∀ g, op ≠ .revoke g) :
    (pv.step op).revoked = pv.revoked := by
  cases op with
  | dispatch k gs => exact Provider.dispatch_revoked pv k gs
  | deliver k => simp only [Provider.step]; split
                 · split <;> rfl
                 · rfl
  | retry k => simp only [Provider.step]; split <;> rfl
  | revoke g => exact absurd rfl (h g)

theorem Org.delegate_revoked (o : Org) (id : Nat) (iss hol : String) (sc : Scope) (via : Option Nat) :
    (o.step (.delegate id iss hol sc via)).revoked = o.revoked := by
  cases via with
  | none => simp only [Org.step]; split <;> rfl
  | some pid =>
    simp only [Org.step]; split
    · split <;> rfl
    · rfl

theorem commitOne_sync (p : Policy) (s : System) (id : EffId) (h : s.Sync) : (s.commitOne p id).Sync := by
  unfold System.commitOne
  split
  · exact h
  · split
    · intro g hg
      rw [Provider.dispatch_revoked] at hg
      rcases h g hg with ⟨aid, ha, he⟩ | ⟨lid, hl, he⟩
      · left; refine ⟨aid, ?_, he⟩
        cases s.store.pickAuth s.org _ <;> simpa [Store.consume] using ha
      · right; exact ⟨lid, hl, he⟩
    · exact h

theorem foldl_commit_sync (p : Policy) (L : List EffId) : ∀ (s : System), s.Sync →
    (L.foldl (System.commitOne p) s).Sync := by
  induction L with
  | nil => intro s h; exact h
  | cons id L ih => intro s h; exact ih _ (commitOne_sync p s id h)

theorem step_sync (p : Policy) (s : System) (op : SOp) (h : s.Sync) : (s.step p op).Sync := by
  cases op with
  | propose q =>
    simp only [System.step]
    split
    · exact h
    · split
      · exact h
      · exact foldl_commit_sync p _ _ h
  | approve id => exact foldl_commit_sync p _ _ h
  | reject id => exact foldl_commit_sync p _ _ h
  | revokeApproval aid =>
    intro g hg
    simp only [System.step, Provider.step, List.mem_cons] at hg
    rcases hg with hg | hg
    · left; exact ⟨aid, List.mem_cons_self, hg⟩
    · rcases h g hg with ⟨a, ha, he⟩ | hl
      · left; exact ⟨a, List.mem_cons_of_mem _ ha, he⟩
      · right; exact hl
  | revokeDelegation lid =>
    intro g hg
    simp only [System.step, Provider.step, List.mem_cons] at hg
    rcases hg with hg | hg
    · right; exact ⟨lid, by simp [System.step, Org.step], hg⟩
    · rcases h g hg with hl | ⟨l, hl, he⟩
      · left; exact hl
      · right; exact ⟨l, by simp [System.step, Org.step, hl], he⟩
  | delegate id iss hol sc via =>
    intro g hg
    rcases h g hg with hl | ⟨l, hl, he⟩
    · left; exact hl
    · right; refine ⟨l, ?_, he⟩
      show l ∈ (s.org.step (.delegate id iss hol sc via)).revoked
      rw [Org.delegate_revoked]; exact hl
  | deliver k =>
    intro g hg
    have : (s.prov.step (.deliver k)).revoked = s.prov.revoked :=
      Provider.nonrevoke_revoked _ _ (by intro g h; cases h)
    exact h g (this ▸ hg)
  | retry k =>
    intro g hg
    have : (s.prov.step (.retry k)).revoked = s.prov.revoked :=
      Provider.nonrevoke_revoked _ _ (by intro g h; cases h)
    exact h g (this ▸ hg)
  | _ => exact h

/-- In every reachable state, a passed commit-time check is never refused at the
provider. -/
theorem committed_never_refused_at_dispatch (p : Policy) (root : String) (sc : Scope)
    (agent : Holder) (ops : List SOp) (r : Request) :
    let s := (System.fresh root sc agent).run p ops
    ∀ g ∈ tagsOf (s.store.pickAuth s.org r) (s.chainFor (s.store.pickAuth s.org r) r),
      g ∉ s.prov.revoked := by
  intro s
  apply dispatch_tags_live
  suffices ∀ t : System, t.Sync → (t.run p ops).Sync from this _ (by simp [System.Sync, System.fresh])
  induction ops with
  | nil => intro t h; exact h
  | cons op ops ih => intro t h; exact ih _ (step_sync p t op h)

/-! ### The pipeline is not vacuous -/

namespace pipelineExample

def scope : Scope :=
  { actions := ["bank.refund", "notes.write"], resources := ["acct"], maxAmount := 1000,
    expires := 100 }
def policy : Policy := [⟨"notes", .allow, .actionIs "notes.write"⟩]
def refund : Request :=
  { principal := "user:me", agent := "agent", action := "bank.refund", resource := "acct",
    tier := .irreversible, amount := 500 }
def note : Request :=
  { principal := "user:me", agent := "agent", action := "notes.write", resource := "acct",
    tier := .reversible }
def approval : Approval :=
  { id := 1, target := refund.target, approver := "user:me", expires := 10 }
def sys0 : System := System.fresh "user:me" scope ⟨"agent", 1000, []⟩

/-- Propose an irreversible refund (asks) and, in the same run, a note (allowed but
held behind the ask); the root grants and approves; the provider delivers. -/
def ops : List SOp :=
  [.propose ⟨(1, 0), 0, refund⟩, .propose ⟨(1, 1), 0, note⟩,
   .grant approval, .approve (1, 0), .deliver (1, 0), .deliver (1, 1)]

/-- **The pipeline works end to end:** before the decision nothing of run 1 has left
the gate (the note is held behind the refund); after it, both land, the refund
tagged with the approval it used. -/
theorem pipeline_lands :
    (sys0.run policy (ops.take 3)).gate.released = [] ∧
    (sys0.run policy ops).prov.landed = [⟨(1, 0), [approvalTag approval.id]⟩, ⟨(1, 1), []⟩] ∧
    (sys0.run policy ops).pop.spent = 500 := by
  decide

/-- Delegated authority: the root delegates refunds to a manager, the manager
approves, the effect is dispatched, then the delegation is revoked before the
provider delivers. -/
def mgrScope : Scope :=
  { actions := ["bank.refund"], resources := ["acct"], maxAmount := 1000, expires := 100 }
def mgrApproval : Approval :=
  { id := 2, target := refund.target, approver := "user:mgr", expires := 10 }
def delegated (revoke : Bool) : List SOp :=
  [.delegate 5 "user:me" "user:mgr" mgrScope none, .propose ⟨(2, 0), 0, refund⟩,
   .grant mgrApproval, .approve (2, 0)] ++
  (if revoke then [.revokeDelegation 5] else []) ++ [.deliver (2, 0)]

/-- **Revoking the delegation drains the dispatched effect:** the carrier is tagged
with the approval and the delegation behind it; without the revocation it lands,
with it nothing lands. -/
theorem delegation_drain_example :
    (sys0.run policy (delegated false)).prov.landed =
      [⟨(2, 0), [approvalTag 2, linkTag 5]⟩] ∧
    (sys0.run policy (delegated true)).prov.landed = [] := by
  decide

end pipelineExample

end FinalSay
