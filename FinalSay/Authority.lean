import FinalSay.Core
import FinalSay.Invariants

/-!
# Invariant 6: an approval counts only if it is exact and current at commit

Reversibility decides *where* authority is exercised and *who* exercises it.
It does not make a given approval valid: invariant 2 (`irreversible_needs_approval`)
is satisfied by any `approved = true`, including one that was revoked, has
expired, was already used, or was given for a different effect.

This module makes approvals data and moves the check to the commit point:

* An `Approval` names the exact effect it covers (`Target`: action, resource,
  amount), when it expires, and whether it is single-use.
* `commitDecide` ignores whatever the request claims about approval and
  re-derives it from the approval store *at commit time*.
* `Sys.step` is a small protocol (grant, revoke, tick, commit) whose log is the
  list of effects that actually happened.

Proved, for every policy and every sequence of operations:
* `commit_ignores_claimed_approval`: the agent cannot approve its own request.
* `irreversible_commit_exact_current`: an irreversible commit has an approval that
  covers exactly that effect, is unexpired, unrevoked and (if single-use) unused.
* `run_log_ok`: every logged effect is bound to the approval it consumed.
* `revocation_is_effective`: after `revoke id`, no later commit consumes `id`.
* `single_use_at_most_once`: a single-use approval backs at most one effect.
* `decision_before_commit_goes_stale`: a decision taken before a revocation would
  allow an effect the commit-time check refuses, so the check must be at commit.

Related work: commit-time authorization and exact-effect binding
(Santos-Grueiro, arXiv 2607.10487); effect closure (arXiv 2609.02866).
-/

namespace FinalSay

/-- The exact effect an approval covers. -/
structure Target where
  action   : String
  resource : String
  amount   : Nat
  /-- The one effect (run, key) this covers, when a gate has assigned ids. Binding to
  the id, not just to (action, resource, amount), stops another identical request,
  e.g. from a forked sub-agent, from consuming an approval granted for this one. -/
  eff      : Option (Nat × Nat) := none
  deriving Repr, DecidableEq

def Request.target (r : Request) : Target := ⟨r.action, r.resource, r.amount, r.eff⟩

/-- An approval from someone with authority, bound to one exact effect. -/
structure Approval where
  id       : Nat
  target   : Target
  approver : String
  /-- Valid while `now < expires` (logical time). -/
  expires  : Nat
  /-- A one-off approval; `false` is a standing grant for this exact target. -/
  oneShot  : Bool := true
  deriving Repr

/-- Approval state held by the gate, outside the agent's reach. -/
structure Store where
  granted : List Approval := []
  revoked : List Nat := []
  used    : List Nat := []
  now     : Nat := 0
  deriving Repr

/-- Does approval `a` cover request `r` right now? -/
def Approval.validFor (s : Store) (r : Request) (a : Approval) : Bool :=
  decide (a.target = r.target) && decide (s.now < a.expires) &&
    !(s.revoked.contains a.id) && !(a.oneShot && s.used.contains a.id)

/-- The approval the gate would consume for `r`, if any. -/
def Store.pick (s : Store) (r : Request) : Option Approval :=
  s.granted.find? (Approval.validFor s r)

/-- The commit-time decision: approval is re-derived from the store, never taken
from the request. -/
def commitDecide (p : Policy) (s : Store) (r : Request) : Response :=
  evaluate p { r with approved := (s.pick r).isSome }

/-- The agent cannot approve its own request: the claimed flag is ignored. -/
theorem commit_ignores_claimed_approval (p : Policy) (s : Store) (r : Request) (b : Bool) :
    commitDecide p s { r with approved := b } = commitDecide p s r := rfl

theorem pick_valid {s : Store} {r : Request} {a : Approval} (h : s.pick r = some a) :
    a ∈ s.granted ∧ a.target = r.target ∧ s.now < a.expires ∧ a.id ∉ s.revoked ∧
      (a.oneShot = true → a.id ∉ s.used) := by
  have hmem := List.mem_of_find?_eq_some h
  have hv := List.find?_some h
  simp only [Approval.validFor, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not, Bool.and_eq_false_iff] at hv
  obtain ⟨⟨⟨ht, hn⟩, hr⟩, hu⟩ := hv
  refine ⟨hmem, ht, hn, hr, fun ho => ?_⟩
  rcases hu with h1 | h1
  · simp [ho] at h1
  · simpa using h1

/-- **Invariant 6, exact and current:** if an irreversible effect is allowed at
commit, some approval in the store covers exactly that effect, has not expired,
has not been revoked, and (if single-use) has not been used. -/
theorem irreversible_commit_exact_current (p : Policy) (s : Store) (r : Request)
    (ht : r.tier = .irreversible) (hal : (commitDecide p s r).decision = .allow) :
    ∃ a ∈ s.granted, a.target = r.target ∧ s.now < a.expires ∧ a.id ∉ s.revoked ∧
      (a.oneShot = true → a.id ∉ s.used) := by
  cases hp : s.pick r with
  | none =>
    have := irreversible_needs_approval p { r with approved := (s.pick r).isSome } ht
      (by simp [hp])
    exact absurd hal this
  | some a =>
    obtain ⟨hm, rest⟩ := pick_valid hp
    exact ⟨a, hm, rest⟩

/-- An approval for a different effect does not help. -/
theorem mismatched_approval_insufficient (p : Policy) (s : Store) (r : Request)
    (ht : r.tier = .irreversible) (hne : ∀ a ∈ s.granted, a.target ≠ r.target) :
    (commitDecide p s r).decision ≠ .allow := fun hal => by
  obtain ⟨a, hm, htg, _⟩ := irreversible_commit_exact_current p s r ht hal
  exact hne a hm htg

/-- A revoked approval does not help. -/
theorem revoked_approval_insufficient (p : Policy) (s : Store) (r : Request)
    (ht : r.tier = .irreversible) (hrev : ∀ a ∈ s.granted, a.target = r.target → a.id ∈ s.revoked) :
    (commitDecide p s r).decision ≠ .allow := fun hal => by
  obtain ⟨a, hm, htg, _, hr, _⟩ := irreversible_commit_exact_current p s r ht hal
  exact hr (hrev a hm htg)

/-! ### The protocol: grant, revoke, tick, commit -/

inductive Op where
  | grant (a : Approval)
  | revoke (id : Nat)
  | tick
  | commit (r : Request)

/-- An effect that actually happened. -/
structure Commit where
  req : Request
  /-- The approval consumed, if any. -/
  via : Option Approval
  /-- Logical time of the commit. -/
  time : Nat

structure Sys where
  store : Store := {}
  log   : List Commit := []

def Store.consume (s : Store) : Option Approval → Store
  | some a => { s with used := a.id :: s.used }
  | none => s

def Sys.step (p : Policy) (sys : Sys) : Op → Sys
  | .grant a => { sys with store := { sys.store with granted := sys.store.granted ++ [a] } }
  | .revoke id => { sys with store := { sys.store with revoked := id :: sys.store.revoked } }
  | .tick => { sys with store := { sys.store with now := sys.store.now + 1 } }
  | .commit r =>
    if (commitDecide p sys.store r).decision = .allow then
      { store := sys.store.consume (sys.store.pick r),
        log := sys.log ++ [⟨r, sys.store.pick r, sys.store.now⟩] }
    else sys

def Sys.run (p : Policy) (sys : Sys) (ops : List Op) : Sys := ops.foldl (Sys.step p) sys

/-- What every logged effect must satisfy. -/
def Commit.Ok (e : Commit) : Prop :=
  (∀ a, e.via = some a → a.target = e.req.target ∧ e.time < a.expires) ∧
    (e.req.tier = .irreversible → e.via.isSome)

theorem step_log (p : Policy) (sys : Sys) (op : Op) :
    ∃ new, (sys.step p op).log = sys.log ++ new ∧ ∀ e ∈ new,
      e.via = sys.store.pick e.req ∧ e.time = sys.store.now ∧
        (commitDecide p sys.store e.req).decision = .allow := by
  cases op with
  | grant a => exact ⟨[], by simp [Sys.step], by simp⟩
  | revoke id => exact ⟨[], by simp [Sys.step], by simp⟩
  | tick => exact ⟨[], by simp [Sys.step], by simp⟩
  | commit r =>
    by_cases h : (commitDecide p sys.store r).decision = .allow
    · exact ⟨[⟨r, sys.store.pick r, sys.store.now⟩], by simp [Sys.step, h], by simp [h]⟩
    · exact ⟨[], by simp [Sys.step, h], by simp⟩

theorem new_entry_ok (p : Policy) (s : Store) (e : Commit) (hv : e.via = s.pick e.req)
    (ht : e.time = s.now) (hal : (commitDecide p s e.req).decision = .allow) : e.Ok := by
  refine ⟨fun a ha => ?_, fun hirr => ?_⟩
  · obtain ⟨_, htg, hn, _⟩ := pick_valid (hv ▸ ha)
    exact ⟨htg, ht ▸ hn⟩
  · cases hp : s.pick e.req with
    | none =>
      exact absurd hal (irreversible_needs_approval p { e.req with approved := _ } hirr (by simp [hp]))
    | some a => simp [hv, hp]

/-- **Every logged effect is bound to the approval it consumed**, which covered
exactly that effect and was unexpired at the time; and no irreversible effect is
logged without one. Holds for every policy and every sequence of operations. -/
theorem run_log_ok (p : Policy) (ops : List Op) :
    ∀ (sys : Sys), (∀ e ∈ sys.log, e.Ok) → ∀ e ∈ (sys.run p ops).log, e.Ok := by
  induction ops with
  | nil => intro sys h; simpa [Sys.run] using h
  | cons op ops ih =>
    intro sys h
    apply ih (sys.step p op)
    obtain ⟨new, hlog, hnew⟩ := step_log p sys op
    intro e he
    rw [hlog, List.mem_append] at he
    rcases he with he | he
    · exact h e he
    · obtain ⟨hv, ht, hal⟩ := hnew e he
      exact new_entry_ok p sys.store e hv ht hal

theorem run_cons (p : Policy) (sys : Sys) (op : Op) (ops : List Op) :
    sys.run p (op :: ops) = (sys.step p op).run p ops := rfl

theorem run_append (p : Policy) (sys : Sys) (xs ys : List Op) :
    sys.run p (xs ++ ys) = (sys.run p xs).run p ys := by
  simp [Sys.run, List.foldl_append]

/-- Revocations are never forgotten. -/
theorem step_revoked_mono (p : Policy) (sys : Sys) (op : Op) (id : Nat)
    (h : id ∈ sys.store.revoked) : id ∈ (sys.step p op).store.revoked := by
  cases op with
  | grant a => simpa [Sys.step] using h
  | revoke i => simp [Sys.step, h]
  | tick => simpa [Sys.step] using h
  | commit r =>
    simp only [Sys.step]
    split
    · cases sys.store.pick r <;> simpa [Store.consume] using h
    · exact h

/-- Single-use marks are never forgotten. -/
theorem step_used_mono (p : Policy) (sys : Sys) (op : Op) (id : Nat)
    (h : id ∈ sys.store.used) : id ∈ (sys.step p op).store.used := by
  cases op with
  | grant a => simpa [Sys.step] using h
  | revoke i => simpa [Sys.step] using h
  | tick => simpa [Sys.step] using h
  | commit r =>
    simp only [Sys.step]
    split
    · cases sys.store.pick r <;> simp [Store.consume, h]
    · exact h

/-- After a revocation, no effect logged from then on consumes that approval. -/
theorem no_use_after_revoke (p : Policy) (id : Nat) (ops : List Op) :
    ∀ (sys : Sys), id ∈ sys.store.revoked →
      ∃ new, (sys.run p ops).log = sys.log ++ new ∧
        ∀ e ∈ new, ∀ a, e.via = some a → a.id ≠ id := by
  induction ops with
  | nil => intro sys _; exact ⟨[], by simp [Sys.run], by simp⟩
  | cons op ops ih =>
    intro sys hrev
    obtain ⟨n1, h1, hn1⟩ := step_log p sys op
    obtain ⟨n2, h2, hn2⟩ := ih (sys.step p op) (step_revoked_mono p sys op id hrev)
    refine ⟨n1 ++ n2, by rw [run_cons, h2, h1, List.append_assoc], ?_⟩
    intro e he a ha
    rw [List.mem_append] at he
    rcases he with he | he
    · obtain ⟨hv, _, _⟩ := hn1 e he
      obtain ⟨_, _, _, hr, _⟩ := pick_valid (hv ▸ ha)
      intro hid; exact hr (hid ▸ hrev)
    · exact hn2 e he a ha

/-- **Revocation is effective:** in any run, once `revoke id` has happened, no later
effect is backed by approval `id`, however long ago it was granted. -/
theorem revocation_is_effective (p : Policy) (sys : Sys) (pre post : List Op) (id : Nat) :
    ∃ new, (sys.run p (pre ++ .revoke id :: post)).log =
        (sys.run p (pre ++ [.revoke id])).log ++ new ∧
      ∀ e ∈ new, ∀ a, e.via = some a → a.id ≠ id := by
  have : pre ++ Op.revoke id :: post = (pre ++ [.revoke id]) ++ post := by simp
  rw [this, run_append]
  apply no_use_after_revoke
  rw [run_append]
  simp [Sys.run, Sys.step]

/-! ### Single use -/

/-- Ids of single-use approvals consumed by the logged effects. -/
def oneShotIds (log : List Commit) : List Nat :=
  log.filterMap fun e => match e.via with
    | some a => if a.oneShot then some a.id else none
    | none => none

theorem oneShotIds_append (l₁ l₂ : List Commit) :
    oneShotIds (l₁ ++ l₂) = oneShotIds l₁ ++ oneShotIds l₂ := by
  simp [oneShotIds, List.filterMap_append]

/-- The single-use invariant: consumed ids are distinct and all marked used. -/
def OnceInv (sys : Sys) : Prop :=
  (oneShotIds sys.log).Nodup ∧ ∀ id ∈ oneShotIds sys.log, id ∈ sys.store.used

theorem oneShotIds_none (r : Request) (t : Nat) : oneShotIds [⟨r, none, t⟩] = [] := rfl

theorem oneShotIds_some (r : Request) (a : Approval) (t : Nat) :
    oneShotIds [⟨r, some a, t⟩] = if a.oneShot then [a.id] else [] := by
  cases h : a.oneShot <;> simp [oneShotIds, h]

theorem step_once (p : Policy) (sys : Sys) (op : Op) (h : OnceInv sys) :
    OnceInv (sys.step p op) := by
  obtain ⟨hnd, hused⟩ := h
  cases op with
  | grant a => exact ⟨hnd, hused⟩
  | revoke i => exact ⟨hnd, hused⟩
  | tick => exact ⟨hnd, hused⟩
  | commit r =>
    simp only [Sys.step]
    split
    · unfold OnceInv
      simp only [oneShotIds_append]
      cases hp : sys.store.pick r with
      | none =>
        rw [oneShotIds_none]
        exact ⟨by simpa using hnd, fun id hid => by
          simp only [List.append_nil] at hid; simpa [Store.consume] using hused id hid⟩
      | some a =>
        obtain ⟨_, _, _, _, hnu⟩ := pick_valid hp
        rw [oneShotIds_some]
        cases ho : a.oneShot
        · exact ⟨by simpa using hnd, fun id hid => by
            simp only [ite_false, Bool.false_eq_true, List.append_nil] at hid
            simp [Store.consume, hused id hid]⟩
        · simp only [ite_true]
          refine ⟨?_, ?_⟩
          · rw [List.nodup_append]
            refine ⟨hnd, by simp, ?_⟩
            intro x hx y hy hxy
            simp at hy
            subst hy; subst hxy
            exact hnu ho (hused _ hx)
          · intro id hid
            simp only [List.mem_append, List.mem_singleton] at hid
            rcases hid with hid | hid
            · simp [Store.consume, hused id hid]
            · simp [Store.consume, hid]
    · exact ⟨hnd, hused⟩

/-- **Single use:** in any run from a clean start, each single-use approval backs at
most one logged effect. -/
theorem single_use_at_most_once (p : Policy) (ops : List Op) :
    (oneShotIds (Sys.run p {} ops).log).Nodup := by
  suffices ∀ sys, OnceInv sys → OnceInv (sys.run p ops) from
    (this {} ⟨by simp [oneShotIds], by simp [oneShotIds]⟩).1
  induction ops with
  | nil => intro sys h; simpa [Sys.run] using h
  | cons op ops ih => intro sys h; exact ih _ (step_once p sys op h)

/-! ### Why the check must be at commit -/

/-- A refund approved for exactly this request. -/
def staleExample.req : Request :=
  { principal := "user:me", agent := "agent", action := "bank.refund",
    resource := "acct", tier := .irreversible, amount := 500 }

def staleExample.approval : Approval :=
  { id := 1, target := staleExample.req.target, approver := "user:me", expires := 10 }

def staleExample.before : Store := { granted := [staleExample.approval] }
def staleExample.after : Store := { staleExample.before with revoked := [1] }

/-- **A decision taken before commit goes stale:** with the same policy and request,
the gate allows before the approval is revoked and refuses after. A gate that decided
once, when the agent proposed the effect, would still let it through. -/
theorem decision_before_commit_goes_stale :
    (commitDecide [] staleExample.before staleExample.req).decision = .allow ∧
    (commitDecide [] staleExample.after staleExample.req).decision ≠ .allow := by
  decide

end FinalSay
