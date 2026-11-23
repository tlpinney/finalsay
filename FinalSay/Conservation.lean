import FinalSay.Core

/-!
# Invariant 7: forking moves authority, it never copies it

The tiers assume one agent. With sub-agents or parallel branches, a budget or a
single-use approval held by a parent must not reappear in full in each child,
or every fork multiplies what one human approved.

This module models a population of agents holding a spending budget and a set
of single-use grants (approval ids). Three operations:

* `fork parent child share give`: the child gets `share` of the parent's budget
  and the grants listed in `give`; the parent keeps only the rest.
* `spend agent n`: spend from the agent's own budget.
* `use agent g`: consume a single-use grant the agent holds.

Proved, for every sequence of operations from any starting population:
* `budget_conserved`: total budget held + total spent is constant, so
  `spent_le_root`: the population never spends more than it started with.
* `grants_conserved`: grants held + grants used is a permutation of the
  starting grants, so `grant_used_at_most_once`: each grant is used at most
  once across the whole population, however many times agents fork.
* `copy_on_fork_overspends`: the naive alternative (a child gets a copy of its
  parent's authority) lets a population spend more than was ever granted.

Related work: authority conservation for self-modifying agent populations
(Zhu & Wang, arXiv 2610.00347); sibling-branch barrier leaks (Khan, arXiv 2607.14166).
-/

namespace FinalSay

structure Holder where
  name   : String
  budget : Nat
  /-- Ids of single-use approvals this agent holds. -/
  grants : List Nat
  deriving Repr

structure Pop where
  agents : List Holder
  spent  : Nat := 0
  /-- Grants consumed so far. -/
  used   : List Nat := []
  deriving Repr

inductive PopOp where
  | fork (parent : Nat) (child : String) (share : Nat) (give : List Nat)
  | spend (agent : Nat) (n : Nat)
  | use (agent : Nat) (grant : Nat)

def Pop.step (s : Pop) : PopOp → Pop
  | .fork i c share give =>
    match s.agents[i]? with
    | some h =>
      if share ≤ h.budget then
        { s with agents :=
            s.agents.set i { h with budget := h.budget - share,
                                    grants := h.grants.filter (fun g => !(give.contains g)) } ++
            [⟨c, share, h.grants.filter (fun g => give.contains g)⟩] }
      else s
    | none => s
  | .spend i n =>
    match s.agents[i]? with
    | some h =>
      if n ≤ h.budget then
        { s with agents := s.agents.set i { h with budget := h.budget - n }, spent := s.spent + n }
      else s
    | none => s
  | .use i g =>
    match s.agents[i]? with
    | some h =>
      if g ∈ h.grants then
        { s with agents := s.agents.set i { h with grants := h.grants.erase g }, used := g :: s.used }
      else s
    | none => s

def Pop.run (s : Pop) (ops : List PopOp) : Pop := ops.foldl Pop.step s

def Pop.totalBudget (s : Pop) : Nat := (s.agents.map Holder.budget).sum
def Pop.held (s : Pop) : List Nat := s.agents.flatMap Holder.grants

/-! ### List lemmas -/

theorem sum_set (f : Holder → Nat) :
    ∀ (l : List Holder) (i : Nat) (h h' : Holder), l[i]? = some h →
      ((l.set i h').map f).sum + f h = (l.map f).sum + f h'
  | [], i, _, _, hi => by simp at hi
  | x :: xs, 0, h, h', hi => by
    simp at hi; subst hi; simp; omega
  | x :: xs, i + 1, h, h', hi => by
    simp at hi
    have := sum_set f xs i h h' hi
    simp at this ⊢; omega

theorem count_flatMap_set (a : Nat) :
    ∀ (l : List Holder) (i : Nat) (h h' : Holder), l[i]? = some h →
      (( l.set i h').flatMap Holder.grants).count a + h.grants.count a =
        (l.flatMap Holder.grants).count a + h'.grants.count a
  | [], i, _, _, hi => by simp at hi
  | x :: xs, 0, h, h', hi => by
    simp at hi; subst hi; simp [List.count_append]; omega
  | x :: xs, i + 1, h, h', hi => by
    simp at hi
    have := count_flatMap_set a xs i h h' hi
    simp [List.count_append]; omega

/-! ### Budget conservation -/

theorem step_budget (s : Pop) (op : PopOp) :
    (s.step op).totalBudget + (s.step op).spent = s.totalBudget + s.spent := by
  cases op with
  | fork i c share give =>
    simp only [Pop.step]
    split
    · next h hi =>
      split
      · have := sum_set Holder.budget s.agents i h
          { h with budget := h.budget - share,
                   grants := h.grants.filter (fun g => !(give.contains g)) } hi
        simp [Pop.totalBudget] at this ⊢; omega
      · rfl
    · rfl
  | spend i n =>
    simp only [Pop.step]
    split
    · next h hi =>
      split
      · have := sum_set Holder.budget s.agents i h { h with budget := h.budget - n } hi
        simp [Pop.totalBudget] at this ⊢; omega
      · rfl
    · rfl
  | use i g =>
    simp only [Pop.step]
    split
    · next h hi =>
      split
      · have := sum_set Holder.budget s.agents i h { h with grants := h.grants.erase g } hi
        simp [Pop.totalBudget] at this ⊢; omega
      · rfl
    · rfl

/-- **Budget is conserved:** across any sequence of forks, spends and grant uses,
budget held by the population plus budget spent never changes. -/
theorem budget_conserved (ops : List PopOp) : ∀ (s : Pop),
    (s.run ops).totalBudget + (s.run ops).spent = s.totalBudget + s.spent := by
  induction ops with
  | nil => intro s; rfl
  | cons op ops ih => intro s; rw [Pop.run, List.foldl_cons, ← Pop.run, ih, step_budget]

/-- **No overspending:** a population that starts with one root budget and nothing
spent never spends more than that budget, however its agents fork. -/
theorem spent_le_root (root : Holder) (ops : List PopOp) :
    (Pop.run { agents := [root] } ops).spent ≤ root.budget := by
  have := budget_conserved ops { agents := [root] }
  simp [Pop.totalBudget] at this; omega

/-! ### Grant conservation -/

theorem step_grants (s : Pop) (op : PopOp) :
    ((s.step op).held ++ (s.step op).used).Perm (s.held ++ s.used) := by
  rw [List.perm_iff_count]
  intro a
  cases op with
  | fork i c share give =>
    simp only [Pop.step]
    split
    · next h hi =>
      split
      · have hs := count_flatMap_set a s.agents i h
          { h with budget := h.budget - share,
                   grants := h.grants.filter (fun g => !(give.contains g)) } hi
        have hf := (List.perm_iff_count.mp
          (List.filter_append_perm (fun g => give.contains g) h.grants)) a
        simp only [List.count_append] at hf
        simp only [Pop.held, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.count_append, List.append_nil] at hs ⊢
        omega
      · rfl
    · rfl
  | spend i n =>
    simp only [Pop.step]
    split
    · next h hi =>
      split
      · have hs := count_flatMap_set a s.agents i h { h with budget := h.budget - n } hi
        simp only [Pop.held, List.count_append] at hs ⊢
        omega
      · rfl
    · rfl
  | use i g =>
    simp only [Pop.step]
    split
    · next h hi =>
      split
      · next hg =>
        have hs := count_flatMap_set a s.agents i h { h with grants := h.grants.erase g } hi
        have he := (List.perm_iff_count.mp (List.perm_cons_erase hg)) a
        simp only [List.count_cons] at he
        simp only [Pop.held, List.count_append, List.count_cons] at hs ⊢
        omega
      · rfl
    · rfl

/-- **Grants are conserved:** grants held plus grants used is always a permutation
of the starting grants. Forking moves a grant; it never duplicates one. -/
theorem grants_conserved (ops : List PopOp) : ∀ (s : Pop),
    ((s.run ops).held ++ (s.run ops).used).Perm (s.held ++ s.used) := by
  induction ops with
  | nil => intro s; exact List.Perm.refl _
  | cons op ops ih =>
    intro s
    rw [Pop.run, List.foldl_cons, ← Pop.run]
    exact (ih (s.step op)).trans (step_grants s op)

/-- **Each grant is used at most once** across the whole population, however its
agents fork, provided the root started with distinct grants. -/
theorem grant_used_at_most_once (root : Holder) (hnd : root.grants.Nodup) (ops : List PopOp) :
    (Pop.run { agents := [root] } ops).used.Nodup := by
  have hp := grants_conserved ops { agents := [root] }
  have : ((Pop.run { agents := [root] } ops).held ++ (Pop.run { agents := [root] } ops).used).Nodup := by
    rw [hp.nodup_iff]; simpa [Pop.held] using hnd
  exact (List.nodup_append.mp this).2.1

/-! ### The alternative fails -/

/-- Naive fork: the child gets a copy of the parent's budget and grants. -/
def Pop.stepCopy (s : Pop) : PopOp → Pop
  | .fork i c _ _ =>
    match s.agents[i]? with
    | some h => { s with agents := s.agents ++ [{ h with name := c }] }
    | none => s
  | op => s.step op

/-- **Copy-on-fork overspends:** fork once, let parent and child each spend the
full budget, and the population has spent twice what was granted. -/
theorem copy_on_fork_overspends :
    let root : Holder := ⟨"root", 100, []⟩
    let ops := [PopOp.fork 0 "child" 0 [], .spend 0 100, .spend 1 100]
    (ops.foldl Pop.stepCopy { agents := [root] }).spent = 200 ∧
    (Pop.run { agents := [root] } ops).spent = 100 := by
  decide

end FinalSay
