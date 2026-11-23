/-!
# Holding a run while it waits for a human

`ask` escalates one effect to a human. In the frameworks Khan measured
("Stop Means Stop", arXiv 2607.14166), the pause holds only the branch that
asked, so a sibling branch's effect lands while the human is still deciding.
The tiers say the human decides; they say nothing about what else the run may
do in the meantime.

This module models an approval gate keyed by run. An effect is an id
`(run, key)`; it either needs approval (it goes to `pending`) or not. While a run
has anything pending, every other effect of that run is `held`, and released only
after the last decision for that run. A cancelled run is fenced. Ids are
deduplicated: an id is admitted once, ever.

Proved, for every sequence of submissions, decisions and cancellations:
* `barrier`: while a run has an effect awaiting a decision, nothing of that run
  lands except through a decision on that run (B1).
* `rejected_never_lands`: a rejected effect never lands, then or later (B2).
* `lands_at_most_once`: every effect lands at most once (B3).
* `cancel_fences`: after a run is cancelled, nothing of it lands again (B4).
* `per_branch_pause_leaks`: the naive gate, which holds only the effect that
  asked, lets a sibling land while the human is deciding.
-/

namespace FinalSay

/-- An effect: `(run, key)`. -/
abbrev EffId := Nat × Nat

structure Gate where
  /-- Every id ever admitted (dedup). -/
  seen      : List EffId := []
  /-- Awaiting a human decision. -/
  pending   : List EffId := []
  /-- Waiting behind a pending effect of the same run. -/
  held      : List EffId := []
  /-- Landed, in order. -/
  released  : List EffId := []
  rejected  : List EffId := []
  /-- Dropped by a cancellation. -/
  dropped   : List EffId := []
  cancelled : List Nat := []
  deriving Repr

def Gate.blocked (g : Gate) (r : Nat) : Bool := g.pending.any (fun x => x.1 == r)

/-- After a decision, release the run's held effects if nothing of it is pending. -/
def Gate.flush (g : Gate) (r : Nat) : Gate :=
  if g.blocked r then g
  else { g with held := g.held.filter (fun x => !(x.1 == r)),
                released := g.released ++ g.held.filter (fun x => x.1 == r) }

inductive GOp where
  | submit (id : EffId) (needsApproval : Bool)
  | decide (id : EffId) (approve : Bool)
  | cancel (run : Nat)

def Gate.step (g : Gate) : GOp → Gate
  | .submit id needs =>
    if g.cancelled.contains id.1 || g.seen.contains id then g
    else if needs then { g with seen := id :: g.seen, pending := g.pending ++ [id] }
    else if g.blocked id.1 then { g with seen := id :: g.seen, held := g.held ++ [id] }
    else { g with seen := id :: g.seen, released := g.released ++ [id] }
  | .decide id approve =>
    if g.pending.contains id then
      (if approve then
        { g with pending := g.pending.erase id, released := g.released ++ [id] }
      else
        { g with pending := g.pending.erase id, rejected := g.rejected ++ [id] }).flush id.1
    else g
  | .cancel r =>
    { g with cancelled := r :: g.cancelled,
             pending := g.pending.filter (fun x => !(x.1 == r)),
             held := g.held.filter (fun x => !(x.1 == r)),
             dropped := g.dropped ++ g.pending.filter (fun x => x.1 == r) ++
               g.held.filter (fun x => x.1 == r) }

def Gate.run (g : Gate) (ops : List GOp) : Gate := ops.foldl Gate.step g

theorem Gate.run_cons (g : Gate) (op : GOp) (ops : List GOp) :
    g.run (op :: ops) = (g.step op).run ops := rfl

/-- Every admitted effect is in exactly one place. -/
def Gate.all (g : Gate) : List EffId := g.released ++ g.rejected ++ g.dropped ++ g.pending ++ g.held

/-! ### Accounting: effects are moved, never copied -/

theorem count_filter_split (a : EffId) (l : List EffId) (r : Nat) :
    (l.filter (fun x => x.1 == r)).count a + (l.filter (fun x => !(x.1 == r))).count a = l.count a :=
  by simpa [List.count_append] using
    (List.perm_iff_count.mp (List.filter_append_perm (fun x : EffId => x.1 == r) l)) a

theorem flush_count (g : Gate) (r : Nat) (a : EffId) :
    (g.flush r).all.count a = g.all.count a ∧ (g.flush r).seen = g.seen ∧
      (g.flush r).rejected = g.rejected ∧ (g.flush r).cancelled = g.cancelled ∧
      (g.flush r).pending = g.pending := by
  unfold Gate.flush
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨?_, rfl, rfl, rfl, rfl⟩
    have := count_filter_split a g.held r
    simp only [Gate.all, List.count_append] at this ⊢
    omega

/-- One step either moves effects between places or admits one fresh id. -/
theorem step_count (g : Gate) (op : GOp) :
    (∀ a, (g.step op).all.count a = g.all.count a ∧ (g.step op).seen = g.seen) ∨
    (∃ id, id ∉ g.seen ∧ (g.step op).seen = id :: g.seen ∧
      ∀ a, (g.step op).all.count a = g.all.count a + (if id = a then 1 else 0)) := by
  cases op with
  | submit id needs =>
    simp only [Gate.step]
    split
    · left; intro a; exact ⟨rfl, rfl⟩
    · next hc =>
      simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq, not_or] at hc
      right
      refine ⟨id, hc.2, ?_, ?_⟩
      · split
        · rfl
        · split <;> rfl
      · intro a
        split
        · simp only [Gate.all, List.count_append, List.count_cons, List.count_nil]
          by_cases h : id = a <;> simp [h] <;> omega
        · split
          · simp only [Gate.all, List.count_append, List.count_cons, List.count_nil]
            by_cases h : id = a <;> simp [h] <;> omega
          · simp only [Gate.all, List.count_append, List.count_cons, List.count_nil]
            by_cases h : id = a <;> simp [h] <;> omega
  | decide id approve =>
    simp only [Gate.step]
    split
    · next hp =>
      left
      intro a
      have hmem : id ∈ g.pending := by simpa using hp
      have he := List.perm_iff_count.mp (List.perm_cons_erase hmem) a
      split
      · obtain ⟨h1, h2, -⟩ := flush_count
          { g with pending := g.pending.erase id, released := g.released ++ [id] } id.1 a
        refine ⟨?_, h2⟩
        rw [h1]
        simp only [List.count_cons] at he
        simp only [Gate.all, List.count_append, List.count_cons, List.count_nil]
        omega
      · obtain ⟨h1, h2, -⟩ := flush_count
          { g with pending := g.pending.erase id, rejected := g.rejected ++ [id] } id.1 a
        refine ⟨?_, h2⟩
        rw [h1]
        simp only [List.count_cons] at he
        simp only [Gate.all, List.count_append, List.count_cons, List.count_nil]
        omega
    · left; intro a; exact ⟨rfl, rfl⟩
  | cancel r =>
    left
    intro a
    refine ⟨?_, rfl⟩
    have h1 := count_filter_split a g.pending r
    have h2 := count_filter_split a g.held r
    simp only [Gate.step, Gate.all, List.count_append] at h1 h2 ⊢
    omega

/-- The accounting invariant: everything admitted is in one place, once. -/
def Gate.Inv (g : Gate) : Prop := g.all.Nodup ∧ ∀ x ∈ g.all, x ∈ g.seen

theorem step_inv (g : Gate) (op : GOp) (h : g.Inv) : (g.step op).Inv := by
  obtain ⟨hnd, hseen⟩ := h
  rcases step_count g op with hc | ⟨id, hfresh, hs, hc⟩
  · have hp : (g.step op).all.Perm g.all := List.perm_iff_count.mpr (fun a => (hc a).1)
    refine ⟨hp.nodup_iff.mpr hnd, fun x hx => ?_⟩
    rw [(hc x).2]
    exact hseen x (hp.subset hx)
  · have hp : (g.step op).all.Perm (id :: g.all) := by
      rw [List.perm_iff_count]; intro a
      rw [hc a, List.count_cons]
      by_cases h : id = a <;> simp [h]
    have hnot : id ∉ g.all := fun hm => hfresh (hseen id hm)
    refine ⟨hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hnot, hnd⟩), fun x hx => ?_⟩
    rw [hs]
    rcases List.mem_cons.mp (hp.subset hx) with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hseen x h)

theorem run_inv (ops : List GOp) : ∀ (g : Gate), g.Inv → (g.run ops).Inv := by
  induction ops with
  | nil => intro g h; exact h
  | cons op ops ih => intro g h; exact ih _ (step_inv g op h)

theorem empty_inv : Gate.Inv {} := by simp [Gate.Inv, Gate.all]

/-- **B3, at most once:** from an empty gate, every effect lands at most once. -/
theorem lands_at_most_once (ops : List GOp) : (Gate.run {} ops).released.Nodup := by
  have := (run_inv ops {} empty_inv).1
  simp only [Gate.all, List.append_assoc] at this
  exact (List.nodup_append.mp this).1

/-! ### What lands in a step -/

/-- `released` only grows, and rejections are permanent. -/
theorem step_grows (g : Gate) (op : GOp) :
    (∃ new, (g.step op).released = g.released ++ new) ∧
      (∀ x ∈ g.rejected, x ∈ (g.step op).rejected) ∧
      (∀ r ∈ g.cancelled, r ∈ (g.step op).cancelled) := by
  cases op with
  | submit id needs =>
    simp only [Gate.step]
    split
    · exact ⟨⟨[], by simp⟩, fun _ h => h, fun _ h => h⟩
    · split
      · exact ⟨⟨[], by simp⟩, fun _ h => h, fun _ h => h⟩
      · split
        · exact ⟨⟨[], by simp⟩, fun _ h => h, fun _ h => h⟩
        · exact ⟨⟨[id], rfl⟩, fun _ h => h, fun _ h => h⟩
  | decide id approve =>
    simp only [Gate.step]
    split
    · split
      · refine ⟨?_, ?_, ?_⟩
        · unfold Gate.flush; split
          · exact ⟨[id], rfl⟩
          · exact ⟨[id] ++ List.filter (fun x => x.1 == id.1) g.held, by simp⟩
        · intro x hx; rw [(flush_count _ id.1 x).2.2.1]; exact hx
        · intro r hr; rw [(flush_count _ id.1 (0, 0)).2.2.2.1]; exact hr
      · refine ⟨?_, ?_, ?_⟩
        · unfold Gate.flush; split
          · exact ⟨[], by simp⟩
          · exact ⟨_, rfl⟩
        · intro x hx; rw [(flush_count _ id.1 x).2.2.1]; simp [hx]
        · intro r hr; rw [(flush_count _ id.1 (0, 0)).2.2.2.1]; exact hr
    · exact ⟨⟨[], by simp⟩, fun _ h => h, fun _ h => h⟩
  | cancel r =>
    exact ⟨⟨[], by simp [Gate.step]⟩, fun _ h => h, fun _ h => List.mem_cons_of_mem _ h⟩

theorem run_grows (ops : List GOp) : ∀ (g : Gate),
    (∃ new, (g.run ops).released = g.released ++ new) ∧
      (∀ x ∈ g.rejected, x ∈ (g.run ops).rejected) ∧
      (∀ r ∈ g.cancelled, r ∈ (g.run ops).cancelled) := by
  induction ops with
  | nil => intro g; exact ⟨⟨[], by simp [Gate.run]⟩, fun _ h => h, fun _ h => h⟩
  | cons op ops ih =>
    intro g
    obtain ⟨⟨n1, h1⟩, r1, c1⟩ := step_grows g op
    obtain ⟨⟨n2, h2⟩, r2, c2⟩ := ih (g.step op)
    exact ⟨⟨n1 ++ n2, by rw [Gate.run_cons, h2, h1, List.append_assoc]⟩,
      fun x hx => r2 x (r1 x hx), fun r hr => c2 r (c1 r hr)⟩

/-- **B2, a rejected effect never lands**, at the time or at any later point. -/
theorem rejected_never_lands (ops : List GOp) (x : EffId)
    (hx : x ∈ (Gate.run {} ops).rejected) : x ∉ (Gate.run {} ops).released := by
  have := (run_inv ops {} empty_inv).1
  simp only [Gate.all, List.append_assoc] at this
  intro hr
  exact (List.nodup_append.mp this).2.2 x hr x (List.mem_append_left _ hx) rfl

/-! ### B1: the barrier -/

/-- **B1, the barrier:** if run `r` has an effect awaiting a decision, a step that is
not a decision on run `r` lands nothing of run `r`. -/
theorem barrier (g : Gate) (op : GOp) (r : Nat) (hb : g.blocked r = true)
    (hop : ∀ id ap, op = .decide id ap → id.1 ≠ r) :
    ∃ new, (g.step op).released = g.released ++ new ∧ ∀ x ∈ new, x.1 ≠ r := by
  cases op with
  | submit id needs =>
    simp only [Gate.step]
    split
    · exact ⟨[], by simp, by simp⟩
    · split
      · exact ⟨[], by simp, by simp⟩
      · split
        · exact ⟨[], by simp, by simp⟩
        · next hnb =>
          refine ⟨[id], rfl, ?_⟩
          intro x hx hxr
          simp at hx; subst hx
          exact hnb (hxr ▸ hb)
  | decide id ap =>
    have hne := hop id ap rfl
    simp only [Gate.step]
    split
    · split
      · unfold Gate.flush; split
        · exact ⟨[id], rfl, by simpa using hne⟩
        · refine ⟨[id] ++ List.filter (fun x => x.1 == id.1) g.held, by simp, ?_⟩
          intro x hx hxr
          simp only [List.mem_append, List.mem_singleton, List.mem_filter, beq_iff_eq] at hx
          rcases hx with hx | ⟨_, hx⟩
          · exact hne (hx ▸ hxr)
          · exact hne (hx ▸ hxr)
      · unfold Gate.flush; split
        · exact ⟨[], by simp, by simp⟩
        · refine ⟨List.filter (fun x => x.1 == id.1) g.held, rfl, ?_⟩
          intro x hx hxr
          simp only [List.mem_filter, beq_iff_eq] at hx
          exact hne (hx.2 ▸ hxr)
    · exact ⟨[], by simp, by simp⟩
  | cancel r' => exact ⟨[], by simp [Gate.step], by simp⟩

/-! ### B4: cancellation fences -/

/-- Nothing waiting belongs to a cancelled run. -/
def Gate.Fenced (g : Gate) : Prop := ∀ x ∈ g.pending ++ g.held, x.1 ∉ g.cancelled

theorem step_fenced (g : Gate) (op : GOp) (h : g.Fenced) :
    (g.step op).Fenced ∧ ∃ new, (g.step op).released = g.released ++ new ∧
      ∀ x ∈ new, x.1 ∉ g.cancelled := by
  cases op with
  | submit id needs =>
    simp only [Gate.step]
    split
    · exact ⟨h, [], by simp, by simp⟩
    · next hc =>
      simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq, not_or] at hc
      split
      · refine ⟨?_, [], by simp, by simp⟩
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with (hx | hx) | hx
        · exact h x (List.mem_append_left _ hx)
        · exact hx ▸ hc.1
        · exact h x (List.mem_append_right _ hx)
      · split
        · refine ⟨?_, [], by simp, by simp⟩
          intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | (hx | hx)
          · exact h x (List.mem_append_left _ hx)
          · exact h x (List.mem_append_right _ hx)
          · exact hx ▸ hc.1
        · exact ⟨h, [id], rfl, by simpa using hc.1⟩
  | decide id ap =>
    simp only [Gate.step]
    split
    · next hp =>
      have hmem : id ∈ g.pending := by simpa using hp
      have hid : id.1 ∉ g.cancelled := h id (List.mem_append_left _ hmem)
      have hsub : ∀ x ∈ g.pending.erase id ++ g.held, x.1 ∉ g.cancelled := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact h x (List.mem_append_left _ (List.erase_subset hx))
        · exact h x (List.mem_append_right _ hx)
      split
      · unfold Gate.flush; split
        · exact ⟨hsub, [id], rfl, by simpa using hid⟩
        · refine ⟨?_, [id] ++ List.filter (fun x => x.1 == id.1) g.held, by simp, ?_⟩
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hsub x (List.mem_append_left _ hx)
            · exact hsub x (List.mem_append_right _ (List.mem_filter.mp hx).1)
          · intro x hx
            simp only [List.mem_append, List.mem_singleton, List.mem_filter] at hx
            rcases hx with hx | ⟨hx, _⟩
            · exact hx ▸ hid
            · exact hsub x (List.mem_append_right _ hx)
      · unfold Gate.flush; split
        · exact ⟨hsub, [], by simp, by simp⟩
        · refine ⟨?_, List.filter (fun x => x.1 == id.1) g.held, rfl, ?_⟩
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hsub x (List.mem_append_left _ hx)
            · exact hsub x (List.mem_append_right _ (List.mem_filter.mp hx).1)
          · intro x hx
            exact hsub x (List.mem_append_right _ (List.mem_filter.mp hx).1)
    · exact ⟨h, [], by simp, by simp⟩
  | cancel r =>
    refine ⟨?_, [], by simp [Gate.step], by simp⟩
    intro x hx
    simp only [Gate.step, List.mem_append, List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq, List.mem_cons, not_or] at hx ⊢
    rcases hx with ⟨hx, hr⟩ | ⟨hx, hr⟩
    · exact ⟨hr, h x (List.mem_append_left _ hx)⟩
    · exact ⟨hr, h x (List.mem_append_right _ hx)⟩

/-- **B4, cancellation fences:** once run `r` is cancelled, nothing of `r` lands in
any later step, including effects that were pending or held at the time and
effects a late branch submits afterwards. -/
theorem cancel_fences (r : Nat) (ops : List GOp) : ∀ (g : Gate), g.Fenced → r ∈ g.cancelled →
    ∃ new, (g.run ops).released = g.released ++ new ∧ ∀ x ∈ new, x.1 ≠ r := by
  induction ops with
  | nil => intro g _ _; exact ⟨[], by simp [Gate.run], by simp⟩
  | cons op ops ih =>
    intro g hf hr
    obtain ⟨hf', n1, h1, hn1⟩ := step_fenced g op hf
    obtain ⟨n2, h2, hn2⟩ := ih (g.step op) hf' ((step_grows g op).2.2 r hr)
    refine ⟨n1 ++ n2, by rw [Gate.run_cons, h2, h1, List.append_assoc], ?_⟩
    intro x hx hxr
    rcases List.mem_append.mp hx with hx | hx
    · exact hn1 x hx (hxr ▸ hr)
    · exact hn2 x hx hxr

theorem run_fenced (ops : List GOp) : ∀ (g : Gate), g.Fenced → (g.run ops).Fenced := by
  induction ops with
  | nil => intro g h; exact h
  | cons op ops ih => intro g h; exact ih _ (step_fenced g op h).1

/-- B4 from a clean start: after `cancel r`, no later effect of run `r` lands. -/
theorem cancel_fences_run (pre post : List GOp) (r : Nat) :
    ∃ new, (Gate.run {} (pre ++ .cancel r :: post)).released =
        (Gate.run {} (pre ++ [.cancel r])).released ++ new ∧ ∀ x ∈ new, x.1 ≠ r := by
  have e : pre ++ GOp.cancel r :: post = (pre ++ [.cancel r]) ++ post := by simp
  have hrun : ∀ xs ys, Gate.run {} (xs ++ ys) = (Gate.run {} xs).run ys := by
    intro xs ys; simp [Gate.run, List.foldl_append]
  rw [e, hrun]
  apply cancel_fences
  · exact run_fenced _ _ (by simp [Gate.Fenced])
  · rw [hrun]; simp [Gate.run, Gate.step]

/-! ### The naive gate leaks -/

/-- Per-branch pause: only the effect that needs approval waits. -/
def Gate.stepNaive (g : Gate) : GOp → Gate
  | .submit id needs =>
    if g.cancelled.contains id.1 || g.seen.contains id then g
    else if needs then { g with seen := id :: g.seen, pending := g.pending ++ [id] }
    else { g with seen := id :: g.seen, released := g.released ++ [id] }
  | op => g.step op

/-- **The sibling leak:** run 1 asks for approval of effect `(1, 0)`; while the
human is still deciding, a sibling branch submits `(1, 1)`. The per-branch pause
lands it; the barrier holds it. -/
theorem per_branch_pause_leaks :
    let ops := [GOp.submit (1, 0) true, .submit (1, 1) false]
    (ops.foldl Gate.stepNaive {}).released = [(1, 1)] ∧
    (Gate.run {} ops).released = [] := by
  decide

end FinalSay
