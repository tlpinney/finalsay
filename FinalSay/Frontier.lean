/-!
# Draining in-flight work after revocation

The commit point is where the gate decides, but the effect lands later, at the
provider: a queued message, a webhook, a scheduled job. Revoking an approval stops
new commits (`FinalSay.Authority.revocation_is_effective`), yet carriers already
handed to the provider can still land, and the provider may redeliver them.
Santos-Grueiro ("When Does Authorization End?", arXiv 2609.02866) calls the point
after which an effect can no longer be prevented the *effect frontier*.

This module models a provider boundary. `dispatch` hands a carrier (an
idempotency key and the grant that authorized it) to the provider; `deliver`
lands it; `retry` is the provider redelivering a carrier it has seen; `revoke`
withdraws a grant. The mediator:

* refuses to dispatch under a revoked grant (stops future use),
* on revocation, drops every in-flight carrier of that grant (the fence), and
* lands each idempotency key at most once (bind), so redelivery is harmless.

Proved, for every sequence of operations:
* `revocation_drains`: once a grant is revoked, nothing authorized by it lands
  again, including carriers already in flight and provider redeliveries.
* `key_lands_at_most_once`: each idempotency key lands at most once.
* `in_flight_outlives_revocation`: a mediator that only refuses new dispatches
  still lets an in-flight carrier land after revocation.
* `redelivery_duplicates`: without binding to the key, a provider retry lands
  the same effect twice.
-/

namespace FinalSay

/-- An effect handed to the provider. -/
structure Carrier where
  /-- Idempotency key: the effect's `(run, key)` id. -/
  key    : Nat × Nat
  /-- Everything that authorized it (an approval, the delegations behind it). Revoking
  any one of them fences the carrier. -/
  grants : List Nat
  deriving Repr, DecidableEq

structure Provider where
  inflight : List Carrier := []
  landed   : List Carrier := []
  revoked  : List Nat := []
  deriving Repr

inductive FOp where
  | dispatch (key : Nat × Nat) (grants : List Nat)
  | deliver (key : Nat × Nat)
  | retry (key : Nat × Nat)
  | revoke (grant : Nat)

def Provider.landedKey (s : Provider) (k : Nat × Nat) : Bool := s.landed.any (fun c => c.key == k)

def Provider.step (s : Provider) : FOp → Provider
  | .dispatch k gs =>
    if gs.any (fun g => s.revoked.contains g) then s
    else { s with inflight := s.inflight ++ [⟨k, gs⟩] }
  | .deliver k =>
    match s.inflight.find? (fun c => c.key == k) with
    | some c =>
      if s.landedKey k then { s with inflight := s.inflight.erase c }
      else { s with inflight := s.inflight.erase c, landed := s.landed ++ [c] }
    | none => s
  | .retry k =>
    match (s.landed ++ s.inflight).find? (fun c => c.key == k) with
    | some c => { s with inflight := s.inflight ++ [c] }
    | none => s
  | .revoke g =>
    { s with revoked := g :: s.revoked, inflight := s.inflight.filter (fun c => !(c.grants.contains g)) }

def Provider.run (s : Provider) (ops : List FOp) : Provider := ops.foldl Provider.step s

theorem Provider.run_cons (s : Provider) (op : FOp) (ops : List FOp) :
    s.run (op :: ops) = (s.step op).run ops := rfl

/-- In-flight carriers of a revoked grant are only redeliveries of keys that already
landed, which the bind step will drop. -/
def Provider.Drained (s : Provider) : Prop :=
  ∀ c ∈ s.inflight, (∃ g ∈ c.grants, g ∈ s.revoked) → s.landedKey c.key = true

theorem landedKey_of_mem {s : Provider} {c : Carrier} (h : c ∈ s.landed) : s.landedKey c.key = true := by
  simp only [Provider.landedKey, List.any_eq_true, beq_iff_eq]; exact ⟨c, h, rfl⟩

theorem step_drained (s : Provider) (op : FOp) (h : s.Drained) :
    (s.step op).Drained ∧ (∀ g ∈ s.revoked, g ∈ (s.step op).revoked) ∧
      ∃ new, (s.step op).landed = s.landed ++ new ∧ ∀ c ∈ new, ∀ g ∈ c.grants, g ∉ s.revoked := by
  cases op with
  | dispatch k gs =>
    simp only [Provider.step]
    split
    · exact ⟨h, fun _ h => h, [], by simp, by simp⟩
    · next hg =>
      refine ⟨?_, fun _ h => h, [], by simp, by simp⟩
      intro c hc hr
      rcases List.mem_append.mp hc with hc | hc
      · exact h c hc hr
      · simp at hc; subst hc
        obtain ⟨g, hgm, hgr⟩ := hr
        simp only [List.any_eq_true, List.contains_eq_mem, decide_eq_true_eq, not_exists,
          not_and] at hg
        exact absurd hgr (hg g hgm)
  | deliver k =>
    simp only [Provider.step]
    split
    · next c hf =>
      have hck : c.key = k := by simpa using List.find?_some hf
      split
      · refine ⟨?_, fun _ h => h, [], by simp, by simp⟩
        intro c' hc' hr
        exact h c' (List.erase_subset hc') hr
      · next hnl =>
        refine ⟨?_, fun _ h => h, [c], rfl, ?_⟩
        · intro c' hc' hr
          have := h c' (List.erase_subset hc') hr
          simp only [Provider.landedKey, List.any_eq_true] at this ⊢
          obtain ⟨d, hd, hdk⟩ := this
          exact ⟨d, List.mem_append_left _ hd, hdk⟩
        · intro c' hc' g hg hr
          simp at hc'; subst hc'
          have := h c' (List.mem_of_find?_eq_some hf) ⟨g, hg, hr⟩
          rw [hck] at this
          exact hnl this
    · exact ⟨h, fun _ h => h, [], by simp, by simp⟩
  | retry k =>
    simp only [Provider.step]
    split
    · next c hf =>
      refine ⟨?_, fun _ h => h, [], by simp, by simp⟩
      intro c' hc' hr
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact h c' hc' hr
      · simp at hc'; subst hc'
        rcases List.mem_append.mp (List.mem_of_find?_eq_some hf) with hm | hm
        · exact landedKey_of_mem hm
        · exact h _ hm hr
    · exact ⟨h, fun _ h => h, [], by simp, by simp⟩
  | revoke g =>
    refine ⟨?_, fun _ h => List.mem_cons_of_mem _ h, [], by simp [Provider.step], by simp⟩
    intro c hc hr
    simp only [Provider.step, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, List.mem_cons] at hc hr ⊢
    obtain ⟨g', hg', hr⟩ := hr
    rcases hr with hr | hr
    · subst hr; exact absurd hg' hc.2
    · exact h c hc.1 ⟨g', hg', hr⟩

/-- From any drained state where `g` is already revoked, nothing of `g` lands. -/
theorem drains_from (g : Nat) (ops : List FOp) : ∀ (s : Provider), s.Drained → g ∈ s.revoked →
    ∃ new, (s.run ops).landed = s.landed ++ new ∧ ∀ c ∈ new, g ∉ c.grants := by
  induction ops with
  | nil => intro s _ _; exact ⟨[], by simp [Provider.run], by simp⟩
  | cons op ops ih =>
    intro s hd hg
    obtain ⟨hd', hmono, n1, h1, hn1⟩ := step_drained s op hd
    obtain ⟨n2, h2, hn2⟩ := ih (s.step op) hd' (hmono g hg)
    refine ⟨n1 ++ n2, by rw [Provider.run_cons, h2, h1, List.append_assoc], ?_⟩
    intro c hc hcg
    rcases List.mem_append.mp hc with hc | hc
    · exact hn1 c hc g hcg hg
    · exact hn2 c hc hcg

theorem run_drained (ops : List FOp) : ∀ (s : Provider), s.Drained → (s.run ops).Drained := by
  induction ops with
  | nil => intro s h; exact h
  | cons op ops ih => intro s h; exact ih _ (step_drained s op h).1

/-- **Revocation drains:** from an empty provider, once `revoke g` has happened,
nothing authorized by `g` lands again, whether it was dispatched before the
revocation and still in flight, redelivered by the provider, or attempted after. -/
theorem revocation_drains (pre post : List FOp) (g : Nat) :
    ∃ new, (Provider.run {} (pre ++ .revoke g :: post)).landed =
        (Provider.run {} (pre ++ [.revoke g])).landed ++ new ∧ ∀ c ∈ new, g ∉ c.grants := by
  have hrun : ∀ xs ys, Provider.run {} (xs ++ ys) = (Provider.run {} xs).run ys := by
    intro xs ys; simp [Provider.run, List.foldl_append]
  have e : pre ++ FOp.revoke g :: post = (pre ++ [.revoke g]) ++ post := by simp
  rw [e, hrun]
  apply drains_from
  · exact run_drained _ _ (by simp [Provider.Drained])
  · rw [hrun]; simp [Provider.run, Provider.step]

/-! ### Bind: each key lands once -/

theorem step_keys_nodup (s : Provider) (op : FOp) (h : (s.landed.map Carrier.key).Nodup) :
    ((s.step op).landed.map Carrier.key).Nodup := by
  cases op with
  | dispatch k gs => simp only [Provider.step]; split <;> exact h
  | deliver k =>
    simp only [Provider.step]
    split
    · next c hf =>
      have hck : c.key = k := by simpa using List.find?_some hf
      split
      · exact h
      · next hnl =>
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [List.nodup_append]
        refine ⟨h, by simp, ?_⟩
        intro x hx y hy hxy
        simp at hy; subst hy; subst hxy
        obtain ⟨d, hd, hdk⟩ := List.mem_map.mp hx
        apply hnl
        simp only [Provider.landedKey, List.any_eq_true, beq_iff_eq]
        exact ⟨d, hd, hdk.trans hck⟩
    · exact h
  | retry k => simp only [Provider.step]; split <;> exact h
  | revoke g => exact h

/-- **Each idempotency key lands at most once**, however often the provider
redelivers. -/
theorem key_lands_at_most_once (ops : List FOp) :
    ((Provider.run {} ops).landed.map Carrier.key).Nodup := by
  suffices ∀ s : Provider, (s.landed.map Carrier.key).Nodup →
      ((s.run ops).landed.map Carrier.key).Nodup from this {} (by simp)
  induction ops with
  | nil => intro s h; exact h
  | cons op ops ih => intro s h; exact ih _ (step_keys_nodup s op h)

/-! ### What goes wrong without the fence or the bind -/

/-- A mediator that only refuses new dispatches under a revoked grant. -/
def Provider.stepNoFence (s : Provider) : FOp → Provider
  | .revoke g => { s with revoked := g :: s.revoked }
  | op => s.step op

/-- **In-flight work outlives revocation:** dispatch under grant 7, revoke 7, and
the provider delivers. Without the fence the effect lands after revocation, even
though new dispatches under 7 are refused. -/
theorem in_flight_outlives_revocation :
    let ops := [FOp.dispatch (0, 1) [7], .revoke 7, .dispatch (0, 2) [7], .deliver (0, 1), .deliver (0, 2)]
    (ops.foldl Provider.stepNoFence {}).landed = [⟨(0, 1), [7]⟩] ∧
    (Provider.run {} ops).landed = [] := by
  decide

/-- Delivery without binding to the idempotency key. -/
def Provider.stepNoBind (s : Provider) : FOp → Provider
  | .deliver k =>
    match s.inflight.find? (fun c => c.key == k) with
    | some c => { s with inflight := s.inflight.erase c, landed := s.landed ++ [c] }
    | none => s
  | op => s.step op

/-- **Redelivery duplicates:** the provider retries a delivered message. Without the
bind it lands twice; with it, once. -/
theorem redelivery_duplicates :
    let ops := [FOp.dispatch (0, 1) [7], .deliver (0, 1), .retry (0, 1), .deliver (0, 1)]
    (ops.foldl Provider.stepNoBind {}).landed = [⟨(0, 1), [7]⟩, ⟨(0, 1), [7]⟩] ∧
    (Provider.run {} ops).landed = [⟨(0, 1), [7]⟩] := by
  decide

end FinalSay
