import FinalSay.Core
import FinalSay.Classify

/-!
# Invariants

The five rules every implementation must keep, proved for *all* policies.
-/

namespace FinalSay

theorem firstMatch_eq_none {eff : Effect} {p : Policy} {r : Request}
    (h : ∀ rule ∈ p, rule.cond.eval r = false) : firstMatch eff p r = none := by
  unfold firstMatch
  rw [List.find?_eq_none]
  intro rule hmem
  simp [Rule.fires, h rule hmem]

theorem firstMatch_isSome {eff : Effect} {p : Policy} {r : Request} {rule : Rule}
    (hmem : rule ∈ p) (heff : rule.effect = eff) (hc : rule.cond.eval r = true) :
    (firstMatch eff p r).isSome := by
  unfold firstMatch
  cases hf : p.find? (Rule.fires eff r) with
  | some _ => rfl
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf rule hmem
    simp [Rule.fires, heff, hc] at this

/-- **Invariant 1, deny wins:** a matching deny rule always produces `deny`. -/
theorem deny_wins (p : Policy) (r : Request) (rule : Rule)
    (hmem : rule ∈ p) (heff : rule.effect = .deny) (hc : rule.cond.eval r = true) :
    (evaluate p r).decision = .deny := by
  have hs := firstMatch_isSome hmem heff hc
  unfold evaluate
  cases hf : firstMatch .deny p r with
  | some _ => rfl
  | none => simp [hf] at hs

/-- **Invariant 2, tier-3 safety:** irreversible without approval is never allowed. -/
theorem irreversible_needs_approval (p : Policy) (r : Request)
    (ht : r.tier = .irreversible) (ha : r.approved = false) :
    (evaluate p r).decision ≠ .allow := by
  unfold evaluate
  cases firstMatch .deny p r with
  | some _ => simp
  | none => simp [ht, ha]

/-- **Invariant 3, the exception escalates:** with no approval and no applicable
rule, the answer is `ask`. -/
theorem no_rule_asks (p : Policy) (r : Request)
    (h : ∀ rule ∈ p, rule.cond.eval r = false) (hap : r.approved = false) :
    (evaluate p r).decision = .ask := by
  have hd : firstMatch .deny p r = none := firstMatch_eq_none h
  have ha : firstMatch .allow p r = none := firstMatch_eq_none h
  unfold evaluate
  simp only [hd, ha, hap, Bool.false_eq_true, ite_false]
  split <;> rfl

/-- Converse view of invariant 3: `allow` only ever comes from an approval by an
authority or from a matching allow rule. Nothing is allowed by default. -/
theorem allow_has_reason (p : Policy) (r : Request)
    (h : (evaluate p r).decision = .allow) :
    r.approved = true ∨ ∃ rule, firstMatch .allow p r = some rule := by
  unfold evaluate at h
  cases hd : firstMatch .deny p r with
  | some _ => simp [hd] at h
  | none =>
    simp only [hd] at h
    by_cases hap : r.approved = true
    · exact Or.inl hap
    · right
      simp only [hap, Bool.false_eq_true, ite_false] at h
      split at h
      · simp at h
      · cases ha : firstMatch .allow p r with
        | some rule => exact ⟨rule, rfl⟩
        | none => simp [ha] at h

/-- **Invariant 4a, the owner's map wins** over any hint. -/
theorem owner_map_wins (m : TierMap) (a : String) (hint : Option Tier) (e : Entry)
    (h : m.lookup a = some e) : effectiveTier m a hint = e.effective := by
  simp [effectiveTier, h]

/-- **Invariant 4b, unknown is irreversible:** no owner entry and no opt-in → tier 3. -/
theorem unknown_is_irreversible (m : TierMap) (a : String) (hint : Option Tier)
    (h : m.lookup a = none) (ht : m.trustHints = false) :
    effectiveTier m a hint = .irreversible := by
  simp [effectiveTier, h, ht]

/-- Compensatable only sticks when the owner declared a compensation. -/
theorem compensatable_has_compensation (m : TierMap) (a : String) (hint : Option Tier)
    (h : effectiveTier m a hint = .compensatable) :
    ∃ e, m.lookup a = some e ∧ e.compensation.isSome := by
  unfold effectiveTier at h
  cases hl : m.lookup a with
  | none =>
    simp only [hl] at h
    split at h
    · unfold hintTier at h; split at h <;> simp at h
    · simp at h
  | some e =>
    simp only [hl] at h
    refine ⟨e, rfl, ?_⟩
    unfold Entry.effective at h
    cases hc : e.compensation with
    | some _ => rfl
    | none => cases ht : e.tier <;> simp [ht, hc] at h

/-! ### Invariant 4c: the trifecta rule -/

/-- Unknown actions count as observable. -/
theorem unknown_is_observable (m : TierMap) (a : String) (h : m.lookup a = none) :
    m.observable a = true := by
  simp [TierMap.observable, h]

/-- In a session holding private data and untrusted input, an observable action is irreversible. -/
theorem trifecta_escalates (m : TierMap) (a : String) (hint : Option Tier) (x : Exposure)
    (ht : x.trifecta = true) (ho : m.observable a = true) :
    sessionTier m a hint x = .irreversible := by
  simp [sessionTier, ht, ho]

/-- **The trifecta rule:** for every policy, an observable action in such a session is
never allowed without approval. (A deny rule can still refuse it outright.) -/
theorem trifecta_needs_approval (p : Policy) (m : TierMap) (hint : Option Tier) (x : Exposure)
    (r : Request) (hr : r.tier = sessionTier m r.action hint x)
    (ht : x.trifecta = true) (ho : m.observable r.action = true) (ha : r.approved = false) :
    (evaluate p r).decision ≠ .allow :=
  irreversible_needs_approval p r (hr.trans (trifecta_escalates m r.action hint x ht ho)) ha

/-- Without the full trifecta, classification is unchanged. -/
theorem no_trifecta_unchanged (m : TierMap) (a : String) (hint : Option Tier) (x : Exposure)
    (ht : x.trifecta = false) :
    sessionTier m a hint x = effectiveTier m a hint := by
  simp [sessionTier, ht]

/-- Unobservable actions are unaffected, so the agent can keep working locally. -/
theorem unobservable_unchanged (m : TierMap) (a : String) (hint : Option Tier) (x : Exposure)
    (ho : m.observable a = false) :
    sessionTier m a hint x = effectiveTier m a hint := by
  simp [sessionTier, ho]

/-- The rule only ever escalates: the result is the classified tier or irreversible. -/
theorem trifecta_only_escalates (m : TierMap) (a : String) (hint : Option Tier) (x : Exposure) :
    sessionTier m a hint x = effectiveTier m a hint ∨ sessionTier m a hint x = .irreversible := by
  unfold sessionTier
  split <;> simp

/-- **Invariant 5, fail closed:** a request that can't be parsed is never allowed. -/
theorem malformed_never_allowed (mode : Mode) (p : Policy) (err : String) :
    (evaluateRaw mode p (.malformed err)).decision ≠ .allow := by
  cases mode <;> simp [evaluateRaw]

end FinalSay
