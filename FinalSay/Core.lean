/-!
# Core governance model

Reversibility tiers, decisions, requests, and policies as plain data.
`evaluate` builds the invariants into its structure, so they hold for
every policy, not just a particular one (see `FinalSay.Invariants`).
-/

namespace FinalSay

/-- Reversibility class of an action. -/
inductive Tier where
  /-- Can still be prevented, or the state that matters restored, from inside the
  boundary, before anything outside it the owner doesn't control acts on it (an
  audit log entry doesn't count against this). The agent decides. -/
  | reversible
  /-- Can't be undone, but a declared compensating action counteracts it. Policy decides. -/
  | compensatable
  /-- No restoration and no adequate compensation. A human with authority decides. -/
  | irreversible
  deriving Repr, DecidableEq, Inhabited

def Tier.name : Tier → String
  | .reversible => "reversible"
  | .compensatable => "compensatable"
  | .irreversible => "irreversible"

/-- The three possible outcomes for a tool call. -/
inductive Decision where
  | allow
  | ask
  | deny
  deriving Repr, DecidableEq, Inhabited

/-- A normalized tool call, ready for a decision. -/
structure Request where
  principal : String
  agent     : String
  /-- Semantic action name, e.g. `email.send`, not the raw tool name. -/
  action    : String
  resource  : String
  /-- Effective tier, filled in by classification (`FinalSay.Classify`). -/
  tier      : Tier
  /-- An approval (one-off or standing grant) from an authority is present. -/
  approved  : Bool := false
  /-- Untrusted content entered the session earlier (from the trace). -/
  tainted   : Bool := false
  /-- Amount involved, e.g. a refund in dollars. -/
  amount    : Nat := 0
  /-- The specific effect this request is, once a gate has assigned it an id
  (run, key). `none` outside a gate. Approvals bind to it (`FinalSay.Authority`). -/
  eff       : Option (Nat × Nat) := none
  deriving Repr

/-- A tiny condition language, so policies are data and proofs cover all of them. -/
inductive Cond where
  | always
  | actionIs (a : String)
  | actionPrefix (p : String)
  | tierIs (t : Tier)
  | isTainted
  | amountAtMost (n : Nat)
  | and (c₁ c₂ : Cond)
  | not (c : Cond)
  deriving Repr

def Cond.eval : Cond → Request → Bool
  | .always,         _ => true
  | .actionIs a,     r => r.action == a
  | .actionPrefix p, r => r.action.startsWith p
  | .tierIs t,       r => decide (r.tier = t)
  | .isTainted,      r => r.tainted
  | .amountAtMost n, r => decide (r.amount ≤ n)
  | .and c₁ c₂,      r => c₁.eval r && c₂.eval r
  | .not c,          r => !c.eval r

inductive Effect where
  | allow
  | deny
  deriving Repr, DecidableEq

structure Rule where
  name   : String
  effect : Effect
  cond   : Cond
  deriving Repr

abbrev Policy := List Rule

structure Response where
  decision : Decision
  /-- The rule that produced the decision, if any. -/
  rule     : Option String
  reason   : String
  deriving Repr

/-- Does `rule` have effect `eff` and match `r`? -/
def Rule.fires (eff : Effect) (r : Request) (rule : Rule) : Bool :=
  decide (rule.effect = eff) && rule.cond.eval r

/-- First rule in the policy with effect `eff` that matches the request. -/
def firstMatch (eff : Effect) (p : Policy) (r : Request) : Option Rule :=
  p.find? (Rule.fires eff r)

/--
The decision function.

1. Any matching deny rule → `deny` (deny wins, even over an approval).
2. Approved by someone with authority → `allow`.
3. Irreversible without approval → `ask` (tier-3 safety).
4. Any matching allow rule → `allow`.
5. Otherwise → `ask` (the case nobody wrote a rule for escalates).
-/
def evaluate (p : Policy) (r : Request) : Response :=
  match firstMatch .deny p r with
  | some rule => ⟨.deny, some rule.name, s!"denied by rule '{rule.name}'"⟩
  | none =>
    if r.approved then
      ⟨.allow, none, "approved by someone with authority"⟩
    else if r.tier = .irreversible then
      ⟨.ask, none, "irreversible action: needs approval from someone with authority"⟩
    else
      match firstMatch .allow p r with
      | some rule => ⟨.allow, some rule.name, s!"allowed by rule '{rule.name}'"⟩
      | none => ⟨.ask, none, "no rule applies: escalating"⟩

/-- How to fail when a request can't be understood. -/
inductive Mode where
  | interactive
  | headless
  deriving Repr, DecidableEq

/-- Raw input at the boundary: either a parsed request or a parse failure. -/
inductive RawInput where
  | parsed (r : Request)
  | malformed (err : String)

/-- Evaluate raw input, failing closed when it can't be parsed. -/
def evaluateRaw (mode : Mode) (p : Policy) : RawInput → Response
  | .parsed r => evaluate p r
  | .malformed err =>
    match mode with
    | .interactive => ⟨.ask, none, s!"could not understand the request ({err}): escalating"⟩
    | .headless    => ⟨.deny, none, s!"could not understand the request ({err}): no one to ask"⟩

end FinalSay
