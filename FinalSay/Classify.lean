import FinalSay.Core

/-!
# Classification

Which tier an action belongs to. Classification is owned by the policy
owner: the owner's tier map always wins, tool-declared hints count only
if the owner opts in, and anything unknown is irreversible.
-/

namespace FinalSay

/-- An owner-declared classification for one action. -/
structure Entry where
  action       : String
  tier         : Tier
  /-- The compensating action, required for a compensatable tier to stick. -/
  compensation : Option String := none
  /-- Can someone outside see that it happened, or what it contained? Anything an
  outsider can observe can carry information out (a covert channel). Defaults to
  `true`: an owner must say an action is unobservable. -/
  observable   : Bool := true
  /-- Does the action bring private data into the session? -/
  readsPrivate : Bool := false
  /-- Does the action always bring untrusted content in (web pages, inbound email)?
  Harnesses that can't inspect results label at decision time from this flag. -/
  readsUntrusted : Bool := false
  deriving Repr

structure TierMap where
  entries    : List Entry
  /-- Whether tool-declared hints (e.g. MCP annotations) are trusted for unmapped actions. -/
  trustHints : Bool := false
  deriving Repr

def TierMap.lookup (m : TierMap) (action : String) : Option Entry :=
  m.entries.find? (fun e => e.action == action)

/-- Compensatable without a declared compensation is really irreversible. -/
def Entry.effective (e : Entry) : Tier :=
  match e.tier, e.compensation with
  | .compensatable, none => .irreversible
  | t, _ => t

/-- A hint can't declare a compensation, so a compensatable hint counts as irreversible. -/
def hintTier : Option Tier → Tier
  | some .reversible => .reversible
  | _ => .irreversible

def effectiveTier (m : TierMap) (action : String) (hint : Option Tier) : Tier :=
  match m.lookup action with
  | some e => e.effective
  | none => if m.trustHints then hintTier hint else .irreversible

/-! ## The trifecta rule

A leak needs three things in one session: private data, untrusted input, and a
way to communicate outward. Covert channels (content, timing, the fact that a
call happened) can't be closed, so once a session holds the first two, every
action an outsider can observe is treated as irreversible: it carries
information across the boundary, and that can't be taken back.

The three conditions are Simon Willison's "lethal trifecta" (private data,
untrusted content, external communication;
https://simonwillison.net/2025/Jun/16/the-lethal-trifecta/). What's added here
is treating every observable action as a channel and escalating it by tier. -/

/-- What the session has been exposed to so far. -/
structure Exposure where
  sawPrivate   : Bool := false
  sawUntrusted : Bool := false
  deriving Repr, DecidableEq

def Exposure.trifecta (x : Exposure) : Bool := x.sawPrivate && x.sawUntrusted

/-- Unknown actions are observable. -/
def TierMap.observable (m : TierMap) (action : String) : Bool :=
  match m.lookup action with
  | some e => e.observable
  | none => true

/-- Unknown actions are not assumed to read private data; private reads are declared. -/
def TierMap.readsPrivate (m : TierMap) (action : String) : Bool :=
  match m.lookup action with
  | some e => e.readsPrivate
  | none => false

/-- Declared untrusted sources. -/
def TierMap.readsUntrusted (m : TierMap) (action : String) : Bool :=
  match m.lookup action with
  | some e => e.readsUntrusted
  | none => false

/-- The tier used for a decision: the classified tier, escalated to irreversible
for observable actions in a session that holds private data and untrusted input. -/
def sessionTier (m : TierMap) (action : String) (hint : Option Tier) (x : Exposure) : Tier :=
  if x.trifecta && m.observable action then .irreversible else effectiveTier m action hint

end FinalSay
