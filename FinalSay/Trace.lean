import Lean.Data.Json
import FinalSay.Core
import FinalSay.Classify
import FinalSay.Invariants

/-!
# The trace as a flow graph

Taint tracking is reachability in a data-flow graph. The nodes are tool calls,
grouped into **contexts** (what one model has in view). Two kinds of edge:

* **Inside a context, everything flows to everything.** A model can be
  influenced by anything in its context, so a context is one mixing node.
  Session-level flags aren't a shortcut here; they're exact.
* **Between contexts, data moves only through explicit handoffs**, like a
  sub-agent returning a result. Handoffs are where the graph gets finer.

Handoffs treat the two labels differently:

* **Untrusted (integrity):** a *structured* result (a boolean, an enum) can't
  carry instructions, so it is endorsed and the label stops. Free text carries it.
* **Private (confidentiality):** any result can carry private bits, so the label
  always propagates. Releasing private data takes a decision, not a schema.

A covert channel can't be seen, but every use of one can be counted:
each event records whether it was observable and how many bytes it sent out.

Related work: endorsing only structured results is the idea behind Willison's
Dual LLM pattern (https://simonwillison.net/2023/Apr/25/dual-llm-pattern/) and
CaMeL's control/data-flow separation (Debenedetti et al., arXiv 2503.18813);
flow labels on secrets and untrusted input also appear in Cordon (Chen et al.,
arXiv 2606.17573).
-/

namespace FinalSay

open Lean

deriving instance ToJson, FromJson for Tier
deriving instance ToJson, FromJson for Decision
deriving instance ToJson, FromJson for Request
deriving instance ToJson, FromJson for Exposure

/-! ## Labels -/

def Exposure.join (x y : Exposure) : Exposure :=
  { sawPrivate := x.sawPrivate || y.sawPrivate, sawUntrusted := x.sawUntrusted || y.sawUntrusted }

/-- `x ≤ y`: every label in `x` is also in `y`. -/
def Exposure.le (x y : Exposure) : Prop :=
  (x.sawPrivate = true → y.sawPrivate = true) ∧ (x.sawUntrusted = true → y.sawUntrusted = true)

theorem Exposure.le_join (x y : Exposure) : x.le (x.join y) := by
  constructor <;> intro h <;> simp [Exposure.join, h]

theorem Exposure.le_refl (x : Exposure) : x.le x := ⟨id, id⟩

/-! ## Events -/

/-- The shape of a result crossing from one context to another. -/
inductive Schema where
  /-- Free text: can carry instructions and arbitrary data. -/
  | freeText
  /-- A typed value with a fixed number of bits (a boolean is 1). -/
  | structured (bits : Nat)
  deriving Repr, DecidableEq, ToJson, FromJson

/-- The labels a handoff carries from its source context. -/
def Schema.carry : Schema → Exposure → Exposure
  | .freeText,     x => x
  | .structured _, x => { x with sawUntrusted := false }

/-- One governed tool call, with everything needed to replay its decision. -/
structure Call where
  ctx        : String
  /-- The tool's self-declared hint (used only if the owner trusts hints). -/
  hint       : Option Tier
  /-- The request as first evaluated (`approved = false`). -/
  request    : Request
  /-- The context's exposure just before the call. -/
  exposure   : Exposure
  /-- A human with authority approved it after an `ask`. -/
  approved   : Bool
  decision   : Decision
  rule       : Option String
  ran        : Bool
  /-- Can someone outside see it? (From the owner's tier map.) -/
  observable : Bool
  /-- Upper bound on bytes the call sent outside the boundary. -/
  bytesOut   : Nat
  /-- Labels the result brought into the context. -/
  brought    : Exposure
  deriving Repr, ToJson, FromJson

inductive Event where
  | call (c : Call)
  /-- A result moves from context `src` into context `dst`. `bytes` is its size. -/
  | handoff (src dst : String) (schema : Schema) (bytes : Nat)
  deriving Repr, ToJson, FromJson

/-! ## Exposure by walking the graph -/

/-- Each context's exposure. -/
abbrev Env := String → Exposure

def Env.empty : Env := fun _ => {}

def Env.set (env : Env) (c : String) (x : Exposure) : Env :=
  fun c' => if c' = c then x else env c'

def Env.step (env : Env) : Event → Env
  | .call c => if c.ran then env.set c.ctx ((env c.ctx).join c.brought) else env
  | .handoff src dst s _ => env.set dst ((env dst).join (s.carry (env src)))

/-- The exposure of every context after a trace. -/
def envOf (t : List Event) : Env := t.foldl Env.step Env.empty

theorem Env.set_same (env : Env) (c : String) (x : Exposure) : env.set c x c = x := by
  simp [Env.set]

theorem Env.set_other (env : Env) (c c' : String) (x : Exposure) (h : c' ≠ c) :
    env.set c x c' = env c' := by
  simp [Env.set, h]

/-- **Exposure only grows:** no event removes a label from any context. -/
theorem step_monotone (env : Env) (e : Event) (c : String) : (env c).le (env.step e c) := by
  cases e with
  | call k =>
    simp only [Env.step]
    by_cases hr : k.ran = true
    · simp only [hr, ↓reduceIte]
      by_cases hc : c = k.ctx
      · subst hc; rw [Env.set_same]; exact Exposure.le_join _ _
      · rw [Env.set_other _ _ _ _ hc]; exact Exposure.le_refl _
    · simp only [hr, Bool.false_eq_true, ↓reduceIte]; exact Exposure.le_refl _
  | handoff src dst s n =>
    simp only [Env.step]
    by_cases hc : c = dst
    · subst hc; rw [Env.set_same]; exact Exposure.le_join _ _
    · rw [Env.set_other _ _ _ _ hc]; exact Exposure.le_refl _

/-- **Private always propagates** through a handoff, whatever the schema. -/
theorem handoff_keeps_private (env : Env) (src dst : String) (s : Schema) (n : Nat)
    (h : (env src).sawPrivate = true) :
    (env.step (.handoff src dst s n) dst).sawPrivate = true := by
  cases s <;> simp [Env.step, Env.set, Schema.carry, Exposure.join, h]

/-- **A structured result endorses:** it adds no untrusted label to its destination. -/
theorem structured_endorses (env : Env) (src dst : String) (bits n : Nat) :
    (env.step (.handoff src dst (.structured bits) n) dst).sawUntrusted = (env dst).sawUntrusted := by
  simp [Env.step, Env.set, Schema.carry, Exposure.join]

/-- **Free text carries untrusted input.** -/
theorem freeText_carries_untrusted (env : Env) (src dst : String) (n : Nat)
    (h : (env src).sawUntrusted = true) :
    (env.step (.handoff src dst .freeText n) dst).sawUntrusted = true := by
  simp [Env.step, Env.set, Schema.carry, Exposure.join, h]

/-! ## Audit -/

/-- The trifecta property for one event: an observable call that ran in a context
holding private data and untrusted input must have been approved. -/
def Event.ok : Event → Bool
  | .call c => !(c.ran && c.observable && c.exposure.trifecta) || c.approved
  | .handoff .. => true

/-- Re-derive a call's decision from its logged request and approval. -/
def replay (p : Policy) (c : Call) : Decision :=
  let d := (evaluate p c.request).decision
  if d = .ask ∧ c.approved = true then (evaluate p { c.request with approved := true }).decision
  else d

/-- Check one call against the owner's configuration, given the context's exposure. -/
def auditCall (m : TierMap) (p : Policy) (x : Exposure) (c : Call) : List String :=
  let a := c.request.action
  let tag := s!"[{c.ctx}] {a}"
  (if c.exposure = x then [] else [s!"{tag}: logged exposure doesn't match the graph"]) ++
  (if c.request.tier = sessionTier m a c.hint c.exposure then []
   else [s!"{tag}: logged tier {c.request.tier.name} doesn't match classification"]) ++
  (if c.request.tainted = c.exposure.sawUntrusted then [] else [s!"{tag}: taint flag doesn't match exposure"]) ++
  (if c.observable = m.observable a then [] else [s!"{tag}: observability doesn't match the tier map"]) ++
  (if c.request.approved = false then [] else [s!"{tag}: request logged as pre-approved"]) ++
  (if c.decision = replay p c then [] else [s!"{tag}: decision doesn't replay"]) ++
  (if c.ran = decide (c.decision = .allow) then [] else [s!"{tag}: ran without allow (or allowed without running)"]) ++
  (if c.ran || c.brought = {} then [] else [s!"{tag}: labels from a call that didn't run"]) ++
  (if !c.ran || c.brought.sawPrivate = m.readsPrivate a then []
   else [s!"{tag}: private label doesn't match the tier map"]) ++
  (if !c.ran || !m.readsUntrusted a || c.brought.sawUntrusted then []
   else [s!"{tag}: declared untrusted source didn't label the context"]) ++
  (if (Event.call c).ok then [] else [s!"{tag}: UNAPPROVED observable action after private + untrusted"])

/-- Walk the trace, recomputing exposure from the graph, and report every finding. -/
def audit (m : TierMap) (p : Policy) (t : List Event) : List String :=
  (t.foldl (fun (env, out) e =>
    let found := match e with
      | .call c => auditCall m p (env c.ctx) c
      | .handoff .. => []
    (env.step e, out ++ found)) (Env.empty, [])).2

/-- One line per observable call that ran: every possible channel use, approved or not. -/
def channelReport (t : List Event) : List String :=
  t.filterMap fun
    | .call c =>
      if c.ran && c.observable then
        let x := c.exposure
        let labels := (if x.sawPrivate then ["private"] else []) ++ (if x.sawUntrusted then ["untrusted"] else [])
        some s!"[{c.ctx}] {c.request.action}: {c.bytesOut} bytes out, context held {labels}{if c.approved then ", approved" else ""}"
      else none
    | .handoff .. => none

end FinalSay

namespace FinalSay

/-! ## Drawing the graph (Mermaid) -/

private def labelsOf (x : Exposure) : String :=
  String.intercalate " " ((if x.sawPrivate then ["+private"] else []) ++
                          (if x.sawUntrusted then ["+untrusted"] else []))

/-- A Mermaid flowchart: one lane per context, handoffs as edges between lanes.
Observable calls that ran in a context holding private data are highlighted:
those are the channel uses worth reviewing. -/
def toMermaid (t : List Event) : String := Id.run do
  let ctxOf : Event → String
    | .call c => c.ctx
    | .handoff _ dst _ _ => dst
  let ctxs := t.foldl (fun acc e => if acc.contains (ctxOf e) then acc else acc ++ [ctxOf e]) []
  let mut nodes : List (String × String) := []   -- (ctx, node line)
  let mut edges : List String := []
  let mut last : List (String × String) := []    -- ctx ↦ last node id
  let mut i := 0
  for e in t do
    let id := s!"e{i}"
    let (ctx, text, cls) := match e with
      | .call c =>
        let d := match c.decision with | .allow => "ALLOW" | .ask => "ASK" | .deny => "DENY"
        let out := if c.ran && c.observable then s!"<br/>{c.bytesOut} bytes out" else ""
        let lab := if c.ran then labelsOf c.brought else ""
        let lab := if lab = "" then "" else s!"<br/>{lab}"
        let cls := if c.ran && c.observable && c.exposure.sawPrivate then "channel"
          else if !c.ran then "blocked" else "ok"
        (c.ctx, s!"{d} {c.request.action}{out}{lab}", cls)
      | .handoff src dst sch n =>
        let what := match sch with
          | .freeText => s!"free text, {n} bytes"
          | .structured b => s!"structured, {b} bit"
        (dst, s!"from {src}<br/>{what}", "handoff")
    nodes := nodes ++ [(ctx, s!"    {id}[\"{text}\"]:::{cls}")]
    match last.lookup ctx with
    | some prev => edges := edges ++ [s!"  {prev} --> {id}"]
    | none => pure ()
    if let .handoff src _ sch _ := e then
      if let some from_ := last.lookup src then
        let lbl := match sch with | .freeText => "free text" | .structured _ => "structured"
        edges := edges ++ [s!"  {from_} -. {lbl} .-> {id}"]
    last := (ctx, id) :: last.filter (·.1 != ctx)
    i := i + 1
  let lanes := ctxs.map fun c =>
    s!"  subgraph {c}\n    direction TB\n" ++
    String.intercalate "\n" ((nodes.filter (·.1 == c)).map (·.2)) ++ "\n  end"
  return String.intercalate "\n" (["flowchart LR"] ++ lanes ++ edges ++ [
    "  classDef ok fill:#e8f5e9,stroke:#2e7d32",
    "  classDef blocked fill:#eeeeee,stroke:#757575,stroke-dasharray: 4 3",
    "  classDef channel fill:#fff3e0,stroke:#e65100,stroke-width:2px",
    "  classDef handoff fill:#e3f2fd,stroke:#1565c0"])

end FinalSay
