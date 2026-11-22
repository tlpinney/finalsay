import FinalSay.Core
import FinalSay.Classify
import FinalSay.World
import FinalSay.Trace

/-!
# The toy agent harness

Every tool call goes through the governance layer:
classify → evaluate → (ask a human if needed) → run → record.

Calls happen in named **contexts** (the main agent, a quarantined reader).
Every call and every handoff between contexts is recorded in the trace, and
each context's exposure is computed from that trace.
-/

namespace FinalSay

structure Session where
  world         : World
  /-- Snapshot taken at the start; restoring it undoes reversible work. -/
  checkpoint    : World
  /-- Compensations registered before each compensatable effect, newest first. -/
  compensations : List Compensation
  /-- Exposure of each context (kept equal to `envOf trace`). -/
  env           : Env
  /-- Every call and handoff, oldest first. -/
  trace         : List Event
  log           : List String

def Session.start (w : World) : Session :=
  { world := w, checkpoint := w, compensations := [], env := Env.empty, trace := [], log := [] }

def label : Decision → String
  | .allow => "ALLOW"
  | .ask   => "ASK  "
  | .deny  => "DENY "

/-- The request for a tool call in context `ctx`, classified with that context's exposure. -/
def Session.mkReq (s : Session) (tierMap : TierMap) (ctx : String) (tool : Tool) : Request :=
  { principal := "user:me", agent := "toy-agent", action := tool.action,
    resource := "sandbox", tier := sessionTier tierMap tool.action tool.hint (s.env ctx),
    amount := tool.amount, tainted := (s.env ctx).sawUntrusted }

/-- Decide on one tool call and describe it as a trace event. Pure: nothing runs yet. -/
def Session.mkCall (s : Session) (tierMap : TierMap) (policy : Policy)
    (approver : Request → Bool) (ctx : String) (tool : Tool) : Call :=
  let x := s.env ctx
  let req := s.mkReq tierMap ctx tool
  let first := evaluate policy req
  -- Escalate: ask the human, then re-evaluate with their answer.
  let approved := decide (first.decision = .ask) && approver req
  let res := if approved then evaluate policy { req with approved := true } else first
  let ran := decide (res.decision = .allow)
  let untrusted := if ran then (tool.run s.world).2.2 else false
  { ctx, hint := tool.hint, request := req, exposure := x, approved,
    decision := res.decision, rule := res.rule, ran,
    observable := tierMap.observable tool.action,
    bytesOut := if ran && tierMap.observable tool.action then tool.bytesOut else 0,
    brought := if ran then { sawPrivate := tierMap.readsPrivate tool.action, sawUntrusted := untrusted }
               else {} }

def ctxTag (ctx : String) : String := if ctx = "main" then "" else s!"[{ctx}] "

/-- Run the tool if it was allowed. Touches only the world and compensations. -/
def Session.effect (s : Session) (ran : Bool) (tool : Tool) : Session :=
  if ran then
    let r := tool.run s.world
    { s with world := r.1,
             compensations := match r.2.1 with | some k => k :: s.compensations | none => s.compensations }
  else s

theorem Session.effect_trace (s : Session) (ran : Bool) (tool : Tool) :
    (s.effect ran tool).trace = s.trace := by
  unfold Session.effect; split <;> rfl

theorem Session.effect_env (s : Session) (ran : Bool) (tool : Tool) :
    (s.effect ran tool).env = s.env := by
  unfold Session.effect; split <;> rfl

/-- One tool call through the governance layer, in context `ctx`. -/
def Session.call (s : Session) (tierMap : TierMap) (policy : Policy)
    (approver : Request → Bool) (ctx : String) (tool : Tool) : Session :=
  let c := s.mkCall tierMap policy approver ctx tool
  let ev := Event.call c
  let first := (evaluate policy c.request).decision
  let note := if first = .ask then (if c.approved then " → human approved" else " → human declined") else ""
  let reason := match c.rule with
    | some r => if c.decision = Decision.deny then s!"denied by rule '{r}'" else s!"allowed by rule '{r}'"
    | none => if c.approved then "approved by someone with authority"
      else if c.request.tier = Tier.irreversible then "irreversible action: needs approval from someone with authority"
      else "no rule applies: escalating"
  let escalated := c.request.tier != effectiveTier tierMap tool.action tool.hint
  let lines :=
    [s!"{label c.decision} {ctxTag ctx}{tool.action} [{c.request.tier.name}] {reason}{note}"] ++
    (if escalated then ["      (escalated: this context holds private data and untrusted input, and this is observable)"] else []) ++
    (if c.brought.sawPrivate && !c.exposure.sawPrivate then [s!"      (private data entered {ctx})"] else []) ++
    (if c.brought.sawUntrusted && !c.exposure.sawUntrusted then [s!"      (untrusted content entered {ctx})"] else [])
  ({ s with env := s.env.step ev, trace := s.trace ++ [ev], log := s.log ++ lines } : Session).effect c.ran tool

/-- A result moves from one context into another (e.g. a sub-agent returns). -/
def Session.handoff (s : Session) (src dst : String) (schema : Schema) (bytes : Nat) : Session :=
  let ev := Event.handoff src dst schema bytes
  let what := match schema with
    | .freeText => s!"free text, {bytes} bytes"
    | .structured b => s!"structured, {b} bit{if b = 1 then "" else "s"}"
  let x := schema.carry (s.env src)
  let carried := (if x.sawPrivate then ["+private"] else []) ++ (if x.sawUntrusted then ["+untrusted"] else [])
  let carries := if carried.isEmpty then "" else s!", carries {String.intercalate " " carried}"
  { s with env := s.env.step ev, trace := s.trace ++ [ev],
           log := s.log ++ [s!"  ↳   {src} → {dst} ({what}{carries})"] }

/-- A scripted step for the toy agent. -/
inductive Step where
  | call (ctx : String) (tool : Tool)
  | handoff (src dst : String) (schema : Schema) (bytes : Nat)

def Session.step (tierMap : TierMap) (policy : Policy) (approver : Request → Bool)
    (s : Session) : Step → Session
  | .call ctx tool => s.call tierMap policy approver ctx tool
  | .handoff src dst sch n => s.handoff src dst sch n

def Session.run (tierMap : TierMap) (policy : Policy) (approver : Request → Bool)
    (s : Session) (steps : List Step) : Session :=
  steps.foldl (Session.step tierMap policy approver) s

/-- Roll back: run compensations newest-first, then restore reversible state. -/
def Session.rollback (s : Session) : Session :=
  let w := s.compensations.foldl Compensation.apply s.world
  -- Reversible state (notes, drafts) comes back exactly from the checkpoint;
  -- compensated and irreversible effects stay as they are.
  let w := { w with notes := s.checkpoint.notes, drafts := s.checkpoint.drafts }
  { s with world := w, compensations := [] }

/-! ## The trace is complete and safe -/

/-- The session's exposure is exactly what the trace says. -/
def Session.Coherent (s : Session) : Prop := s.env = envOf s.trace

theorem envOf_append (t : List Event) (e : Event) : envOf (t ++ [e]) = (envOf t).step e := by
  simp [envOf, List.foldl_append]

/-- **Every call is recorded:** it appends exactly its own event. -/
theorem call_records (s : Session) (m : TierMap) (p : Policy) (ap : Request → Bool)
    (ctx : String) (tool : Tool) :
    (s.call m p ap ctx tool).trace = s.trace ++ [.call (s.mkCall m p ap ctx tool)] := by
  simp [Session.call, Session.effect_trace]

theorem call_coherent (s : Session) (m : TierMap) (p : Policy) (ap : Request → Bool)
    (ctx : String) (tool : Tool) (h : s.Coherent) : (s.call m p ap ctx tool).Coherent := by
  unfold Session.Coherent at *
  simp [Session.call, Session.effect_trace, Session.effect_env, envOf_append, h]

theorem handoff_coherent (s : Session) (src dst : String) (sch : Schema) (n : Nat)
    (h : s.Coherent) : (s.handoff src dst sch n).Coherent := by
  unfold Session.Coherent at *
  simp [Session.handoff, envOf_append, h]

/-- **The harness never leaks unapproved:** every call it makes satisfies the trifecta property. -/
theorem mkCall_ok (s : Session) (m : TierMap) (p : Policy) (ap : Request → Bool)
    (ctx : String) (tool : Tool) : (Event.call (s.mkCall m p ap ctx tool)).ok = true := by
  have h1 : (s.mkReq m ctx tool).tier =
      sessionTier m (s.mkReq m ctx tool).action tool.hint (s.env ctx) := rfl
  have h2 : (s.mkReq m ctx tool).action = tool.action := rfl
  have h3 : (s.mkReq m ctx tool).approved = false := rfl
  simp only [Event.ok, Session.mkCall]
  generalize s.mkReq m ctx tool = req at h1 h2 h3 ⊢
  by_cases happ : (decide ((evaluate p req).decision = .ask) && ap req) = true
  · simp [happ]
  · have hf : (decide ((evaluate p req).decision = .ask) && ap req) = false := by
      simpa using happ
    simp only [hf, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
    by_cases hx : ((s.env ctx).trifecta && m.observable tool.action) = true
    · have ht : (s.env ctx).trifecta = true := by simp_all
      have ho : m.observable req.action = true := by rw [h2]; simp_all
      have hna := trifecta_needs_approval p m tool.hint (s.env ctx) req h1 ht ho h3
      simp [hna]
    · cases h1' : (s.env ctx).trifecta <;> cases h2' : m.observable tool.action <;> simp_all

def Session.AllOk (s : Session) : Prop := ∀ e ∈ s.trace, e.ok = true

theorem step_preserves (m : TierMap) (p : Policy) (ap : Request → Bool) (s : Session) (st : Step)
    (hc : s.Coherent) (ho : s.AllOk) :
    (Session.step m p ap s st).Coherent ∧ (Session.step m p ap s st).AllOk := by
  cases st with
  | call ctx tool =>
    refine ⟨call_coherent s m p ap ctx tool hc, ?_⟩
    intro e he
    simp only [Session.step, call_records, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ho e he
    · exact mkCall_ok s m p ap ctx tool
  | handoff src dst sch n =>
    refine ⟨handoff_coherent s src dst sch n hc, ?_⟩
    intro e he
    simp only [Session.step, Session.handoff, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ho e he
    · rfl

/-- **For every script:** the trace matches the session's exposure, and no observable
call ran unapproved in a context holding private data and untrusted input. -/
theorem run_safe (m : TierMap) (p : Policy) (ap : Request → Bool) (w : World) (steps : List Step) :
    (Session.run m p ap (Session.start w) steps).Coherent ∧
    (Session.run m p ap (Session.start w) steps).AllOk := by
  unfold Session.run
  suffices ∀ s : Session, s.Coherent → s.AllOk →
      (steps.foldl (Session.step m p ap) s).Coherent ∧ (steps.foldl (Session.step m p ap) s).AllOk from
    this _ rfl (by intro e he; simp [Session.start] at he)
  induction steps with
  | nil => intro s hc ho; exact ⟨hc, ho⟩
  | cons st rest ih =>
    intro s hc ho
    obtain ⟨hc', ho'⟩ := step_preserves m p ap s st hc ho
    exact ih _ hc' ho'

/-! ## What rollback can and can't do -/

theorem apply_preserves_sent (w : World) (c : Compensation) : (c.apply w).sent = w.sent := by
  cases c <;> rfl

theorem foldl_preserves_sent (cs : List Compensation) (w : World) :
    (cs.foldl Compensation.apply w).sent = w.sent := by
  induction cs generalizing w with
  | nil => rfl
  | cons c cs ih => simp [List.foldl, ih, apply_preserves_sent]

/-- Reversible: rollback restores notes exactly as they were at the checkpoint. -/
theorem rollback_restores_notes (s : Session) :
    s.rollback.world.notes = s.checkpoint.notes := rfl

/-- Irreversible: no rollback can unsend an email. -/
theorem rollback_cannot_unsend (s : Session) :
    s.rollback.world.sent = s.world.sent := by
  simp [Session.rollback, foldl_preserves_sent]

end FinalSay
