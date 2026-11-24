import Lean.Data.Json
import FinalSay.System

/-!
# Conformance fixtures for the composed system

Each case is a starting configuration, a policy, and a sequence of operations;
the expected outcome is computed by `System.run`. An independent implementation
reproduces the outcome exactly (what landed and with which tags, the audit log,
the gate's released and rejected lists, the approvals used, the amount spent).

Cases are the named scenarios from `FinalSay.System` plus pseudo-random runs
from a fixed seed over a small universe of operations.
-/

namespace FinalSay.SystemFixtures

open Lean FinalSay

instance : Inhabited SOp := ⟨.tick⟩
instance : Inhabited Approval := ⟨{ id := 0, target := ⟨"", "", 0, none⟩, approver := "", expires := 0 }⟩

/-! ### JSON encoders -/

def tierJson (t : Tier) : Json := Json.str t.name

def effJson (id : EffId) : Json := Json.arr #[toJson id.1, toJson id.2]

def optEff : Option EffId → Json
  | some id => effJson id
  | none => Json.null

def targetJson (t : Target) : Json :=
  Json.mkObj [("action", Json.str t.action), ("resource", Json.str t.resource),
              ("amount", toJson t.amount), ("eff", optEff t.eff)]

def requestJson (r : Request) : Json :=
  Json.mkObj [("principal", Json.str r.principal), ("agent", Json.str r.agent),
              ("action", Json.str r.action), ("resource", Json.str r.resource),
              ("tier", tierJson r.tier), ("approved", toJson r.approved),
              ("context", Json.mkObj [("tainted", toJson r.tainted), ("amount", toJson r.amount)])]

def approvalJson (a : Approval) : Json :=
  Json.mkObj [("id", toJson a.id), ("target", targetJson a.target),
              ("approver", Json.str a.approver), ("expires", toJson a.expires),
              ("oneShot", toJson a.oneShot)]

def scopeJson (s : Scope) : Json :=
  Json.mkObj [("actions", toJson s.actions), ("resources", toJson s.resources),
              ("maxAmount", toJson s.maxAmount), ("expires", toJson s.expires)]

def optNat : Option Nat → Json
  | some n => toJson n
  | none => Json.null

def opJson : SOp → Json
  | .propose q => Json.mkObj [("op", "propose"), ("id", effJson q.id), ("agent", toJson q.agent),
                              ("request", requestJson q.req)]
  | .approve id => Json.mkObj [("op", "approve"), ("id", effJson id)]
  | .reject id => Json.mkObj [("op", "reject"), ("id", effJson id)]
  | .cancel r => Json.mkObj [("op", "cancel"), ("run", toJson r)]
  | .grant a => Json.mkObj [("op", "grant"), ("approval", approvalJson a)]
  | .revokeApproval aid => Json.mkObj [("op", "revokeApproval"), ("approval", toJson aid)]
  | .tick => Json.mkObj [("op", "tick")]
  | .delegate id iss hol sc via =>
    Json.mkObj [("op", "delegate"), ("link", toJson id), ("issuer", Json.str iss),
                ("holder", Json.str hol), ("scope", scopeJson sc), ("via", optNat via)]
  | .revokeDelegation lid => Json.mkObj [("op", "revokeDelegation"), ("link", toJson lid)]
  | .fork i c share => Json.mkObj [("op", "fork"), ("parent", toJson i), ("child", Json.str c),
                                   ("share", toJson share)]
  | .deliver k => Json.mkObj [("op", "deliver"), ("key", effJson k)]
  | .retry k => Json.mkObj [("op", "retry"), ("key", effJson k)]

def carrierJson (c : Carrier) : Json :=
  Json.mkObj [("key", effJson c.key), ("grants", toJson c.grants)]

def recordJson (r : Record) : Json :=
  Json.mkObj [("id", effJson r.id), ("agent", toJson r.agent),
              ("via", optNat (r.via.map Approval.id)), ("chain", toJson r.chain)]

def outcomeJson (s : System) : Json :=
  Json.mkObj [("landed", Json.arr (s.prov.landed.map carrierJson).toArray),
              ("records", Json.arr (s.recs.map recordJson).toArray),
              ("released", Json.arr (s.gate.released.map effJson).toArray),
              ("rejected", Json.arr (s.gate.rejected.map effJson).toArray),
              ("used", toJson s.store.used),
              ("spent", toJson s.pop.spent)]

/-! ### The universe -/

def root : String := "user:me"
def rootScope : Scope :=
  { actions := ["bank.refund", "notes.write", "calendar.create_event", "email.send"],
    resources := ["acct", "sandbox"], maxAmount := 1000, expires := 100 }
def rootAgent : Holder := ⟨"agent", 800, []⟩

/-- The owner's classification. Proposals may claim any tier; the system uses this. -/
def tierMap : TierMap :=
  { entries := [{ action := "bank.refund", tier := .irreversible },
                { action := "notes.write", tier := .reversible, observable := false },
                { action := "calendar.create_event", tier := .compensatable,
                  compensation := some "calendar.delete_event" },
                { action := "email.send", tier := .irreversible }] }

def entryJson (e : Entry) : Json :=
  Json.mkObj [("action", Json.str e.action), ("tier", tierJson e.tier),
              ("compensation", match e.compensation with | some c => Json.str c | none => Json.null)]

def mk (action resource : String) (tier : Tier) (amount : Nat) : Request :=
  { principal := root, agent := "agent", action, resource, tier, amount }

def refundBig : Request := mk "bank.refund" "acct" .irreversible 500
def refundSmall : Request := mk "bank.refund" "acct" .irreversible 50
def note : Request := mk "notes.write" "sandbox" .reversible 0
def event : Request := mk "calendar.create_event" "sandbox" .compensatable 0
def email : Request := mk "email.send" "sandbox" .irreversible 0

def policies : List (String × Policy) := [
  ("allow-notes", [⟨"notes", .allow, .actionIs "notes.write"⟩]),
  ("allow-notes-and-events", [⟨"notes", .allow, .actionIs "notes.write"⟩,
                              ⟨"events", .allow, .actionIs "calendar.create_event"⟩]),
  ("deny-email", [⟨"notes", .allow, .actionIs "notes.write"⟩,
                  ⟨"no-email", .deny, .actionIs "email.send"⟩]),
  ("allow-reversible", [⟨"rev-ok", .allow, .tierIs .reversible⟩]),
  ("empty", [])
]

def mgrScope : Scope :=
  { actions := ["bank.refund", "email.send"], resources := ["acct", "sandbox"], maxAmount := 600,
    expires := 50 }
def helperScope : Scope :=
  { actions := ["bank.refund"], resources := ["acct"], maxAmount := 100, expires := 50 }

def approvals : List Approval := [
  { id := 1, target := refundBig.target, approver := root, expires := 8 },
  { id := 2, target := refundSmall.target, approver := "user:mgr", expires := 8 },
  { id := 3, target := refundSmall.target, approver := "agent:helper", expires := 8 },
  { id := 4, target := email.target, approver := "user:mgr", expires := 3, oneShot := false },
  { id := 5, target := refundSmall.target, approver := "user:nobody", expires := 8 },
  { id := 6, target := refundBig.target, approver := "agent:helper", expires := 8 }
]

/-- An approval for effect `id`: approvals bind to one effect. -/
def bindTo (a : Approval) (id : EffId) : Approval := { a with target := { a.target with eff := some id } }

def runs : List Nat := [1, 2]
def keys : List Nat := [0, 1, 2]
def ids : List EffId := runs.flatMap fun r => keys.map fun k => (r, k)
def requests : List Request := [refundBig, refundSmall, note, event, email]

/-- What the generator picks from: single operations and short bundles that make
full flows (propose → grant → approve → deliver, delegation chains) likely. -/
def pool : Array (List SOp) := Id.run do
  let mut out : Array (List SOp) := #[]
  for id in ids do
    for (r, i) in requests.zipIdx do
      out := out.push [.propose ⟨id, i % 2, r⟩]
      out := out.push [.propose ⟨id, i % 2, r⟩, .deliver id]
      -- the proposer claims the wrong tier; the system must ignore it
      out := out.push [.propose ⟨id, i % 2, { r with tier := .reversible }⟩, .deliver id]
    out := out.push [.approve id]
    out := out.push [.reject id]
    out := out.push [.deliver id]
    out := out.push [.retry id]
    for a in approvals do
      out := out.push [.grant (bindTo a id), .approve id, .deliver id]
    out := out.push [.delegate 5 root "user:mgr" mgrScope none,
                     .delegate 6 "user:mgr" "agent:helper" helperScope (some 5),
                     .propose ⟨id, 0, refundSmall⟩, .grant (bindTo approvals[2]! id), .approve id, .deliver id]
    -- targeted flows: cascade, fence (approval and delegation), bind, fork
    out := out.push [.delegate 5 root "user:mgr" mgrScope none,
                     .delegate 6 "user:mgr" "agent:helper" helperScope (some 5), .revokeDelegation 5,
                     .propose ⟨id, 0, refundSmall⟩, .grant (bindTo approvals[2]! id), .approve id, .deliver id]
    out := out.push [.propose ⟨id, 0, refundBig⟩, .grant (bindTo approvals[0]! id), .approve id,
                     .revokeApproval 1, .deliver id]
    out := out.push [.delegate 5 root "user:mgr" mgrScope none, .propose ⟨id, 0, refundSmall⟩,
                     .grant (bindTo approvals[1]! id), .approve id, .revokeDelegation 5, .deliver id]
    out := out.push [.propose ⟨id, 0, note⟩, .deliver id, .retry id, .deliver id]
    out := out.push [.delegate 5 root "user:mgr" mgrScope none,
                     .delegate 7 "user:mgr" "agent:helper" rootScope (some 5),
                     .propose ⟨id, 0, refundBig⟩, .grant (bindTo approvals[5]! id), .approve id, .deliver id]
    out := out.push [.fork 0 "sub" 300, .grant (bindTo approvals[0]! id), .propose ⟨id, 1, refundBig⟩,
                     .deliver id]
  for a in approvals do
    out := out.push [.grant (bindTo a (1, 0))]
    out := out.push [.revokeApproval a.id]
  for r in runs do
    out := out.push [.cancel r]
  out := out.push [.tick]
  out := out.push [.tick, .tick, .tick]
  out := out.push [.delegate 5 root "user:mgr" mgrScope none]
  out := out.push [.delegate 5 root "user:mgr" mgrScope none,
                   .delegate 6 "user:mgr" "agent:helper" helperScope (some 5)]
  out := out.push [.delegate 6 "user:mgr" "agent:helper" helperScope (some 5)]
  out := out.push [.delegate 7 "user:mgr" "agent:helper" rootScope (some 5)]
  out := out.push [.revokeDelegation 5]
  out := out.push [.revokeDelegation 6]
  out := out.push [.fork 0 "sub" 300]
  return out

/-- A fixed linear congruential generator, so the corpus is reproducible. -/
def lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

def randomOps (seed len : Nat) : List SOp := Id.run do
  let mut s := seed
  let mut out : List SOp := []
  for _ in [0:len] do
    s := lcg s
    out := out ++ pool[(s / 65536) % pool.size]!
  return out

/-! ### Named scenarios -/

def named : List (String × String × List SOp) := [
  ("pipeline", "allow-notes", pipelineExample.ops),
  ("delegation-lands", "allow-notes", pipelineExample.delegated false),
  ("delegation-drains", "allow-notes", pipelineExample.delegated true),
  ("sibling-held-behind-ask", "allow-notes",
    [.propose ⟨(1, 0), 0, refundBig⟩, .propose ⟨(1, 1), 0, note⟩, .deliver (1, 1)]),
  ("revoke-in-flight", "allow-notes",
    [.propose ⟨(1, 0), 0, refundBig⟩, .grant (bindTo approvals[0]! (1, 0)), .approve (1, 0),
     .revokeApproval 1, .deliver (1, 0)]),
  ("redelivery-once", "allow-notes",
    [.propose ⟨(1, 0), 0, note⟩, .deliver (1, 0), .retry (1, 0), .deliver (1, 0)]),
  ("unauthorized-approver", "allow-notes",
    [.propose ⟨(1, 0), 0, refundSmall⟩, .grant (bindTo approvals[4]! (1, 0)), .approve (1, 0), .deliver (1, 0)]),
  ("expired-approval", "allow-notes",
    [.propose ⟨(1, 0), 0, refundBig⟩, .grant (bindTo approvals[0]! (1, 0)), .tick, .tick, .tick, .tick, .tick,
     .tick, .tick, .tick, .approve (1, 0), .deliver (1, 0)]),
  ("single-use-not-reused", "allow-notes",
    [.grant (bindTo approvals[0]! (1, 0)), .propose ⟨(1, 0), 0, refundBig⟩, .propose ⟨(2, 0), 0, refundBig⟩,
     .deliver (1, 0), .deliver (2, 0)]),
  ("budget-across-fork", "allow-notes",
    [.fork 0 "sub" 300, .grant (bindTo approvals[0]! (1, 0)), .grant (bindTo { approvals[0]! with id := 7 } (2, 0)),
     .propose ⟨(1, 0), 0, refundBig⟩, .propose ⟨(2, 0), 1, refundBig⟩]),
  ("cancel-fences", "allow-notes",
    [.propose ⟨(1, 0), 0, refundBig⟩, .propose ⟨(1, 1), 0, note⟩, .cancel 1,
     .propose ⟨(1, 2), 0, note⟩, .grant (bindTo approvals[0]! (1, 0)), .approve (1, 0)]),
  ("chain-revoked-above", "allow-notes",
    [.delegate 5 root "user:mgr" mgrScope none,
     .delegate 6 "user:mgr" "agent:helper" helperScope (some 5),
     .propose ⟨(1, 0), 0, refundSmall⟩, .grant (bindTo approvals[2]! (1, 0)), .approve (1, 0),
     .revokeDelegation 5, .deliver (1, 0)]),
  ("cascade-revoked-before-use", "allow-notes",
    [.delegate 5 root "user:mgr" mgrScope none,
     .delegate 6 "user:mgr" "agent:helper" helperScope (some 5), .revokeDelegation 5,
     .propose ⟨(1, 0), 0, refundSmall⟩, .grant (bindTo approvals[2]! (1, 0)), .approve (1, 0), .deliver (1, 0)]),
  ("forked-agent-over-budget", "allow-notes",
    [.fork 0 "sub" 300, .grant (bindTo approvals[0]! (1, 0)), .propose ⟨(1, 0), 1, refundBig⟩, .deliver (1, 0)]),
  ("amplifying-delegation-refused", "allow-notes",
    [.delegate 5 root "user:mgr" mgrScope none,
     .delegate 7 "user:mgr" "agent:helper" rootScope (some 5),
     .propose ⟨(1, 0), 0, refundSmall⟩, .grant (bindTo approvals[2]! (1, 0)), .approve (1, 0), .deliver (1, 0)]),
  ("spoofed-tier", "allow-reversible",
    [.propose ⟨(1, 0), 0, { refundBig with tier := .reversible }⟩, .deliver (1, 0)]),
  ("approval-capture", "allow-notes",
    [.fork 0 "sub" 300, .propose ⟨(1, 0), 0, refundSmall⟩, .propose ⟨(2, 0), 1, refundSmall⟩,
     .grant (bindTo approvals[0]! (1, 0)), .grant (bindTo approvals[1]! (1, 0)),
     .approve (2, 0), .approve (1, 0), .deliver (2, 0), .deliver (1, 0)])
]

def fresh : System := System.fresh tierMap root rootScope rootAgent

def caseJson (id pname : String) (p : Policy) (ops : List SOp) : Json :=
  Json.mkObj [("id", Json.str id), ("policy", Json.str pname),
              ("ops", Json.arr (ops.map opJson).toArray),
              ("expected", outcomeJson (fresh.run p ops))]

def policyOf (name : String) : Policy := ((policies.find? (·.1 == name)).map (·.2)).getD []

def cases (n : Nat) : Array Json := Id.run do
  -- named scenarios first, then `n` random runs
  let mut out : Array Json := #[]
  for (id, pname, ops) in named do
    out := out.push (caseJson s!"named/{id}" pname (policyOf pname) ops)
  for i in [0:n] do
    let (pname, p) := policies[i % policies.length]!
    let ops := randomOps (i + 1) (6 + i % 12)
    out := out.push (caseJson s!"random/{i}" pname p ops)
  return out

def config : Json :=
  Json.mkObj [("root", Json.str root), ("rootScope", scopeJson rootScope),
              ("tierMap", Json.arr (tierMap.entries.map entryJson).toArray),
              ("agent", Json.mkObj [("name", Json.str rootAgent.name),
                                    ("budget", toJson rootAgent.budget)])]

end FinalSay.SystemFixtures
