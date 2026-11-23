import Lean.Data.Json
import FinalSay.Core
import FinalSay.Classify
import FinalSay.Demo
import FinalSay.SystemFixtures

/-!
# Conformance fixtures

Exports test cases as JSON, with expected answers computed by the Lean
reference semantics. Any other implementation (Cedar, OPA, a script) that
reproduces these answers implements the model.
-/

namespace FinalSay.Fixtures

open Lean FinalSay

def tierJson (t : Tier) : Json := Json.str t.name

def decisionJson : Decision → Json
  | .allow => "allow"
  | .ask   => "ask"
  | .deny  => "deny"

def condJson : Cond → Json
  | .always         => Json.mkObj [("op", "always")]
  | .actionIs a     => Json.mkObj [("op", "actionIs"), ("action", Json.str a)]
  | .actionPrefix p => Json.mkObj [("op", "actionPrefix"), ("prefix", Json.str p)]
  | .tierIs t       => Json.mkObj [("op", "tierIs"), ("tier", tierJson t)]
  | .isTainted      => Json.mkObj [("op", "tainted")]
  | .amountAtMost n => Json.mkObj [("op", "amountAtMost"), ("amount", toJson n)]
  | .and c₁ c₂      => Json.mkObj [("op", "and"), ("args", Json.arr #[condJson c₁, condJson c₂])]
  | .not c          => Json.mkObj [("op", "not"), ("arg", condJson c)]

def ruleJson (r : Rule) : Json :=
  Json.mkObj [("name", Json.str r.name),
              ("effect", Json.str (match r.effect with | .allow => "allow" | .deny => "deny")),
              ("when", condJson r.cond)]

def policyJson (p : Policy) : Json := Json.arr (p.map ruleJson).toArray

def requestJson (r : Request) : Json :=
  Json.mkObj [("principal", Json.str r.principal), ("agent", Json.str r.agent),
              ("action", Json.str r.action), ("resource", Json.str r.resource),
              ("tier", tierJson r.tier), ("approved", toJson r.approved),
              ("context", Json.mkObj [("tainted", toJson r.tainted), ("amount", toJson r.amount)])]

def optStr : Option String → Json
  | some s => Json.str s
  | none => Json.null

/-- Policies the decision fixtures are run against. -/
def policies : List (String × Policy) := [
  ("demo", Demo.policy),
  ("empty", []),
  ("allow-everything", [{ name := "allow-all", effect := .allow, cond := .always }]),
  ("allow-and-deny-overlap", [
    { name := "allow-all", effect := .allow, cond := .always },
    { name := "deny-email", effect := .deny, cond := .actionPrefix "email." }]),
  ("negation", [
    { name := "allow-non-bank", effect := .allow, cond := .not (.actionPrefix "bank.") }])
]

def actions : List String :=
  ["notes.write", "calendar.create_event", "bank.refund", "email.send", "mystery.tool"]

def tiers : List Tier := [.reversible, .compensatable, .irreversible]

/-- Which invariants a case exercises, so failures point at the broken rule. -/
def invariantsFor (p : Policy) (r : Request) : List String :=
  let denyMatches := (firstMatch .deny p r).isSome
  let anyMatch := p.any (fun rule => rule.cond.eval r)
  (if denyMatches then ["1-deny-wins"] else []) ++
  (if r.tier = .irreversible && !r.approved then ["2-irreversible-needs-approval"] else []) ++
  (if !anyMatch && !r.approved then ["3-no-rule-asks"] else [])

def decisionCases : Array Json := Id.run do
  let mut out := #[]
  for (pname, p) in policies do
    for a in actions do
      for t in tiers do
        for approved in [false, true] do
          for tainted in [false, true] do
            for amount in (if a == "bank.refund" then [40, 400] else [0]) do
              let r : Request := { principal := "user:me", agent := "toy-agent", action := a,
                                   resource := "sandbox", tier := t, approved, tainted, amount }
              let res := evaluate p r
              out := out.push <| Json.mkObj [
                ("id", Json.str s!"{pname}/{a}/{t.name}/approved={approved}/tainted={tainted}/amount={amount}"),
                ("policy", Json.str pname),
                ("invariants", toJson (invariantsFor p r)),
                ("request", requestJson r),
                ("expected", Json.mkObj [("decision", decisionJson res.decision),
                                         ("rule", optStr res.rule)])]
  return out

def entryJson (e : Entry) : Json :=
  Json.mkObj [("action", Json.str e.action), ("tier", tierJson e.tier),
              ("compensation", optStr e.compensation),
              ("observable", toJson e.observable), ("readsPrivate", toJson e.readsPrivate),
              ("readsUntrusted", toJson e.readsUntrusted)]

def exposureJson (x : Exposure) : Json :=
  Json.mkObj [("sawPrivate", toJson x.sawPrivate), ("sawUntrusted", toJson x.sawUntrusted)]

def tierMapJson (m : TierMap) : Json :=
  Json.mkObj [("entries", Json.arr (m.entries.map entryJson).toArray),
              ("trustHints", toJson m.trustHints)]

def hintJson : Option Tier → Json
  | some t => tierJson t
  | none => Json.null

def classificationCases : Array Json := Id.run do
  let maps : List (String × TierMap) := [
    ("demo", Demo.tierMap),
    ("demo-trusting-hints", { Demo.tierMap with trustHints := true }),
    ("compensatable-without-compensation",
      { entries := [{ action := "bank.refund", tier := .compensatable }] })
  ]
  let hints : List (Option Tier) := [none, some .reversible, some .compensatable, some .irreversible]
  let exposures : List Exposure := [{}, { sawPrivate := true }, { sawUntrusted := true },
                                     { sawPrivate := true, sawUntrusted := true }]
  let mut out := #[]
  for (mname, m) in maps do
    for a in actions do
      for h in hints do
        for x in exposures do
          let tags := ["4-classification"] ++
            (if x.trifecta && m.observable a then ["4c-trifecta"] else [])
          out := out.push <| Json.mkObj [
            ("id", Json.str s!"{mname}/{a}/hint={(h.map Tier.name).getD "none"}/private={x.sawPrivate}/untrusted={x.sawUntrusted}"),
            ("tierMap", Json.str mname),
            ("invariants", toJson tags),
            ("action", Json.str a),
            ("hint", hintJson h),
            ("exposure", exposureJson x),
            ("expected", tierJson (sessionTier m a h x))]
  return out

def malformedCases : Array Json :=
  #[(Mode.interactive, "interactive"), (Mode.headless, "headless")].map fun (mode, name) =>
    let res := evaluateRaw mode Demo.policy (.malformed "unparseable input")
    Json.mkObj [("id", Json.str s!"malformed/{name}"), ("mode", Json.str name),
                ("input", Json.str "{not json"),
                ("expected", Json.mkObj [("decision", decisionJson res.decision)])]

def all : Json :=
  Json.mkObj [
    ("format", "finalsay-fixtures/v3"),
    ("generatedBy", "Lean reference semantics (FinalSay.evaluate)"),
    ("policies", Json.mkObj (policies.map fun (n, p) => (n, policyJson p))),
    ("tierMaps", Json.mkObj [
      ("demo", tierMapJson Demo.tierMap),
      ("demo-trusting-hints", tierMapJson { Demo.tierMap with trustHints := true }),
      ("compensatable-without-compensation",
        tierMapJson { entries := [{ action := "bank.refund", tier := .compensatable }] })]),
    ("decisions", Json.arr decisionCases),
    ("classification", Json.arr classificationCases),
    ("malformed", Json.arr malformedCases),
    ("system", Json.mkObj [
      ("config", SystemFixtures.config),
      ("policies", Json.mkObj (SystemFixtures.policies.map fun (n, p) => (n, policyJson p))),
      ("cases", Json.arr (SystemFixtures.cases 600))])
  ]

end FinalSay.Fixtures
