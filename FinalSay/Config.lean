import Lean.Data.Json
import FinalSay.Core
import FinalSay.Classify
import FinalSay.Demo
import FinalSay.Fixtures

/-!
# Reading an owner's configuration

Decodes a tier map and a policy from JSON, in the same format as the
conformance fixtures, so a trace written by any harness can be audited
against the configuration that harness used.

```json
{ "tierMap": { "entries": [ { "action": "email.send", "tier": "irreversible" } ],
               "trustHints": false },
  "policy":  [ { "name": "reversible-ok", "effect": "allow",
                 "when": { "op": "tierIs", "tier": "reversible" } } ] }
```

Optional entry fields: `compensation` (default none), `observable` (default
true), `readsPrivate` and `readsUntrusted` (default false). Anything else
that doesn't parse is an error: the audit fails closed.
-/

namespace FinalSay.Config

open Lean FinalSay

def parseTier : String → Except String Tier
  | "reversible"    => .ok .reversible
  | "compensatable" => .ok .compensatable
  | "irreversible"  => .ok .irreversible
  | s => .error s!"unknown tier '{s}'"

partial def parseCond (j : Json) : Except String Cond := do
  match ← j.getObjValAs? String "op" with
  | "always"       => pure .always
  | "actionIs"     => .actionIs <$> j.getObjValAs? String "action"
  | "actionPrefix" => .actionPrefix <$> j.getObjValAs? String "prefix"
  | "tierIs"       => .tierIs <$> (j.getObjValAs? String "tier" >>= parseTier)
  | "tainted"      => pure .isTainted
  | "amountAtMost" => .amountAtMost <$> j.getObjValAs? Nat "amount"
  | "and" =>
    match (← j.getObjValAs? (Array Json) "args").toList with
    | [a, b] => .and <$> parseCond a <*> parseCond b
    | _ => throw "'and' needs exactly two args"
  | "not" => .not <$> (j.getObjVal? "arg" >>= parseCond)
  | op => throw s!"unknown op '{op}'"

def parseRule (j : Json) : Except String Rule := do
  let name ← j.getObjValAs? String "name"
  let effect ← match ← j.getObjValAs? String "effect" with
    | "allow" => pure Effect.allow
    | "deny"  => pure Effect.deny
    | e => throw s!"rule '{name}': unknown effect '{e}'"
  let cond ← j.getObjVal? "when" >>= parseCond
  return { name, effect, cond }

def parsePolicy (j : Json) : Except String Policy := do
  (← j.getArr?).toList.mapM parseRule

/-- An optional field: absent or null gives the default; present must have the right type. -/
def optField {α} [FromJson α] (j : Json) (k : String) (d : α) : Except String α :=
  match j.getObjVal? k with
  | .error _ | .ok .null => .ok d
  | .ok v => fromJson? v

def parseEntry (j : Json) : Except String Entry := do
  let action ← j.getObjValAs? String "action"
  let tier ← j.getObjValAs? String "tier" >>= parseTier
  let compensation ← optField j "compensation" (none : Option String)
  let observable ← optField j "observable" true
  let readsPrivate ← optField j "readsPrivate" false
  let readsUntrusted ← optField j "readsUntrusted" false
  return { action, tier, compensation, observable, readsPrivate, readsUntrusted }

def parseTierMap (j : Json) : Except String TierMap := do
  let entries ← (← j.getObjValAs? (Array Json) "entries").toList.mapM parseEntry
  let trustHints ← optField j "trustHints" false
  return { entries, trustHints }

structure Config where
  tierMap : TierMap
  policy  : Policy

def parse (j : Json) : Except String Config := do
  return { tierMap := ← (j.getObjVal? "tierMap" >>= parseTierMap),
           policy  := ← (j.getObjVal? "policy" >>= parsePolicy) }

/-! Decoding inverts the fixture encoders on the demo configuration. -/

#guard (parsePolicy (Fixtures.policyJson Demo.policy)).toOption.map Fixtures.policyJson
  == some (Fixtures.policyJson Demo.policy)
#guard (parseTierMap (Fixtures.tierMapJson Demo.tierMap)).toOption.map Fixtures.tierMapJson
  == some (Fixtures.tierMapJson Demo.tierMap)

end FinalSay.Config
