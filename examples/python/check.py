"""Independent implementation of the finalsay model, checked against the
Lean-generated conformance fixtures. Standard library only.

Usage: python3 examples/python/check.py fixtures/fixtures.json

The composed-system cases (invariants 6-10) are replayed by composed.py.
"""
import json
import sys

from composed import run as run_system


def cond(c, req):
    op = c["op"]
    if op == "always":
        return True
    if op == "actionIs":
        return req["action"] == c["action"]
    if op == "actionPrefix":
        return req["action"].startswith(c["prefix"])
    if op == "tierIs":
        return req["tier"] == c["tier"]
    if op == "tainted":
        return req["context"]["tainted"]
    if op == "amountAtMost":
        return req["context"]["amount"] <= c["amount"]
    if op == "and":
        return all(cond(a, req) for a in c["args"])
    if op == "not":
        return not cond(c["arg"], req)
    raise ValueError(f"unknown op {op}")


def first_match(policy, effect, req):
    return next((r for r in policy if r["effect"] == effect and cond(r["when"], req)), None)


def evaluate(policy, req):
    deny = first_match(policy, "deny", req)
    if deny:
        return "deny", deny["name"]                 # invariant 1: deny wins
    if req["approved"]:
        return "allow", None                        # approved by an authority
    if req["tier"] == "irreversible":
        return "ask", None                          # invariant 2
    allow = first_match(policy, "allow", req)
    if allow:
        return "allow", allow["name"]
    return "ask", None                              # invariant 3: no rule asks


def effective_tier(tier_map, action, hint):
    entry = next((e for e in tier_map["entries"] if e["action"] == action), None)
    if entry:                                       # invariant 4: owner wins
        if entry["tier"] == "compensatable" and entry["compensation"] is None:
            return "irreversible"
        return entry["tier"]
    if tier_map["trustHints"]:
        return "reversible" if hint == "reversible" else "irreversible"
    return "irreversible"


def session_tier(tier_map, action, hint, exposure):
    entry = next((e for e in tier_map["entries"] if e["action"] == action), None)
    observable = entry["observable"] if entry else True   # unknown is observable
    if exposure["sawPrivate"] and exposure["sawUntrusted"] and observable:
        return "irreversible"                       # invariant 4c: trifecta
    return effective_tier(tier_map, action, hint)


def evaluate_raw(policy, raw, mode):
    try:
        req = json.loads(raw)
    except json.JSONDecodeError:                    # invariant 5: fail closed
        return "ask" if mode == "interactive" else "deny"
    return evaluate(policy, req)[0]


def main(path):
    fx = json.load(open(path))
    failures = []
    for case in fx["decisions"]:
        got = evaluate(fx["policies"][case["policy"]], case["request"])
        want = (case["expected"]["decision"], case["expected"]["rule"])
        if got != want:
            failures.append((case["id"], case["invariants"], want, got))
    for case in fx["classification"]:
        got = session_tier(fx["tierMaps"][case["tierMap"]], case["action"], case["hint"],
                           case["exposure"])
        if got != case["expected"]:
            failures.append((case["id"], case["invariants"], case["expected"], got))
    for case in fx["malformed"]:
        got = evaluate_raw(fx["policies"]["demo"], case["input"], case["mode"])
        if got != case["expected"]["decision"]:
            failures.append((case["id"], ["5-fail-closed"], case["expected"]["decision"], got))

    system = fx.get("system", {"cases": []})
    for case in system["cases"]:
        got = run_system(system["config"], system["policies"][case["policy"]], case["ops"], evaluate)
        if got != case["expected"]:
            diff = {k: (case["expected"][k], got[k]) for k in got if got[k] != case["expected"][k]}
            failures.append((case["id"], ["6-10-composed-system"], diff, ""))

    total = (len(fx["decisions"]) + len(fx["classification"]) + len(fx["malformed"])
             + len(system["cases"]))
    for f in failures:
        print("FAIL", *f)
    print(f"{total - len(failures)}/{total} fixtures pass")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
