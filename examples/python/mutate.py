"""Mutation test for the composed-system fixtures: break one guarantee at a time in
the Python implementation and count how many Lean-generated cases notice.
A corpus that lets a broken guarantee pass is too weak to certify it.

Usage: python3 examples/python/mutate.py fixtures/fixtures.json
"""
import json
import sys

import check
import composed


def nofence(self, g):
    self.revoked.insert(0, g)


def per_branch_pause(self, i, needs):
    if i[0] in self.cancelled or i in self.seen:
        return
    self.seen.insert(0, i)
    (self.pending if needs else self.released).append(i)


def no_approver_authority(self, org, req):
    return next((a for a in self.granted if self.valid_for(req, a)), None)


def no_bind(self, key):
    c = next((c for c in self.inflight if c[0] == key), None)
    if c is not None:
        self.inflight.remove(c)
        self.landed.append(c)


def no_cascade(self, l):
    return l["id"] not in self.revoked


def copy_on_fork(self, i, child, share):
    if i < len(self.agents):
        self.agents.append(dict(name=child, budget=self.agents[i]["budget"]))


def reuse_single_use(self, req, a):
    return (a["target"] == composed.target(req) and self.now < a["expires"]
            and a["id"] not in self.revoked)


def dispatch_ignores_revoked(self, key, grants):
    self.inflight.append((key, tuple(grants)))


def no_attenuation(a, b):
    return True


# (name, owner, attribute, replacement, equivalent?)
MUTANTS = [
    ("no provider fence", composed.Provider, "revoke", nofence, False),
    ("per-branch pause", composed.Gate, "submit", per_branch_pause, False),
    ("no approver authority", composed.Store, "pick_auth", no_approver_authority, False),
    ("no idempotency bind", composed.Provider, "deliver", no_bind, False),
    ("no revocation cascade", composed.Org, "live", no_cascade, False),
    ("copy-on-fork", composed.Pop, "fork", copy_on_fork, False),
    ("single-use ignored", composed.Store, "valid_for", reuse_single_use, False),
    ("no attenuation check", composed, "within", no_attenuation, False),
    # Equivalent by design: the commit-time check already refuses anything a
    # revoked approval or delegation backed, so the provider's own refusal at
    # dispatch is defence in depth and changes no outcome. Proved in Lean as
    # `committed_never_refused_at_dispatch`.
    ("dispatch ignores revoked", composed.Provider, "dispatch", dispatch_ignores_revoked, True),
]


def main(path):
    fx = json.load(open(path))
    system = fx["system"]

    def failing():
        return sum(1 for c in system["cases"]
                   if composed.run(system["config"], system["policies"][c["policy"]], c["ops"],
                                   check.evaluate) != c["expected"])

    base = failing()
    print(f"{len(system['cases'])} system cases, {base} failing unmutated")
    bad = base != 0
    for name, owner, attr, fn, equivalent in MUTANTS:
        orig = getattr(owner, attr)
        setattr(owner, attr, fn)
        n = failing()
        setattr(owner, attr, orig)
        verdict = ("ok (equivalent: expected 0)" if equivalent and n == 0 else
                   "ok" if not equivalent and n > 0 else "SURVIVED")
        bad |= verdict == "SURVIVED"
        print(f"  {name:26s} {n:4d} failing  {verdict}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
