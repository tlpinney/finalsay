"""Independent implementation of the composed finalsay system
(FinalSay/System.lean), written from the specification, standard library only.

`run(config, policy, ops, evaluate)` replays a list of operations from a fresh
system and returns the observable outcome, in the same shape as the Lean
fixtures' "expected" field.
"""
import copy


def tid(x):
    return (x[0], x[1])


# ---- scopes and delegation -------------------------------------------------

def covers(sc, t, now):
    return (t["action"] in sc["actions"] and t["resource"] in sc["resources"]
            and t["amount"] <= sc["maxAmount"] and now < sc["expires"])


def within(a, b):
    return (all(x in b["actions"] for x in a["actions"])
            and all(x in b["resources"] for x in a["resources"])
            and a["maxAmount"] <= b["maxAmount"] and a["expires"] <= b["expires"])


class Org:
    def __init__(self, root, root_scope):
        self.root, self.root_scope = root, root_scope
        self.links, self.revoked = [], []

    def live(self, l):
        return l["id"] not in self.revoked and all(a not in self.revoked for a in l["ancestors"])

    def witness(self, who, t, now):
        return next((l for l in self.links
                     if self.live(l) and l["holder"] == who and covers(l["scope"], t, now)), None)

    def holds(self, who, t, now):
        return (who == self.root and covers(self.root_scope, t, now)) or \
            self.witness(who, t, now) is not None

    def chain(self, who, t, now):
        if who == self.root and covers(self.root_scope, t, now):
            return []
        l = self.witness(who, t, now)
        return l["ancestors"] + [l["id"]] if l else []

    def delegate(self, lid, issuer, holder, scope, via):
        if via is None:
            if issuer == self.root and within(scope, self.root_scope):
                self.links.append(dict(id=lid, issuer=issuer, holder=holder, scope=scope, ancestors=[]))
            return
        p = next((l for l in self.links if l["id"] == via), None)
        if p and self.live(p) and p["holder"] == issuer and within(scope, p["scope"]):
            self.links.append(dict(id=lid, issuer=issuer, holder=holder, scope=scope,
                                   ancestors=p["ancestors"] + [p["id"]]))

    def revoke(self, lid):
        self.revoked.insert(0, lid)


# ---- approvals --------------------------------------------------------------

def target(req):
    # `eff` binds an approval to one effect id; the system stamps it on propose.
    return dict(action=req["action"], resource=req["resource"], amount=req["context"]["amount"],
                eff=req.get("eff"))


# ---- classification -----------------------------------------------------------

def effective_tier(tier_map, action):
    """The owner's tier for an action: compensatable without a declared compensation
    counts as irreversible, and unknown actions are irreversible (no hints)."""
    e = next((e for e in tier_map if e["action"] == action), None)
    if e is None:
        return "irreversible"
    if e["tier"] == "compensatable" and e.get("compensation") is None:
        return "irreversible"
    return e["tier"]


class Store:
    def __init__(self):
        self.granted, self.revoked, self.used, self.now = [], [], [], 0

    def valid_for(self, req, a):
        return (a["target"] == target(req) and self.now < a["expires"]
                and a["id"] not in self.revoked
                and not (a["oneShot"] and a["id"] in self.used))

    def pick_auth(self, org, req):
        return next((a for a in self.granted
                     if self.valid_for(req, a) and org.holds(a["approver"], target(req), self.now)),
                    None)


def commit_decide_auth(evaluate, policy, org, store, req):
    r = dict(req, approved=store.pick_auth(org, req) is not None)
    return evaluate(policy, r)[0]


# ---- run gate ----------------------------------------------------------------

class Gate:
    def __init__(self):
        self.seen, self.pending, self.held = [], [], []
        self.released, self.rejected, self.dropped, self.cancelled = [], [], [], []

    def blocked(self, run):
        return any(x[0] == run for x in self.pending)

    def submit(self, i, needs):
        if i[0] in self.cancelled or i in self.seen:
            return
        self.seen.insert(0, i)
        if needs:
            self.pending.append(i)
        elif self.blocked(i[0]):
            self.held.append(i)
        else:
            self.released.append(i)

    def decide(self, i, approve):
        if i not in self.pending:
            return
        self.pending.remove(i)
        (self.released if approve else self.rejected).append(i)
        run = i[0]
        if not self.blocked(run):
            self.released += [x for x in self.held if x[0] == run]
            self.held = [x for x in self.held if x[0] != run]

    def cancel(self, run):
        self.cancelled.insert(0, run)
        self.dropped += [x for x in self.pending if x[0] == run] + [x for x in self.held if x[0] == run]
        self.pending = [x for x in self.pending if x[0] != run]
        self.held = [x for x in self.held if x[0] != run]


# ---- provider ----------------------------------------------------------------

class Provider:
    def __init__(self):
        self.inflight, self.landed, self.revoked = [], [], []

    def dispatch(self, key, grants):
        if any(g in self.revoked for g in grants):
            return
        self.inflight.append((key, tuple(grants)))

    def deliver(self, key):
        c = next((c for c in self.inflight if c[0] == key), None)
        if c is None:
            return
        self.inflight.remove(c)
        if not any(d[0] == key for d in self.landed):   # bind: each key lands once
            self.landed.append(c)

    def retry(self, key):
        c = next((c for c in self.landed + self.inflight if c[0] == key), None)
        if c is not None:
            self.inflight.append(c)

    def revoke(self, g):                                 # fence
        self.revoked.insert(0, g)
        self.inflight = [c for c in self.inflight if g not in c[1]]


# ---- population ----------------------------------------------------------------

class Pop:
    def __init__(self, agent):
        self.agents = [dict(name=agent["name"], budget=agent["budget"])]
        self.spent = 0

    def budget_ok(self, i, n):
        return i < len(self.agents) and n <= self.agents[i]["budget"]

    def spend(self, i, n):
        if self.budget_ok(i, n):
            self.agents[i]["budget"] -= n
            self.spent += n

    def fork(self, i, child, share):
        if i < len(self.agents) and share <= self.agents[i]["budget"]:
            self.agents[i]["budget"] -= share
            self.agents.append(dict(name=child, budget=share))


# ---- the composed system -------------------------------------------------------

def approval_tag(aid):
    return 2 * aid


def link_tag(lid):
    return 2 * lid + 1


class System:
    def __init__(self, config, policy, evaluate):
        self.policy, self.evaluate = policy, evaluate
        self.org = Org(config["root"], config["rootScope"])
        self.store, self.gate, self.prov = Store(), Gate(), Provider()
        self.pop = Pop(config["agent"])
        self.tier_map = config["tierMap"]
        self.props, self.recs = [], []

    def classify(self, request, i):
        """The proposer's claimed tier is ignored: the owner's map decides, and the
        request is stamped with its effect id so approvals bind to this effect."""
        return dict(request, tier=effective_tier(self.tier_map, request["action"]), eff=list(i))

    def decide(self, req):
        return commit_decide_auth(self.evaluate, self.policy, self.org, self.store, req)

    def commit_one(self, i):
        q = next((q for q in self.props if q["id"] == i), None)
        if q is None:
            return
        req = q["request"]
        if not (self.decide(req) == "allow" and self.pop.budget_ok(q["agent"], target(req)["amount"])):
            return
        via = self.store.pick_auth(self.org, req)          # all judged in the pre-state
        chain = self.org.chain(via["approver"], target(req), self.store.now) if via else []
        tags = [approval_tag(via["id"])] + [link_tag(l) for l in chain] if via else []
        if via:
            self.store.used.insert(0, via["id"])
        self.pop.spend(q["agent"], target(req)["amount"])
        self.prov.dispatch(i, tags)
        self.recs.append(dict(id=i, agent=q["agent"], via=via["id"] if via else None, chain=chain))

    def through_gate(self, action):
        before = len(self.gate.released)
        action()
        for i in self.gate.released[before:]:
            self.commit_one(i)

    def step(self, op):
        kind = op["op"]
        if kind == "propose":
            i = tid(op["id"])
            if any(q["id"] == i for q in self.props):
                return
            req = self.classify(op["request"], i)
            self.props.append(dict(id=i, agent=op["agent"], request=req))
            d = self.decide(req)
            if d == "deny":
                return
            self.through_gate(lambda: self.gate.submit(i, d != "allow"))
        elif kind == "approve":
            self.through_gate(lambda: self.gate.decide(tid(op["id"]), True))
        elif kind == "reject":
            self.through_gate(lambda: self.gate.decide(tid(op["id"]), False))
        elif kind == "cancel":
            self.gate.cancel(op["run"])
        elif kind == "grant":
            self.store.granted.append(op["approval"])
        elif kind == "revokeApproval":
            self.store.revoked.insert(0, op["approval"])
            self.prov.revoke(approval_tag(op["approval"]))
        elif kind == "tick":
            self.store.now += 1
        elif kind == "delegate":
            self.org.delegate(op["link"], op["issuer"], op["holder"], op["scope"], op["via"])
        elif kind == "revokeDelegation":
            self.org.revoke(op["link"])
            self.prov.revoke(link_tag(op["link"]))
        elif kind == "fork":
            self.pop.fork(op["parent"], op["child"], op["share"])
        elif kind == "deliver":
            self.prov.deliver(tid(op["key"]))
        elif kind == "retry":
            self.prov.retry(tid(op["key"]))
        else:
            raise ValueError(f"unknown op {kind}")

    def outcome(self):
        return dict(
            landed=[dict(key=list(k), grants=list(g)) for k, g in self.prov.landed],
            records=[dict(id=list(r["id"]), agent=r["agent"], via=r["via"], chain=r["chain"])
                     for r in self.recs],
            released=[list(x) for x in self.gate.released],
            rejected=[list(x) for x in self.gate.rejected],
            used=self.store.used,
            spent=self.pop.spent)


def run(config, policy, ops, evaluate):
    s = System(copy.deepcopy(config), policy, evaluate)
    for op in ops:
        s.step(op)
    return s.outcome()
