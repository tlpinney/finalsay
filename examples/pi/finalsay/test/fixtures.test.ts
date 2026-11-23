// Conformance: the TypeScript core against the Lean-generated fixtures.
// Usage: node examples/pi/finalsay/test/fixtures.test.ts fixtures/fixtures.json
import { readFileSync } from "node:fs";
import { evaluate, sessionTier } from "../core.ts";

const fx = JSON.parse(readFileSync(process.argv[2] ?? "fixtures/fixtures.json", "utf8"));
let total = 0;
const failures: string[] = [];

for (const c of fx.decisions) {
  total++;
  // Fixture requests keep tainted and amount under `context`.
  const r = c.request;
  const got = evaluate(fx.policies[c.policy], { ...r, tainted: r.context.tainted, amount: r.context.amount });
  if (got.decision !== c.expected.decision || got.rule !== c.expected.rule)
    failures.push(`${c.id} ${c.invariants} want ${JSON.stringify(c.expected)} got ${JSON.stringify(got)}`);
}
for (const c of fx.classification) {
  total++;
  const got = sessionTier(fx.tierMaps[c.tierMap], c.action, c.hint, c.exposure);
  if (got !== c.expected) failures.push(`${c.id} ${c.invariants} want ${c.expected} got ${got}`);
}

for (const f of failures) console.log("FAIL", f);
console.log(`${total - failures.length}/${total} fixtures pass (decisions + classification)`);
process.exit(failures.length ? 1 : 0);
