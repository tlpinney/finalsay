// Path classification on the real filesystem: case variants, symlinks,
// absolute paths, and run-later config at any depth.
import { mkdtempSync, readFileSync, rmSync, symlinkSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { execFileSync } from "node:child_process";
import { type Config, Gate } from "../core.ts";
import { normalizePath } from "../paths.ts";

const here = dirname(fileURLToPath(import.meta.url));
const cfg: Config = JSON.parse(readFileSync(join(here, "..", "config.json"), "utf8"));
const repo = mkdtempSync(join(tmpdir(), "ap-paths-"));
execFileSync("git", ["init", "-q"], { cwd: repo });
symlinkSync(".git", join(repo, "gitlink"));

const gate = new Gate(cfg, () => {}, undefined, undefined, (p) => normalizePath(p, repo));
const cases: [string, string, string][] = [
  ["write", "src/main.ts", "file.write"],
  ["write", ".git/hooks/pre-commit", "file.write.vcs"],
  ["write", ".GIT/hooks/pre-commit", "file.write.vcs"],    // case-insensitive disk
  ["edit", "./.Git/config", "file.write.vcs"],
  ["write", "gitlink/hooks/pre-commit", "file.write.vcs"], // symlink to .git
  ["write", `${repo}/.git/HEAD`, "file.write.vcs"],         // absolute path
  ["write", ".envrc", "file.write.exec"],
  ["edit", ".github/workflows/ci.yml", "file.write.exec"],
  ["write", ".pi/sandbox.json", "file.write.exec"],
  ["write", "docs/.github-notes.md", "file.write"],         // a segment must match exactly
  ["read", ".git/config", "file.read"],                     // rules apply to write/edit only
  // Other agents' project config dirs, at any depth: something outside the
  // sandbox runs them later, so they're irreversible wherever they land.
  ["write", "sub/.codex/config.toml", "file.write.exec"],
  ["edit", "pkg/a/.cursor/hooks.json", "file.write.exec"],
  ["write", ".agents/hooks.json", "file.write.exec"],
  ["write", "x/y/.claude/settings.local.json", "file.write.exec"],
  ["write", ".opencode/plugins/evil.js", "file.write.exec"],
  ["write", "sub/.GIT/hooks/pre-push", "file.write.vcs"],   // nested + case, still caught
];

let failed = 0;
for (const [tool, path, want] of cases) {
  const got = gate.actionOf(tool, { path });
  const ok = got === want;
  if (!ok) failed++;
  console.log(`${ok ? "ok  " : "FAIL"} ${tool} ${path} → ${got}${ok ? "" : ` (want ${want})`}`);
}
rmSync(repo, { recursive: true, force: true });
console.log(`${cases.length - failed}/${cases.length} path cases pass`);
process.exit(failed ? 1 : 0);
