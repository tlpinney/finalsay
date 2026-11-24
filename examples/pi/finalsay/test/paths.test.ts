// Path classification on the real filesystem: case variants, symlinks,
// absolute paths, and run-later config at any depth.
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync } from "node:fs";
import { homedir, tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { execFileSync } from "node:child_process";
import { type Config, Gate } from "../core.ts";
import { makePaths, resolveLikePi } from "../paths.ts";

const here = dirname(fileURLToPath(import.meta.url));
const cfg: Config = JSON.parse(readFileSync(join(here, "..", "config.json"), "utf8"));
const repo = mkdtempSync(join(tmpdir(), "ap-paths-"));
execFileSync("git", ["init", "-q"], { cwd: repo });
symlinkSync(".git", join(repo, "gitlink"));

mkdirSync(join(repo, "vendor", "lib"), { recursive: true });
execFileSync("git", ["init", "-q"], { cwd: join(repo, "vendor", "lib") });
const gate = new Gate(cfg, () => {}, undefined, undefined, makePaths(repo));
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
  // Spellings pi's own resolver accepts: classify what the tool will open.
  ["write", "@.git/hooks/pre-commit", "file.write.vcs"],    // pi strips a leading @
  ["edit", "@.claude/settings.json", "file.write.exec"],
  ["write", `file://${repo}/.git/config`, "file.write.vcs"], // file:// URL
  // Outside the project: the checkpoint can't undo it.
  ["write", "~/.zshrc", "file.write.outside"],
  ["write", "../elsewhere.txt", "file.write.outside"],
  ["write", "/tmp/x.txt", "file.write.outside"],
  ["write", "node_modules/.bin/jest", "file.write"],         // in-tree, covered by the checkpoint
  // A git repo nested in the project: the checkpoint can't restore it.
  ["edit", "vendor/lib/code.c", "file.write.nested-repo"],
  ["write", "vendor/lib/sub/new.sh", "file.write.nested-repo"],
  ["write", "vendor/other.c", "file.write"],
];

let failed = 0;
for (const [tool, path, want] of cases) {
  const got = gate.actionOf(tool, { path });
  const ok = got === want;
  if (!ok) failed++;
  console.log(`${ok ? "ok  " : "FAIL"} ${tool} ${path} → ${got}${ok ? "" : ` (want ${want})`}`);
}
// The gate pins the call to the path it classified.
const call = { toolName: "write", toolCallId: "t1", input: { path: "@notes.md" } as Record<string, unknown> };
await gate.onToolCall(call as never, { hasUI: false, confirm: async () => false });
const pinned = call.input.path === join(realpathSync.native(repo), "notes.md");
if (!pinned) failed++;
console.log(`${pinned ? "ok  " : "FAIL"} write @notes.md pinned to ${String(call.input.path)}`);
const home = resolveLikePi("~/x", repo) === join(homedir(), "x");
if (!home) failed++;
console.log(`${home ? "ok  " : "FAIL"} ~ expands like pi`);
rmSync(repo, { recursive: true, force: true });
console.log(`${cases.length + 2 - failed}/${cases.length + 2} path cases pass`);
process.exit(failed ? 1 : 0);
