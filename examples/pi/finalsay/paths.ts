// Path resolution for classifying file writes. Node-only (no pi imports).
//
// Two rules:
// 1. Resolve the way the tool will. pi strips a leading "@", expands "~",
//    accepts file:// URLs and turns unicode spaces into plain ones before it
//    opens a path; if the gate didn't, "@.git/hooks/x" would be classified as an
//    ordinary file and then written into .git. `resolveLikePi` mirrors pi 1.3.0's
//    resolveToCwd, and the gate pins the tool's input to the real path it
//    classified. (A symlink created in the not-yet-existing part of the path
//    between the decision and the write is still a race; run the tools under the
//    OS sandbox, which checks the file actually opened.)
// 2. Classify what the name refers to, not the text. A check like
//    `path.includes(".git/")` misses `.GIT/hooks/x` on a case-insensitive disk
//    (the macOS default) and `link/hooks/x` when `link` points at `.git`. So:
//    follow symlinks on the part that exists, and lowercase. Lowercasing can only
//    add matches, which errs toward asking.
import { existsSync, realpathSync } from "node:fs";
import { homedir } from "node:os";
import { basename, dirname, join, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const UNICODE_SPACES = /[\u00A0\u2000-\u200A\u202F\u205F\u3000]/g;

/** The absolute path pi's file tools would open for `p` (case preserved). */
export function resolveLikePi(p: string, cwd = process.cwd()): string {
  let s = p.replace(UNICODE_SPACES, " ");
  if (s.startsWith("@")) s = s.slice(1);
  if (s === "~") s = homedir();
  else if (s.startsWith("~/")) s = join(homedir(), s.slice(2));
  else if (/^file:\/\//.test(s)) s = fileURLToPath(s);
  return resolve(cwd, s);
}

/** The resolved path with symlinks followed on the part that exists, case kept. */
export function realPath(p: string, cwd = process.cwd()): string {
  let head = resolveLikePi(p, cwd);
  const tail: string[] = [];
  while (!existsSync(head) && dirname(head) !== head) {
    tail.unshift(basename(head));
    head = dirname(head);
  }
  let real = head;
  try {
    real = realpathSync.native(head);
  } catch {
    // keep the unresolved path
  }
  return join(real, ...tail);
}

/** What to classify: the real path, lowercased (lowercasing only adds matches). */
export function normalizePath(p: string, cwd = process.cwd()): string {
  return realPath(p, cwd).toLowerCase();
}

/** Is `real` the directory `root` or inside it? Compared with case kept: folding
 *  here would let `/home/u/Proj/x` count as inside `/home/u/proj` on a
 *  case-sensitive disk, which would lower its tier. */
export function isInside(real: string, root: string): boolean {
  return real === root || real.startsWith(root.endsWith(sep) ? root : root + sep);
}

/** Is `real` inside a git repository nested in `root` (a directory below the root
 *  that has its own .git)? The checkpoint stores a nested repo as a pointer, not
 *  its files, so writes there can't be restored. */
export function inNestedRepo(real: string, root: string): boolean {
  let dir = dirname(real);
  while (dir !== root && isInside(dir, root)) {
    if (existsSync(join(dir, ".git"))) return true;
    dir = dirname(dir);
  }
  return false;
}

/** The gate's view of paths for a project rooted at `cwd`. */
export function makePaths(cwd = process.cwd()) {
  const root = realPath(".", cwd);
  return {
    normalize: (p: string) => normalizePath(p, cwd),
    resolve: (p: string) => realPath(p, cwd),
    inside: (p: string) => isInside(realPath(p, cwd), root),
    nestedRepo: (p: string) => inNestedRepo(realPath(p, cwd), root),
  };
}
