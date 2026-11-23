// Path normalization for classifying file writes. Node-only (no pi imports).
//
// A text check like `path.includes(".git/")` misses `.GIT/hooks/x` on a
// case-insensitive disk (the macOS default) and `link/hooks/x` when `link`
// points at `.git` (see experiments/case-insensitive-path.sh). So: resolve the
// path, follow symlinks on the part that exists, and lowercase it. Lowercasing
// can only add matches, which errs toward asking.
import { existsSync, realpathSync } from "node:fs";
import { basename, dirname, join, resolve } from "node:path";

export function normalizePath(p: string, cwd = process.cwd()): string {
  let head = resolve(cwd, p);
  const tail: string[] = [];
  while (!existsSync(head) && dirname(head) !== head) {
    tail.unshift(basename(head));
    head = dirname(head);
  }
  let real = head;
  try {
    real = realpathSync.native(head);
  } catch {
    // keep the unresolved path; it still gets lowercased
  }
  return join(real, ...tail).toLowerCase();
}
