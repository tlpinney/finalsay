import Lean.Data.Json
import FinalSay.Core

/-!
# Generating the outer sandbox policy

The outer floor (an OS sandbox such as Anthropic's `srt`) only allows or denies.
What it should deny comes from the model: a write to a file that something
outside the sandbox will later execute is irreversible, so the floor denies it,
at any depth and under any spelling the filesystem resolves to the same name.

This module owns that policy and generates the `srt` settings from it, so the
policy is written once (here) instead of by hand in JSON.

**Trusted assumption (not proved here).** `srt` enforces a `denyWrite` pattern
`**/n` as `Glob.denies` says: a write is denied when some segment of its path
resolves to `n`, at any depth, including everything beneath that segment; on a
case-insensitive filesystem resolution folds case. Lean cannot see the kernel.
This is what the outer-wrapper probes check empirically (`experiments/wrapper/probe.sh`).

Proved:
* `generated_covers`: every write the model classifies as irreversible
  (a run-later write) is denied by the generated policy;
* `generated_exact`: the generated policy denies nothing else, so it never
  blocks an ordinary project write;
* `nested_case_variant_denied`: in particular, a run-later name at any depth,
  in any letter case, is denied (e.g. `sub/.codex`, the `.GIT` variant).
-/

namespace FinalSay.Srt

open Lean

/-- A path inside the project, as its segments: `["sub", ".codex", "config.toml"]`. -/
abbrev Path := List String

/-- Case folding as a case-insensitive filesystem resolves names (ASCII). -/
def fold (s : String) : String := String.ofList (s.toList.map Char.toLower)

/-- The outer policy, owned by the policy owner. -/
structure Outer where
  /-- Names of files and directories something outside the sandbox runs later. -/
  runLater       : List String
  /-- Paths the sandbox may not read (credentials). -/
  denyRead       : List String
  /-- Network destinations allowed out; empty means no network. -/
  allowedDomains : List String := []
  deriving Repr

/-- The default outer policy: common run-later configuration (VCS, CI, editor and
agent config dirs), plus the usual credential stores. -/
def defaultOuter : Outer where
  runLater := [".git", ".codex", ".cursor", ".agents", ".claude", ".pi", ".opencode",
               ".github", ".husky", ".vscode", ".envrc", ".gitmodules",
               ".pre-commit-config.yaml"]
  denyRead := ["~/.ssh", "~/.aws", "~/.gnupg"]

/-- The model's classification of a write inside the project: irreversible if any
segment of the path resolves to a run-later name, reversible otherwise (the
project itself is restorable). -/
def classifyWrite (o : Outer) (p : Path) : Tier :=
  if p.any (fun seg => o.runLater.any (fun n => fold seg == fold n)) then .irreversible
  else .reversible

/-- The `srt` patterns we generate. -/
inductive Glob where
  /-- `**/name`: the name at any depth. -/
  | anyDepth (name : String)
  deriving Repr, DecidableEq

def Glob.render : Glob → String
  | .anyDepth n => "**/" ++ n

/-- How `srt` enforces a pattern (the trusted assumption above). -/
def Glob.denies : Glob → Path → Bool
  | .anyDepth n, p => p.any (fun seg => fold seg == fold n)

/-- The generated `srt` settings. `"PROJ"` stands for the project directory. -/
structure SrtPolicy where
  denyWrite      : List Glob
  denyRead       : List String
  allowWrite     : List String
  allowedDomains : List String
  deriving Repr

def generate (o : Outer) : SrtPolicy where
  denyWrite := o.runLater.map .anyDepth
  denyRead := o.denyRead
  -- Only the project: it is what the checkpoint covers. `/tmp` isn't, so a write
  -- there couldn't be undone (point TMPDIR inside the project instead).
  allowWrite := ["PROJ"]
  allowedDomains := o.allowedDomains

def SrtPolicy.deniesWrite (sp : SrtPolicy) (p : Path) : Bool :=
  sp.denyWrite.any (fun g => g.denies p)

/-- The deny rule covering `p`, if any, so a denial can name its rule. -/
def SrtPolicy.ruleFor (sp : SrtPolicy) (p : Path) : Option Glob :=
  sp.denyWrite.find? (fun g => g.denies p)

def SrtPolicy.toJson (sp : SrtPolicy) : Json :=
  Json.mkObj [
    ("network", Json.mkObj [("allowedDomains", Lean.toJson sp.allowedDomains),
                            ("deniedDomains", Lean.toJson ([] : List String))]),
    ("filesystem", Json.mkObj [
      ("denyRead", Lean.toJson sp.denyRead),
      ("allowWrite", Lean.toJson sp.allowWrite),
      ("denyWrite", Lean.toJson (sp.denyWrite.map Glob.render))])]

/-! ### The generated policy denies exactly the run-later writes -/

theorem deniesWrite_iff (o : Outer) (p : Path) :
    (generate o).deniesWrite p = true ↔
      ∃ seg ∈ p, ∃ n ∈ o.runLater, fold seg = fold n := by
  simp only [SrtPolicy.deniesWrite, generate, List.any_map, List.any_eq_true,
    Function.comp, Glob.denies, beq_iff_eq]
  constructor
  · rintro ⟨n, hn, seg, hs, he⟩; exact ⟨seg, hs, n, hn, he⟩
  · rintro ⟨seg, hs, n, hn, he⟩; exact ⟨n, hn, seg, hs, he⟩

theorem classifyWrite_irreversible_iff (o : Outer) (p : Path) :
    classifyWrite o p = .irreversible ↔ ∃ seg ∈ p, ∃ n ∈ o.runLater, fold seg = fold n := by
  have key : p.any (fun seg => o.runLater.any (fun n => fold seg == fold n)) = true ↔
      ∃ seg ∈ p, ∃ n ∈ o.runLater, fold seg = fold n := by
    simp only [List.any_eq_true, beq_iff_eq]
  unfold classifyWrite
  cases h : p.any (fun seg => o.runLater.any (fun n => fold seg == fold n))
  · simp only [Bool.false_eq_true, ite_false]
    constructor
    · intro hc; exact absurd hc (by decide)
    · intro hx; have := key.mpr hx; rw [h] at this; exact absurd this (by decide)
  · simp only [ite_true, true_iff]
    exact key.mp h

/-- **Coverage:** every write the model classifies as irreversible is denied by the
generated policy, for every outer policy. -/
theorem generated_covers (o : Outer) (p : Path) (h : classifyWrite o p = .irreversible) :
    (generate o).deniesWrite p = true :=
  (deniesWrite_iff o p).mpr ((classifyWrite_irreversible_iff o p).mp h)

/-- **Exactness:** the generated policy denies nothing the model would let the agent
decide, so ordinary project writes are never blocked. -/
theorem generated_exact (o : Outer) (p : Path) (h : (generate o).deniesWrite p = true) :
    classifyWrite o p = .irreversible :=
  (classifyWrite_irreversible_iff o p).mpr ((deniesWrite_iff o p).mp h)

/-- **The nested plant and the case variant:** a run-later name at any depth, spelled
in any case the filesystem folds together, is denied. -/
theorem nested_case_variant_denied (o : Outer) (n : String) (hn : n ∈ o.runLater)
    (pre post : Path) (v : String) (hv : fold v = fold n) :
    (generate o).deniesWrite (pre ++ v :: post) = true :=
  (deniesWrite_iff o _).mpr ⟨v, by simp, n, hn, hv⟩

/-- Concretely, for the default policy: nested and case-variant run-later writes. -/
theorem default_denies_nested_run_later :
    (generate defaultOuter).deniesWrite ["sub", ".codex", "config.toml"] = true ∧
    (generate defaultOuter).deniesWrite [".GIT", "hooks", "pre-commit"] = true ∧
    (generate defaultOuter).deniesWrite ["nested", "repo", ".cursor", "mcp.json"] = true ∧
    (generate defaultOuter).deniesWrite [".agents", "hooks.json"] = true ∧
    (generate defaultOuter).deniesWrite ["src", "main.rs"] = false := by
  decide

end FinalSay.Srt
