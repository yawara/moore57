import Mathlib.Tactic.Linter.TextBased

/-!
# `lake exe lintText`

Runs mathlib's text-based style linters over every `.lean` module under
the given roots (default: `Moore57`). Reports trailing whitespace,
windows line endings, semicolon-before-space, disallowed unicode
characters and "adaptation note" usage.

Output is emitted in GitHub-annotation format so CI annotations show up
inline on the PR. Exits non-zero when any violations are found
(clamped to 125 so the exit code remains a valid shell status).
-/

open Lean.Linter Mathlib.Linter.TextBased System

/-- Convert a relative file path like `Moore57/Foo/Bar.lean` to the
    module name `Moore57.Foo.Bar`. -/
def pathToModule (p : FilePath) : Lean.Name :=
  let stripped := if p.extension == some "lean" then p.withExtension "" else p
  stripped.toString.splitOn "/" |>.foldl Lean.Name.mkStr Lean.Name.anonymous

/-- Recursively collect every `.lean` file under `dir` as a module name. -/
partial def collectModules (dir : FilePath) : IO (Array Lean.Name) := do
  let mut acc : Array Lean.Name := #[]
  for entry in (← dir.readDir) do
    let p := entry.path
    if ← p.isDir then
      acc := acc ++ (← collectModules p)
    else if p.extension == some "lean" then
      acc := acc.push (pathToModule p)
  return acc

def main (args : List String) : IO UInt32 := do
  let roots : Array FilePath :=
    if args.isEmpty then #[("Moore57" : FilePath)]
    else args.toArray.map FilePath.mk
  let opts : LinterOptions := { toOptions := {}, linterSets := {} }
  let mut allModules : Array Lean.Name := #[]
  for root in roots do
    allModules := allModules ++ (← collectModules root)
  let numErrors ← lintModules opts #[] allModules ErrorFormat.github false
  return min numErrors 125
