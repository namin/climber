/-
  Elaborate an LLM-proposed `SoundExtension` term by delegating to
  Lean.

  Splices the LLM's `SoundExtension` term into a wrapper file that
  defines `proposalExtension`, builds
  `cascadeT₁ := Theory.base.extend proposalExtension`, and prints
  `ADMITTED`. If the wrapper compiles, the kernel verified the
  `sound` field — soundness of the extension is established.

  Outcomes: `ADMITTED` (the kernel admitted the extension) or
  `ELAB-ERROR` (compilation failed; the diagnostic is fed back).

  The static artifact provides the unreachable-line claims
  separately — `peirce_not_derivable_in_T₀` (in `Counter.lean`)
  and `con_not_derivable_in_T₀` (in `Reflection.lean`) prove
  T₀-non-derivability with kernel-checked countermodels. The
  cascade is just the proposer/gate soundness loop made
  interactive; "outside T₀" claims are not part of its verdict.

  Splicing Lean source and running `lake env lean --run` is **not**
  itself a security boundary.
-/

import Climber.Climb

namespace Climber.Elab

inductive Result where
  | elabError (msg : String)
  | admitted
  deriving Repr

def Result.isAdmitted : Result → Bool
  | .admitted => true
  | _         => false

instance : ToString Result where
  toString
    | .elabError m => s!"ELAB-ERROR: {m}"
    | .admitted    => "ADMITTED"

structure Config where
  wrapperPath : String := "/tmp/climber-extension-check.lean"
  /-- Working directory for the spawned `lake`. Must contain `lakefile.lean`. -/
  workingDir  : Option String := none

def defaultConfig : Config := {}

private def buildWrapper (extensionSrc : String) : String :=
  s!"import Climber

open Climber

def proposalExtension : SoundExtension :=
{extensionSrc}

def cascadeT₁ : Theory := Theory.base.extend proposalExtension

def main : IO Unit :=
  IO.println \"ADMITTED\"
"

private def runWrapper (path : String) (workingDir : Option String) :
    IO (Bool × String × String) := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", path]
    cwd := workingDir
  }
  return (out.exitCode == 0, out.stdout, out.stderr)

private def linesContain (output : String) (marker : String) : Bool :=
  (output.splitOn "\n").any (·.trimAscii.toString == marker)

/-- Elaborate the LLM's proposal: write the wrapper, run it,
    classify. -/
def checkProposal (cfg : Config) (extensionSrc : String) : IO Result := do
  IO.FS.writeFile cfg.wrapperPath (buildWrapper extensionSrc)
  let (ok, out, err) ← runWrapper cfg.wrapperPath cfg.workingDir
  if ok && linesContain out "ADMITTED" then
    return .admitted
  return .elabError (out ++ err).trimAscii.toString

end Climber.Elab
