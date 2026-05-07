/-
  Elaborate an LLM-proposed `SoundExtension` term — and optionally a
  *strictness witness* — by delegating to Lean.

  Two wrappers, two checks:

  1. **Extension wrapper.** Splices the LLM's `SoundExtension` term
     into a file that defines `proposalExtension`, builds
     `cascadeT₁ := Theory.base.extend proposalExtension`. If the
     wrapper compiles, the kernel verified the `sound` field —
     soundness of the extension is established.

  2. **Strictness wrapper.** In addition to the extension, splices a
     proof of the existential

       ∃ (φ : Formula) (env : String → H3) (provVal : Formula → H3),
         proposalExtension.schema φ ∧
         Formula.heyting env provVal φ ≠ H3.top

     If this compiles, the kernel verified that *some instance
     admitted by the schema is H3-invalid* — and therefore not
     T₀-derivable (`Derivable₀.h3Valid`). The climb genuinely
     extends T₀.

  Outcomes: `ELAB-ERROR` (the extension wrapper failed),
  `ADMITTED` (sound; no strictness certificate accepted — the
  proposal *may* still be base-strict, no claim is being made
  either way), or `ADMITTED-STRICT` (sound *and* certified to
  admit at least one formula outside T₀, i.e. base-strict).
  The gate does not certify *relative* strictness over previously
  admitted rounds.

  This is the LCF discipline at the climb's gate, with a second
  optional gate for strictness. Splicing Lean source and running
  `lake env lean --run` is **not** itself a security boundary.
-/

import Climber.Climb
import Climber.Counter

namespace Climber.Elab

inductive Result where
  | elabError      (msg : String)
  | admitted
  | admittedStrict
  deriving Repr

def Result.isAdmitted : Result → Bool
  | .admitted        => true
  | .admittedStrict  => true
  | _                => false

def Result.isStrict : Result → Bool
  | .admittedStrict  => true
  | _                => false

instance : ToString Result where
  toString
    | .elabError m     => s!"ELAB-ERROR: {m}"
    | .admitted        => "ADMITTED"
    | .admittedStrict  => "ADMITTED-STRICT"

structure Config where
  wrapperPath       : String := "/tmp/climber-extension-check.lean"
  strictWrapperPath : String := "/tmp/climber-strictness-check.lean"
  /-- Working directory for the spawned `lake`. Must contain `lakefile.lean`. -/
  workingDir        : Option String := none

def defaultConfig : Config := {}

private def buildExtensionWrapper (extensionSrc : String) : String :=
  s!"import Climber

open Climber

def proposalExtension : SoundExtension :=
{extensionSrc}

def cascadeT₁ : Theory := Theory.base.extend proposalExtension

def main : IO Unit :=
  IO.println \"ADMITTED\"
"

private def buildStrictnessWrapper (extensionSrc : String) (strictSrc : String) :
    String :=
  s!"import Climber

open Climber

def proposalExtension : SoundExtension :=
{extensionSrc}

def cascadeT₁ : Theory := Theory.base.extend proposalExtension

theorem proposalStrict :
    ∃ (φ : Formula) (env : String → H3) (provVal : Formula → H3),
      proposalExtension.schema φ ∧
      Formula.heyting env provVal φ ≠ H3.top :=
{strictSrc}

def main : IO Unit :=
  IO.println \"ADMITTED-STRICT\"
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

/-- Elaborate the LLM's proposal and (optionally) its strictness
    witness. Tries the strictness wrapper first; on failure, falls
    back to the extension-only wrapper. -/
def checkProposal (cfg : Config)
    (extensionSrc : String) (strictSrc : Option String) : IO Result := do
  -- Try strictness first if a witness was supplied.
  match strictSrc with
  | some s =>
    IO.FS.writeFile cfg.strictWrapperPath
      (buildStrictnessWrapper extensionSrc s)
    let (sok, sout, _) ← runWrapper cfg.strictWrapperPath cfg.workingDir
    if sok && linesContain sout "ADMITTED-STRICT" then
      return .admittedStrict
    -- strictness failed; fall through to extension-only check
    IO.FS.writeFile cfg.wrapperPath (buildExtensionWrapper extensionSrc)
    let (eok, eout, eerr) ← runWrapper cfg.wrapperPath cfg.workingDir
    if eok && linesContain eout "ADMITTED" then
      return .admitted
    return .elabError (eout ++ eerr).trimAscii.toString
  | none =>
    IO.FS.writeFile cfg.wrapperPath (buildExtensionWrapper extensionSrc)
    let (eok, eout, eerr) ← runWrapper cfg.wrapperPath cfg.workingDir
    if eok && linesContain eout "ADMITTED" then
      return .admitted
    return .elabError (eout ++ eerr).trimAscii.toString

end Climber.Elab
