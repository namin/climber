/-
  Elaborate an LLM-proposed `(Formula, soundness proof)` pair by
  delegating to Lean itself.

  The LLM proposes:
    - a closed `Formula` term (the candidate axiom);
    - a Lean proof term of `∀ env, Formula.interp env <formula>`
      (the soundness certificate).

  We splice both into a wrapper file:

      import Climber
      open Climber
      def proposalFormula : Formula := <FORMULA>
      theorem proposalSound (env : String → Prop) :
          Formula.interp env proposalFormula := <PROOF>
      ... cascade boilerplate ...
      def main : IO Unit := IO.println "ADMITTED-FORMULA ..."

  …and run it via `lake env lean --run`.

  If the wrapper compiles, both the formula and the soundness proof
  passed the kernel — the SoundExtension can be constructed and the
  candidate enters T₁. If the wrapper fails to compile, the kernel
  refused: either the formula didn't elaborate or the proof didn't
  type-check (i.e., the formula isn't actually metalanguage-true).
  The Lean diagnostic is fed back to the LLM for retry.

  This is the LCF discipline at the climb's gate: the kernel is the
  arbiter, the LLM is constrained to the proposer side. Splicing
  Lean source and running `lake env lean --run` is **not** itself
  a security boundary — the proposal is trusted not to abuse Lean
  elaboration-time effects (see `GOTCHAS.md` style notes in
  lean-green for the corresponding analysis there).
-/

import Climber.Climb

namespace Climber.Elab

inductive Result where
  | elabError (msg : String)
  | admitted
  deriving Repr

def Result.isAdmitted : Result → Bool
  | .admitted => true
  | _ => false

instance : ToString Result where
  toString
    | .elabError m => s!"ELAB-ERROR: {m}"
    | .admitted    => "ADMITTED"

structure Config where
  wrapperPath : String := "/tmp/climber-cascade-check.lean"
  /-- Working directory for the spawned `lake`. Must contain `lakefile.lean`. -/
  workingDir  : Option String := none

def defaultConfig : Config := {}

private def buildWrapper (formulaSrc : String) (proofSrc : String) : String :=
  s!"import Climber

open Climber

abbrev proposalFormula : Formula :=
{formulaSrc}

theorem proposalSound : ∀ env : String → Prop, Formula.interp env proposalFormula :=
{proofSrc}

def proposalExtension : SoundExtension where
  schema := fun ψ => ψ = proposalFormula
  sound  := fun ψ env h => h ▸ proposalSound env

def cascadeT₁ : Theory := Theory.base.extend proposalExtension

theorem cascadeT₁_derives_proposal : derives cascadeT₁ proposalFormula :=
  derives.extra proposalExtension proposalFormula
    (by simp [cascadeT₁, Theory.extend, Theory.base]) rfl

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

/-- Elaborate the LLM's proposal, run the wrapper, parse the verdict. -/
def checkProposal (cfg : Config) (formulaSrc : String) (proofSrc : String) :
    IO Result := do
  IO.FS.writeFile cfg.wrapperPath (buildWrapper formulaSrc proofSrc)
  let (ok, stdout, stderr) ← runWrapper cfg.wrapperPath cfg.workingDir
  if !ok then return .elabError (stdout ++ stderr).trimAscii.toString
  let lines := stdout.splitOn "\n"
  if lines.any (·.trimAscii.toString == "ADMITTED") then
    return .admitted
  return .elabError s!"unexpected wrapper output:\n{stdout}"

end Climber.Elab
