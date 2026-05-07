/-
  An LLM/Lean cascade over the climber's gate.

  Each round:
    1. Prompt Bedrock for an EXTENSION (a `SoundExtension` term).
    2. Run the soundness gate: the extension must elaborate (its
       `sound` field type-checks against the metalanguage interp).
    3. Outcome: `.admitted` (the kernel checked the soundness
       certificate; the schema enters the climbed theory) or
       `.elabError` (the gate failed; Lean's diagnostic is fed
       back into the prompt for one retry).
    4. After each non-error round, the runner regenerates
       `Climbed.lean` containing the accumulated extensions and
       the composite theory `T_climbed`, then verifies it
       elaborates.

  The cascade is the proposer/gate soundness loop made
  interactive. Unreachable-line claims live in the static artifact
  (`peirce_not_derivable_in_T₀`, `con_not_derivable_in_T₀`); the
  cascade itself just admits sound extensions.
-/

import Climber.Bedrock
import Climber.Elab

namespace Climber.Runner

structure RoundResult where
  extensionSrc : String
  outcome      : Climber.Elab.Result

structure Config where
  maxRetries  : Nat    := 1
  /-- Path the runner writes the accumulated climbed theory to. -/
  climbedPath : String := "Climbed.lean"

def defaultConfig : Config := {}

/-- Pull a section's body out of the LLM's reply. Sections are
    introduced by an ALL-CAPS header line ending in ':'. -/
def extractSection (header : String) (raw : String) : String :=
  let s := raw.replace "```lean" "" |>.replace "```lean4" "" |>.replace "```" ""
  let lines := s.splitOn "\n"
  let rec collect (taking : Bool) (acc : List String) : List String → List String
    | [] => acc.reverse
    | l :: rest =>
      if l.trimAscii.toString == header then
        collect true acc rest
      else if taking && l.trimAscii.toString.endsWith ":" &&
              (l.trimAscii.toString.toList.all
                  (fun c => c.isUpper || c == ':' || c == ' ')) then
        acc.reverse
      else if taking then
        collect true (l :: acc) rest
      else
        collect false acc rest
  (String.intercalate "\n" (collect false [] lines)).trimAscii.toString

/-- Add a leading indent on the first non-empty line if the LLM
    trimmed it. -/
def fixFirstLineIndent (src : String) : String :=
  match src.splitOn "\n" with
  | first :: rest =>
    let firstNeedsFix := !first.trimAscii.isEmpty && !first.startsWith " "
    let restHasIndent := rest.any (fun l => l.startsWith "  ")
    if firstNeedsFix && restHasIndent then
      String.intercalate "\n" (("  " ++ first) :: rest)
    else src
  | _ => src

def buildPrompt (admitted : List String)
    (retry : Option (String × String) := none) : String :=
  let admittedSection := if admitted.isEmpty then "" else
    "\n\nPreviously admitted extensions (don't propose duplicates):\n" ++
    String.intercalate "\n---\n" admitted ++ "\n"
  let retrySection := match retry with
    | none => ""
    | some (prevExt, err) =>
      s!"\n\nYour previous attempt was rejected by Lean.\n\nEXTENSION:\n{prevExt}\n\nLean's diagnostic:\n{err}\n\nProduce a corrected version.\n"
  s!"You are proposing a SoundExtension to the climber's base theory T₀.

T₀ is minimal implicational logic with ⊥-elim:
  - Axiom K:    φ → ψ → φ
  - Axiom S:    (φ → ψ → χ) → (φ → ψ) → φ → χ
  - Axiom ⊥-E:  ⊥ → φ
  - MP:         from φ → ψ and φ infer ψ

T₀ has an inert internal provability constructor `prov : Formula → Formula`,
interpreted in the metalanguage as `Derivable₀ φ`.

Your job: propose a `SoundExtension` whose schema admits new sound
formulas. The kernel checks the soundness certificate; on
admission, the extension enters the accumulated climbed theory.

Data types:

  inductive Formula where
    | bot   : Formula
    | atom  : String → Formula
    | imp   : Formula → Formula → Formula
    | prov  : Formula → Formula

  structure SoundExtension where
    schema : Formula → Prop
    sound  : ∀ φ env, schema φ → Formula.interp env φ

Output exactly one ALL-CAPS section.

EXTENSION:
  <Lean 4 term of type `SoundExtension`>

Examples of classical-only schemas (vary across rounds):

  Peirce:  schema admits  ((φ → ψ) → φ) → φ
  DNE:     schema admits  ((φ → ⊥) → ⊥) → φ
  ConsM:   schema admits  ((φ → ⊥) → φ) → φ      (consequentia mirabilis)

Example EXTENSION (Peirce schema, via `SoundExtension.mk`):

EXTENSION:
  SoundExtension.mk
    (fun ψ => ∃ p q : String, ψ =
      .imp (.imp (.imp (.atom p) (.atom q)) (.atom p)) (.atom p))
    (by
      rintro ψ env ⟨p, q, rfl⟩
      simp only [Formula.interp_imp, Formula.interp_atom]
      intro h
      by_cases hp : env p
      · exact hp
      · exact h (fun hp' => absurd hp' hp))

No markdown fences. No commentary inside sections. Use
`Classical.em`, `by_cases`, `decide`, `simp`, `intro`, `exact`,
etc. as needed.{admittedSection}{retrySection}"

/-- Regenerate `Climbed.lean` with all admitted extensions and a
    composite theory `T_climbed`. -/
def writeClimbedFile (path : String) (admittedSrcs : List String) : IO Unit := do
  let header := "import Climber

namespace Climber.Climbed

"
  let defs := admittedSrcs.zipIdx.foldl (fun acc (src, i) =>
    acc ++ s!"def round_{i} : SoundExtension :=\n{src}\n\n") ""
  let composite :=
    if admittedSrcs.isEmpty then
      "def T_climbed : Theory := Theory.base\n\n"
    else
      "def T_climbed : Theory :=\n  Theory.base" ++
      String.intercalate ""
        (admittedSrcs.zipIdx.map (fun (_, i) => s!"\n    |>.extend round_{i}")) ++
      "\n\n"
  let coda :=
"theorem T_climbed_sound {φ : Formula} {env : String → Prop}
    (h : derives T_climbed φ) : Formula.interp env φ :=
  climb_sound h

end Climber.Climbed
"
  IO.FS.writeFile path (header ++ defs ++ composite ++ coda)

/-- Verify the regenerated `Climbed.lean` elaborates. -/
def verifyClimbedFile (path : String) (workingDir : Option String) : IO Bool := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", path]
    cwd := workingDir
  }
  if out.exitCode != 0 then
    IO.eprintln s!"Climbed.lean failed to elaborate:\n{out.stdout}\n{out.stderr}"
    return false
  return true

/-- Run one LLM proposal round through the cascade. -/
def runOneRound
    (bcfg : Climber.Bedrock.Config) (ecfg : Climber.Elab.Config)
    (rcfg : Config) (admitted : List String)
    : IO (Option RoundResult) := do
  let rec attempt (retry : Option (String × String)) (remaining : Nat) :
      IO (Option RoundResult) := do
    let prompt := buildPrompt admitted retry
    match ← Climber.Bedrock.invoke bcfg prompt with
    | .error e =>
      IO.eprintln s!"Bedrock error: {e}"
      return none
    | .ok rawResponse =>
      let extensionSrc := fixFirstLineIndent (extractSection "EXTENSION:" rawResponse)
      IO.println "--- LLM proposed EXTENSION ---"
      IO.println extensionSrc
      let outcome ← Climber.Elab.checkProposal ecfg extensionSrc
      match outcome with
      | .elabError msg =>
        if remaining > 0 then
          IO.println s!"(elab error; retrying, {remaining} left)\n{msg}"
          attempt (some (extensionSrc, msg)) (remaining - 1)
        else
          return some ⟨extensionSrc, outcome⟩
      | _ => return some ⟨extensionSrc, outcome⟩
  attempt none rcfg.maxRetries

end Climber.Runner
