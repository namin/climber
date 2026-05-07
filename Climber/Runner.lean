/-
  An LLM/Lean cascade over the climber's gate.

  Each round:
    1. Prompt Bedrock for an EXTENSION (a `SoundExtension` term) and
       a STRICTNESS proof (an existential
       `∃ φ env provVal, schema φ ∧ heyting env provVal φ ≠ H3.top`).
    2. Run two checks:
       - **Soundness gate**: the extension must elaborate (its
         `sound` field type-checks against the metalanguage interp).
       - **Strictness gate**: the strictness proof must elaborate
         (the kernel verified some admitted instance is H3-invalid,
         hence not T₀-derivable).
    3. Outcome: `.admittedStrict` (both gates pass — sound *and*
       certified to admit something outside T₀, i.e. base-strict),
       `.admitted` (only soundness — sound; no strictness
       certificate accepted), or `.elabError` (the soundness gate
       failed).

       Note: base-strictness ≠ relative strictness. A duplicate
       extension whose schema still reaches outside T₀ will pass
       the strictness gate even if it adds nothing beyond
       previously admitted rounds. Relative strictness over the
       accumulated `T_climbed` is a refinement, not in the current
       gate.
    4. After each non-error round, the runner regenerates
       `Climbed.lean` containing the accumulated extensions and the
       composite theory `T_climbed`. The user can run
       `lake env lean Climbed.lean` to confirm that a kernel-checked
       climbed theory has been left behind.

  The cascade is the climb made interactive — the proposer offers
  schemas with metalanguage soundness certificates; the kernel
  admits or refuses; admitted schemas accumulate into a
  kernel-buildable composite theory.
-/

import Climber.Bedrock
import Climber.Elab

namespace Climber.Runner

structure RoundResult where
  extensionSrc : String
  strictSrc    : Option String
  outcome      : Climber.Elab.Result

structure Config where
  maxRetries     : Nat    := 1
  /-- Path the runner writes the accumulated climbed theory to. -/
  climbedPath    : String := "Climbed.lean"

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

/-- Treat empty / placeholder strictness sections as absent. -/
def normalizeStrictSrc (s : String) : Option String :=
  let trimmed := s.trimAscii.toString
  if trimmed.isEmpty || trimmed == "(none)" || trimmed == "none" then
    none
  else
    some (fixFirstLineIndent s)

def buildPrompt (admitted : List String)
    (retry : Option (String × String × String) := none) : String :=
  let admittedSection := if admitted.isEmpty then "" else
    "\n\nPreviously admitted extensions (don't propose duplicates):\n" ++
    String.intercalate "\n---\n" admitted ++ "\n"
  let retrySection := match retry with
    | none => ""
    | some (prevExt, prevStrict, err) =>
      s!"\n\nYour previous attempt was rejected by Lean.\n\nEXTENSION:\n{prevExt}\n\nSTRICTNESS:\n{prevStrict}\n\nLean's diagnostic:\n{err}\n\nProduce a corrected version.\n"
  s!"You are proposing a SoundExtension to the climber's base theory T₀.

T₀ is minimal implicational logic with ⊥-elim:
  - Axiom K:    φ → ψ → φ
  - Axiom S:    (φ → ψ → χ) → (φ → ψ) → φ → χ
  - Axiom ⊥-E:  ⊥ → φ
  - MP:         from φ → ψ and φ infer ψ

T₀ has an inert internal provability constructor `prov : Formula → Formula`,
interpreted in the metalanguage as `Derivable₀ φ`. T₀ has no rule for
`prov`; reflection schemas can install rules involving it.

Your job: propose a `SoundExtension` whose schema admits new sound
formulas, and supply a *strictness witness* proving that some
admitted instance is not T₀-derivable.

Data types:

  inductive Formula where
    | bot   : Formula
    | atom  : String → Formula
    | imp   : Formula → Formula → Formula
    | prov  : Formula → Formula

  structure SoundExtension where
    schema : Formula → Prop
    sound  : ∀ φ env, schema φ → Formula.interp env φ

  -- 3-element Heyting algebra for separating model
  inductive H3 where | bot | mid | top

Output exactly two ALL-CAPS sections.

EXTENSION:
  <Lean 4 term of type `SoundExtension`>

STRICTNESS:
  <Lean 4 proof term of type
   ∃ φ env provVal, proposalExtension.schema φ ∧
                    Formula.heyting env provVal φ ≠ H3.top>

The strictness proof witnesses an admitted instance that fails to
be top in some H3 separating model — by `Derivable₀.h3Valid` this
means it is not T₀-derivable. Without strictness, the proposal is
sound but doesn't actually climb (it stays inside T₀).

If you cannot supply a strictness proof, write `(none)` for the
STRICTNESS section. The proposal will still be admitted as sound
but flagged non-strict.

Examples of classical-only schemas (vary across rounds):

  Peirce:  schema admits  ((φ → ψ) → φ) → φ
  DNE:     schema admits  ((φ → ⊥) → ⊥) → φ
  EM:      schema admits  φ ∨ ¬φ                (tricky: no ∨ in
                                                  the language)
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

Example STRICTNESS for Peirce (witnesses the standard
peirceFormula \"p\" \"q\" via the H3 countermodel):

STRICTNESS:
  ⟨.imp (.imp (.imp (.atom \"p\") (.atom \"q\")) (.atom \"p\")) (.atom \"p\"),
   counterEnv, counterProvVal,
   ⟨\"p\", \"q\", rfl⟩,
   by simp [Formula.heyting, counterEnv, counterProvVal, H3.imp]⟩

No markdown fences. No commentary inside sections. Use
`Classical.em`, `by_cases`, `decide`, `simp`, `intro`, `exact`,
etc. as needed for soundness proofs.{admittedSection}{retrySection}"

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
  let rec attempt (retry : Option (String × String × String)) (remaining : Nat) :
      IO (Option RoundResult) := do
    let prompt := buildPrompt admitted retry
    match ← Climber.Bedrock.invoke bcfg prompt with
    | .error e =>
      IO.eprintln s!"Bedrock error: {e}"
      return none
    | .ok rawResponse =>
      let extensionSrc := fixFirstLineIndent (extractSection "EXTENSION:" rawResponse)
      let strictRaw    := extractSection "STRICTNESS:" rawResponse
      let strictSrc    := normalizeStrictSrc strictRaw
      IO.println "--- LLM proposed EXTENSION ---"
      IO.println extensionSrc
      IO.println "--- LLM proposed STRICTNESS ---"
      IO.println (strictSrc.getD "(none)")
      let outcome ← Climber.Elab.checkProposal ecfg extensionSrc strictSrc
      match outcome with
      | .elabError msg =>
        if remaining > 0 then
          IO.println s!"(elab error; retrying, {remaining} left)\n{msg}"
          attempt (some (extensionSrc, strictSrc.getD "(none)", msg)) (remaining - 1)
        else
          return some ⟨extensionSrc, strictSrc, outcome⟩
      | _ => return some ⟨extensionSrc, strictSrc, outcome⟩
  attempt none rcfg.maxRetries

end Climber.Runner
