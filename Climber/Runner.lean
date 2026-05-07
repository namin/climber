/-
  An LLM/Lean cascade over the climber's gate.

  Each round:
    1. Prompt Bedrock for a FORMULA (a closed `Formula` term)
       and a PROOF (a Lean term of type
       `∀ env, Formula.interp env <FORMULA>`).
    2. Splice both into a wrapper file, run `checkProposal`. The
       wrapper imports Climber, defines `proposalExtension` from the
       pair, builds `cascadeT₁ := Theory.base.extend proposalExtension`,
       and proves `derives cascadeT₁ proposalFormula`.
    3. Outcome: `.admitted` (kernel checked the soundness proof and
       T₁ derives the new formula) or `.elabError` (kernel refused
       at any stage, with the Lean diagnostic).
    4. On elab error, retry up to `maxRetries` times with the
       diagnostic fed back into the prompt.

  The kernel discipline is direct: the soundness proof is checked
  by Lean's kernel; admission and "T₁ derives the candidate" are
  consequences of the proof type-checking.
-/

import Climber.Bedrock
import Climber.Elab

namespace Climber.Runner

structure RoundResult where
  formulaSrc : String
  proofSrc   : String
  outcome    : Climber.Elab.Result

structure Config where
  maxRetries : Nat := 1

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
              (l.trimAscii.toString.toList.all (fun c => c.isUpper || c == ':' || c == ' ')) then
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
    (retry : Option (String × String × String) := none) : String :=
  let admittedSection := if admitted.isEmpty then "" else
    "\n\nPreviously admitted formulas (don't propose duplicates):\n" ++
    String.intercalate "\n---\n" admitted ++ "\n"
  let retrySection := match retry with
    | none => ""
    | some (prevF, prevP, err) =>
      s!"\n\nYour previous attempt was rejected by Lean.\n\nFORMULA:\n{prevF}\n\nPROOF:\n{prevP}\n\nLean's diagnostic:\n{err}\n\nProduce a corrected version.\n"
  s!"You are proposing a soundness extension to the climber's base theory T₀.

T₀ is minimal implicational logic with ⊥-elim:
  - Axiom K:    φ → ψ → φ
  - Axiom S:    (φ → ψ → χ) → (φ → ψ) → φ → χ
  - Axiom ⊥-E:  ⊥ → φ
  - MP:         from φ → ψ and φ infer ψ

T₀ is sound for the standard truth-functional interpretation but
incomplete: it cannot derive Peirce's law, double-negation
elimination, the law of excluded middle, or other classical-only
tautologies.

Your job: propose a closed `Formula` that is **classically valid
but not intuitionistically valid** — i.e., a tautology that T₀
provably cannot reach — and supply a Lean proof of its
metalanguage truth. The kernel checks the proof; if admitted, the
formula enters T₁ as a new sound axiom and the system has climbed
across an unreachable line.

Examples of classical-only tautologies you might consider (do NOT
just propose Peirce's law — vary across rounds):
- Double-negation elimination: `((φ → ⊥) → ⊥) → φ`
- Excluded middle (in implicational form):
  `((φ → ψ) → φ) → φ` (this IS Peirce — already used)
- `((φ → ⊥) → φ) → φ` (consequentia mirabilis)
- De Morgan-via-implication patterns
- `(φ → ψ) → ((φ → ⊥) → ⊥) → ((ψ → ⊥) → ⊥)` etc.

Use `Classical.em` or `by_cases` in the proof — these classical
tactics are what make the certificate *classical* rather than
intuitionistic. A proof that goes through without classical
reasoning is suspicious: it likely means the formula was already
in T₀ and the climb didn't actually advance.

Data type:

  inductive Formula where
    | bot    : Formula
    | atom   : String → Formula
    | imp    : Formula → Formula → Formula

Interpretation:

  def Formula.interp (env : String → Prop) : Formula → Prop
    | .bot     => False
    | .atom a  => env a
    | .imp φ ψ => interp env φ → interp env ψ

The wrapper exposes the goal as `∀ env, Formula.interp env <FORMULA>`
— begin your proof with `intro env`. To unfold `Formula.interp`, use
the simp lemmas `Formula.interp_imp`, `Formula.interp_atom`, and
`Formula.interp_bot` (the last one rewrites `Formula.interp env .bot`
to `False`). Do NOT use `Formula.interp` on its own as a simp arg —
the equation lemmas are the only ones registered.

Output exactly two ALL-CAPS sections. Do NOT include commentary
between or inside sections — extra lines inside FORMULA: or PROOF:
will be spliced into the wrapper and break compilation.

Output format: TWO sections, exactly.

FORMULA:
  <Lean 4 term of type `Formula`>

PROOF:
  <Lean 4 proof term of type `∀ env, Formula.interp env <FORMULA>`>

No markdown fences. No commentary. The proof may use `Classical.em`,
`by_cases`, `decide`, `simp`, `intro`, `exact`, etc.

Example (Peirce's law):

FORMULA:
  .imp (.imp (.imp (.atom \"p\") (.atom \"q\")) (.atom \"p\")) (.atom \"p\")

PROOF:
  by
    intro env
    simp only [Formula.interp_imp, Formula.interp_atom]
    intro h
    by_cases hp : env \"p\"
    · exact hp
    · exact h (fun hp' => absurd hp' hp){admittedSection}{retrySection}"

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
      let formulaSrc := fixFirstLineIndent (extractSection "FORMULA:" rawResponse)
      let proofSrc   := fixFirstLineIndent (extractSection "PROOF:"   rawResponse)
      IO.println "--- LLM proposed FORMULA ---"
      IO.println formulaSrc
      IO.println "--- LLM proposed PROOF ---"
      IO.println proofSrc
      let outcome ← Climber.Elab.checkProposal ecfg formulaSrc proofSrc
      match outcome with
      | .elabError msg =>
        if remaining > 0 then
          IO.println s!"(elab error; retrying, {remaining} left)\n{msg}"
          attempt (some (formulaSrc, proofSrc, msg)) (remaining - 1)
        else
          return some ⟨formulaSrc, proofSrc, outcome⟩
      | _ => return some ⟨formulaSrc, proofSrc, outcome⟩
  attempt none rcfg.maxRetries

end Climber.Runner
