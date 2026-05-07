/-
  Climber/Object.lean — the object theory T₀.

  Minimal implicational logic with ⊥. T₀ has axiom schemas K, S, ⊥-elim,
  closed under modus ponens. This is the implicational fragment of
  intuitionistic propositional logic plus ex falso quodlibet.

  We prove soundness₀: every Derivable₀ formula holds under the
  standard interpretation. This is the metalanguage "truth lemma"
  for T₀, and it is what the proposer is asked to produce in order
  to admit RFN(T₀) as a derivation rule.
-/

namespace Climber

inductive Formula where
  | bot
  | atom (a : String)
  | imp (φ ψ : Formula)
deriving DecidableEq, Repr

namespace Formula

def interp (env : String → Prop) : Formula → Prop
  | .bot => False
  | .atom a => env a
  | .imp φ ψ => interp env φ → interp env ψ

@[simp] theorem interp_bot (env : String → Prop) :
    interp env .bot = False := rfl

@[simp] theorem interp_atom (env : String → Prop) (a : String) :
    interp env (.atom a) = env a := rfl

@[simp] theorem interp_imp (env : String → Prop) (φ ψ : Formula) :
    interp env (.imp φ ψ) = (interp env φ → interp env ψ) := rfl

end Formula

/-- T₀: minimal implicational logic with ⊥-elim. -/
inductive Derivable₀ : Formula → Prop where
  | k (φ ψ : Formula) :
      Derivable₀ (.imp φ (.imp ψ φ))
  | s (φ ψ χ : Formula) :
      Derivable₀ (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | bot_e (φ : Formula) :
      Derivable₀ (.imp .bot φ)
  | mp {φ ψ : Formula} :
      Derivable₀ (.imp φ ψ) → Derivable₀ φ → Derivable₀ ψ

/-- Soundness of T₀: every Derivable₀ formula holds under any interpretation.

    This is the metalanguage truth lemma for T₀. It is exactly the term
    the proposer must supply to admit RFN(T₀) as a new derivation rule. -/
theorem soundness₀ {φ : Formula} {env : String → Prop}
    (h : Derivable₀ φ) : Formula.interp env φ := by
  induction h with
  | k φ' ψ' =>
    simp only [Formula.interp_imp]
    intro hp _
    exact hp
  | s φ' ψ' χ' =>
    simp only [Formula.interp_imp]
    intro habc hab a
    exact habc a (hab a)
  | bot_e φ' =>
    simp only [Formula.interp_imp, Formula.interp_bot]
    intro hbot
    exact False.elim hbot
  | mp _ _ ih₁ ih₂ =>
    exact ih₁ ih₂

end Climber
