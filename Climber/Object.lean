/-
  Climber/Object.lean — the object theory T₀.

  Minimal implicational logic with ⊥ and an internal provability
  predicate `prov`. T₀'s axiom schemas K, S, ⊥-elim are arbitrary in
  φ, ψ, χ — they apply to *any* formula, including those containing
  `prov`. T₀ has no rule introducing `prov` itself; the predicate is
  inert at level 0 and acquires meaning only when a higher rung
  admits a reflection schema (see `Reflection.lean`).

  The interpretation is fixed: `prov φ` is interpreted as the Lean
  proposition `Derivable₀ φ`. The soundness theorem `soundness₀`
  then says that T₀ is sound for this fixed interpretation — the
  metalanguage truth lemma the proposer must reproduce in order to
  admit RFN(T₀) at the next rung.
-/

namespace Climber

mutual

inductive Formula where
  | bot
  | atom (a : String)
  | imp (φ ψ : Formula)
  /-- Internal provability predicate: `prov φ` represents
      "T₀ proves φ" as a formula of the object language. T₀ has no
      derivation rule introducing `prov`; it is inert at level 0. -/
  | prov (φ : Formula)
deriving Repr

end

/-- T₀: minimal implicational logic with ⊥-elim. K, S, ⊥-elim are
    schematic in φ, ψ, χ — instances may contain `prov` even though
    T₀ itself has no rule for `prov`. -/
inductive Derivable₀ : Formula → Prop where
  | k (φ ψ : Formula) :
      Derivable₀ (.imp φ (.imp ψ φ))
  | s (φ ψ χ : Formula) :
      Derivable₀ (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | bot_e (φ : Formula) :
      Derivable₀ (.imp .bot φ)
  | mp {φ ψ : Formula} :
      Derivable₀ (.imp φ ψ) → Derivable₀ φ → Derivable₀ ψ

namespace Formula

/-- Standard truth-functional interpretation, with `prov φ`
    interpreted as `Derivable₀ φ`. -/
def interp (env : String → Prop) : Formula → Prop
  | .bot     => False
  | .atom a  => env a
  | .imp φ ψ => interp env φ → interp env ψ
  | .prov φ  => Derivable₀ φ

@[simp] theorem interp_bot (env : String → Prop) :
    interp env .bot = False := rfl

@[simp] theorem interp_atom (env : String → Prop) (a : String) :
    interp env (.atom a) = env a := rfl

@[simp] theorem interp_imp (env : String → Prop) (φ ψ : Formula) :
    interp env (.imp φ ψ) = (interp env φ → interp env ψ) := rfl

@[simp] theorem interp_prov (env : String → Prop) (φ : Formula) :
    interp env (.prov φ) = Derivable₀ φ := rfl

end Formula

/-- Soundness of T₀: every Derivable₀ formula holds under the
    standard interpretation. The case for `prov` does not arise as
    a derivation step (T₀ has no rule for `prov`); axiom-schema
    instances containing `prov` are sound by case analysis on
    whether their `interp` reduces to True/False structurally. -/
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
