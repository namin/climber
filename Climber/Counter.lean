import Climber.Demo

/-
  Climber/Counter.lean — non-derivability of Peirce's law in T₀.

  T₀ is the implicational fragment of intuitionistic propositional
  logic plus ex falso quodlibet. We give a model — the 3-element
  linear Heyting algebra {⊥ < m < ⊤} — for which T₀ is sound: K, S,
  ⊥-elim are always ⊤, and MP preserves ⊤. Peirce's law over the
  atoms (p, q) evaluates to m under the assignment p ↦ m, q ↦ ⊥, so
  it cannot be derivable in T₀.

  This sharpens the demo's narrative: T₀ provably *cannot reach*
  Peirce's law; T₁ does. The climb crossed an unreachable line.
-/

namespace Climber

/-- A 3-element linear Heyting algebra: bot < mid < top. -/
inductive H3 where
  | bot
  | mid
  | top
deriving DecidableEq, Repr

namespace H3

/-- Heyting implication for the 3-element chain. -/
def imp : H3 → H3 → H3
  | .bot, _    => .top
  | .mid, .bot => .bot
  | .mid, .mid => .top
  | .mid, .top => .top
  | .top, .bot => .bot
  | .top, .mid => .mid
  | .top, .top => .top

end H3

/-- Interpret a formula into the 3-element Heyting algebra. The
    `provVal` parameter assigns an H3 value to each `prov φ` atom;
    since T₀ has no rule for `prov`, any `provVal` makes the axiom
    schemas of T₀ valid. -/
def Formula.heyting (env : String → H3) (provVal : Formula → H3) :
    Formula → H3
  | .bot     => H3.bot
  | .atom a  => env a
  | .imp φ ψ => H3.imp (heyting env provVal φ) (heyting env provVal ψ)
  | .prov φ  => provVal φ

/-- The K axiom is H3-valid. -/
private theorem h3_K (a b : H3) : H3.imp a (H3.imp b a) = H3.top := by
  cases a <;> cases b <;> rfl

/-- The S axiom is H3-valid. -/
private theorem h3_S (a b c : H3) :
    H3.imp (H3.imp a (H3.imp b c)) (H3.imp (H3.imp a b) (H3.imp a c)) = H3.top := by
  cases a <;> cases b <;> cases c <;> rfl

/-- ⊥-elim is H3-valid. -/
private theorem h3_botE (a : H3) : H3.imp H3.bot a = H3.top := rfl

/-- MP preserves H3-validity. -/
private theorem h3_mp (a : H3) : H3.imp H3.top a = H3.top → a = H3.top := by
  cases a <;> intro h
  · exact h
  · cases h
  · rfl

/-- Validity in H3: the formula evaluates to top under every
    environment and every `prov`-assignment. -/
def Formula.h3Valid (φ : Formula) : Prop :=
  ∀ env : String → H3, ∀ provVal : Formula → H3,
    Formula.heyting env provVal φ = H3.top

/-- Every T₀-derivable formula is H3-valid. -/
theorem Derivable₀.h3Valid {φ : Formula} (h : Derivable₀ φ) :
    Formula.h3Valid φ := by
  induction h with
  | k φ' ψ' =>
    intro env provVal
    simp only [Formula.heyting]
    exact h3_K _ _
  | s φ' ψ' χ' =>
    intro env provVal
    simp only [Formula.heyting]
    exact h3_S _ _ _
  | bot_e φ' =>
    intro env provVal
    simp only [Formula.heyting]
    exact h3_botE _
  | mp _ _ ih₁ ih₂ =>
    intro env provVal
    have h₁ := ih₁ env provVal
    have h₂ := ih₂ env provVal
    simp only [Formula.heyting] at h₁
    rw [h₂] at h₁
    exact h3_mp _ h₁

/-- Counterexample environment: p ↦ mid, every other atom ↦ bot. -/
def counterEnv : String → H3
  | "p" => H3.mid
  | _   => H3.bot

/-- A trivial `prov`-assignment. The Peirce demo doesn't use `prov`,
    so any value works; we pick `bot` for definiteness. -/
def counterProvVal : Formula → H3 := fun _ => H3.bot

/-- Peirce's law over (p, q) evaluates to mid under counterEnv. -/
theorem peirce_h3_value :
    Formula.heyting counterEnv counterProvVal (peirceFormula "p" "q") = H3.mid := by
  simp [peirceFormula, Formula.heyting, counterEnv, H3.imp]

/-- Peirce's law over (p, q) is not derivable in T₀.

    The counter-model shows the climb to T₁ crossed an unreachable
    line — `peirceFormula "p" "q"` is provably outside the closure
    of T₀'s axioms under MP, but inside the closure of T₁ via the
    admitted Peirce extension. -/
theorem peirce_not_derivable_in_T₀ : ¬ Derivable₀ (peirceFormula "p" "q") := by
  intro h
  have hval := h.h3Valid counterEnv counterProvVal
  rw [peirce_h3_value] at hval
  exact H3.noConfusion hval

end Climber
