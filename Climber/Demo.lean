import Climber.Climb

/-
  Climber/Demo.lean — the one-rung demo.

  Peirce's law `((p → q) → p) → p` is the simplest formula that is
  classically valid but not derivable in T₀ (intuitionistic
  implicational logic). The proposer offers it as a sound extension;
  the kernel admits the soundness certificate; T₁ = T₀ + Peirce
  derives it.

  The non-derivability of Peirce in T₀ is a well-known result; a
  formal proof would go through Heyting-algebra or Kripke semantics
  (~50 LOC of model theory). It is omitted here — the climb
  *mechanism* is what the demo exercises. See README.md for the
  status of that obligation and the path to its discharge.
-/

namespace Climber

/-- Peirce's law instantiated at atoms `p` and `q`. -/
def peirceFormula (p q : String) : Formula :=
  .imp (.imp (.imp (.atom p) (.atom q)) (.atom p)) (.atom p)

/-- Soundness of Peirce's law under any environment.

    The proof uses classical case analysis (`Classical.em`) — Peirce
    is *classically* valid but not intuitionistically valid. The
    certificate the proposer must supply for admission is exactly
    this term. -/
theorem peirceSound (p q : String) (env : String → Prop) :
    Formula.interp env (peirceFormula p q) := by
  simp only [peirceFormula, Formula.interp_imp, Formula.interp_atom]
  intro h
  by_cases hp : env p
  · exact hp
  · exact h (fun hp' => absurd hp' hp)

/-- The proposed extension. The schema admits any instance of
    Peirce's law over any pair of atoms. -/
def peirceExtension : SoundExtension where
  schema := fun φ => ∃ p q : String, φ = peirceFormula p q
  sound := by
    rintro φ env ⟨p, q, rfl⟩
    exact peirceSound p q env

/-- T₁ — T₀ extended with Peirce's law. -/
def T₁ : Theory := Theory.base.extend peirceExtension

/-- The headline of the rung: T₁ derives Peirce's law. -/
theorem T₁_derives_peirce (p q : String) :
    derives T₁ (peirceFormula p q) :=
  derives.extra peirceExtension (peirceFormula p q)
    (by simp [T₁, Theory.extend, Theory.base])
    ⟨p, q, rfl⟩

/-- Soundness of T₁ — corollary of `climb_sound`. The system has
    climbed (Peirce now derivable) and stayed sound (no falsehoods
    derivable). -/
theorem T₁_sound {φ : Formula} {env : String → Prop}
    (h : derives T₁ φ) : Formula.interp env φ :=
  climb_sound h

end Climber
