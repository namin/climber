import Climber.Climb
import Climber.Counter

/-
  Climber/Reflection.lean — internal RFN(T₀) and Con(T₀).

  The RFN(T₀) reflection schema admits, for any formula φ, the
  object-language formula `prov φ → φ`. The soundness certificate
  is exactly `soundness₀` — the metalanguage truth lemma for T₀.

  The headline rung-jump: T₁_rfn = T₀ + RFN(T₀) derives `Con(T₀)`,
  the formula `prov ⊥ → ⊥` ("T₀ does not derive ⊥"). T₀ provably
  cannot reach this formula — the H3 countermodel with
  `provVal ⊥ = mid` makes it H3-invalid, contradicting T₀'s
  H3-validity.

  This is the climber instantiated in the *Beklemishev shape*:
  the proposed extension is the local reflection principle for the
  base theory, the gate accepts because the metalanguage soundness
  proof type-checks, and the system's logical strength climbs into
  reach of its predecessor's consistency claim.
-/

namespace Climber

/-- RFN(T₀) schema: admits any object-language formula of the form
    `prov φ → φ`. -/
def rfn0Schema (ψ : Formula) : Prop :=
  ∃ φ : Formula, ψ = .imp (.prov φ) φ

/-- The RFN(T₀) extension. Soundness reduces to `soundness₀`:
    `interp env (prov φ → φ)` unfolds to `Derivable₀ φ → interp env φ`,
    which is exactly the metalanguage truth lemma for T₀. -/
def rfn0Extension : SoundExtension where
  schema := rfn0Schema
  sound  := by
    rintro ψ env ⟨φ, rfl⟩
    simp only [Formula.interp_imp, Formula.interp_prov]
    exact fun h => soundness₀ h

/-- T₁_rfn — T₀ extended with the RFN(T₀) reflection schema. -/
def T₁_rfn : Theory := Theory.base.extend rfn0Extension

/-- The consistency formula for T₀: `prov ⊥ → ⊥`. -/
def consistencyFormula : Formula := .imp (.prov .bot) .bot

/-- T₁_rfn derives Con(T₀). The witness is the RFN(T₀) instance at
    φ = ⊥, which is exactly `consistencyFormula`. -/
theorem T₁_rfn_derives_con : derives T₁_rfn consistencyFormula :=
  derives.extra rfn0Extension consistencyFormula
    (by simp [T₁_rfn, Theory.extend, Theory.base])
    ⟨.bot, rfl⟩

/-- Soundness of T₁_rfn — corollary of `climb_sound`. -/
theorem T₁_rfn_sound {φ : Formula} {env : String → Prop}
    (h : derives T₁_rfn φ) : Formula.interp env φ :=
  climb_sound h

/-- A `provVal` assignment that makes Con(T₀) H3-invalid: assign
    `prov ⊥` the value `mid`. The other prov-formulas don't matter. -/
def conProvVal : Formula → H3
  | .bot => H3.mid
  | _    => H3.bot

/-- Con(T₀) evaluates to `bot` under (counterEnv, conProvVal):
    `imp (prov ⊥) ⊥ = imp mid bot = bot`. -/
theorem con_h3_value :
    Formula.heyting counterEnv conProvVal consistencyFormula = H3.bot := by
  simp [consistencyFormula, Formula.heyting, conProvVal, H3.imp]

/-- T₀ provably cannot reach Con(T₀).

    Every T₀-derivable formula is H3-valid for any `provVal`
    (`Derivable₀.h3Valid`). The countermodel above gives a `provVal`
    making Con(T₀) H3-invalid. So Con(T₀) is not T₀-derivable.

    This is the climber's Beklemishev rung: T₀ cannot prove its own
    consistency, T₁_rfn = T₀ + RFN(T₀) does, the climb stays sound
    by `climb_sound`. -/
theorem con_not_derivable_in_T₀ : ¬ Derivable₀ consistencyFormula := by
  intro h
  have hval := h.h3Valid counterEnv conProvVal
  rw [con_h3_value] at hval
  exact H3.noConfusion hval

end Climber
