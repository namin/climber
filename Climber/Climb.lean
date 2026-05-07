import Climber.Object

/-
  Climber/Climb.lean — the climb infrastructure.

  An admitted extension is a predicate over formulas (the "schema"
  of admitted instances) plus a soundness certificate. A Theory is
  the list of admitted extensions on top of T₀. The derivability
  predicate `derives T` is the closure of T₀ + the extensions
  under modus ponens.

  The headline metatheorem is `climb_sound`: every theory built by
  this climbing procedure preserves metalanguage truth.

  This is the architectural floor. The Beklemishev-shaped instance
  — admitting RFN(T_n) at each rung, with the soundness-of-T_n
  proof as the certificate — is the same architecture; the present
  artifact instantiates it for one rung with the simpler "admit a
  sound axiom schema" mode. See README.md for the path to the full
  reflection-principle climb.
-/

namespace Climber

/-- A SoundExtension carries a schema (predicate on formulas saying
    which instances are admitted) plus a soundness certificate. -/
structure SoundExtension where
  /-- Which formulas this extension admits as new axioms. -/
  schema : Formula → Prop
  /-- Soundness certificate: every admitted instance is metalanguage-true. -/
  sound  : ∀ (φ : Formula) (env : String → Prop),
             schema φ → Formula.interp env φ

/-- A theory is T₀ extended with a list of admitted SoundExtensions. -/
structure Theory where
  extras : List SoundExtension

namespace Theory

/-- The empty theory: just T₀, no extensions. -/
def base : Theory := { extras := [] }

/-- Extend a theory with one more admitted extension. -/
def extend (T : Theory) (se : SoundExtension) : Theory :=
  { extras := se :: T.extras }

end Theory

/-- Derivability in a theory: closure of T₀ + admitted schemas under MP.

    `base`  — anything T₀ proves.
    `extra` — any instance admitted by any extension in the theory.
    `mp`    — modus ponens. -/
inductive derives (T : Theory) : Formula → Prop where
  | base {φ : Formula} :
      Derivable₀ φ → derives T φ
  | extra (se : SoundExtension) (φ : Formula) :
      se ∈ T.extras → se.schema φ → derives T φ
  | mp {φ ψ : Formula} :
      derives T (.imp φ ψ) → derives T φ → derives T ψ

/-- Headline metatheorem: every theory built by climbing preserves truth.

    By induction on the derivation. T₀-derivations are sound by
    `soundness₀`. Each admitted extension carries its own `sound`
    certificate, kernel-checked at admission time. MP preserves
    truth. -/
theorem climb_sound {T : Theory} {φ : Formula} {env : String → Prop}
    (h : derives T φ) : Formula.interp env φ := by
  induction h with
  | base h₀ => exact soundness₀ h₀
  | extra se _ _ hsch => exact se.sound _ env hsch
  | mp _ _ ih₁ ih₂ => exact ih₁ ih₂

/-- Corollary: no theory built by climbing can derive ⊥. -/
theorem climb_consistent {T : Theory} : ¬ derives T .bot := by
  intro h
  have : Formula.interp (fun _ => True) .bot := climb_sound h
  exact this

end Climber
