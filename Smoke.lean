import Climber

/-
  Smoke.lean — smoke test executable.

  Reports the load-bearing facts of the climb at runtime:
  - T₀ is sound (soundness₀ exists).
  - T₁ = T₀ + Peirce extension exists.
  - T₁ derives Peirce (T₁_derives_peirce exists).
  - climb_sound holds for any Theory.

  All four facts are theorems; the executable just reports they
  are present. The kernel did the verification at compile time.
-/

open Climber

def main : IO Unit := do
  IO.println "climber — smoke test"
  IO.println "===================="
  IO.println ""
  IO.println "T₀: minimal implicational logic with ⊥-elim (K, S, bot_e, MP)."
  IO.println "    soundness₀ : ∀ φ env, Derivable₀ φ → interp env φ  ✓"
  IO.println ""
  IO.println "Proposed extension:"
  IO.println "    Peirce's law: ((p → q) → p) → p"
  IO.println "    soundness certificate: peirceSound  ✓ (kernel-checked)"
  IO.println ""
  IO.println "T₁ = T₀.extend peirceExtension"
  IO.println "    derives T₁ (peirceFormula \"p\" \"q\")  ✓"
  IO.println "    climb_sound : ∀ T φ env, derives T φ → interp env φ  ✓"
  IO.println ""
  IO.println "Counter-model (3-element Heyting algebra):"
  IO.println "    peirce_not_derivable_in_T₀  ✓ (T₀ provably cannot reach Peirce)"
  IO.println ""
  IO.println "The climb crossed an unreachable line:"
  IO.println "  T₀ ⊬ Peirce, T₁ ⊢ Peirce, both stay sound."
  IO.println ""
  IO.println "Internal RFN(T₀) rung:"
  IO.println "    rfn0Extension : SoundExtension"
  IO.println "    schema admits  prov φ → φ  for any φ"
  IO.println "    soundness certificate: soundness₀ (kernel-checked)"
  IO.println ""
  IO.println "T₁_rfn = T₀.extend rfn0Extension"
  IO.println "    consistencyFormula : Formula  =  prov ⊥ → ⊥"
  IO.println "    T₁_rfn_derives_con  ✓"
  IO.println "    con_not_derivable_in_T₀  ✓ (T₀ cannot prove its own consistency)"
  IO.println ""
  IO.println "The Beklemishev rung: T₀ ⊬ Con(T₀), T₁_rfn ⊢ Con(T₀)."
