import Climber

namespace Climber.Climbed

def round_0 : SoundExtension :=
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

def round_1 : SoundExtension :=
  SoundExtension.mk
    (fun ψ => ∃ φ : Formula, ψ = .imp (.imp (.imp φ .bot) .bot) φ)
    (by
      rintro ψ env ⟨φ, rfl⟩
      simp only [Formula.interp_imp, Formula.interp_bot]
      intro h
      by_cases hp : Formula.interp env φ
      · exact hp
      · exact (h hp).elim)

def T_climbed : Theory :=
  Theory.base
    |>.extend round_0
    |>.extend round_1

theorem T_climbed_sound {φ : Formula} {env : String → Prop}
    (h : derives T_climbed φ) : Formula.interp env φ :=
  climb_sound h

end Climber.Climbed
