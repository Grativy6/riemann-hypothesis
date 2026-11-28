import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import Mathlib.Tactic

open Nat ZMod DirichletCharacter
namespace Hearthline.ConductorWitness

/-- The principal unit 18 is invisible at level 17 and is detected by a complex character
of exact conductor 289. Thus a search modulus may forget a repeated prime that the character needs. -/
theorem eighteen_detected : ∃ χ : DirichletCharacter ℂ 289, χ.conductor = 289 ∧ χ 18 ≠ 1 := by
  obtain ⟨χ, hit⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (by decide : (18 : ZMod 289) ≠ 1)
  refine ⟨χ, ?_, hit⟩
  by_contra wrong
  have divs := Nat.mem_divisors.2 ⟨χ.conductor_dvd_level, (by decide : (289 : ℕ) ≠ 0)⟩
  have small : ∀ f ∈ (289 : ℕ).divisors, f ≠ 289 → f ∣ 17 := by decide +kernel
  have lost : (18 : ZMod χ.conductor) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff 18 1 χ.conductor).2
      ((by decide : 18 ≡ 1 [MOD 17]).of_dvd (small _ divs wrong))
  have unit : IsCoprime (18 : ℤ) 289 := ⟨-16, 1, by norm_num⟩
  have ev := χ.primitiveCharacter.changeLevel_eq_cast_of_dvd' χ.conductor_dvd_level unit
  rw [χ.changeLevel_primitiveCharacter] at ev
  have eqval : χ 18 = χ.primitiveCharacter 18 := by simpa using ev
  exact hit (eqval.trans (by rw [lost, map_one]))

example : (18 : ZMod 17) = 1 ∧ (18 : ZMod 289) ^ 16 = 273 := by decide +kernel

/-- The lcm is the minimum for divisibility, for every multiple accepted by both sets of inputs. -/
theorem least_level (base f N : ℕ) : Nat.lcm base f ∣ N ↔ base ∣ N ∧ f ∣ N :=
  ⟨fun h ↦ ⟨(Nat.dvd_lcm_left _ _).trans h, (Nat.dvd_lcm_right _ _).trans h⟩,
    fun h ↦ Nat.lcm_dvd h.1 h.2⟩

/-- Changing only the declared level of a principal character has no effect on its conductor. -/
example : (1 : DirichletCharacter ℂ 289).conductor = 1 ∧ Nat.lcm 18480 1 = 18480 ∧
    18480 * 289 = 5340720 := by simp [DirichletCharacter.conductor_one]

end Hearthline.ConductorWitness
