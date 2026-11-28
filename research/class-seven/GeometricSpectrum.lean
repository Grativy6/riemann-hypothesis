import OrbitSpectrum
import New.Reduction.OneSidedBound
import Mathlib.Tactic

open Nat Filter ZMod New Hearthline.OrbitSpectrum
open scoped Topology
noncomputable section
namespace Hearthline.GeometricSpectrum

private theorem odd_support (k : ℕ) : oddPrimeProduct (1680 * 17 ^ (k+1)) = 19635 := by
  unfold oddPrimeProduct
  rw [← Nat.mul_assoc, Nat.primeFactors_mul (by decide) (pow_ne_zero _ (by decide)),
    Nat.primeFactors_prime_pow (Nat.succ_ne_zero k) (by decide : Nat.Prime 17)]
  decide +kernel

/-- The order spectrum survives simultaneously requiring the actual geometric estimate and
zero-free twists for every character at every divisor of a separately prescribed common level. -/
theorem exact_joint_spectrum (k extra o B : ℕ) [NeZero extra] {β : ℝ} (hβ : 1/2 < β) (H : ℝ) :
    (∃ d : Nat.Primes, B < (d : ℕ) ∧ (d : ℕ) ≡ 157079 [MOD 314160] ∧
      orderOf ((d : ℕ) : ZMod (1680 * 17^(k+1))) = o ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, primeRemainder d (1680 * 17^(k+1)) x ≤
        (128 * ((1680 * 17^(k+1)).totient : ℝ) + 32) * x ^ (-1/2 + ε)) ∧
      ∀ (m : ℕ) [NeZero m], m ∣ Nat.lcm (1680 * 17^(k+1)) extra →
        m.Coprime d ∧ ∀ (χ : DirichletCharacter ℂ m) (s : ℂ), β ≤ s.re → |s.im| ≤ H →
          entireL (quadTwist χ d) s ≠ 0) ↔ ∃ j ≤ k, o = 2 * 17^j := by
  constructor
  · rintro ⟨d, _, cls, eq, _, _⟩
    obtain ⟨j, small, size⟩ := period_in_range k d.prop cls
    exact ⟨j, small, eq.symm.trans size⟩
  · rintro ⟨j, small, rfl⟩
    let N := 1680 * 17 ^ (k+1)
    let L := Nat.lcm N extra
    have : NeZero N := ⟨Nat.mul_ne_zero (by decide) (pow_ne_zero _ (by decide))⟩
    have : NeZero L := ⟨Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne extra)⟩
    obtain ⟨d, large, cls, order, cop, nz⟩ := choose_period k j small L hβ H B
    have condition : GeometricPrimeConditions N d :=
      geometricPrimeConditions_of_search (dvd_mul_right 1680 _) (by
        simpa only [N, twistSearchModulus, twistSearchResidue, odd_support] using cls)
    let P : Parameters := ⟨N, d, dvd_mul_right 1680 _, d.prop, condition⟩
    refine ⟨d, large, cls, order, fun ε hε ↦ P.eventually_primeRemainder_le_mul_rpow hε, ?_⟩
    intro m _ hm
    refine ⟨cop.of_dvd_left hm, fun χ s hs hi ↦ ?_⟩
    apply entireL_ne_zero_of_changeLevel (quadTwist χ d) (Nat.mul_dvd_mul_right hm (d : ℕ))
    rw [← quadTwist_changeLevel_eq]
    exact nz (χ.changeLevel hm) s hs hi

example : Nat.lcm 485520 314160 = 5340720 ∧ 157079 % 314160 = 157079 ∧
    2670359 % 314160 = 157079 ∧ (157079 + 1) % 289 ≠ 0 ∧ (2670359 + 1) % 289 = 0 := by
  decide +kernel

/-- The smallest incompatible unit class, even though the all-class proposal can cover it. -/
example {N : ℕ} [NeZero N] {β : ℝ} (hβ : 1/2 < β) (H : ℝ) :
    ¬ (∀ B : ℕ, ∃ d : Primes, B < (d : ℕ) ∧ (d : ℕ) ≡ 1 [MOD 4] ∧ (d : ℕ) % 8 = 7 ∧
      N.Coprime d ∧ ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), β ≤ s.re → |s.im| ≤ H →
        entireL (quadTwist χ d) s ≠ 0) := by
  rw [New.cofinal_seven_iff (N := N) (Q := 4) (a := 1) hβ H]
  decide

end Hearthline.GeometricSpectrum
