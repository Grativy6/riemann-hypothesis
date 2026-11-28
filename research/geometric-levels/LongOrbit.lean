import New.Reduction.OneSidedBound
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

open Filter Nat ZMod New
namespace Hearthline.LongOrbit

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The prime search keeps the same odd support while the seventeens accumulate in the field. -/
theorem odd_support (k : ℕ) : oddPrimeProduct (1680 * 17 ^ (k+1)) = 19635 := by
  unfold oddPrimeProduct
  rw [← Nat.mul_assoc, Nat.primeFactors_mul (by decide) (pow_ne_zero _ (by decide)),
    Nat.primeFactors_prime_pow (Nat.succ_ne_zero k) (by decide : Nat.Prime 17)]
  decide +kernel

def parameters (k : ℕ) : Parameters where
  q₀ := 1680 * 17 ^ (k+1)
  d := 1099559
  dvd_q₀ := dvd_mul_right _ _
  d_prime := by norm_num1
  prime_conditions := by
    apply geometricPrimeConditions_of_search (dvd_mul_right _ _)
    simp only [twistSearchResidue, twistSearchModulus, odd_support]
    decide

theorem no_minus_one (k n : ℕ) :
    (1099559 : ZMod (1680 * 17 ^ (k+1))) ^ n ≠ -1 := (parameters k).d_pow_ne_neg_one n

private theorem even_power (k m : ℕ) :
    17 ^ (k+1) ∣ (1099559 ^ 2) ^ m - 1 ↔ 17 ^ k ∣ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have large : 1 < (1099559 ^ 2 : ℕ) ^ m := Nat.one_lt_pow hm (by decide)
  have nz : (1099559 ^ 2 : ℕ) ^ m - 1 ≠ 0 := by omega
  have v := Nat.multiplicity_pow_sub_pow (p := 17) (x := 1099559^2) (y := 1)
    (by decide) (by decide) (by decide) (by decide) hm
  simp only [one_pow, Nat.multiplicity_eq_factorization (by decide : Nat.Prime 17)] at v
  have base : (1099559 ^ 2 - 1).factorization 17 = 1 := by
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 17)
      (by decide : 1099559 ^ 2 - 1 ≠ 0)).1 (by decide : 17 ^ 1 ∣ 1099559 ^ 2 - 1)
    have h2 : ¬ (2 ≤ (1099559 ^ 2 - 1).factorization 17) := fun h ↦
      (by decide : ¬ 17 ^ 2 ∣ 1099559 ^ 2 - 1) ((Nat.Prime.pow_dvd_iff_le_factorization
        (by decide : Nat.Prime 17) (by decide : 1099559 ^ 2 - 1 ≠ 0)).2 h)
    omega
  rw [base] at v
  rw [Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 17) nz,
    Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 17) hm]
  omega

theorem return_iff (k n : ℕ) :
    1099559 ^ n ≡ 1 [MOD 1680 * 17 ^ (k+1)] ↔ 2 * 17 ^ k ∣ n := by
  have p17 : 17 ∣ 1680 * 17 ^ (k+1) :=
    (dvd_pow_self 17 (Nat.succ_ne_zero k)).trans (dvd_mul_left _ 1680)
  constructor
  · intro ret
    have even : Even n := by
      rcases Nat.even_or_odd n with even | odd
      · exact even
      have at17 := (ZMod.natCast_eq_natCast_iff (1099559 ^ n) 1 17).2 (ret.of_dvd p17)
      push_cast at at17
      rw [show (1099559 : ZMod 17) = -1 by decide, odd.neg_one_pow] at at17
      exact False.elim ((by decide : (-1 : ZMod 17) ≠ 1) at17)
    obtain ⟨m, hm⟩ := even
    have two : n = 2 * m := by omega
    rw [two] at ret ⊢
    have sub := (Nat.modEq_iff_dvd' (by exact Nat.succ_le_of_lt (by positivity) : 1 ≤ 1099559 ^ (2*m))).1
      (ret.of_dvd (dvd_mul_left (17 ^ (k+1)) 1680)).symm
    rw [pow_mul] at sub
    exact Nat.mul_dvd_mul_left 2 ((even_power k m).1 sub)
  · rintro ⟨c, rfl⟩
    have equalExp : 2 * 17 ^ k * c = 2 * (17 ^ k * c) := Nat.mul_assoc ..
    rw [equalExp, pow_mul]
    apply Nat.ModEq.symm
    apply (Nat.modEq_iff_dvd' (by exact Nat.succ_le_of_lt (by positivity) : 1 ≤ (1099559^2)^(17^k*c))).2
    have small := (Nat.modEq_iff_dvd' (by exact Nat.succ_le_of_lt (by positivity) : 1 ≤ (1099559^2)^(17^k*c))).1
      (show 1 ≡ (1099559^2)^(17^k*c) [MOD 1680] by
        simpa only [one_pow] using (show 1 ≡ 1099559^2 [MOD 1680] by decide).pow (17^k*c))
    have big := (even_power k (17^k*c)).2 (dvd_mul_right _ _)
    exact ((by decide : Nat.Coprime 1680 17).pow_right _).mul_dvd_of_dvd_of_dvd small big

theorem period (k : ℕ) : orderOf (1099559 : ZMod (1680 * 17 ^ (k+1))) = 2 * 17 ^ k := by
  have test (n : ℕ) : (1099559 : ZMod (1680 * 17 ^ (k+1))) ^ n = 1 ↔ 2 * 17 ^ k ∣ n := by
    simpa only [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using return_iff k n
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((test _).2 dvd_rfl))
    ((test _).1 (pow_orderOf_eq_one _))

/-- The single prime 1099559 supplies the actual geometric estimate at this infinite family
of levels. The eventual cutoff may depend on the level and the positive exponent allowance. -/
theorem fixed_prime_remainder (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in Filter.atTop, @primeRemainder 1099559 ⟨(parameters k).d_prime⟩ (1680 * 17 ^ (k+1)) _ y ≤
      (128 * ((1680 * 17 ^ (k+1)).totient : ℝ) + 32) * y ^ (-1 / 2 + ε) :=
  (parameters k).eventually_primeRemainder_le_mul_rpow hε

end Hearthline.LongOrbit
