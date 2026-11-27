module

public import New.Reduction.Zeros.FixedStripCount
public import New.Reduction.Zeros.PrimeNumberTheorem
import Mathlib.Tactic

/-!
# A fixed-strip estimate for the project's weighted prime count

The coefficient bound and the principal main term are the same for every
analytic representative of the regular part.
-/

@[expose] public section

open Complex Real Filter Finset
namespace New.PrimeCutoff

theorem weighted_count_of_rectangle {d q : ℕ} [Fact d.Prime] [NeZero q] {G : ℂ → ℂ} {D σ τ : ℝ}
    (s₀ : 1 / 2 ≤ σ) (s₁ : σ < 1) (st : σ < τ) (pos : 0 ≤ D)
    (analytic : ∀ s : ℂ, σ ≤ s.re → DifferentiableAt ℂ G s)
    (series : ∀ s : ℂ, 1 < s.re →
      LSeries (fun n ↦ (lambdaKResidueClass d q n : ℂ)) s = G s + (q.totient : ℂ)⁻¹ / (s - 1))
    (rect : ∀ᶠ x : ℝ in atTop, ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 → |s.im| ≤ x ^ 2 →
      ‖G s‖ ≤ D * Real.log x) :
    ∃ K : ℝ, ∀ᶠ x : ℝ in atTop, |countError d q x| ≤ K * x ^ τ := by
  let a := fun n : ℕ ↦ (lambdaKResidueClass d q n : ℂ)
  let r : ℂ := (q.totient : ℂ)⁻¹
  have coeff (n : ℕ) (hn : 1 ≤ n) : ‖a n‖ ≤ 2 * Real.log ((n : ℝ) + 1) := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lambdaKResidueClass_nonneg d q n)]
    exact (lambdaKResidueClass_le_two_mul_vonMangoldt n).trans (mul_le_mul_of_nonneg_left
      (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (by linarith))) (by norm_num))
  obtain ⟨K, hK⟩ := count_of_fixed_strip s₀ s₁ st (by norm_num : (0 : ℝ) ≤ 2) pos coeff analytic series rect
  refine ⟨K, hK.mono fun x h ↦ ?_⟩
  have eq : ((countError d q x : ℝ) : ℂ) = ∑ n ∈ Ioc 0 ⌊x⌋₊, a n - r * x := by
    have zero : lambdaKResidueClass d q 0 = 0 := le_antisymm
      (by simpa only [Nat.cast_zero, mul_zero] using lambdaKResidueClass_le_two_mul (d := d) (q := q) 0)
      (lambdaKResidueClass_nonneg d q 0)
    rw [countError, Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, zero, zero_add]
    simp only [Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, a, r, div_eq_inv_mul]
  change ‖∑ i ∈ Ioc 0 ⌊x⌋₊, a i - r * x‖ ≤ K * x ^ τ at h
  simpa only [← eq, Complex.norm_real, Real.norm_eq_abs] using h

end New.PrimeCutoff
