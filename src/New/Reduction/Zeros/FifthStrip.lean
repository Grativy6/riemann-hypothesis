module

public import New.Reduction.Zeros.PrimeNumberTheorem
import Lib.Analytic.PrimeNumberTheorem.LFunctionGrowth
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import Mathlib.Tactic

/-!
# A logarithmic derivative in the fixed strip

A disk centered at 2 + it with radius 7/5 stays in Re > 3/5.
Every point at the same height with 2/3 ≤ Re ≤ 2 lies at distance at most 4/3
from its center. The gap between these radii makes the disk estimate uniform.
-/

@[expose] public section

open Complex Real Metric Set Filter DirichletCharacter
namespace New.PrimeCutoff

/-- Polynomial size of the pole-cleared function, including its principal factor. -/
lemma entire_growth {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : ‖entireL χ s‖ ≤ 8 * N * (‖s‖ + 1) ^ 2 := by
  let b : ℂ := if χ = 1 then s else 1
  have bne : b ≠ 0 := by dsimp [b]; split <;> simp_all [ne_zero_of_re_pos (by linarith : 0 < s.re)]
  have bn : ‖b‖ ≤ ‖s‖ + 1 := by dsimp [b]; split <;> simp [norm_nonneg]
  have eq : regularL χ s * b = entireL χ s := div_mul_cancel₀ _ bne
  rw [← eq, norm_mul]
  calc _ ≤ (8 * N * ‖s‖) * (‖s‖ + 1) := mul_le_mul (norm_regularL_le_linear χ hs) bn (norm_nonneg _) (by positivity)
       _ ≤ _ := by nlinarith [show 0 ≤ 8 * (N : ℝ) * (‖s‖ + 1) by positivity]

/-- Uniform positive lower bound at the center of each horizontal disk. -/
lemma entire_center_lower {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {c : ℂ}
    (hc : c.re = 2) : Real.exp (-(riemannZeta 2).re) ≤ ‖entireL χ c‖ := by
  have h := χ.exp_neg_re_riemannZeta_le_norm_LFunction (s := c) (by linarith)
  rw [hc] at h
  have hc₁ : c ≠ 1 := by intro he; simp [he] at hc
  have factor : 1 ≤ ‖c - 1‖ := by
    calc (1 : ℝ) = (c - 1).re := by norm_num [hc]
         _ ≤ _ := re_le_norm _
  by_cases e : χ = 1
  · subst χ
    apply h.trans
    simp only [entireL, ite_true, LFunctionTrivChar₁, Function.update_of_ne hc₁, norm_mul, LFunctionTrivChar]
    exact le_mul_of_one_le_left (norm_nonneg _) factor
  · simpa [entireL, e] using h

/-- A fixed zero-free half-plane bounds the logarithmic derivative everywhere in
the smaller rectangle of height x². The threshold may depend on the modulus. -/
theorem logDeriv_on_rectangle {N : ℕ} [NeZero N] :
    ∀ᶠ x : ℝ in atTop, ∀ χ : DirichletCharacter ℂ N,
      (∀ z : ℂ, 3 / 5 < z.re → entireL χ z ≠ 0) →
      ∀ s : ℂ, 2 / 3 ≤ s.re → s.re ≤ 2 → |s.im| ≤ x ^ 2 →
        ‖logDeriv (entireL χ) s‖ ≤ 13000 * Real.log x := by
  let B := Real.exp (-(riemannZeta 2).re)
  have bp : 0 < B := Real.exp_pos _
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (72 * (N : ℝ) / B)] with x hx hN
  intro χ clear s hleft hright him
  let c : ℂ := 2 + (s.im : ℂ) * I
  have cr : c.re = 2 := by simp [c]
  have dnorm : ‖s - c‖ ≤ 4 / 3 := by
    have e : s - c = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.2 hright)]
    linarith
  have cp : ‖c‖ ≤ 2 + x ^ 2 := by
    calc _ ≤ ‖(2 : ℂ)‖ + ‖(s.im : ℂ) * I‖ := norm_add_le _ _
         _ ≤ _ := by simpa using him
  have wd {w : ℂ} (hw : w ∈ ball c (7 / 5)) : 3 / 5 < w.re ∧ ‖w‖ ≤ 2 * x ^ 2 := by
    have hdist := mem_ball_iff_norm.1 hw
    have hre := neg_le_of_abs_le (Complex.abs_re_le_norm (w - c))
    rw [sub_re, cr] at hre
    constructor
    · linarith
    · nlinarith only [norm_le_norm_sub_add w c, cp, hdist, show 4 ≤ x ^ 2 by nlinarith [sq_nonneg (x - 2)]]
  have bound (w : ℂ) (hw : w ∈ ball c (7 / 5)) : ‖entireL χ w‖ ≤ x ^ 5 * ‖entireL χ c‖ := by
    obtain ⟨wre, wn⟩ := wd hw
    have large : 72 * (N : ℝ) ≤ x * B := (div_le_iff₀ bp).1 hN
    have z : ‖w‖ + 1 ≤ 3 * x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
    calc _ ≤ 8 * N * (‖w‖ + 1) ^ 2 := entire_growth χ (by linarith)
         _ ≤ 8 * N * (3 * x ^ 2) ^ 2 := by gcongr
         _ = (72 * N) * x ^ 4 := by ring
         _ ≤ (x * B) * x ^ 4 := mul_le_mul_of_nonneg_right large (by positivity)
         _ = x ^ 5 * B := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (entire_center_lower χ cr) (by positivity)
  have disk := Complex.norm_logDeriv_le_of_forall_mem_ball_norm_le_mul
    (fun w _ ↦ (analyticAt_entireL χ w).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ clear w (wd hw).1) bound (show ‖s - c‖ < 7 / 5 by linarith)
  have denom : (1 / 15 : ℝ) ≤ 7 / 5-‖s - c‖ := by linarith
  have ratio : 4 * (7 / 5 + ‖s - c‖) / (7 / 5-‖s - c‖) ^ 2 ≤ (2600 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 7 / 5-‖s - c‖))).2
    have ds := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 15) denom 2
    linarith
  have lx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [Real.log_pow] at disk
  exact disk.trans ((mul_le_mul_of_nonneg_right ratio (by positivity : 0 ≤ ((5 : ℕ) : ℝ) * Real.log x)).trans_eq (by norm_num; ring))

end New.PrimeCutoff
