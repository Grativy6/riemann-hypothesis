module

public import TauCeti.NumberTheory.LSeries.SmoothedSum.ContourEstimate
import TauCeti.NumberTheory.LSeries.SmoothedSum.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Multiplicative
import TauCeti.Analysis.MellinTransform.SmoothCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# A sharp count from a fixed zero-free strip

Use smoothing width 1/x and contour height x². Removing the smoothing then costs
only O(log x). On a fixed left edge σ ≥ 1/2, logarithmic growth of the regular part gives
O(x^σ log² x). Every larger power absorbs the two logarithms.
-/

@[expose] public section

open Real Complex Set Filter MeasureTheory TauCeti
namespace New.PrimeCutoff

private lemma rectangle_cost {x B C D R η : ℝ} (he : 0 < η) (he₂ : η ≤ 1/2)
    (hx : 4 ≤ x) (hL : 1 ≤ Real.log x) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hR : 0 ≤ R) :
    (1 / (2 * Real.pi)) *
      (2 * (8 * B * Real.log x ^ 2 * C * (Real.exp 1 * x)) / (x⁻¹ * x ^ 2) +
       4 * ((D * Real.log x + R / η) * C * x ^ (1 - η)) * Real.log (1 + x ^ 2 / (1 - η)) +
       2 * (((Real.log x)⁻¹ + η) * ((D * Real.log x + R / η) * C) * (Real.exp 1 * x) / (x⁻¹ * (x ^ 2) ^ 2))) ≤
      (16 * B * C * Real.exp 1 + 12 * (D + R / η) * C + 4 * (D + R / η) * C * Real.exp 1) *
        (x ^ (1 - η) * Real.log x ^ 2) := by
  let L := Real.log x
  let X := x ^ (1 - η)
  have xp : 0 < x := by linarith
  have lp : 1 ≤ L := hL
  have Xp : 1 ≤ X := Real.one_le_rpow (by linarith) (by linarith)
  have Pb : 0 ≤ D + R / η := by positivity
  have P : D * L + R / η ≤ (D + R / η) * L := by nlinarith only [mul_nonneg (div_nonneg hR he.le) (sub_nonneg.2 lp)]
  have height : Real.log (1 + x ^ 2 / (1 - η)) ≤ 3 * L := by
    have le : 1 + x ^ 2 / (1 - η) ≤ x ^ 3 := by
      have inv : x ^ 2 / (1 - η) ≤ 2 * x ^ 2 := by
        apply (div_le_iff₀ (by linarith : 0 < 1 - η)).2
        nlinarith only [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1 - 2 * η)]
      nlinarith only [inv, mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx), sq_nonneg (x - 1), hx]
    exact (Real.log_le_log (by linarith [div_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1 - η)]) le).trans_eq (by simp [L, Real.log_pow])
  have tail : 2 * (8 * B * L ^ 2 * C * (Real.exp 1 * x)) / (x⁻¹ * x ^ 2) ≤
      (16 * B * C * Real.exp 1) * (X * L ^ 2) := by
    calc _ = 16 * B * C * Real.exp 1 * L ^ 2 := by field_simp; ring
         _ ≤ _ := by nlinarith only [mul_nonneg (show 0 ≤ 16 * B * C * Real.exp 1 * L ^ 2 by positivity) (sub_nonneg.2 Xp)]
  have left : 4 * ((D * L + R / η) * C * X) * Real.log (1 + x ^ 2 / (1 - η)) ≤
      (12 * (D + R / η) * C) * (X * L ^ 2) := by
    calc _ ≤ 4 * (((D + R / η) * L) * C * X) * (3 * L) := by
              apply mul_le_mul _ height _ (by positivity)
              · gcongr
              · apply Real.log_nonneg; linarith [div_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1 - η)]
         _ = _ := by ring
  have invL : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ lp
  have one : 1 ≤ x ^ 2 := one_le_pow₀ (by linarith) (n := 2)
  have horizontal : 2 * ((L⁻¹ + η) * ((D * L + R / η) * C) * (Real.exp 1 * x) / (x⁻¹ * (x ^ 2) ^ 2)) ≤
      (4 * (D + R / η) * C * Real.exp 1) * (X * L ^ 2) := by
    calc _ = 2 * (L⁻¹ + η) * (D * L + R / η) * C * Real.exp 1 / x ^ 2 := by field_simp
         _ ≤ 2 * (L⁻¹ + η) * (D * L + R / η) * C * Real.exp 1 := div_le_self (by positivity) one
         _ ≤ 2 * 2 * ((D + R / η) * L) * C * Real.exp 1 := by gcongr; linarith
         _ ≤ _ := by
           have lX : L ≤ X * L ^ 2 := calc
             L ≤ L ^ 2 := by nlinarith [mul_nonneg (show 0 ≤ L by linarith) (sub_nonneg.2 lp)]
             _ ≤ X * L ^ 2 := le_mul_of_one_le_left (sq_nonneg _) Xp
           nlinarith only [mul_le_mul_of_nonneg_left lX (show 0 ≤ 4 * (D + R / η) * C * Real.exp 1 by positivity)]
  have sum := add_le_add (add_le_add tail left) horizontal
  apply (mul_le_mul_of_nonneg_left sum (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans
  have f : 1 / (2 * Real.pi) ≤ 1 := (div_le_one (by positivity)).2 (by linarith [Real.pi_gt_three])
  calc _ ≤ 1 * _ := mul_le_mul_of_nonneg_right f (by positivity)
       _ = _ := by dsimp [X, L]; ring

/-- A simple pole with residue r and logarithmic growth on the fixed rectangle
suffice to control the actual sharp partial sums. -/
theorem count_of_fixed_strip {a : ℕ → ℂ} {B D : ℝ} {G : ℂ → ℂ} {r : ℂ}
    {σ τ : ℝ} (hslo : 1 / 2 ≤ σ) (hshi : σ < 1) (hστ : σ < τ)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (coeff : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ B * Real.log (n + 1))
    (reg : ∀ s : ℂ, σ ≤ s.re → DifferentiableAt ℂ G s)
    (series : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + r / (s - 1))
    (bound : ∀ᶠ x : ℝ in atTop, ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 → |s.im| ≤ x ^ 2 →
        ‖G s‖ ≤ D * Real.log x) :
    ∃ K : ℝ, ∀ᶠ x : ℝ in atTop, ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n - r * x‖ ≤ K * x ^ τ := by
  obtain ⟨ν, hνd, hν0, hνs, hνm,-⟩ := exists_smooth_symmetric_bump one_lt_two
  have hνs' : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2 := fun y hy ↦ by
    simpa only [one_div] using hνs hy.1
  have hν1 : ContDiffOn ℝ 1 ν (Ioi 0) := (hνd.of_le (by exact_mod_cast le_top)).contDiffOn
  obtain ⟨C, hC⟩ := exists_norm_mellin_smoothCutoff_le (k := 1) hν1 hνs' (σ₁ := 1 / 2) (σ₂ := 2) (by norm_num)
  simp only [pow_one] at hC
  let C' := |C|
  let η := 1 - σ
  have he : 0 < η := sub_pos.2 hshi
  have he₂ : η ≤ 1/2 := by dsimp [η]; linarith
  have se : 1 - η = σ := by dsimp [η]; ring
  let H := 16 * B * C' * Real.exp 1 + 12 * (D + ‖r‖ / η) * C' + 4 * (D + ‖r‖ / η) * C' * Real.exp 1
  let K := 9 * B + H + 2 * ‖r‖ * Real.log 2
  have l2 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ x ^ (τ - σ) := by
    have h := (isLittleO_log_rpow_rpow_atTop 2 (sub_pos.2 hστ)).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hh hx
    simpa [Real.rpow_two, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using hh
  refine ⟨K,?_⟩
  filter_upwards [bound, l2, eventually_ge_atTop (4 : ℝ)] with x strip logs hx
  have xp : 0 < x := by linarith
  have x1 : 1 ≤ x := by linarith
  have lx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le xp).2 (by linarith [Real.exp_one_lt_three])
  have hε := inv_pos.mpr xp
  have hε1 := inv_le_one_of_one_le₀ x1
  have height : η ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
  have rc : DifferentiableOn ℂ G (Icc (1 - η) (1 + (Real.log x)⁻¹) ×ℂ Icc (-(x ^ 2)) (x ^ 2)) :=
    fun z hz ↦ (reg z (se ▸ hz.1.1)).differentiableWithinAt

  -- Shift the smoothed sum to the fixed inner edge, with height x² and width 1/x.
  have big := TauCeti.LSeries.norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log (G := G) (r := r)
    coeff hν1 hνs' hε (by linarith : 2 ≤ x) he (by linarith) height rc.continuousOn
    (rc.mono fun z hz ↦ ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩)
    (fun s hs ↦ strip s (se ▸ hs.1.1) (by linarith only [hs.1.2, inv_le_one_of_one_le₀ lx])
      (abs_le.2 hs.2))
    (fun s hs ↦ series s (by linarith [inv_pos.2 (zero_lt_one.trans_le lx)]))
    (C := C') (fun s lo hi ↦ (hC x⁻¹ hε hε1 s (by linarith only [lo,se,hslo]) (by linarith [inv_le_one_of_one_le₀ lx])).trans
      (div_le_div_of_nonneg_right (le_abs_self C) (by positivity)))

  -- Restore the sharp cutoff and the residue's unsmoothed main term.
  have cnt := norm_sum_sub_tsum_mul_smoothCutoff_le coeff (fun y _ ↦ hν0 y) hνs' hνm hε hε1
    (X := x) (by linarith)
  have main := norm_mellin_smoothCutoff_one_sub_one_le (fun y _ ↦ hν0 y) hνs' hνm hε hε1
  set m := mellin (fun y : ℝ ↦ (smoothCutoff ν x⁻¹ y : ℂ)) 1
  let A := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n
  let S := ∑' n, a n * smoothCutoff ν x⁻¹ (n / x)
  let X := x ^ σ * Real.log x ^ 2
  have X1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow x1 (by linarith : 0 ≤ σ)) (one_le_pow₀ lx)
  have logX : Real.log x ≤ X := by
    have : Real.log x ≤ Real.log x ^ 2 := by nlinarith [mul_nonneg (zero_lt_one.trans_le lx).le (sub_nonneg.2 lx)]
    exact this.trans (le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_rpow x1 (by linarith : 0 ≤ σ)))
  have cs : ‖A - S‖ ≤ 9 * B * X := calc
    _ ≤ 3 * B * (2 * x⁻¹ * x + 1) * Real.log x := cnt
    _ = 9 * B * Real.log x := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left logX (by positivity)
  have ms : ‖r * (m - 1) * x‖ ≤ (2 * ‖r‖ * Real.log 2) * X := calc
    _ ≤ ‖r‖ * (2 * Real.log 2 * x⁻¹) * x := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos xp]
      gcongr
    _ = 2 * ‖r‖ * Real.log 2 := by field_simp
    _ ≤ _ := le_mul_of_one_le_right (by positivity) X1
  have mid : ‖S - r * m * x‖ ≤ H * X :=
    by
      have h := big.trans (rectangle_cost he he₂ hx lx hB (abs_nonneg _) hD (norm_nonneg _))
      simpa only [se, H, X] using h
  have pos : 0 ≤ K := by dsimp [K, H, C']; positivity
  have local_bound : ‖A - r * x‖ ≤ K * X := by
    rw [show A - r * x = (A - S) + (S - r * m * x) + r * (m - 1) * x by ring]
    calc _ ≤ ‖A - S‖ + ‖S - r * m * x‖ + ‖r * (m - 1) * x‖ := norm_add₃_le
         _ ≤ _ := (add_le_add (add_le_add cs mid) ms).trans_eq (by dsimp [K]; ring)
  apply local_bound.trans (mul_le_mul_of_nonneg_left _ pos)
  calc X ≤ x ^ σ * x ^ (τ - σ) := mul_le_mul_of_nonneg_left logs (by positivity)
       _ = _ := by rw [← Real.rpow_add xp]; congr 1; ring


/-- A simple pole with residue r and logarithmic growth on the fixed rectangle
suffice to control the actual sharp partial sums. -/
theorem count_of_rectangle {a : ℕ → ℂ} {B D : ℝ} {G : ℂ → ℂ} {r : ℂ}
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (coeff : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ B * Real.log (n + 1))
    (reg : ∀ s : ℂ, 3 / 5 < s.re → DifferentiableAt ℂ G s)
    (series : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + r / (s - 1))
    (bound : ∀ᶠ x : ℝ in atTop, ∀ s : ℂ, 2 / 3 ≤ s.re → s.re ≤ 2 → |s.im| ≤ x ^ 2 →
        ‖G s‖ ≤ D * Real.log x) :
    ∃ K : ℝ, ∀ᶠ x : ℝ in atTop, ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n - r * x‖ ≤ K * x ^ (7 / 10 : ℝ) := by
  exact count_of_fixed_strip (σ := 2/3) (by norm_num) (by norm_num) (by norm_num)
    hB hD coeff (fun s hs ↦ reg s (by linarith)) series bound

end New.PrimeCutoff
