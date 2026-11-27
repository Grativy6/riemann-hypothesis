module

public import New.Reduction.Zeros.MatchedOrders
public import New.Reduction.Zeros.FixedStripCount
import TauCeti.Analysis.Complex.LocalLogDeriv
import Mathlib.Tactic

/-!
# Counting when the products share zeros

Landau's local logarithmic-derivative estimate subtracts the polar sum in one
closed disk. Matching the two divisors cancels that exact sum. Continuity then
puts back the value at any shared zero before the contour is moved.
-/

@[expose] public section

open Complex Real Nat Filter Finset Set Metric Topology MeromorphicOn
namespace New.PrimeCutoff

private lemma family_sphere {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N] :
    ∀ᶠ x : ℝ in atTop, ∀ c : ℂ, c.re = 2 → ‖c‖ ≤ 2 + x ^ 2 →
      ∀ κ : ι → DirichletCharacter ℂ N, ∀ w ∈ sphere c (3 / 2),
        ‖familyProduct κ w‖ ≤ (x ^ 5) ^ (Fintype.card ι) * ‖familyProduct κ c‖ := by
  let b := Real.exp (-(riemannZeta 2).re)
  have bp : 0 < b := Real.exp_pos _
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (72 * (N : ℝ) / b)] with x hx hN
  intro c cr cn κ w hw
  have dist : ‖w - c‖ = 3 / 2 := mem_sphere_iff_norm.1 hw
  have wr : 1 / 2 ≤ w.re := by
    have lower := neg_le_of_abs_le (abs_re_le_norm (w - c))
    rw [sub_re, cr, dist] at lower
    linarith
  have wn : ‖w‖ + 1 ≤ 3 * x ^ 2 := by nlinarith [norm_le_norm_sub_add w c, sq_nonneg (x - 2)]
  have one (i : ι) : ‖entireL (κ i) w‖ ≤ x ^ 5 * ‖entireL (κ i) c‖ := by
    calc _ ≤ 8 * N * (‖w‖ + 1) ^ 2 := entire_growth (κ i) wr
         _ ≤ 8 * N * (3 * x ^ 2) ^ 2 := by gcongr
         _ = (72 * N) * x ^ 4 := by ring
         _ ≤ (x * b) * x ^ 4 := mul_le_mul_of_nonneg_right ((div_le_iff₀ bp).1 hN) (by positivity)
         _ = x ^ 5 * b := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (entire_center_lower (κ i) cr) (by positivity)
  calc ‖familyProduct κ w‖ = ∏ i, ‖entireL (κ i) w‖ := by simp [familyProduct, Finset.prod_apply, norm_prod]
       _ ≤ ∏ i, x ^ 5 * ‖entireL (κ i) c‖ := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ one i)
       _ = _ := by simp [familyProduct, Finset.prod_apply, Finset.prod_mul_distrib, norm_prod]

private noncomputable def diskCost (r D : ℝ) :=
  4 * (r + D) / (r - D) ^ 2 + r / (((3 / 2 : ℝ) ^ 2 - r * D) * Real.log ((3 / 2) / r))

private lemma diskCost_pos {r D : ℝ} (d₀ : 0 ≤ D) (dr : D < r) (rR : r < 3 / 2) :
    0 < diskCost r D := by
  have rp := d₀.trans_lt dr
  have denom : 0 < (3 / 2 : ℝ) ^ 2 - r * D := by nlinarith [mul_nonneg rp.le (sub_nonneg.2 dr.le), sq_lt_sq' (by linarith : -(3 / 2 : ℝ) < r) rR]
  have lg := Real.log_pos ((one_lt_div rp).2 rR)
  unfold diskCost
  positivity [sub_pos.2 dr]

private lemma diskCost_mono {r D u : ℝ} (u₀ : 0 ≤ u) (ud : u ≤ D) (dr : D < r) (rR : r < 3 / 2) :
    diskCost r u ≤ diskCost r D := by
  have dn : 0 ≤ D := u₀.trans ud
  have rp := dn.trans_lt dr
  have lg := Real.log_pos ((one_lt_div rp).2 rR)
  have dpos : 0 < (3 / 2 : ℝ) ^ 2 - r * D := by
    nlinarith [mul_nonneg rp.le (sub_nonneg.2 dr.le), sq_lt_sq' (by linarith : -(3 / 2 : ℝ) < r) rR]
  unfold diskCost
  apply _root_.add_le_add
  · exact div_le_div₀ (by positivity) (by linarith) (sq_pos_of_pos (sub_pos.2 dr))
      (pow_le_pow_left₀ (sub_nonneg.2 dr.le) (by linarith) 2)
  · exact div_le_div_of_nonneg_left rp.le (mul_pos dpos lg)
      (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left ud rp.le]) lg.le)

private lemma mean_eq_product_difference {d q : ℕ} [Fact d.Prime] [NeZero q] {w : ℂ}
    (hb : ∀ χ : DirichletCharacter ℂ q, entireL χ w ≠ 0)
    (ht : ∀ χ : DirichletCharacter ℂ q, entireL (quadTwist χ d) w ≠ 0) :
    regularMean d q w =
      (logDeriv (familyProduct (fun χ : DirichletCharacter ℂ q ↦ quadTwist χ d)) w -
       logDeriv (familyProduct (id : DirichletCharacter ℂ q → _)) w) / q.totient := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
  rw [regularMean, TauCeti.toMeromorphicNFOn_apply_of_analyticAt (meromorphic_mean d q)
    (analyticAt_logDerivMean hb ht), familyProduct_logDeriv ht, familyProduct_logDeriv (κ:= id) hb]
  simp only [logDerivMean, Finset.sum_sub_distrib, id_eq]
  field_simp
  ring

/-- The logarithmic derivative of the ratio is O(log x) right of any smaller
fixed strip, even when both products vanish there. -/
theorem rectangle_of_matched {d q : ℕ} [Fact d.Prime] [NeZero q] {θ σ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hσ : θ < σ) (s₁ : σ < 1) (ord : matchedOrders d q θ) :
    ∃ D ≥ (0 : ℝ), ∀ᶠ x : ℝ in atTop, ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 → |s.im| ≤ x ^ 2 →
      ‖regularMean d q s‖ ≤ D * Real.log x := by
  let r := 2 - (θ + σ) / 2
  let v := (2 - σ + r) / 2
  have range : 2 - σ < v ∧ v < r ∧ r < 3 / 2 := by
    dsimp [v, r]
    exact ⟨by linarith, by linarith, by linarith⟩
  have vp : 0 ≤ v := by linarith only [range.1, s₁]
  have cost := diskCost_pos vp range.2.1 range.2.2
  let I := DirichletCharacter ℂ q
  let base : I → DirichletCharacter ℂ q := id
  let twists : I → DirichletCharacter ℂ (q * d) := fun χ ↦ quadTwist χ d
  let K := diskCost r v
  refine ⟨10 * K * Fintype.card I, by dsimp only [K]; positivity, ?_⟩
  filter_upwards [family_sphere (ι:= I) (N := q), family_sphere (ι:= I) (N := q * d),
    eventually_ge_atTop (2 : ℝ)] with x sb st hx
  intro s hleft hright height
  let c : ℂ := 2 + (s.im : ℂ) * Complex.I
  have cr : c.re = 2 := by simp [c]
  have cn : ‖c‖ ≤ 2 + x ^ 2 := by
    calc _ ≤ ‖(2 : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
         _ ≤ _ := by simpa using height
  have sc : ‖s - c‖ ≤ 2 - σ := by
    have e : s - c = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.2 hright)]
    linarith
  let U := closedBall c r
  have divs : divisor (familyProduct twists) U = divisor (familyProduct base) U := by
    apply family_divisors_eq ord
    intro z hz
    have nr : ‖z - c‖ ≤ r := mem_closedBall_iff_norm.1 hz
    have h := neg_le_of_abs_le (abs_re_le_norm (z - c))
    rw [sub_re, cr] at h
    dsimp [r] at nr
    linarith
  let M := (x ^ 5) ^ (Fintype.card I)
  have logM : Real.log M = (Fintype.card I : ℝ) * 5 * Real.log x := by dsimp [M]; rw [Real.log_pow, Real.log_pow]; push_cast; ring
  have lg : 0 ≤ Real.log M := Real.log_nonneg (one_le_pow₀ (one_le_pow₀ (by linarith : 1 ≤ x) (n := 5)) (n := Fintype.card I))
  have near : ball c v ∈ 𝓝 s := isOpen_ball.mem_nhds (mem_ball_iff_norm.2 (sc.trans_lt range.1))
  have hnorm : Tendsto (fun w ↦ ‖regularMean d q w‖) (𝓝[≠] s) (𝓝 ‖regularMean d q s‖) := (regularMean_analytic ord (hσ.trans_le hleft)).continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hnorm
  filter_upwards [nhdsWithin_le_nhds near, family_punctured_nonzero base s, family_punctured_nonzero twists s] with w hw hb ht
  have nv := (mem_ball_iff_norm.1 hw).le
  have bound {N : ℕ} [NeZero N] (κ : I → DirichletCharacter ℂ N)
      (sphereBound : ∀ z ∈ sphere c (3 / 2), ‖familyProduct κ z‖ ≤ M * ‖familyProduct κ c‖)
      (nz : ∀ i, entireL (κ i) w ≠ 0) :
      ‖logDeriv (familyProduct κ) w - ∑ᶠ z, (divisor (familyProduct κ) U z : ℂ) / (w - z)‖ ≤ K * Real.log M := by
    have outer : AnalyticOnNhd ℂ (familyProduct κ) (closedBall c (3 / 2)) := fun z _ ↦ familyProduct_analytic κ z
    have nonzero : familyProduct κ w ≠ 0 := by
      simpa only [familyProduct, Finset.prod_apply, Finset.prod_ne_zero_iff] using (fun i (_ : i ∈ (univ:Finset I)) ↦ nz i)
    exact (outer.norm_logDeriv_sub_finsum_divisor_le range.2.2 sphereBound (nv.trans_lt range.2.1) nonzero).trans
      (mul_le_mul_of_nonneg_right (diskCost_mono (norm_nonneg _) nv range.2.1 range.2.2) lg)
  have e₀ := bound base (sb c cr cn base) hb
  have e₁ := bound twists (st c cr cn twists) ht
  rw [divs] at e₁
  let P := ∑ᶠ z, (divisor (familyProduct base) U z : ℂ) / (w - z)
  have diff := (norm_sub_le (logDeriv (familyProduct twists) w - P) (logDeriv (familyProduct base) w - P)).trans (add_le_add e₁ e₀)
  simp only [sub_sub_sub_cancel_right] at diff
  rw [mean_eq_product_difference hb ht, norm_div, Complex.norm_natCast]
  calc _ ≤ ‖logDeriv (familyProduct twists) w - logDeriv (familyProduct base) w‖ :=
          div_le_self (norm_nonneg _) (by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q))
       _ ≤ _ := diff.trans_eq (by rw [logM]; ring)

end New.PrimeCutoff
