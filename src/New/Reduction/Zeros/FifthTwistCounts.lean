module

public import New.Reduction.Zeros.FifthCountCriterion
public import New.Reduction.Zeros.FifthStrip
public import New.Reduction.Zeros.WeightedCountRectangle
import Mathlib.Tactic

/-!
# Counting the actual weighted prime powers

Character orthogonality gives one main term x/φ(q). The remaining analytic
function is the difference of the twisted and untwisted logarithmic derivatives,
with the constant required by the project's normalization restored.
-/

@[expose] public section

open Complex Real Nat Filter Finset Set
namespace New.PrimeCutoff

/-- Zero-freeness for the two finite families belonging to this d gives a
two-sided bound for its own sharp, unsmoothed count. -/
theorem count_of_clear_families {d q : ℕ} [Fact d.Prime] [NeZero q] (hd : d ≠ 2) (cop : q.Coprime d)
    (base : ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), 3 / 5 < s.re → entireL χ s ≠ 0)
    (twists : ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), 3 / 5 < s.re → entireL (quadTwist χ d) s ≠ 0) :
    ∃ K : ℝ, ∀ᶠ x : ℝ in atTop, |countError d q x| ≤ K * x ^ (7 / 10 : ℝ) := by
  let r : ℂ := (q.totient : ℂ)⁻¹
  let G := fun s : ℂ ↦ logDerivMean d q s + r
  let a := fun n : ℕ ↦ (lambdaKResidueClass d q n : ℂ)
  have φpos : 0 < q.totient := Nat.totient_pos.2 (NeZero.pos q)
  have φne : (q.totient : ℂ) ≠ 0 := by exact_mod_cast φpos.ne'
  have nr : ‖r‖ ≤ 1 := by
    dsimp [r]
    rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast φpos)
  have series (s : ℂ) (hs : 1 < s.re) : LSeries a s = G s + r / (s - 1) := by
    have s1 : s - 1 ≠ 0 := sub_ne_zero.2 (ne_of_apply_ne Complex.re (by simpa using hs.ne'))
    dsimp [a, G, r]
    rw [LSeries_lambdaKResidueClass_eq_add_logDerivMean hd cop hs]
    field_simp
    ring
  have analytic (s : ℂ) (hs : 3 / 5 < s.re) : DifferentiableAt ℂ G s :=
    (analyticAt_logDerivMean (base · s hs) (twists · s hs)).differentiableAt.add_const _
  have rect : ∀ᶠ x : ℝ in atTop, ∀ s : ℂ, 2 / 3 ≤ s.re → s.re ≤ 2 → |s.im| ≤ x ^ 2 →
      ‖G s‖ ≤ 26002 * Real.log x := by
    filter_upwards [logDeriv_on_rectangle (N := q), logDeriv_on_rectangle (N := q * d),
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with x B T L
    intro s sl sr si
    have h := norm_logDerivMean_le (fun χ ↦ B χ (base χ) s sl sr si)
      (fun χ ↦ T (quadTwist χ d) (twists χ) s sl sr si)
    exact (norm_add_le _ _).trans (by linarith only [h, nr, L])
  exact weighted_count_of_rectangle (σ := 2/3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun s hs ↦ analytic s (by linarith)) series rect

/-- A sharp count bound gives a shortfall bound on every subinterval of one fifth
cell. Both endpoints use the same constant, chosen after d is fixed. -/
theorem local_fifths_of_count {d q : ℕ} [Fact d.Prime] {C : ℝ}
    (bound : ∀ᶠ x : ℝ in atTop, |countError d q x| ≤ C * x ^ (7 / 10 : ℝ)) :
    fifthCellCountBound d q := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 bound
  intro ε εp
  have tends : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 5) atTop atTop :=
    (tendsto_pow_atTop (by decide : 5 ≠ 0)).comp tendsto_natCast_atTop_atTop
  refine ⟨64 * |C|,?_⟩
  filter_upwards [tends.eventually_ge_atTop T, eventually_ge_atTop (1 : ℕ)] with n nT hn
  intro u v lo uv hi
  let y := (n : ℝ) ^ 5
  have np : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have yp : 1 ≤ y := one_le_pow₀ np
  have cap : ((n : ℝ) + 1) ^ 5 ≤ 32 * y := calc
    _ ≤ (2 * (n : ℝ)) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
    _ = _ := by dsimp [y]; ring
  have weight (t : ℝ) (yt : y ≤ t) (tz : t ≤ 32 * y) :
      |countError d q t| ≤ 32 * |C| * y ^ (7 / 10 + ε) := by
    calc _ ≤ C * t ^ (7 / 10 : ℝ) := hT _ (nT.trans yt)
         _ ≤ |C| * ((32 * y) ^ (7 / 10 : ℝ)) := mul_le_mul (le_abs_self _)
              (Real.rpow_le_rpow (zero_le_one.trans (yp.trans yt)) tz (by norm_num))
              (by positivity [zero_le_one.trans (yp.trans yt)]) (abs_nonneg _)
         _ = |C| * ((32 : ℝ) ^ (7 / 10 : ℝ) * y ^ (7 / 10 : ℝ)) := by rw [Real.mul_rpow (by norm_num) (zero_le_one.trans yp)]
         _ ≤ |C| * (32 * y ^ (7 / 10 + ε)) := by
              have a : (32 : ℝ) ^ (7 / 10 : ℝ) ≤ 32 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
              gcongr; linarith
         _ = _ := by ring
  rw [← countError_drop_eq uv]
  have u' := weight u lo (uv.trans (hi.trans cap))
  have v' := weight v (lo.trans uv) (hi.trans cap)
  linarith only [u', v', le_abs_self (countError d q u), neg_le_abs (countError d q v)]

end New.PrimeCutoff
