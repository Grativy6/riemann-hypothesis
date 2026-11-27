module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# A full turn at each doubling

Integer points in log₂ x always see the same phase. The quarter-turns show
that a bound on this geometric grid alone does not control a general signal.
-/

@[expose] public section

open Real Nat Filter Topology
namespace New.PrimeCutoff.DyadicBoundary

noncomputable def wave (x : ℝ) : ℝ := x ^ (-(1 / 4) : ℝ) * Real.sin (2 * π * Real.logb 2 x)

lemma at_doubling (n : ℕ) : wave ((2 : ℝ) ^ n) = 0 := by
  rw [wave, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  have z : Real.sin ((n : ℝ) * (2 * π)) = 0 := by simpa using Real.sin_add_nat_mul_two_pi 0 n
  rw [mul_one, mul_comm (2 * π), z, mul_zero]

lemma at_quarter (n : ℕ) : wave ((2 : ℝ) ^ ((n : ℝ) + 1 / 4)) = ((2 : ℝ) ^ ((n : ℝ) + 1 / 4)) ^ (-(1 / 4) : ℝ) := by
  rw [wave, Real.logb_rpow (by norm_num) (by norm_num)]
  rw [show 2 * π * ((n : ℝ) + 1 / 4) = π / 2 + (n : ℝ) * (2 * π) by ring, Real.sin_add_nat_mul_two_pi,
    Real.sin_pi_div_two, mul_one]

/-- Even a zero reading between x/2 and x at every large cutoff allows the
signal to return to x^(-1/4). -/
theorem nearby_dyadic_zero {x : ℝ} (hx : 1 ≤ x) :
    ∃ y : ℝ, x / 2 ≤ y ∧ y ≤ x ∧ wave y = 0 := by
  let n := ⌊Real.logb 2 x⌋₊
  have xp := zero_lt_one.trans_le hx
  have logp : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  have left : (n : ℝ) ≤ Real.logb 2 x := Nat.floor_le logp
  have right : Real.logb 2 x < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have root := Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) xp
  have bot := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) left
  have top := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) right.le
  rw [root, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, Real.rpow_one] at top
  rw [root, Real.rpow_natCast] at bot
  exact ⟨_, by linarith, bot, at_doubling n⟩

/-- No upper decay bound with exponent greater than 1/4 holds throughout the
tail, for any finite constant. -/
theorem no_faster_decay {γ C : ℝ} (hg : 1 / 4 < γ) :
    ¬ ∀ᶠ x : ℝ in atTop, wave x ≤ C * x ^ (-γ) := by
  intro bound
  let y := fun n : ℕ ↦ (2 : ℝ) ^ ((n : ℝ) + 1 / 4)
  have grow : Tendsto y atTop atTop := by
    have small : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    apply tendsto_atTop_mono _ small
    intro n
    dsimp [y]
    rw [← Real.rpow_natCast (2 : ℝ) n]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have big := ((tendsto_rpow_atTop (sub_pos.2 hg)).comp grow).eventually_gt_atTop C
  obtain ⟨n, h, large⟩ := ((grow.eventually bound).and big).exists
  have yp : 0 < y n := Real.rpow_pos_of_pos (by norm_num) _
  change wave ((2 : ℝ) ^ ((n : ℝ) + 1 / 4)) ≤ C * (y n) ^ (-γ) at h
  rw [at_quarter] at h
  have multiplied := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg yp.le γ)
  change (y n) ^ (-(1 / 4) : ℝ) * (y n) ^ γ ≤ C * (y n) ^ (-γ) * (y n) ^ γ at multiplied
  rw [← Real.rpow_add yp, mul_assoc,← Real.rpow_add yp, neg_add_cancel, Real.rpow_zero, mul_one] at multiplied
  rw [show -(1 / 4 : ℝ) + γ = γ - 1 / 4 by ring] at multiplied
  exact large.not_ge multiplied

end New.PrimeCutoff.DyadicBoundary
