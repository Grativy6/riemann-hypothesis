module

public import New.Reduction.Zeros.TentCountDiscrepancy
import Mathlib.Tactic

/-!
# Moving from a good reading on either side

Every sufficiently large cutoff has one good reading within a power-saving
distance. Compare the two cutoffs by integrating the same sharp counting
error. The reading can lie on either side and can depend on the cutoff.
-/

@[expose] public section

open Real Finset Set Filter MeasureTheory
namespace New.PrimeCutoff

/-- Upper readings with exponent β−1 within distance L x^(1−δ) of every large x.
The sample may lie on either side of x. -/
def nearbyUpper (d q : ℕ) [Fact d.Prime] [NeZero q] (β δ : ℝ) : Prop :=
  ∃ L A : ℝ, ∀ᶠ x : ℝ in atTop, ∃ y : ℝ,
    |x - y| ≤ L * x ^ (1 - δ) ∧ primeRemainder d q y ≤ A * y ^ (β - 1)

private lemma count_variation {d q : ℕ} [Fact d.Prime] [NeZero q] {b B T x u v : ℝ}
    (counting : ∀ t ≥ T, |countError d q t| ≤ B * t ^ b)
    (b₀ : 0 ≤ b) (b₁ : b ≤ 1) (hx : 2 ≤ x) (hT : T ≤ x / 2)
    (lo : x / 2 ≤ u) (uv : u ≤ v) (hi : v ≤ 2 * x) :
    |primeRemainder d q v - primeRemainder d q u| ≤
      (8 * |B| * x ^ b / x ^ 2) * |v - u| := by
  have xp : 0 < x := by linarith
  have est (t : ℝ) (ht : t ∈ uIoc u v) :
      ‖countError d q t / t ^ 2‖ ≤ 8 * |B| * x ^ b / x ^ 2 := by
    rw [uIoc_of_le uv] at ht
    have tl : x / 2 ≤ t := lo.trans ht.1.le
    have tp : 0 < t := by linarith
    have th := ht.2.trans hi
    have p : t ^ b ≤ 2 * x ^ b := calc
      _ ≤ (2 * x) ^ b := Real.rpow_le_rpow tp.le th b₀
      _ = (2 : ℝ) ^ b * x ^ b := Real.mul_rpow (by norm_num) xp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) b₁) (by positivity)
    have c : |countError d q t| ≤ 2 * |B| * x ^ b := calc
      _ ≤ B * t ^ b := counting t (hT.trans tl)
      _ ≤ |B| * (2 * x ^ b) := mul_le_mul (le_abs_self _) p (by positivity) (abs_nonneg _)
      _ = _ := by ring
    have sq : (x / 2) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) tl 2
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
    calc _ ≤ 2 * |B| * x ^ b / (x / 2) ^ 2 := div_le_div₀ (by positivity) c (by positivity) sq
         _ = _ := by ring
  rw [remainder_change (by linarith) uv]
  simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const est

/-- A sharp count bound of exponent b transports a nearby upper reading to a
real-cutoff bound of exponent τ−1 whenever τ ≥ β and τ ≥ b−δ. -/
theorem real_of_nearby_count {d q : ℕ} [Fact d.Prime] [NeZero q] {β δ b τ B : ℝ}
    (δp : 0 < δ) (b₀ : 0 ≤ b) (b₁ : b ≤ 1) (β₀ : 0 ≤ β) (β₁ : β ≤ 1)
    (βτ : β ≤ τ) (gain : b - δ ≤ τ) (samples : nearbyUpper d q β δ)
    (counting : ∀ᶠ t : ℝ in atTop, |countError d q t| ≤ B * t ^ b) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ C * x ^ (τ - 1) := by
  obtain ⟨L, A, near⟩ := samples
  obtain ⟨T, hT⟩ := eventually_atTop.1 counting
  refine ⟨2 * |A| + 8 * |B| * |L|,?_⟩
  filter_upwards [near, (tendsto_rpow_atTop δp).eventually_ge_atTop (2 * |L|),
    eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (2 * T)] with x hy huge hx far
  obtain ⟨y, gap, reading⟩ := hy
  have xp : 0 < x := by linarith
  have x1 : 1 ≤ x := by linarith
  have distance : |x - y| ≤ |L| * x ^ (1 - δ) :=
    gap.trans (mul_le_mul_of_nonneg_right (le_abs_self L) (by positivity))
  have half : |x - y| ≤ x / 2 := by
    rw [Real.rpow_sub xp, Real.rpow_one] at distance
    apply distance.trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos xp _)).2
    nlinarith only [mul_le_mul_of_nonneg_left huge xp.le]
  have xy := abs_le.1 half
  have yl : x / 2 ≤ y := by linarith [xy.2]
  have yh : y ≤ 2 * x := by linarith [xy.1]
  have yp : 0 < y := by linarith
  have move : |primeRemainder d q x - primeRemainder d q y| ≤
      8 * |B| * x ^ b / x ^ 2 * |x - y| := by
    obtain h | h := le_total y x
    · exact count_variation hT b₀ b₁ hx (by linarith) yl h (by linarith)
    · rw [abs_sub_comm (primeRemainder d q x), abs_sub_comm x y]
      exact count_variation hT b₀ b₁ hx (by linarith) (by linarith) h yh
  have samplePower : y ^ (β - 1) ≤ 2 * x ^ (τ - 1) := by
    calc _ ≤ (x / 2) ^ (β - 1) := Real.rpow_le_rpow_of_nonpos (by positivity) yl (by linarith)
         _ = x ^ (β - 1) / (2 : ℝ) ^ (β - 1) := Real.div_rpow xp.le (by norm_num) _
         _ ≤ x ^ (β - 1) / (2 : ℝ) ^ (-1 : ℝ) := div_le_div_of_nonneg_left (by positivity) (by positivity)
              (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
         _ ≤ _ := by
           rw [Real.rpow_neg_one, div_inv_eq_mul, mul_comm]
           exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le x1 (by linarith)) (by norm_num)
  have ry : primeRemainder d q y ≤ (2 * |A|) * x ^ (τ - 1) := calc
    _ ≤ |A| * (2 * x ^ (τ - 1)) := reading.trans (mul_le_mul (le_abs_self A) samplePower (by positivity) (abs_nonneg _))
    _ = _ := by ring
  have diff : |primeRemainder d q x - primeRemainder d q y| ≤ (8 * |B| * |L|) * x ^ (τ - 1) := by
    calc _ ≤ 8 * |B| * x ^ b / x ^ 2 * (|L| * x ^ (1 - δ)) := move.trans (mul_le_mul_of_nonneg_left distance (by positivity))
         _ = (8 * |B| * |L|) * x ^ (b - δ - 1) := by
           rw [show b - δ - 1 = b + (1 - δ) - 2 by ring, Real.rpow_sub xp (b + (1 - δ)) 2, Real.rpow_add xp b (1 - δ), Real.rpow_two]
           ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le x1 (by linarith)) (by positivity)
  rw [add_mul]
  linarith only [ry, diff, le_abs_self (primeRemainder d q x - primeRemainder d q y)]

end New.PrimeCutoff
