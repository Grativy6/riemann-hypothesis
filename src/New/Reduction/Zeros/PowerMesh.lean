module

public import New.Reduction.Zeros.SampleMesh
import New.Reduction.Zeros.PowerGridCriterion
import Mathlib.Tactic

/-!
# Every fixed positive power gives a power saving in the distance

For k=j+1 and u≥1, the gap to the next power is at most 2^k u^j.
The constant and the exponent may be chosen separately for each auxiliary prime.
-/

@[expose] public section

open Real Nat Filter
namespace New.PrimeCutoff

lemma power_gap (j : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    (u + 1) ^ (j + 1) - u ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) * u ^ j := by
  have up : 0 ≤ u := zero_le_one.trans hu
  induction j with
  | zero => simp
  | succ j ih =>
    have upper : (u + 1) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 1) * u ^ (j + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    calc (u + 1) ^ (j + 1 + 1) - u ^ (j + 1 + 1) = (u + 1) ^ (j + 1) + u * ((u + 1) ^ (j + 1) - u ^ (j + 1)) := by ring
         _ ≤ (2 : ℝ) ^ (j + 1) * u ^ (j + 1) + u * ((2 : ℝ) ^ (j + 1) * u ^ j) :=
           add_le_add upper (mul_le_mul_of_nonneg_left ih up)
         _ = _ := by ring

/-- Eventual samples at nᵏ give a good reading within O(x^(1−1/k)) of every
large real cutoff. The lower power is one such reading. -/
theorem nearby_of_powers {d q k : ℕ} [Fact d.Prime] [NeZero q] {β A : ℝ} (hk : 0 < k)
    (samples : ∀ᶠ n : ℕ in atTop, primeRemainder d q ((n : ℝ) ^ k) ≤ A * ((n : ℝ) ^ k) ^ (β - 1)) :
    nearbyUpper d q β (1 / (k : ℝ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  let k := j + 1
  have kp : 0 < (k : ℝ) := by exact_mod_cast hk
  have κ : 0 ≤ 1 - 1 / (k : ℝ) := by
    have k₁ : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    linarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) k₁]
  have grows : Tendsto (fun x : ℝ ↦ ⌊x ^ (1 / (k : ℝ))⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by positivity))
  refine ⟨(2 : ℝ) ^ k, A,?_⟩
  filter_upwards [grows.eventually samples, eventually_ge_atTop (1 : ℝ)] with x at_n hx
  let n := ⌊x ^ (1 / (k : ℝ))⌋₊
  obtain ⟨hn, lo, hi⟩ := enclose_by_powers hk hx
  change 1 ≤ n at hn
  change (n : ℝ) ^ k ≤ x at lo
  change x ≤ ((n : ℝ) + 1) ^ k at hi
  have np : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have exp : (k : ℝ) * (1 - 1 / (k : ℝ)) = (j : ℝ) := by dsimp [k]; push_cast; field_simp; ring
  have lift : (n : ℝ) ^ j ≤ x ^ (1 - 1 / (k : ℝ)) := calc
    _ = ((n : ℝ) ^ k) ^ (1 - 1 / (k : ℝ)) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n), exp, Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg n) _) lo κ
  refine ⟨(n : ℝ) ^ k,?_, at_n⟩
  rw [abs_of_nonneg (sub_nonneg.2 lo)]
  exact ((sub_le_sub_right hi _).trans (power_gap j np)).trans
    (mul_le_mul_of_nonneg_left lift (by positivity))

end New.PrimeCutoff
