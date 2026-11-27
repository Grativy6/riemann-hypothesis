module

public import New.Reduction.Zeros.FifthCountCriterion
import Mathlib.Tactic

/-!
# What fifth-power samples give before using the zeros

The quadratic interpolation cost between n⁵ and (n+1)⁵ is O(x^(-2/5)).
This first estimate uses only the sign of the weights and the two sampled values.
-/

@[expose] public section

open Nat Real Filter
namespace New.PrimeCutoff

lemma fifth_span {u x : ℝ} (hu : 1 ≤ u) (left : u ^ 5 ≤ x) :
    (u + 1) ^ 5 - u ^ 5 ≤ 31 * x ^ (4 / 5 : ℝ) := by
  have a := le_self_pow₀ hu (by decide : 4 ≠ 0)
  have b := pow_le_pow_right₀ hu (by decide : 2 ≤ 4)
  have c := pow_le_pow_right₀ hu (by decide : 3 ≤ 4)
  have h₁ := one_le_pow₀ hu (n := 4)
  have f : (u + 1) ^ 5 - u ^ 5 ≤ 31 * u ^ 4 := by nlinarith only [a, b, c, h₁]
  have up : 0 < u := zero_lt_one.trans_le hu
  have power : u ^ 4 = (u ^ 5) ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_natCast_mul up.le]
    norm_num
  rw [power] at f
  exact f.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (pow_nonneg up.le _) left (by norm_num)) (by norm_num))

/-- A bound of order x^(-2/5) at fifth powers gives the same bound at every real cutoff. -/
theorem real_two_fifths {d q : ℕ} [Fact d.Prime] [NeZero q] {A : ℝ}
    (samples : ∀ᶠ n : ℕ in atTop, primeRemainder d q ((n : ℝ) ^ 5) ≤ A * ((n : ℝ) ^ 5) ^ (-(2 / 5) : ℝ)) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ C * x ^ (-(2 / 5) : ℝ) := by
  have tends : Tendsto (fun x : ℝ ↦ ⌊x ^ (1 / (5 : ℝ))⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num))
  refine ⟨32 * |A| + 961, ?_⟩
  filter_upwards [tends.eventually samples, tends.eventually ((tendsto_add_atTop_nat 1).eventually samples),
    eventually_ge_atTop (1 : ℝ)] with x h₁ h₂ hx
  let n := ⌊x ^ (1 / (5 : ℝ))⌋₊
  let y := (n : ℝ) ^ 5
  let z := ((n : ℝ) + 1) ^ 5
  obtain ⟨hn, lo, hi⟩ := enclose_by_powers (k := 5) (by decide) hx
  change 1 ≤ n at hn
  change y ≤ x at lo
  change x ≤ z at hi
  have np : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have yp : 0 < y := pow_pos (zero_lt_one.trans_le np) _
  have xp : 0 < x := zero_lt_one.trans_le hx
  have yz : y < z := pow_lt_pow_left₀ (lt_add_one (n : ℝ)) (Nat.cast_nonneg _) (by decide)
  have z32 : z ≤ 32 * y := by
    calc _ ≤ (2 * (n : ℝ)) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) _
         _ = _ := by dsimp [y]; ring
  have small : y ^ (-(2 / 5) : ℝ) ≤ 32 * x ^ (-(2 / 5) : ℝ) := by
    calc _ ≤ (x / 32) ^ (-(2 / 5) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hi, z32]) (by norm_num)
      _ = x ^ (-(2 / 5) : ℝ) / (32 : ℝ) ^ (-(2 / 5) : ℝ) := Real.div_rpow xp.le (by norm_num) _
      _ ≤ x ^ (-(2 / 5) : ℝ) / (32 : ℝ) ^ (-1 : ℝ) := div_le_div_of_nonneg_left (by positivity)
          (by positivity) (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
      _ = _ := by rw [Real.rpow_neg_one]; ring
  have bound {u : ℝ} (yu : y ≤ u) (h : primeRemainder d q u ≤ A * u ^ (-(2 / 5) : ℝ)) :
      primeRemainder d q u ≤ (32 * |A|) * x ^ (-(2 / 5) : ℝ) := by
    have pu : 0 < u := yp.trans_le yu
    calc _ ≤ |A| *(32 * x ^ (-(2 / 5) : ℝ)) := h.trans (mul_le_mul (le_abs_self _)
          ((Real.rpow_le_rpow_of_nonpos yp yu (by norm_num)).trans small) (by positivity) (abs_nonneg _))
         _ = _ := by ring
  have endpoint₁ := bound (u := y) le_rfl h₁
  have endpoint₂ := bound (u := z) yz.le (by simpa only [Nat.cast_add_one] using h₂)
  have span : z - y ≤ 31 * x ^ (4 / 5 : ℝ) := fifth_span np lo
  let m := 31 * x ^ (4 / 5 : ℝ)
  have lhs : x - y ≤ m := (sub_le_sub_right hi _).trans span
  have rhs : z - x ≤ m := (sub_le_sub_left lo _).trans span
  have err : (x - y) * (z - x) / (x ^ 2 * q.totient) ≤ 961 * x ^ (-(2 / 5) : ℝ) := by
    rw [← div_div]
    calc _ ≤ (x - y) * (z - x) / x ^ 2 := div_le_self (by positivity [sub_nonneg.2 lo, sub_nonneg.2 hi])
            (by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q) : (1 : ℝ) ≤ q.totient)
      _ ≤ m * m / x ^ 2 := div_le_div_of_nonneg_right (mul_le_mul lhs rhs (sub_nonneg.2 hi)
            (by dsimp [m]; positivity)) (sq_nonneg _)
      _ = _ := by
        dsimp [m]
        rw [show -(2 / 5 : ℝ) = 4 / 5 + 4 / 5 - 2 by ring, Real.rpow_sub xp, Real.rpow_add xp, Real.rpow_two]
        ring
  calc primeRemainder d q x ≤ (32 * |A|) * x ^ (-(2 / 5) : ℝ) + (x - y) * (z - x) / (x ^ 2 * q.totient) :=
          remainder_le_of_endpoint_bounds yp lo hi yz endpoint₁ endpoint₂
    _ ≤ (32 * |A|) * x ^ (-(2 / 5) : ℝ) + 961 * x ^ (-(2 / 5) : ℝ) := add_le_add (le_refl _) err
    _ = _ := by ring

end New.PrimeCutoff
