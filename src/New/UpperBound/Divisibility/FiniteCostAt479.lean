module

public import New.UpperBound.Divisibility.FiniteMarkedCollisions
public import New.UpperBound.Divisibility.SixPairsAt479
import New.Reduction.PrimeSums
import Mathlib.Tactic

/-!
# The first return and the scalar saving at 479

At these fixed parameters the first positive part already exceeds both ordinary local loss
allowances and the entire possible distinguished-place surplus if a pair remains uncovered.
The finite cutoff nevertheless reduces the scalar exponent of the common witness by a positive
integer. At a full mark the resulting local determinant allowance per source dimension drops
by at least one off weight per active exponent divided by 640.
-/

@[expose] public section

open Finset Real

namespace New.Data.CollisionPrimeExample

local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩

/-- The scale bounds compare the number of lifts to the square-log allowance, and the
secondary cutoff to the first collision norm. -/
private lemma loss_scales {P : Parameters} (D : Data P) :
    24 * 18480 * D.logB^2 * (479 : ℝ)^14 < D.m ∧ 14 * (479 : ℝ)^15 < D.x₁ := by
  have hB0 : 0 < D.logB := HasLogBound.pos D
  have hbig : 479 < log D.logB := by linarith [D.constantBound_le, (le_constantBound (P := P)).1]
  have hB : 479 < D.logB := by linarith [log_le_sub_one_of_pos hB0]
  have hm : D.logB^50 ≤ D.m := calc
    D.logB^50 = exp (50 * log D.logB) := by
      rw [show (50 : ℝ) = (50 : ℕ) by norm_num, exp_natCast_mul, exp_log hB0]
    _ ≤ exp (D.logX / 2) := exp_le_exp.2 (by linarith [D.mul_log_logB_le_logX])
    _ ≤ D.m := D.m_mem.1
  constructor
  · calc 24 * 18480 * D.logB^2 * (479 : ℝ)^14 =
          D.logB^2 * (24 * 18480 * (479 : ℝ)^14) := by ring
      _ < D.logB^2 * D.logB^48 := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        exact lt_of_lt_of_le (by norm_num : 24 * 18480 * (479 : ℝ)^14 < 479^48)
          (pow_le_pow_left₀ (by norm_num) hB.le 48)
      _ = D.logB^50 := by ring
      _ ≤ _ := hm
  · have hx : 16 * (479 : ℝ) < D.logX₁ := by
      linarith [D.logX_le_logX₁, D.mul_log_logB_le_logX]
    calc 14 * (479 : ℝ)^15 ≤ 479^16 := by norm_num
      _ ≤ (exp 479)^16 := by gcongr; linarith [add_one_le_exp (479 : ℝ)]
      _ = exp (16 * 479) := by rw [← exp_natCast_mul]; norm_num
      _ < D.x₁ := exp_lt_exp.2 hx

/-- One sixth of the first long-row deficit, summed over the lifts, exceeds the two
loss allowances plus the place surplus maximized over all distinguished places. -/
theorem first_term_exceeds_allowances_479 (D : Data params) :
    6 * (2 * D.loss 479 + D.m * #D.aPlaces * (D.a / D.x₁)) <
      D.m * #D.aPlaces * ((D.a : ℝ)/(479 : ℝ)^15 - D.a/D.x₁) := by
  let A : ℝ := #D.aPlaces
  let q : ℝ := (479 : ℝ)^15
  have hq : 1 < q := one_lt_pow₀ (by norm_num : (1 : ℝ) < 479) (by decide)
  have hq0 : 0 < q := by linarith
  have hA : 0 < A := by
    dsimp only [A]
    exact_mod_cast (card_pos.2 ⟨1, by simp [aPlaces]⟩ : 0 < #D.aPlaces)
  have ha : 0 < (D.a : ℝ) := HasLogBound.pos D
  have hm : 0 < (D.m : ℝ) := HasLogBound.pos D
  have hφ : (params.q₀.totient : ℝ) ≤ 18480 := by exact_mod_cast Nat.totient_le params.q₀
  have hscale : 24 * (params.q₀.totient : ℝ) * D.logB^2 * (479 : ℝ)^14 < D.m := by
    refine lt_of_le_of_lt ?_ (loss_scales D).1
    gcongr
  have hloss : D.loss 479 = A * params.q₀.totient * D.a * D.logB^2 / 479 := by
    rw [loss, ite_eq_right (exceptional_479 D).2.1, Nat.cast_one, mul_one, D.f_eq_card_aPlaces_mul, Nat.cast_mul]
    dsimp only [A]
    push_cast
    ring
  have hL : 12 * D.loss 479 < D.m * A * D.a / (2*q) := by
    rw [hloss, lt_div_iff₀ (by positivity : 0 < 2*q)]
    convert mul_lt_mul_of_pos_right hscale (mul_pos hA ha) using 1 <;> first | (dsimp only [q]; ring) | ring
  have hS : 7 * (D.m * A * (D.a / D.x₁)) < D.m * A * D.a / (2*q) := by
    calc 7 * (D.m * A * (D.a / D.x₁)) = 7 * (D.m * A * D.a) / D.x₁ := by ring
      _ < 7 * (D.m * A * D.a) / (14*q) :=
        div_lt_div_of_pos_left (by positivity) (by positivity) (loss_scales D).2
      _ = _ := by field_simp; ring
  have hid : 2 * (D.m * A * D.a / (2*q)) = D.m * A * D.a / q := by ring
  calc 6 * (2 * D.loss 479 + D.m * A * (D.a / D.x₁)) <
      D.m * A * D.a / q - D.m * A * (D.a / D.x₁) := by linarith
    _ = D.m * A * (D.a / q - D.a / D.x₁) := by ring

/-- The cutoff removes the same fraction of every uncovered pair, so each selected prime
still accounts for exactly one sixth of the finite charge. -/
theorem collisionDeficit_share_479 (D : Data params) (ι : PadicPlace 479)
    {Λ : Finset (FinPlace D.E)} (h : D.IsMarked (p := 479) Λ) :
    6 * D.collisionDeficit 479 (placesInducing Λ) = (6 - (#Λ : ℝ)) * D.collisionDeficit 479 ∅ := by
  classical
  let n := orderOf (D.placeOfInt (-(479 : ℤ))) / D.o₀ 479
  let u := D.aPlaces.filter fun σ ↦ inducedPlace σ ∉ Λ ∧ star (inducedPlace σ) ∉ Λ
  have hc : (#u : ℝ) + (#Λ : ℝ)*n = #D.aPlaces := by exact_mod_cast h.card_uncovered_add_card_mul_pair
  have ha : 6 * (n : ℝ) = #D.aPlaces := by exact_mod_cast six_mul_pair_size_479 D
  have hu : 6 * (#u : ℝ) = (6 - (#Λ : ℝ)) * #D.aPlaces := by
    rw [← ha] at hc ⊢
    linear_combination 6 * hc
  let R := 1 - ((((479 : ℕ) : ℝ)^D.o₀ 479)^2)⁻¹^(D.collisionTermCount 479)
  let W : ℝ := D.collisionTermCount 479 * (D.offWeight : ℝ)
  rw [h.collisionDeficit_formula, h.isExceptional.collisionDeficit_empty h.isSmallNonsplit]
  change 6 * (D.collisionSum 479 (placesInducing Λ)*R - (#u : ℝ)*_ * _) =
    (6 - (#Λ : ℝ)) * (D.collisionSum 479 ∅*R - (#D.aPlaces : ℝ)*_ * _)
  have hraw := collisionSum_share_479 D ι h
  linear_combination R * hraw - W * hu

private lemma first_power_below_479 (D : Data params) : (((479 : ℕ) : ℝ)^15) < D.x₁ := by
  have hx := (loss_scales D).2
  have qpos : (0 : ℝ) < 479^15 := by positivity
  push_cast
  linarith

/-- The first term alone, with its actual partner weight subtracted, costs more than both
loss allowances and the maximal available place surplus at 479. -/
theorem finite_one_pair_exceeds_allowances_479 (D : Data params) :
    6 * (2 * D.loss 479 + D.m * #D.aPlaces * (D.a / D.x₁)) <
      D.m * D.collisionDeficit 479 ∅ := by
  have hχ := (exceptional_479 D).1
  have hdiv : D.o₀ 479 ∣ 15 := (order_479 D) ▸ dvd_rfl
  have h := first_active_term_le_deficit hχ (by decide : Odd 15) hdiv (first_power_below_479 D)
  refine (first_term_exceeds_allowances_479 D).trans_le ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_ofNat] using h) (by positivity)

/-- No incomplete mark at 479 can pay the collision charge from the old loss and surplus
allowances, even after every inactive exponent has been removed. -/
theorem incomplete_mark_exceeds_finite_allowances_479 (D : Data params) (ι : PadicPlace 479)
    {Λ : Finset (FinPlace D.E)} (h : D.IsMarked (p := 479) Λ) (hk : #Λ < 6) :
    2 * D.loss 479 + D.m * #D.aPlaces * (D.a / D.x₁) <
      D.m * D.collisionDeficit 479 (placesInducing Λ) := by
  have hshare := collisionDeficit_share_479 D ι h
  have hk' : (#Λ : ℝ) ≤ 5 := by exact_mod_cast (by omega : #Λ ≤ 5)
  have hle : D.collisionDeficit 479 ∅ ≤ 6 * D.collisionDeficit 479 (placesInducing Λ) := by
    rw [hshare]
    exact le_mul_of_one_le_left (D.collisionDeficit_nonneg 479 ∅) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg D.m (α := ℝ))
  linarith [finite_one_pair_exceeds_allowances_479 D]

/-- The refinement saves at least one off weight at every active exponent, distinguished
place and lift on the actual scalar summand, measured against the raw reciprocal cutoff. -/
theorem clearance_saving_479 (D : Data params) (ι : PadicPlace 479) :
    D.collisionClearance 479 + D.m * #D.aPlaces * D.collisionTermCount 479 * D.offWeight ≤
      ⌈D.m * D.collisionSum 479 ∅ - D.loss 479⌉₊ := by
  have he := exceptional_479 D
  have hsmall : D.IsSmallNonsplit 479 :=
    ⟨by have := first_power_below_479 D; push_cast at *; linarith, by rw [he.1]; norm_num⟩
  have hL : 0 ≤ D.loss 479 := le_trans (by positivity) (D.le_loss 479)
  have hS : 0 ≤ (D.m : ℝ)*#D.aPlaces*(D.a/D.x₁) := by positivity
  apply he.clearance_saving hsmall
  linarith [finite_one_pair_exceeds_allowances_479 D]

/-- At least one exponent is active, and the saved allowance is a positive integer. -/
theorem clearance_saving_pos_479 (D : Data params) :
    0 < D.m * #D.aPlaces * D.collisionTermCount 479 * D.offWeight := by
  have hcard : 0 < #D.aPlaces := card_pos.2 ⟨1, by simp [aPlaces]⟩
  have hbelow : (479 : ℕ)^15 < D.natX₁ := by
    have hx := first_power_below_479 D
    rw [show D.x₁ = (D.natX₁ : ℝ) from D.exp_logX₁] at hx
    exact_mod_cast hx
  have hk : 1 < (479^15).clog D.natX₁ := (Nat.lt_clog_iff_pow_lt
    (by norm_num : 1 < (479 : ℕ)^15)).2 (by simpa using hbelow)
  have hk' : 0 < D.collisionTermCount 479 := by rw [collisionTermCount, order_479]; omega
  have hm : 0 < D.m := by have := D.ten_thousand_le_m; omega
  have hoff : 0 < D.offWeight := by
    have ha : 0 < (D.a : ℝ) := HasLogBound.pos D
    have hpos : 0 < (D.offWeight : ℝ) := by rw [D.cast_offWeight]; positivity
    exact_mod_cast hpos
  positivity

end New.Data.CollisionPrimeExample

namespace New.Data.CollisionPrimeExample

open Finset Real
local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩

private lemma base_totient : params.q₀.totient = 3840 := by
  change (16 * (3 * (5 * (7 * 11)))).totient = 3840
  rw [Nat.totient_mul (by decide : Nat.Coprime 16 (3 * (5 * (7 * 11)))),
    Nat.totient_mul (by decide : Nat.Coprime 3 (5 * (7 * 11))),
    Nat.totient_mul (by decide : Nat.Coprime 5 (7 * 11)),
    Nat.totient_mul (by decide : Nat.Coprime 7 11)]
  decide

/-- Compare the scalar exponent used by the finite witness with the exponent actually used by
the earlier construction. The saved quantity is a positive integer at every admissible scale. -/
theorem clearance_saving_vs_original_479 (D : Data params) (ι : PadicPlace 479) :
    D.collisionClearance 479 + D.m * #D.aPlaces * D.collisionTermCount 479 * D.offWeight ≤
      D.collisionExponent 479 := by
  refine (clearance_saving_479 D ι).trans (Nat.ceil_le.2 ?_)
  have hpaid := mul_collisionSum_le_collisionExponent (D := D) (p := 479)
  have hL : 0 ≤ D.loss 479 := le_trans (by positivity) (D.le_loss 479)
  linarith

/-- For a full mark at 479, the new additive index allowance per source dimension is smaller
by at least K w / 640, where w is the integral off weight and K counts the active terms. -/
theorem fullMark_index_saving_479 (D : Data params) (ι : PadicPlace 479)
    {Λ : Finset (FinPlace D.E)} (h : D.IsFullMark (p := 479) Λ) :
    (D.collisionTermCount 479 : ℝ) * D.offWeight / 640 ≤
      D.markedProductIndexCost 479 Λ (D.collisionExponent 479) -
      D.markedProductIndexCost 479 Λ (D.collisionClearance 479) := by
  rw [D.markedProductIndexCost_sub, fullMark_card_479 D ι h]
  have hm : 0 < (D.m : ℝ) := HasLogBound.pos D
  have hf : 0 < (D.f : ℝ) := HasLogBound.pos D
  have ha : 0 < (#D.aPlaces : ℝ) := by
    exact_mod_cast (card_pos.2 ⟨1, by simp [aPlaces]⟩ : 0 < #D.aPlaces)
  have hfA : (D.f : ℝ) = #D.aPlaces * (3840 : ℝ) := by
    rw [D.f_eq_card_aPlaces_mul, Nat.cast_mul, base_totient]
    norm_num
  have gap : (D.m : ℝ) * #D.aPlaces * D.collisionTermCount 479 * D.offWeight ≤
      D.collisionExponent 479 - (D.collisionClearance 479 : ℝ) := by
    have ht : (D.collisionClearance 479 : ℝ) +
        D.m * (#D.aPlaces : ℝ) * D.collisionTermCount 479 * D.offWeight ≤ D.collisionExponent 479 := by
      exact_mod_cast clearance_saving_vs_original_479 D ι
    linarith
  calc (D.collisionTermCount 479 : ℝ) * D.offWeight / 640 =
        6 * (D.m * (#D.aPlaces : ℝ) * D.collisionTermCount 479 * D.offWeight) / (D.m * (D.f : ℝ)) := by
          rw [hfA]
          field_simp
          ring
    _ ≤ _ := by push_cast; gcongr

end New.Data.CollisionPrimeExample
