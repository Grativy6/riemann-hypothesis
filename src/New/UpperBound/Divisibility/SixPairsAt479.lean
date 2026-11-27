module

public import New.UpperBound.Divisibility.CollisionPrimeFloor
import New.Reduction.PrimeSums
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic

/-!
# Six marked pairs above 479

Fix q₀ = 18480 and d = 9239. At each admissible scale 479 is exceptional and has a nonempty
full mark. The local order is 15. The prime-power orders in the tower give six orbits of
distinguished places above unordered conjugate pairs. A mark with k members therefore leaves
(6 − k) / 6 of the unmarked collision mass. The last identity applies to every marked set.
-/

@[expose] public section

open Finset

namespace New.Data.CollisionPrimeExample

private lemma window_479 {P : Parameters} (D : Data P) :
    479^14 < D.m ∧ 480 < D.m ∧ (479 : ℝ) < D.x₁ := by
  have hx : 14 * (479 : ℝ) < D.logX / 2 := by
    linarith [D.mul_log_logB_le_logX, D.constantBound_le, (le_constantBound (P := P)).1]
  have hm : (479 : ℝ)^14 < D.m := calc
    (479 : ℝ)^14 ≤ (Real.exp 479)^14 := by
      gcongr
      linarith [Real.add_one_le_exp (479 : ℝ)]
    _ = Real.exp (14 * 479) := by rw [← Real.exp_natCast_mul]; norm_num
    _ < Real.exp (D.logX / 2) := Real.exp_lt_exp.2 hx
    _ ≤ D.m := D.m_mem.1
  refine ⟨by exact_mod_cast hm, by have := D.ten_thousand_le_m; omega, ?_⟩
  change (479 : ℝ) < Real.exp D.logX₁
  linarith [D.logX_le_logX₁, Real.add_one_le_exp D.logX₁]

local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩

/-- The actual scale conditions put 479 in the exceptional range for every admissible data set
with the selected fixed parameters. -/
theorem exceptional_479 (D : Data params) : D.IsExceptional 479 := by
  have hχ := ((D.collision_empty_iff 1 15).1 (collision_479 D)).2.1
  obtain ⟨hm, hlarge, _⟩ := window_479 D
  refine ⟨hχ, ?_, by rw [order_479]; decide, ?_⟩
  · intro h
    rcases h with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 479 - 1) h
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 479 + 1) h
      omega
  · rw [order_479, ceilLogLifts]
    exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 479)).2 hm

/-- The local Hecke construction has an actual nonempty full mark at this prime. -/
theorem exists_nonempty_fullMark_479 (D : Data params) (ι : PadicPlace 479) :
    ∃ Λ : Finset (FinPlace D.E), D.IsFullMark (p := 479) Λ ∧ Λ.Nonempty := by
  obtain ⟨Λ, hΛ⟩ := D.exists_isFullMark (p := 479) (window_479 D).2.2 (exceptional_479 D)
  have hid : (1 : D.Φ) ∈ D.aPlaces := by simp [aPlaces]
  rcases hΛ.mem_or_star_mem 1 hid with h | h
  · exact ⟨Λ, hΛ, _, h⟩
  · exact ⟨Λ, hΛ, _, h⟩


/-! ## The two growing prime powers -/

private lemma order_cast_mul (m n : ℕ) (h : m.Coprime n) (z : ℤ) :
    orderOf (z : ZMod (m*n)) = (orderOf (z : ZMod m)).lcm (orderOf (z : ZMod n)) := by
  calc orderOf (z : ZMod (m*n)) = orderOf (ZMod.chineseRemainder h (z : ZMod (m*n))) :=
        ((ZMod.chineseRemainder h).toMulEquiv.orderOf_eq _).symm
    _ = _ := by rw [map_intCast, Prod.orderOf]; rfl

private lemma lcm_three_pow_fifteen (h : ℕ) (hh : 0 < h) : (3^h).lcm 15 = 3^h * 5 := by
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · exact dvd_mul_right ..
    · exact Nat.mul_dvd_mul (dvd_pow_self 3 hh.ne') (dvd_refl 5)
  · exact ((show Nat.Coprime 3 5 by decide).pow_left h).mul_dvd_of_dvd_of_dvd
      (Nat.dvd_lcm_left _ _) ((by decide : 5 ∣ 15).trans (Nat.dvd_lcm_right _ _))

private lemma order_385 : orderOf ((-479 : ℤ) : ZMod 385) = 15 := by
  apply (orderOf_eq_iff (by decide : 0 < 15)).2
  refine ⟨by decide, ?_⟩
  intro i hi hi0
  interval_cases i <;> decide

/-- The orders at the two growing prime powers and at 385 determine the full order of -479. -/
lemma order_cast_479_tower (k h : ℕ) (hh : 0 < h) :
    orderOf ((-479 : ℤ) : ZMod (2^(k+5) * (3^(h+1) * 385))) = 2^k * (3^h * 5) := by
  have h2 : orderOf ((-479 : ℤ) : ZMod (2^(k+5))) = 2^k := by
    have hz : ((-479 : ℤ) : ZMod (2^(k+5))) = 1 + (2 : ℕ)^5 * ((-15 : ℤ) : ZMod (2^(k+5))) := by
      push_cast
      ring
    rw [hz]
    exact ZMod.orderOf_one_add_mul_prime_pow Nat.prime_two 5 (by decide) (-15) (by decide) k
  have h3 : orderOf ((-479 : ℤ) : ZMod (3^(h+1))) = 3^h := by
    have hz : ((-479 : ℤ) : ZMod (3^(h+1))) = 1 + (3 : ℕ) * ((-160 : ℤ) : ZMod (3^(h+1))) := by
      push_cast
      ring
    rw [hz]
    exact ZMod.orderOf_one_add_mul_prime Nat.prime_three (by decide) (-160) (by decide) h
  have h3c := (show Nat.Coprime 3 385 by decide).pow_left (h+1)
  have h2c := (((show Nat.Coprime 2 3 by decide).pow_right (h+1)).mul_right
    (show Nat.Coprime 2 385 by decide)).pow_left (k+5)
  rw [order_cast_mul _ _ h2c, order_cast_mul _ _ h3c, h2, h3, order_385, lcm_three_pow_fifteen h hh]
  exact ((((show Nat.Coprime 2 3 by decide).pow_right h).mul_right
    (show Nat.Coprime 2 5 by decide)).pow_left k).lcm_eq_mul

/-- At every admissible scale with these parameters, one pair accounts for one sixth of the
distinguished places. The order o modulo the fixed modulus is fifteen. -/
theorem six_mul_pair_size_479 (D : Data params) :
    6 * (orderOf (D.placeOfInt (-(479 : ℤ))) / D.o₀ 479) = #D.aPlaces := by
  have hcop : IsCoprime (-(479 : ℤ)) (params.q₀ : ℤ) := by decide
  have hg : orderOf (D.placeOfInt (-(479 : ℤ))) = orderOf ((-479 : ℤ) : ZMod D.q₁) := by
    calc orderOf (D.placeOfInt (-(479 : ℤ))) =
        orderOf ((params.placeMulEquiv D.towerExp) (D.placeOfInt (-(479 : ℤ)))) :=
          ((params.placeMulEquiv D.towerExp).orderOf_eq _).symm
      _ = _ := by rw [← orderOf_units, params.placeMulEquiv_placeOfInt hcop]
  obtain ⟨r, _, hr⟩ := D.exists_m_eq_two_pow
  have hs : 0 < D.towerExp := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  let j := Nat.log 3 (k+1) + 4
  have hmod : D.q₁ = 2^(k+5) * (3^((j+1)+1)*385) := by
    change 18480 * towerDeg D.towerExp = _
    rw [hk]; unfold towerDeg j
    simp only [Nat.succ_eq_add_one, pow_add]
    ring
  rw [hg, order_479, hmod, order_cast_479_tower _ _ (Nat.succ_pos _), D.card_aPlaces, hk]
  have hn : 2^k * (3^(j+1)*5) = 15 * (2^k*3^j) := by rw [pow_succ]; ring
  rw [hn, Nat.mul_div_cancel_left _ (by decide)]
  unfold towerDeg j
  simp only [pow_add, Nat.succ_eq_add_one]
  ring

end New.Data.CollisionPrimeExample





namespace New.Data.CollisionPrimeExample

open Finset

local instance fact479ForCounts : Fact (Nat.Prime 479) := ⟨by norm_num1⟩

/-- The general arithmetic pair count agrees with the direct prime-power calculation at 479. -/
theorem returnPairCount_479 (D : Data params) : D.returnPairCount 479 = 6 := by
  have he := exceptional_479 D
  have hcount := returnPairCount_mul_period he.chiK_eq_neg_one he.odd_o₀
  have hd : D.o₀ 479 ∣ orderOf (D.placeOfInt (-(479 : ℤ))) := orderOf_map_dvd _ _
  have hpos := Nat.div_pos (Nat.le_of_dvd (orderOf_pos _) hd) he.odd_o₀.pos
  exact Nat.eq_of_mul_eq_mul_right hpos (hcount.trans (six_mul_pair_size_479 D).symm)

/-- Every full mark above 479 contains exactly six chosen primes. -/
theorem fullMark_card_479 (D : Data params) (ι : PadicPlace 479)
    {Λ : Finset (FinPlace D.E)} (h : D.IsFullMark (p := 479) Λ) : #Λ = 6 := by
  exact h.card_eq_returnPairCount.trans (returnPairCount_479 D)

/-- A mark with k members leaves exactly (6-k)/6 of the unmarked collision sum. -/
theorem collisionSum_share_479 (D : Data params) (ι : PadicPlace 479)
    {Λ : Finset (FinPlace D.E)} (h : D.IsMarked (p := 479) Λ) :
    6 * D.collisionSum 479 (placesInducing Λ) = (6 - (#Λ : ℝ)) * D.collisionSum 479 ∅ := by
  simpa only [returnPairCount_479 D, Nat.cast_ofNat] using h.collisionSum_return_share

end New.Data.CollisionPrimeExample
