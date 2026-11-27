module

public import New.UpperBound.Divisibility.MarkedCollisionFormula
import New.Reduction.Data.Existence
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-!
# The first prime admitting a collision

An odd order in the unit group modulo a divisor of q₀ divides the odd part of the group
cardinality. Modulo 240 the image is the identity. Modulo 7 the prime 239 fails the test.
At 479 the parameters q₀ = 18480 and d = 9239 realize an actual collision at exponent 15.
-/

@[expose] public section

open Finset

namespace New.Data

variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime]

/-- Every genuine collision gives an odd exponent and the corresponding modular equality. -/
lemma IsCollision.neg_prime_pow_eq_one {S : Finset D.Φ} {τ : D.Φ} {e : ℕ}
    (h : D.IsCollision p S τ e) : (-(p : ZMod P.q₀))^e = 1 := by
  obtain ⟨hd, _, ho⟩ := h.ne_and_odd_and_dvd
  have hχ := ((mem_partnerExponents.1 (mem_positivePartnerExponents.1 h.1).2).resolve_left hd).1
  exact (dvd_iff_neg_prime_pow hχ e).1 ho

/-- If a collision exponent is odd, the order of its image modulo n divides
the odd part of the cardinality of the unit group. -/
lemma IsCollision.neg_prime_pow_of_totient {S : Finset D.Φ} {τ : D.Φ} {e n k t : ℕ}
    [NeZero n] (h : D.IsCollision p S τ e) (hn : n ∣ P.q₀)
    (ht : n.totient = 2^k * t) : (-(p : ZMod n))^t = 1 := by
  obtain ⟨hd, he, _⟩ := h.ne_and_odd_and_dvd
  have hχ := ((mem_partnerExponents.1 (mem_positivePartnerExponents.1 h.1).2).resolve_left hd).1
  let u := P.placeClass (hn.trans (dvd_mul_right _ _)) (D.placeOfInt (-(p : ℤ)))
  have hu : (u : ZMod n) = -(p : ZMod n) := placeClass_neg_prime_val hχ hn
  have hz : (-(p : ZMod n))^e = 1 := by
    simpa only [map_pow, map_one, map_neg, map_natCast] using
      congrArg (ZMod.castHom hn (ZMod n)) h.neg_prime_pow_eq_one
  have hdvd : orderOf u ∣ e := orderOf_dvd_iff_pow_eq_one.2 <| Units.ext <| by
    simpa only [Units.val_pow_eq_pow_val, hu, Units.val_one] using hz
  have hcard : orderOf u ∣ 2^k * t := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, ht] using orderOf_dvd_natCard u
  have hcop := (Nat.coprime_two_right.2 (Odd.of_dvd_nat he hdvd)).pow_right k
  have hpow : u^t = 1 := orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_left hcard)
  simpa only [Units.val_pow_eq_pow_val, hu, Units.val_one] using
    congrArg (fun z : (ZMod n)ˣ ↦ (z : ZMod n)) hpow

/-- A collision forces p = -1 modulo 240. The residual candidate 239 below 479
has the wrong odd power modulo 7. -/
theorem IsCollision.four_seventy_nine_le {S : Finset D.Φ} {τ : D.Φ} {e : ℕ}
    (h : D.IsCollision p S τ e) : 479 ≤ p := by
  have hp240 : -(p : ZMod 240) = 1 := by
    simpa only [pow_one] using h.neg_prime_pow_of_totient
      ((by decide : 240 ∣ 18480).trans P.dvd_q₀) (k := 6) (t := 1) (by decide)
  have hz : (((p + 1 : ℕ) : ZMod 240)) = 0 := by push_cast; linear_combination -hp240
  have hdvd := (ZMod.natCast_eq_zero_iff _ _).1 hz
  obtain ⟨k, hk⟩ := hdvd
  by_contra! small
  have : p = 239 := by omega
  subst p
  have h7 := h.neg_prime_pow_of_totient ((by decide : 7 ∣ 18480).trans P.dvd_q₀)
    (k := 1) (t := 3) (by decide)
  exact (by decide : (-((239 : ℕ) : ZMod 7))^3 ≠ 1) h7

/-- Every excluded set has zero collision mass at primes below 479. -/
theorem collisionSum_eq_zero_of_lt_479 (D : Data P) {p : ℕ} [Fact p.Prime]
    (hlt : p < 479) (S : Finset D.Φ) : D.collisionSum p S = 0 := by
  have hf (τ : D.Φ) (e : ℕ) : ¬D.IsCollision p S τ e := fun h ↦ (not_le_of_gt hlt) h.four_seventy_nine_le
  simp [collisionSum, hf]


namespace CollisionPrimeExample

/-- The smallest fixed modulus allowed in the construction, with d = 9239. -/
def params : Parameters where
  q₀ := 18480
  d := 9239
  dvd_q₀ := dvd_rfl
  d_prime := by norm_num1
  q₀_dvd_and_not_dvd := by decide

private lemma inert : chiK params.d (479 : ℕ) = -1 := by
  have : Fact (Nat.Prime 9239) := ⟨by norm_num1⟩
  change chiK 9239 (479 : ℕ) = -1
  rw [chiK_eq_legendreSym, jacobiSym.legendreSym.to_jacobiSym]
  norm_num

/-- The place order for this prime is fifteen for every admissible choice of the scale data. -/
lemma order_479 (D : Data params) : D.o₀ 479 = 15 := by
  have : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
  unfold o₀
  rw [← orderOf_units, placeClass_neg_prime_val (D := D) (p := 479) inert dvd_rfl]
  change orderOf (-((479 : ℕ) : ZMod 18480)) = 15
  apply (orderOf_eq_iff (by decide : 0 < 15)).2
  refine ⟨by decide, ?_⟩
  intro i hi hi0
  interval_cases i <;> decide

/-- At the identity place the first eligible exponent 15 is realized. -/
lemma collision_479 (D : Data params) : D.IsCollision 479 ∅ 1 15 := by
  have : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
  have he : Odd 15 := by decide
  have hid : (1 : D.Φ) ∈ D.aPlaces := by simp [aPlaces]
  refine ⟨mem_positivePartnerExponents.2 ⟨by decide,
    mem_partnerExponents.2 (.inr ⟨inert, he⟩)⟩, by simpa using hid, ?_⟩
  have ho : D.o₀ 479 ∣ 15 := (order_479 D) ▸ dvd_rfl
  simpa using (D.placeOfInt_mul_mem_aPlaces_iff he 1 hid).2 ho

/-- The admitted parameter choice has actual scale data. -/
theorem exists_collision_479 : ∃ D : Data params, D.IsCollision 479 ∅ 1 15 := by
  obtain ⟨x, D, _⟩ := (New.eventually_exists_data params (ε := 1 / 200)
    (by norm_num) (by norm_num)).exists
  exact ⟨D, collision_479 D⟩


/-- The first prime with a collision has positive mass for every scale choice for these parameters. -/
lemma collisionSum_479_eq (D : Data params) :
    D.collisionSum 479 ∅ =
      (#D.aPlaces : ℝ) * (D.a * ((479 : ℕ) : ℝ)^15 / ((((479 : ℕ) : ℝ)^15)^2 - 1)) := by
  have : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
  rw [D.collisionSum_empty_value, order_479 D, ite_eq_left ⟨inert, by decide⟩]

/-- The positive value rules out a default zero from a divergent summation convention. -/
lemma collisionSum_479_pos (D : Data params) : 0 < D.collisionSum 479 ∅ := by
  have hcard : 0 < #D.aPlaces := card_pos.2 ⟨1, by simp [aPlaces]⟩
  have ha : 0 < (D.a : ℝ) := HasLogBound.pos D
  have hq : 1 < (479 : ℝ)^15 := one_lt_pow₀ (by norm_num) (by decide)
  have hden : 0 < ((479 : ℝ)^15)^2 - 1 := sub_pos.2 (one_lt_pow₀ hq (by decide))
  rw [collisionSum_479_eq]
  positivity

end CollisionPrimeExample

end New.Data
