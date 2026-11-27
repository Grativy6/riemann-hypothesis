module

public import New.UpperBound.Divisibility.CollisionPrimeFloor
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-!
# One operator at one prime, 36 at another

Both primes are −1 modulo 18480, inert for d = 9239, and exceptional for every admissible
scale. Their return quotients are 29 and 36. One is coprime to the tower factor and the other
divides it. At the first prime the finite prime of the identity place itself gives a full mark.
-/

@[expose] public section

namespace New.Data

open Finset Real

variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime]

/-- An inert prime has local order one exactly when its successor is divisible by the base modulus. -/
lemma order_one_iff_base_dvd_succ (hi : chiK P.d p = -1) :
    D.o₀ p = 1 ↔ P.q₀ ∣ p+1 := by
  have h : D.o₀ p ∣ 1 ↔ (-(p : ZMod P.q₀))^1 = 1 := dvd_iff_neg_prime_pow hi 1
  rw [Nat.dvd_one] at h
  rw [h, pow_one, ← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor <;> intro z <;> linear_combination -z

/-- With local order one, the smallness and noncongruence conditions are automatic when p lies
below the secondary cutoff and p+1 is smaller than the number of lifts. -/
lemma exceptional_of_local_order_one (hi : chiK P.d p = -1) (ho : D.o₀ p = 1)
    (hm : p+1 < D.m) : D.IsExceptional p := by
  refine ⟨hi, ?_, by rw [ho]; decide, ?_⟩
  · rintro (hd | hd)
    · have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.out.one_lt) hd
      omega
    · exact (not_le_of_gt hm) (Nat.le_of_dvd (Nat.succ_pos _) hd)
  · rw [ho, ceilLogLifts]
    exact (Nat.lt_clog_iff_pow_lt hp.out.one_lt).2 (by simp; omega)

end New.Data

namespace New.Data.CollisionPrimeExample

open Finset Real

local instance firstPrime : Fact (Nat.Prime 535919) := ⟨by norm_num1⟩
local instance secondPrime : Fact (Nat.Prime 665279) := ⟨by norm_num1⟩

private lemma small_example_window {P : Parameters} (D : Data P) :
    700000 < D.m ∧ (700000 : ℝ) < D.x₁ := by
  have hx : (700000 : ℝ) < D.logX / 2 := by
    linarith [D.mul_log_logB_le_logX, D.constantBound_le, (le_constantBound (P := P)).1]
  constructor
  · have h : (700000 : ℝ) < D.m :=
      lt_of_lt_of_le (by linarith [Real.add_one_le_exp (D.logX / 2)]) D.m_mem.1
    exact_mod_cast h
  · change (700000 : ℝ) < Real.exp D.logX₁
    linarith [D.logX_le_logX₁, Real.add_one_le_exp D.logX₁]

private lemma inert_first : chiK params.d (535919 : ℕ) = -1 := by
  have : Fact (Nat.Prime 9239) := ⟨by norm_num1⟩
  change chiK 9239 (535919 : ℕ) = -1
  rw [chiK_eq_legendreSym, jacobiSym.legendreSym.to_jacobiSym]
  norm_num

private lemma inert_second : chiK params.d (665279 : ℕ) = -1 := by
  have : Fact (Nat.Prime 9239) := ⟨by norm_num1⟩
  change chiK 9239 (665279 : ℕ) = -1
  rw [chiK_eq_legendreSym, jacobiSym.legendreSym.to_jacobiSym]
  norm_num

lemma first_return_counts (D : Data params) :
    D.o₀ 535919 = 1 ∧ D.returnQuotient 535919 = 29 ∧ D.returnPairCount 535919 = 1 := by
  have ho := (order_one_iff_base_dvd_succ (D := D) inert_first).2 (by decide)
  have hb : D.returnQuotient 535919 = 29 := by rw [returnQuotient, ho]; decide
  refine ⟨ho, hb, ?_⟩
  rw [returnPairCount, hb]
  exact (((by decide : Nat.Coprime 3 29).pow_left _).mul_left
    ((by decide : Nat.Coprime 2 29).pow_left _)).gcd_eq_one

lemma second_return_counts (D : Data params) :
    D.o₀ 665279 = 1 ∧ D.returnQuotient 665279 = 36 ∧ D.returnPairCount 665279 = 36 := by
  have ho := (order_one_iff_base_dvd_succ (D := D) inert_second).2 (by decide)
  have hb : D.returnQuotient 665279 = 36 := by rw [returnQuotient, ho]; decide
  refine ⟨ho, hb, ?_⟩
  rw [returnPairCount, hb]
  apply Nat.gcd_eq_right
  obtain ⟨e, _, he⟩ := D.exists_m_eq_two_pow
  have h₂ : 2 ≤ D.towerExp := by omega
  have h₃ : 2 ≤ Nat.log 3 D.towerExp + 5 := by omega
  exact Nat.mul_dvd_mul (pow_dvd_pow 3 h₃) (pow_dvd_pow 2 h₂)

/-- On the same admissible data, the identity place gives a singleton full mark at the first
prime. A full mark exists at the second prime, and every such mark has 36 members. -/
theorem singleton_and_thirty_six (D : Data params) (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    (letI : PadicPlace 535919 := ι₁
     D.IsFullMark (p := 535919) {inducedPlace (p := 535919) (1 : D.Φ)}) ∧
    (letI : PadicPlace 665279 := ι₂
     (∃ Λ : Finset (FinPlace D.E), D.IsFullMark (p := 665279) Λ) ∧
       ∀ Λ : Finset (FinPlace D.E), D.IsFullMark (p := 665279) Λ → #Λ = 36) := by
  classical
  obtain ⟨hm, hx⟩ := small_example_window D
  constructor
  · let : PadicPlace 535919 := ι₁
    have first := first_return_counts D
    have he := exceptional_of_local_order_one inert_first first.1 (by omega)
    have hs : D.IsSmallNonsplit 535919 := ⟨by push_cast; linarith, by rw [inert_first]; norm_num⟩
    exact he.fullMark_singleton hs first.2.2 1 (by simp [aPlaces])
  · let : PadicPlace 665279 := ι₂
    have second := second_return_counts D
    have he := exceptional_of_local_order_one inert_second second.1 (by omega)
    exact ⟨D.exists_isFullMark (p := 665279) (by push_cast; linarith) he,
      fun Λ hΛ ↦ hΛ.card_eq_returnPairCount.trans second.2.2⟩


/-- At the even local order of 239, the power of the negative place returns to the
distinguished fiber. Putting the minus sign outside the power takes it away. -/
theorem even_return_at_239 (D : Data params) :
    D.o₀ 239 = 10 ∧ D.placeOfInt (-(239 : ℤ))^10 ∈ D.aPlaces ∧
      D.placeOfInt (-((239 : ℤ)^10)) ∉ D.aPlaces := by
  have pprime : Fact (Nat.Prime 239) := ⟨by norm_num1⟩
  have dprime : Fact (Nat.Prime 9239) := ⟨by norm_num1⟩
  have hi : chiK params.d (239 : ℕ) = -1 := by
    change chiK 9239 (239 : ℕ) = -1
    rw [chiK_eq_legendreSym, jacobiSym.legendreSym.to_jacobiSym]
    norm_num
  have ho : D.o₀ 239 = 10 := by
    unfold o₀
    rw [← orderOf_units, placeClass_neg_prime_val (D := D) (p := 239) hi dvd_rfl]
    change orderOf (-((239 : ℕ) : ZMod 18480)) = 10
    apply (orderOf_eq_iff (by decide : 0 < 10)).2
    refine ⟨by decide, ?_⟩
    intro i hie hip
    interval_cases i <;> decide
  refine ⟨ho, ?_, ?_⟩
  · simp only [aPlaces, mem_filter, mem_univ, true_and, map_pow]
    rw [← ho]
    exact pow_orderOf_eq_one _
  · have hcop : IsCoprime (-((239 : ℤ)^10)) (params.q₀ : ℤ) := by decide
    have hx : (params.placeClass (params.q₀.dvd_mul_right _) (D.placeOfInt (-((239 : ℤ)^10))) :
        ZMod params.q₀) = -1 := by
      rw [params.placeClass_placeOfInt hcop]
      decide
    intro hmem
    have hone : params.placeClass (params.q₀.dvd_mul_right _) (D.placeOfInt (-((239 : ℤ)^10))) = 1 := by
      simpa [aPlaces] using hmem
    rw [hone, Units.val_one] at hx
    exact (by decide : (1 : ZMod 18480) ≠ -1) hx

end New.Data.CollisionPrimeExample
