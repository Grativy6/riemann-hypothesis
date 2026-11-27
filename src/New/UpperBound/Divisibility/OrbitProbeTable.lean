module

public import New.UpperBound.Divisibility.ActualNormProfiles
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-!
# Actual measuring primes for all the even periods dividing 72

Each rational prime is -1 modulo 18480 and inert for d = 9239. Its local order is one.
The 2,3-part of (p+1)/18480 gives the number of unordered pairs in every admissible tower.
-/

@[expose] public section

open Finset Real NumberField ThreePrimeEnvelope ColoredSparse
namespace New.Data.CollisionPrimeExample
namespace OrbitProbes

/-- The possible half-periods G with 2G dividing the 72-residue board. -/
def halfPeriod : Fin 9 → ℕ := ![1,2,3,4,6,9,12,18,36]
def rationalPrime : Fin 9 → ℕ := ![535919,628319,942479,3622079,776159,1829519,6431039,6320159,665279]
def cofactor : Fin 9 → ℕ := ![29,17,17,49,7,11,29,19,1]

instance primeFact (i : Fin 9) : Fact (Nat.Prime (rationalPrime i)) := by
  constructor; fin_cases i <;> norm_num [rationalPrime]

lemma arithmetic (i : Fin 9) :
    rationalPrime i+1 = 18480*(halfPeriod i*cofactor i) ∧
    halfPeriod i ∣ 36 ∧ Nat.Coprime 2 (cofactor i) ∧ Nat.Coprime 3 (cofactor i) ∧
    rationalPrime i+1 < 7000000 := by fin_cases i <;> decide

lemma all_half_periods {G : ℕ} (hG : 2*G ∣ 72) : ∃ i, halfPeriod i=G := by
  have dvd : G ∣ 36 := by exact (Nat.mul_dvd_mul_iff_left (by decide : 0<2)).1 hG
  have small := Nat.le_of_dvd (by decide : 0<36) dvd
  have table : ∀ r : Fin 37, r.val ∣ 36 → ∃ i, halfPeriod i=r.val := by decide
  exact table ⟨G,by omega⟩ dvd

lemma inert (i : Fin 9) : chiK params.d (rationalPrime i) = -1 := by
  have : Fact (Nat.Prime 9239) := ⟨by norm_num1⟩
  change chiK 9239 (rationalPrime i) = -1
  rw [chiK_eq_legendreSym,jacobiSym.legendreSym.to_jacobiSym]
  fin_cases i <;> norm_num [rationalPrime]

lemma large_lift_rank (D : Data params) : 7000000 < D.m := by
  have lb : (3000 : ℝ) ≤ D.logX/4 := by
    linarith [D.mul_log_logB_le_logX,D.constantBound_le,(le_constantBound (P := params)).1]
  have base : (3000 : ℝ) ≤ exp (D.logX/4) := by linarith [Real.add_one_le_exp (D.logX/4)]
  have bound : (7000000 : ℝ) < exp (D.logX/2) := calc
    _ < (3000:ℝ)^2 := by norm_num
    _ ≤ (exp (D.logX/4))^2 := pow_le_pow_left₀ (by norm_num) base 2
    _ = _ := by rw [← Real.exp_natCast_mul];congr 1;ring
  exact_mod_cast bound.trans_le D.m_mem.1

lemma gcd_with_coprime_cofactor {T G c : ℕ} (div : G ∣ T) (h : T.Coprime c) :
    T.gcd (G*c)=G := by
  obtain ⟨s,eq⟩ := div
  have sc : s.Coprime c := h.coprime_dvd_left (by rw [eq];exact dvd_mul_left _ _)
  rw [eq,Nat.gcd_mul_left,sc.gcd_eq_one,mul_one]

theorem period_and_exceptional (D : Data params) (i : Fin 9) :
    D.IsExceptional (rationalPrime i) ∧ D.o₀ (rationalPrime i)=1 ∧
      D.returnQuotient (rationalPrime i)=halfPeriod i*cofactor i ∧
      D.returnPairCount (rationalPrime i)=halfPeriod i := by
  obtain ⟨eq,div,c₂,c₃,small⟩ := arithmetic i
  have ho := (order_one_iff_base_dvd_succ (D := D) (inert i)).2
    (show params.q₀ ∣ rationalPrime i+1 from ⟨_,eq⟩)
  have ret : D.returnQuotient (rationalPrime i)=halfPeriod i*cofactor i := by
    rw [returnQuotient,ho,pow_one,eq]
    exact Nat.mul_div_cancel_left _ (by decide : 0<18480)
  have whole : 36 ∣ towerDeg D.towerExp := by
    rw [← (second_return_counts D).2.2]; exact Nat.gcd_dvd_left _ _
  have cop : (towerDeg D.towerExp).Coprime (cofactor i) := (c₃.pow_left _).mul_left (c₂.pow_left _)
  exact ⟨exceptional_of_local_order_one (inert i) ho (small.trans (large_lift_rank D)),ho,ret,
    by rw [returnPairCount,ret,gcd_with_coprime_cofactor (div.trans whole) cop]⟩

end OrbitProbes
end New.Data.CollisionPrimeExample
