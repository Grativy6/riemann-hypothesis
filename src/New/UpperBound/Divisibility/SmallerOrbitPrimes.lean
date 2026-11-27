module

public import New.UpperBound.Divisibility.NextHalfTurn
import Mathlib.Tactic

/-!
# Four exceptional primes of local order fifteen

On every admissible tower the primes 67679, 72959, 82799 and 97919 have half-periods
18, 48, 9 and 72. Their complete local orders and rank conditions are checked here.
-/

@[expose] public section
open Finset Real NumberField
namespace New.Data.CollisionPrimeExample

/-- Smaller order-fifteen primes. The second leaves the 72-board at a period of 96, while
the fourth has period 144. The other two replicate the 18- and 36-period decoders. -/
def smallerPrime : Fin 4 → ℕ := ![67679,72959,82799,97919]
def smallerG : Fin 4 → ℕ := ![18,48,9,72]

instance smaller_prime (i : Fin 4) : Fact (smallerPrime i).Prime := by
  constructor;fin_cases i <;> norm_num [smallerPrime]

lemma small_probe_facts (D : Data params) (i : Fin 4) :
    D.IsExceptional (smallerPrime i) ∧ D.o₀ (smallerPrime i)=15 ∧
      D.returnPairCount (smallerPrime i)=smallerG i := by
  let p := smallerPrime i
  have : Fact (Nat.Prime 9239) := ⟨by norm_num1⟩
  have hi : chiK params.d p = -1 := by
    change chiK 9239 (smallerPrime i) = -1
    rw [chiK_eq_legendreSym,jacobiSym.legendreSym.to_jacobiSym]
    fin_cases i <;> norm_num [smallerPrime]
  have ho : D.o₀ p=15 := by
    unfold o₀
    rw [← orderOf_units,placeClass_neg_prime_val (D := D) (p := p) hi dvd_rfl]
    change orderOf (-(p:ZMod 18480))=15
    apply (orderOf_eq_iff (by decide : 0<15)).2
    constructor
    · fin_cases i <;> decide
    · intro a ha hp
      fin_cases i <;> interval_cases a <;> decide
  have upper : p≤97919 := (by decide : ∀ j,smallerPrime j≤97919) i
  have p_real : (p:ℝ)≤exp 628 := calc
    _ ≤ 97919 := by exact_mod_cast upper
    _ ≤ (314:ℝ)^2 := by norm_num
    _ ≤ (exp 314)^2 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (314:ℝ)]) 2
    _ = exp (314+314:ℝ) := by rw [Real.exp_add,pow_two]
    _ = _ := by norm_num
  have m_power : p^14<D.m := by
    have low : (8800:ℝ)<D.logX/2 := by
      linarith [D.mul_log_logB_le_logX,D.constantBound_le,(le_constantBound (P := params)).1]
    have h : (p:ℝ)^14 < exp (D.logX/2) := calc
      _ ≤ (exp 628)^14 := pow_le_pow_left₀ (by positivity) p_real 14
      _ = exp (14*628:ℝ) := (Real.exp_natCast_mul 14 628).symm
      _ < _ := Real.exp_lt_exp.2 (by linarith)
    exact_mod_cast h.trans_le D.m_mem.1
  have M : p+1 < D.m := by have := OrbitProbes.large_lift_rank D; omega
  have ex : D.IsExceptional p := by
    refine ⟨hi,?_,by rw [ho];decide,?_⟩
    · rintro (a|a)
      · have prime : p.Prime := (smaller_prime i).out
        have := Nat.le_of_dvd (Nat.sub_pos_of_lt prime.one_lt) a
        omega
      · exact (not_le_of_gt M) (Nat.le_of_dvd (Nat.succ_pos _) a)
    · rw [ho,ceilLogLifts]
      exact (Nat.lt_clog_iff_pow_lt (smaller_prime i).out.one_lt).2 m_power
  let q := (p^15+1)/18480
  have ret : D.returnQuotient p=q := by rw [returnQuotient,ho];rfl
  have split : q=smallerG i*(q/smallerG i) := by fin_cases i <;> decide
  have c₂ : Nat.Coprime 2 (q/smallerG i) := by fin_cases i <;> decide
  have c₃ : Nat.Coprime 3 (q/smallerG i) := by fin_cases i <;> decide
  obtain ⟨e,_,hs⟩ := D.exists_m_eq_two_pow
  have dvd144 : 144 ∣ towerDeg D.towerExp := Nat.mul_dvd_mul
    (pow_dvd_pow 3 (show 2 ≤ Nat.log 3 D.towerExp+5 by omega))
    (pow_dvd_pow 2 (show 4 ≤ D.towerExp by omega))
  have g : smallerG i ∣ towerDeg D.towerExp :=
    ((by decide : ∀ a : Fin 4, smallerG a ∣ 144) i).trans dvd144
  have cop : (towerDeg D.towerExp).Coprime (q/smallerG i) := (c₃.pow_left _).mul_left (c₂.pow_left _)
  refine ⟨ex,ho,?_⟩
  change (towerDeg D.towerExp).gcd (D.returnQuotient p)=smallerG i
  rw [ret]
  calc (towerDeg D.towerExp).gcd q = (towerDeg D.towerExp).gcd (smallerG i*(q/smallerG i)) :=
        congrArg _ split
    _ = _ := OrbitProbes.gcd_with_coprime_cofactor g cop

end New.Data.CollisionPrimeExample
