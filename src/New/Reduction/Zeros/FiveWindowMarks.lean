module

public import New.Reduction.Zeros.PrescribedTwistSigns
public import New.Reduction.Zeros.PrimeWindowPrecision
import Mathlib.Tactic

/-!
# Five freely chosen marks in the original modulus

Each finite assignment can coexist with a clear zero rectangle in the original
modulus. No numerical surrogate for the L-functions enters the construction.
-/

@[expose] public section

open Nat Finset Real ArithmeticFunction
open ArithmeticFunction.vonMangoldt
namespace New.PrimeWindow

/-- All possible visible bases up to the seventh positive step of the 18480 progression. -/
def five : Finset ℕ := {18481,55441,92401,110881,129361}

lemma five_primes (p : ℕ) (hp : p∈five) : p.Prime ∧ p%4=1 ∧ p.Coprime 314160 ∧
    p%18480=1 ∧ p≤129361 := by
  simp only [five,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma two_different_factors {n p r : ℕ} (hp : Nat.Prime p) (hr : Nat.Prime r)
    (different : p ≠ r) (left : p ∣ n) (right : r ∣ n) : ¬ IsPrimePow n := by
  intro power
  obtain ⟨v,j,hv,hj,rfl⟩ := (isPrimePow_nat_iff _).1 power
  have vp := ((Nat.dvd_prime hv).1 (hp.dvd_of_dvd_pow left)).resolve_left hp.ne_one
  have vr := ((Nat.dvd_prime hv).1 (hr.dvd_of_dvd_pow right)).resolve_left hr.ne_one
  exact different (vp.trans vr.symm)

lemma five_class_weight {d : ℕ} [Fact d.Prime] (flag : ℕ → Bool)
    (values : ∀ p∈five, chiK d p = if flag p then -1 else 1) (n : ℕ) (cut : n≤129361) :
    lambdaKResidueClass d 18480 n = if n∈five ∧ flag n then 2*Real.log n else 0 := by
  classical
  by_cases present : n∈five
  · obtain ⟨prime,_,_,cls,_⟩ := five_primes n present
    have residue := (ZMod.natCast_eq_natCast_iff n 1 18480).2 (show n≡1 [MOD 18480] from cls)
    have weight := weight_power (d:=d) (q:=18480) prime (by decide : 0<1)
    simp only [pow_one,Nat.cast_one] at weight residue
    rw [weight,ite_eq_left residue,values n present]
    cases h : flag n <;> simp [present]
    ring
  · rw [ite_eq_right (fun h ↦ present h.1)]
    by_cases cls : (n:ZMod 18480)=1
    · have eq := (ZMod.natCast_eq_natCast_iff n 1 18480).1 (by simpa using cls)
      change n%18480=1%18480 at eq
      simp only [five,Finset.mem_insert,Finset.mem_singleton,not_or] at present
      have bad : n=1 ∨ n=36961 ∨ n=73921 := by omega
      have nonpow : ¬ IsPrimePow n := by
        rcases bad with rfl | rfl | rfl
        · exact not_isPrimePow_one
        · exact two_different_factors (by norm_num1 : Nat.Prime 23) (by norm_num1 : Nat.Prime 1607)
            (by decide) (by decide) (by decide)
        · exact two_different_factors (by norm_num1 : Nat.Prime 29) (by norm_num1 : Nat.Prime 2549)
            (by decide) (by decide) (by decide)
      simp [lambdaKResidueClass,residueClass,Set.indicator,cls,vonMangoldt_apply,nonpow]
    · simp [lambdaKResidueClass,residueClass,Set.indicator,cls]

/-- Every choice of the five marks occurs in the actual refined class, together
with simultaneous nonvanishing on an independently specified height box. -/
theorem all_five_with_clear_box (flag : ℕ → Bool) {β : ℝ} (hβ : 1/2<β)
    (H : ℝ) (bound : ℕ) :
    ∃ d : Primes, bound<(d:ℕ) ∧ (d:ℕ)≡194039 [MOD 314160] ∧
      (∀ n≤129361, lambdaKResidueClass d 18480 n =
        if n∈five ∧ flag n then 2*Real.log n else 0) ∧
      ∀ (χ : DirichletCharacter ℂ 18480) (s : ℂ),
        β≤s.re → |s.im|≤H → entireL (quadTwist χ d) s≠0 := by
  obtain ⟨d,late,cls,values,clear⟩ := prescribed_clear_prime (q:=18480) (m:=314160) (a:=194039)
    (by decide) (by decide) (by decide) (by decide) five
    (fun p hp ↦ ⟨(five_primes p hp).1,(five_primes p hp).2.1,(five_primes p hp).2.2.1⟩) flag hβ H bound
  exact ⟨d,late,cls,five_class_weight flag values,clear⟩

theorem five_integer_reading {d : ℕ} [Fact d.Prime] (flag : ℕ → Bool)
    (values : ∀ p∈five, chiK d p = if flag p then -1 else 1) :
    countCode d 18480 129361 = (∏ p ∈ five.filter (fun p ↦ flag p),p)^2 := by
  classical
  let active := five.filter (fun p ↦ flag p)
  have sub : active ⊆ Finset.Icc 1 129361 := by
    intro p hp
    have good := five_primes p (Finset.mem_filter.1 hp).1
    exact Finset.mem_Icc.2 ⟨good.1.pos,good.2.2.2.2⟩
  have prod_pos : 0< ∏ p ∈ active,p := Finset.prod_pos fun p hp ↦ (five_primes p (Finset.mem_filter.1 hp).1).1.pos
  have pos : 0<countCode d 18480 129361 := Finset.prod_pos fun n _ ↦ pow_pos (Nat.minFac_pos n) _
  have eq : Real.log (countCode d 18480 129361) = Real.log (((∏ p ∈ active,p)^2 : ℕ):ℝ) := by
    rw [log_countCode, Nat.cast_pow,Real.log_pow,Nat.cast_prod,Real.log_prod (fun p h ↦ by
      exact_mod_cast (five_primes p (Finset.mem_filter.1 h).1).1.ne_zero)]
    push_cast
    rw [Finset.mul_sum]
    rw [← Finset.sum_subset sub (fun n hn outside ↦ by
      rw [five_class_weight flag values n (Finset.mem_Icc.1 hn).2]
      exact ite_eq_right (fun h ↦ outside (Finset.mem_filter.2 h)))]
    exact Finset.sum_congr rfl (fun p hp ↦ by
      rw [five_class_weight flag values p (Finset.mem_Icc.1 (sub hp)).2,ite_eq_left (Finset.mem_filter.1 hp)])
  exact_mod_cast Real.log_injOn_pos (show (0:ℝ)<countCode d 18480 129361 by exact_mod_cast pos)
    (show (0:ℝ)<(((∏ p ∈ active,p)^2 : ℕ):ℝ) by exact_mod_cast pow_pos prod_pos 2) eq

end New.PrimeWindow
