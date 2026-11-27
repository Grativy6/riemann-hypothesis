module

public import New.Reduction.Zeros.PrimeCutoffRamps
public import New.Reduction.Zeros.ThinPrimeCriterion
public import Lib.CM.FormalGroup.PrimeNotation
import Mathlib.Tactic

/-!
# Arithmetic sources of the bends

The three-reading reconstruction is calibrated by a quadratic character. The
recovered prime-power weight matches the local formal-group exponent rule.
-/

@[expose] public section

open Nat Finset Real ArithmeticFunction
open ArithmeticFunction.vonMangoldt
namespace New.PrimeCutoff

/-- At a positive prime power, the recovered bend is exactly twice its formal-group
place weight times log p, provided that the exponent and congruence both qualify. -/
theorem weight_at_prime_power {d q p e : ℕ} [Fact d.Prime] [Fact p.Prime] (he : 0<e) :
    lambdaKResidueClass d q (p^e) =
      if ((p^e : ℕ) : ZMod q) = 1 ∧ e ∈ positivePartnerExponents d p then
        2 * Real.log p * piPrimeValuation d p else 0 := by
  classical
  have hp := (inferInstance : Fact p.Prime).out
  have chi : (chiK d ((p^e : ℕ):ZMod d) : ℝ) = (chiK d p : ℝ)^e := by simp
  by_cases hclass : ((p^e : ℕ) : ZMod q) = 1
  · have coeff : residueClass (1:ZMod q) (p^e) = Real.log p := by
      simp [residueClass,Set.indicator,hclass,vonMangoldt_apply_pow he.ne',vonMangoldt_apply_prime hp]
    rw [lambdaKResidueClass,coeff,chi]
    have val := one_sub_chiK_pow_div_two d p e
    by_cases partner : e ∈ positivePartnerExponents d p
    · simp only [hclass,partner,and_self,ite_true] at val ⊢
      linear_combination (2*Real.log p)*val
    · simp only [hclass,partner,and_false,ite_false] at val ⊢
      linear_combination (2*Real.log p)*val
  · have not_in : (p : ZMod q)^e ≠ 1 := by simpa only [Nat.cast_pow] using hclass
    simp [lambdaKResidueClass, residueClass, Set.indicator,not_in]

/-- At an even power an unramified prime always drops out of the quadratic weight. -/
theorem even_power_of_other_prime {d q p j : ℕ} [Fact d.Prime] [Fact p.Prime]
    (different : p ≠ d) (hj : 0<j) : lambdaKResidueClass d q (p^(2*j))=0 := by
  rw [weight_at_prime_power (by omega : 0<2*j)]
  have no : 2*j ∉ positivePartnerExponents d p := by
    simp [mem_positivePartnerExponents, mem_partnerExponents, different]
  simp [no]

/-- If d² is 1 in the cutoff modulus, every positive even power of d carries log d. -/
theorem even_ramified_weight {d q j : ℕ} [Fact d.Prime]
    (square : (d:ZMod q)^2=1) (hj : 0<j) : lambdaKResidueClass d q (d^(2*j))=Real.log d := by
  rw [weight_at_prime_power (by omega : 0<2*j)]
  have residue : ((d^(2*j):ℕ):ZMod q)=1 := by simp [pow_mul,square]
  simp [residue,mem_positivePartnerExponents,mem_partnerExponents,piPrimeValuation,hj]
  ring

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The first active bend for d=7, q=8 occurs at 17. -/
theorem first_bend_seventeen :
    (∀ n : ℕ, n<17 → lambdaKResidueClass 7 8 n=0) ∧ lambdaKResidueClass 7 8 17=2*Real.log 17 := by
  constructor
  · intro n hn
    by_cases hc : (n : ZMod 8) = 1
    · have eq := (ZMod.natCast_eq_natCast_iff n 1 8).1 (by simpa only [Nat.cast_one] using hc)
      change n%8=1%8 at eq
      obtain rfl | rfl : n=1 ∨ n=9 := by omega
      · simp [lambdaKResidueClass, residueClass, Set.indicator]
      · let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
        exact even_power_of_other_prime (d:=7) (q:=8) (p:=3) (j:=1) (by decide) (by decide)
    · simp [lambdaKResidueClass, residueClass, Set.indicator, hc]
  · have hc : ((17:ℕ):ZMod 8) = 1 := by decide
    have coeff : residueClass (1:ZMod 8) 17 = Real.log 17 := by
      unfold residueClass
      rw [Set.indicator_of_mem hc,vonMangoldt_apply_prime (by decide : Nat.Prime 17)]
      norm_num
    have chi : chiK 7 (17:ℕ) = -1 := by
      rw [chiK_eq_legendreSym,jacobiSym.legendreSym.to_jacobiSym]; norm_num
    change residueClass (1:ZMod 8) 17*(1-(chiK 7 (17:ℕ):ℝ))=_
    rw [coeff,chi]
    push_cast
    ring

theorem bend_at_49 : lambdaKResidueClass 7 8 49 = Real.log 7 :=
  even_ramified_weight (d:=7) (q:=8) (j:=1) (by decide) (by decide)

/-- At every auxiliary prime retained in the original frame, its own positive
even powers survive with weight log d. Every other prime's even powers vanish. -/
theorem retained_ramified_bend (d : Nat.Primes) (hd : (d:ℕ)∈TwistSelection.seventeenPool)
    {j : ℕ} (hj : 0<j) : lambdaKResidueClass d 18480 ((d:ℕ)^(2*j))=Real.log d := by
  obtain ⟨_,res,_⟩ := TwistSelection.arithmetic_of_seventeenPool hd
  refine even_ramified_weight ?_ hj
  rw [(ZMod.natCast_eq_natCast_iff d 9239 18480).2 res]
  decide

end New.PrimeCutoff
