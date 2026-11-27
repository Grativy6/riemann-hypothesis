module

public import New.Reduction.Zeros.PrimeWindowCode
import Mathlib.Tactic

/-!
# Decoding a quadratic prime prefix

For the admissible moduli and auxiliary primes, the possible ramified and
unramified visible base primes are separated by their residue modulo eight.
This makes the support of an integer code sufficient to decode the whole prefix.
-/

@[expose] public section

open Nat Real Set Finset ArithmeticFunction
open ArithmeticFunction.vonMangoldt
namespace New.PrimeWindow

lemma weight_power {d q p j : ℕ} [Fact d.Prime] (hp : Nat.Prime p) (hj : 0<j) :
    lambdaKResidueClass d q (p^j) =
      if ((p^j:ℕ):ZMod q)=1 then Real.log p*(1-(chiK d p:ℝ)^j) else 0 := by
  classical
  by_cases hc : ((p^j:ℕ):ZMod q)=1
  · have coeff : residueClass (1:ZMod q) (p^j)=Real.log p := by
      simp [residueClass,Set.indicator,hc,vonMangoldt_apply_pow hj.ne',vonMangoldt_apply_prime hp]
    rw [lambdaKResidueClass,coeff,ite_eq_left hc]
    simp
  · have hc' : (p:ZMod q)^j≠1 := by simpa only [Nat.cast_pow] using hc
    simp [lambdaKResidueClass,residueClass,Set.indicator,hc']

lemma visible_is_power {d q n : ℕ} [Fact d.Prime] (seen : 0<lambdaKResidueClass d q n) :
    ∃ j : ℕ, 0<j ∧ n.minFac^j=n := by
  have pp : IsPrimePow n := by
    by_contra h
    simp [lambdaKResidueClass,residueClass,Set.indicator,vonMangoldt_apply,h] at seen
  obtain ⟨p,j,hp,hj,rfl⟩ := (isPrimePow_nat_iff _).1 pp
  exact ⟨j,hj,by rw [Nat.pow_minFac hj.ne',hp.minFac_eq]⟩

lemma even_of_seven_class {p j q : ℕ} (hq : 8∣q) (hp : p%8=7) (cls : ((p^j:ℕ):ZMod q)=1) :
    Even j := by
  obtain e | o := j.even_or_odd
  · exact e
  · have modq := (ZMod.natCast_eq_natCast_iff (p^j) 1 q).1 (by simpa using cls)
    have mod8 := (ZMod.natCast_eq_natCast_iff (p^j) 1 8).2 (modq.of_dvd hq)
    have minus : (p : ZMod 8) = -1 :=
      ((ZMod.natCast_eq_natCast_iff p 7 8).2 (show p ≡ 7 [MOD 8] from hp)).trans (by decide)
    rw [Nat.cast_pow,minus,o.neg_one_pow,Nat.cast_one] at mod8
    exact False.elim ((by decide : (-1:ZMod 8)≠1) mod8)

/-- A visible base that is 7 mod 8 is the auxiliary prime itself. Every other
visible base is an unramified quadratic nonresidue. -/
lemma visible_base_cases {d q a b p : ℕ} [Fact d.Prime] (hp : Nat.Prime p)
    (hq : 8∣q) (ha : 1≤a) (hab : a<b) (div : p ∣ code d q a b) :
    p=d ∨ (p%8≠7 ∧ chiK d p = -1) := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨n,_,fac,seen⟩ := (prime_dvd_code_iff hp ha hab).1 div
  obtain ⟨j,hj,eq⟩ := visible_is_power seen
  rw [fac] at eq
  rw [← eq] at seen
  obtain ⟨ram,_⟩ | ⟨other,split | inert⟩ := chiK_cases d p
  · exact Or.inl ram
  · rw [weight_power hp hj,split] at seen
    split at seen <;> simp at seen
  · apply Or.inr
    refine ⟨fun seven ↦ ?_,inert⟩
    have cls : ((p^j:ℕ):ZMod q)=1 := by
      by_contra h
      rw [weight_power hp hj,ite_eq_right h] at seen
      exact (lt_irrefl _ seen)
    obtain ⟨l,eqj⟩ := even_of_seven_class hq seven cls
    have pair : j=2*l := by omega
    rw [pair,PrimeCutoff.even_power_of_other_prime other (by omega : 0<l)] at seen
    exact lt_irrefl _ seen

/-- Decode each visible prime power using only the distinct prime factors of the
window code, the public cutoff modulus, and the exponent being queried. -/
theorem recover_power {d q a b p j : ℕ} [Fact d.Prime]
    (hq : 8∣q) (hd : d%8=7) (ha : 1≤a) (hab : a<b) (hp : Nat.Prime p)
    (hj : 0<j) (below : p^j<b) :
    lambdaKResidueClass d q (p^j) =
      if p ∣ code d q a b ∧ ((p^j:ℕ):ZMod q)=1 then
        if p%8=7 then Real.log p else if Odd j then 2*Real.log p else 0
      else 0 := by
  classical
  by_cases marked : p∣code d q a b
  · by_cases cls : ((p^j:ℕ):ZMod q)=1
    · rw [ite_eq_left ⟨marked,cls⟩,weight_power hp hj,ite_eq_left cls]
      obtain rfl | ⟨unram,neg⟩ := visible_base_cases hp hq ha hab marked
      · simp [hd,chiK_self,hj.ne']
      · rw [ite_eq_right unram,neg]
        obtain even | odd := j.even_or_odd
        · simp [Nat.not_odd_iff_even.2 even,even.neg_one_pow]
        · simp [odd,odd.neg_one_pow];ring
    · rw [weight_power hp hj,ite_eq_right cls,ite_eq_right (fun h ↦ cls h.2)]
  · rw [ite_eq_right (fun h ↦ marked h.1)]
    apply le_antisymm _ (lambdaKResidueClass_nonneg d q _)
    by_contra! pos
    exact marked ((prime_dvd_code_iff hp ha hab).2 ⟨p^j,below,
      by rw [Nat.pow_minFac hj.ne',hp.minFac_eq],pos⟩)

theorem increment_eq_iff_prefix_eq {d r q a b : ℕ} [Fact d.Prime] [Fact r.Prime] [NeZero q]
    (hq : 8∣q) (hd : d%8=7) (hr : r%8=7) (ha : 1≤a) (hab : a<b) :
    primeRemainder d q b - primeRemainder d q a = primeRemainder r q b - primeRemainder r q a ↔
      ∀ n : ℕ, n<b → lambdaKResidueClass d q n = lambdaKResidueClass r q n := by
  classical
  constructor
  · intro eq n hn
    have same := (code_eq_iff_reading_eq ha hab).2 eq
    by_cases power : IsPrimePow n
    · obtain ⟨p,j,hp,hj,rfl⟩ := (isPrimePow_nat_iff n).1 power
      rw [recover_power hq hd ha hab hp hj hn,recover_power hq hr ha hab hp hj hn,same]
    · simp [lambdaKResidueClass,residueClass,Set.indicator,vonMangoldt_apply,power]
  · intro pair
    apply add_right_cancel (b := Real.log ((b:ℝ)/a)/q.totient)
    rw [increment_eq_window ha hab,increment_eq_window ha hab]
    apply Finset.sum_congr rfl
    intro n hn
    obtain below | eq := (Finset.mem_Icc.1 hn).2.lt_or_eq
    · rw [pair n below]
    · subst n;simp [max_eq_right hab.le]

theorem identify_auxiliary {d r q a b : ℕ} [Fact d.Prime] [Fact r.Prime] [NeZero q]
    (hq : 8∣q) (hd : d%8=7) (hr : r%8=7) (ha : 1≤a) (hab : a<b)
    (res : (d:ZMod q)^2=1) (visible : d^2<b)
    (same : primeRemainder d q b-primeRemainder d q a = primeRemainder r q b-primeRemainder r q a) :
    d=r := by
  obtain eq := (increment_eq_iff_prefix_eq hq hd hr ha hab).1 same (d^2) visible
  by_contra distinct
  have first := PrimeCutoff.even_ramified_weight (d:=d) (q:=q) (j:=1) res (by decide)
  have other := PrimeCutoff.even_power_of_other_prime (d:=r) (q:=q) (j:=1) distinct (by decide)
  simp only [mul_one] at first other
  rw [first,other] at eq
  exact (Real.log_pos (by exact_mod_cast (inferInstance : Fact d.Prime).out.one_lt)).ne' eq

end New.PrimeWindow
