module

public import New.Reduction.Zeros.PrimePowerBends
import Mathlib.Tactic

/-!
# A finite integer for the drift-corrected cutoff difference

After clearing the rational endpoint denominators, the observed change is the
logarithm of a positive integer. Its prime divisors are the visible bases.
-/

@[expose] public section

open Nat Real Finset ArithmeticFunction
open ArithmeticFunction.vonMangoldt
namespace New.PrimeWindow

/-- A permitted prime power contributes the natural digit 0, 1 or 2 times
the logarithm of its underlying prime. -/
noncomputable def digit (d q n : ℕ) [Fact d.Prime] : ℕ :=
  if (n : ZMod q)=1 ∧ IsPrimePow n then (1-chiK d n).toNat else 0

lemma weight_digit (d q n : ℕ) [Fact d.Prime] :
    lambdaKResidueClass d q n = (digit d q n:ℝ) * Real.log n.minFac := by
  classical
  have hnn : (0:ℤ) ≤ 1-chiK d n := by exact_mod_cast (one_sub_chiK_mem_Icc d n).1
  have cast : (((1-chiK d n).toNat:ℕ):ℝ) = 1-(chiK d n:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnn
  by_cases cls : (n : ZMod q)=1 <;> by_cases power : IsPrimePow n <;>
    simp [digit,lambdaKResidueClass,residueClass,Set.indicator,cls,power,vonMangoldt_apply,
      cast,mul_comm]

/-- A positive integer multiple of the coefficient of λ(n) in the difference
between two positive integer cutoffs. The multiple is (b!)². -/
def ticket (a b n : ℕ) : ℕ := (b-max a n)*(b ! / max a n)*(b ! / b)

lemma cast_ticket {a b n : ℕ} (ha : 1≤a) (hab : a<b) (hn : n≤b) :
    (ticket a b n : ℝ) = (b !:ℝ)^2*(1/((max a n:ℕ):ℝ)-1/(b:ℝ)) := by
  have hp : 0<max a n := lt_of_lt_of_le ha (le_max_left _ _)
  have hb : 0<b := by omega
  have le := max_le hab.le hn
  have d₁ := Nat.dvd_factorial hp le
  have d₂ := Nat.dvd_factorial hb (le_refl b)
  have nr : ((max a n:ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  have br : (b:ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  simp only [ticket,Nat.cast_mul,Nat.cast_sub le,Nat.cast_div d₁ nr,Nat.cast_div d₂ br]
  field

lemma ticket_pos {a b n : ℕ} (ha : 1≤a) (hab : a<b) (hn : n<b) : 0<ticket a b n := by
  have hp : 0<max a n := (show 0<a from ha).trans_le (le_max_left _ _)
  have hb : 0<b := by omega
  have h := max_lt hab hn
  exact Nat.mul_pos (Nat.mul_pos (Nat.sub_pos_of_lt h)
    (Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos b) (Nat.dvd_factorial hp h.le)) hp))
    (Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos b) (Nat.dvd_factorial hb le_rfl)) hb)

/-- The positive integer whose logarithm is the cleared, drift-corrected reading.
A prime divides it exactly when some visible power of that prime contributes. -/
noncomputable def code (d q a b : ℕ) [Fact d.Prime] : ℕ :=
  ∏ n ∈ Finset.Icc 1 b, n.minFac ^ (digit d q n * ticket a b n)

lemma code_pos (d q a b : ℕ) [Fact d.Prime] : 0<code d q a b :=
  Finset.prod_pos fun n _ ↦ pow_pos (Nat.minFac_pos n) _

lemma window_kernel {a b n : ℕ} (ha : 1≤a) (hn : 1≤n) (hnb : n≤b) :
    (1/(n:ℝ)-1/b)⁺ - (1/(n:ℝ)-1/a)⁺ = 1/((max a n:ℕ):ℝ)-1/(b:ℝ) := by
  have na : (0:ℝ)<a := by exact_mod_cast ha
  have nn : (0:ℝ)<n := by exact_mod_cast hn
  have sn : (1:ℝ)/b ≤ 1/n := one_div_le_one_div_of_le nn (by exact_mod_cast hnb)
  rw [posPart_of_nonneg (sub_nonneg.2 sn)]
  obtain h | h := le_total n a
  · rw [max_eq_left h,posPart_of_nonneg (sub_nonneg.2 (one_div_le_one_div_of_le nn (show (n:ℝ)≤a by exact_mod_cast h)))]
    ring
  · rw [max_eq_right h,posPart_of_nonpos (sub_nonpos.2 (one_div_le_one_div_of_le na (show (a:ℝ)≤n by exact_mod_cast h))),sub_zero]

theorem increment_eq_window {d q a b : ℕ} [Fact d.Prime] [NeZero q] (ha : 1≤a) (hab : a<b) :
    primeRemainder d q b - primeRemainder d q a + Real.log ((b:ℝ)/a)/q.totient =
      ∑ n ∈ Finset.Icc 1 b, lambdaKResidueClass d q n*(1/((max a n:ℕ):ℝ)-1/(b:ℝ)) := by
  have na : (0:ℝ)<a := by exact_mod_cast ha
  have nb : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  rw [primeRemainder_eq_sum_posPart nb (show ⌊(b:ℝ)⌋₊≤b by simp),
    primeRemainder_eq_sum_posPart na (show ⌊(a:ℝ)⌋₊≤b by simpa using hab.le),
    Real.log_div nb.ne' na.ne',sub_div]

  have eq : (∑ n ∈ Finset.Icc 1 b, lambdaKResidueClass d q n*(1/(n:ℝ)-1/b)⁺) -
      (∑ n ∈ Finset.Icc 1 b, lambdaKResidueClass d q n*(1/(n:ℝ)-1/a)⁺) =
      ∑ n ∈ Finset.Icc 1 b, lambdaKResidueClass d q n*(1/((max a n:ℕ):ℝ)-1/(b:ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← mul_sub,window_kernel ha (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2]
  linarith only [eq]

theorem log_code {d q a b : ℕ} [Fact d.Prime] [NeZero q] (ha : 1≤a) (hab : a<b) :
    Real.log (code d q a b) =
      (b !:ℝ)^2*(primeRemainder d q b-primeRemainder d q a+Real.log ((b:ℝ)/a)/q.totient) := by
  rw [code,Nat.cast_prod,Real.log_prod (fun n _ ↦ by positivity [Nat.minFac_pos n]),
    increment_eq_window ha hab,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.cast_pow,Real.log_pow,Nat.cast_mul,cast_ticket ha hab (Finset.mem_Icc.1 hn).2,weight_digit]
  ring


lemma digit_positive_iff {d q n : ℕ} [Fact d.Prime] :
    0<digit d q n ↔ 0<lambdaKResidueClass d q n := by
  by_cases h : n=1
  · subst n
    simp [digit,lambdaKResidueClass,residueClass,Set.indicator]
  have hp := (Nat.minFac_prime h).one_lt
  rw [weight_digit,mul_pos_iff_of_pos_right (Real.log_pos (by exact_mod_cast hp))]
  exact_mod_cast Iff.rfl

theorem prime_dvd_code_iff {d q a b p : ℕ} [Fact d.Prime] (hp : Nat.Prime p) (ha : 1≤a) (hab : a<b) :
    p ∣ code d q a b ↔ ∃ n : ℕ, n<b ∧ n.minFac=p ∧ 0<lambdaKResidueClass d q n := by
  classical
  rw [code,hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨n,hn,div⟩
    have exp_ne : digit d q n * ticket a b n ≠ 0 := by
      intro h
      exact hp.not_dvd_one (by simpa [h] using div)
    have pos := (digit_positive_iff (d:=d) (q:=q) (n:=n)).1
      (Nat.pos_of_ne_zero (left_ne_zero_of_mul exp_ne))
    have n₁ : n≠1 := by rintro rfl; simp [lambdaKResidueClass,residueClass,Set.indicator] at pos
    have base := ((Nat.dvd_prime (Nat.minFac_prime n₁)).1 (hp.dvd_of_dvd_pow div)).resolve_left hp.ne_one
    have below : n<b := by
      apply lt_of_le_of_ne (Finset.mem_Icc.1 hn).2
      rintro rfl
      simp [ticket,max_eq_right hab.le] at exp_ne
    exact ⟨n,below,base.symm,pos⟩
  · rintro ⟨n,below,base,pos⟩
    have hn : 0<n := by
      obtain rfl | good := Nat.eq_zero_or_pos n
      · simp [lambdaKResidueClass,residueClass,Set.indicator] at pos
      · exact good
    refine ⟨n,Finset.mem_Icc.2 ⟨hn,below.le⟩,?_⟩
    rw [base]
    exact dvd_pow_self p (Nat.mul_pos (digit_positive_iff.2 pos) (ticket_pos ha hab below)).ne'

theorem code_eq_iff_reading_eq {d r q a b : ℕ} [Fact d.Prime] [Fact r.Prime] [NeZero q]
    (ha : 1≤a) (hab : a<b) :
    code d q a b = code r q a b ↔
      primeRemainder d q b-primeRemainder d q a = primeRemainder r q b-primeRemainder r q a := by
  have divisor : ((b !:ℝ)^2)≠0 := by positivity
  constructor
  · intro he
    have logs := congrArg (fun k : ℕ ↦ Real.log (k:ℝ)) he
    change Real.log (code d q a b) = Real.log (code r q a b) at logs
    rw [log_code ha hab,log_code ha hab] at logs
    exact add_right_cancel (mul_left_cancel₀ divisor logs)
  · intro he
    have logs : Real.log (code d q a b) = Real.log (code r q a b) := by rw [log_code ha hab,log_code ha hab,he]
    exact_mod_cast Real.log_injOn_pos (show (0:ℝ)<code d q a b by exact_mod_cast code_pos d q a b)
      (show (0:ℝ)<code r q a b by exact_mod_cast code_pos r q a b) logs



end New.PrimeWindow
