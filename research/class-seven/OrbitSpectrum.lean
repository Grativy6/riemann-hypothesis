import CofinalSeven
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

open Nat ZMod New
open scoped BigOperators
namespace Hearthline.OrbitSpectrum

/-- For an odd prime, the square of a residue that is -1 modulo p makes its first move
away from one at exactly the depth of d+1. -/
private theorem square_depth {p d : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (large : 1 < d)
    (front : p ∣ d + 1) : (d ^ 2 - 1).factorization p = (d + 1).factorization p := by
  have missing : ¬p ∣ d - 1 := fun h ↦ h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    (show p ∣ 2 from (show (d+1)-(d-1) = 2 by omega) ▸ Nat.dvd_sub front h))
  have shape : d ^ 2 - 1 = (d-1) * (d+1) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    rw [show (a+1)^2 = a*(a+1+1)+1 by ring, Nat.add_sub_cancel]
  rw [shape, Nat.factorization_mul (by omega) (Nat.succ_ne_zero d), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd missing, zero_add]

/-- A positive odd prime power reads every return time, including the zero exponent. -/
theorem returns_at_prime_power {p d : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (large : 1 < d)
    (front : p ∣ d + 1) {e : ℕ} (he : e ≠ 0) (n : ℕ) :
    d ^ n ≡ 1 [MOD p ^ e] ↔ 2 * p ^ (e - (d+1).factorization p) ∣ n := by
  have pos : 0 < d := by omega
  have hx : ¬p ∣ d := fun h ↦ hp.not_dvd_one (by simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub front h)
  have nontrivial : (-1 : ZMod p) ≠ 1 := by
    intro same
    have eq : (2 : ZMod p) = 0 := by linear_combination -same
    have div : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast eq)
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 div)
  have root : (d : ZMod p) = -1 := by
    have h := (ZMod.natCast_eq_zero_iff (d + 1) p).2 front
    push_cast at h
    linear_combination h
  have square : 1 < d ^ 2 := Nat.one_lt_pow (by decide) large
  have evenStep (m : ℕ) : p ^ e ∣ (d ^ 2) ^ m - 1 ↔ p ^ (e - (d+1).factorization p) ∣ m := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    have hmpos : 1 < (d ^ 2) ^ m := Nat.one_lt_pow hm square
    have hbase := square_depth hp h2 large front
    have first : p ∣ d ^ 2 - 1 := by
      apply (hp.dvd_iff_one_le_factorization (by omega : d ^ 2 - 1 ≠ 0)).2
      rw [hbase]
      exact (hp.dvd_iff_one_le_factorization (Nat.succ_ne_zero d)).1 front
    have : Fact p.Prime := ⟨hp⟩
    have val := Nat.multiplicity_pow_sub_pow (p := p) (x := d^2) (y := 1)
      (hp.odd_of_ne_two h2) square first (fun h ↦ hx (hp.dvd_of_dvd_pow h)) hm
    simp only [one_pow, Nat.multiplicity_eq_factorization hp, hbase] at val
    rw [hp.pow_dvd_iff_le_factorization (by omega : (d^2)^m - 1 ≠ 0),
      hp.pow_dvd_iff_le_factorization hm]
    omega
  constructor
  · intro ret
    have even : Even n := by
      rcases Nat.even_or_odd n with even | odd
      · exact even
      have atp := (ZMod.natCast_eq_natCast_iff (d ^ n) 1 p).2
        (ret.of_dvd (dvd_pow_self p he))
      push_cast at atp
      rw [root, odd.neg_one_pow] at atp
      exact False.elim (nontrivial atp)
    obtain ⟨m, hm⟩ := even
    have eq : n = 2 * m := by omega
    rw [eq] at ret ⊢
    have sub := (Nat.modEq_iff_dvd' (Nat.succ_le_of_lt (pow_pos pos (2*m)))).1 ret.symm
    rw [pow_mul] at sub
    exact Nat.mul_dvd_mul_left 2 ((evenStep m).1 sub)
  · rintro ⟨c, rfl⟩
    rw [Nat.mul_assoc, pow_mul]
    exact ((Nat.modEq_iff_dvd' (Nat.succ_le_of_lt (pow_pos (pow_pos pos 2) _))).2
      ((evenStep _).2 (dvd_mul_right _ _))).symm

/-- Combining a square-one base with a coprime odd prime power does not add another factor
of two to the period. -/
theorem order_over_base {b p d e : ℕ} (cop : b.Coprime p) (hp : p.Prime) (h2 : p ≠ 2)
    (large : 1 < d) (front : p ∣ d+1) (he : e ≠ 0) (base : d^2 ≡ 1 [MOD b]) :
    orderOf ((d : ℕ) : ZMod (b * p^e)) = 2 * p ^ (e - (d+1).factorization p) := by
  have test (n : ℕ) : ((d : ZMod (b*p^e))^n = 1) ↔ 2*p^(e-(d+1).factorization p) ∣ n := by
    have cast : ((d : ZMod (b*p^e))^n = 1) ↔ d^n ≡ 1 [MOD b*p^e] := by
      simpa only [Nat.cast_pow, Nat.cast_one] using ZMod.natCast_eq_natCast_iff (d^n) 1 (b*p^e)
    rw [cast, ← Nat.modEq_and_modEq_iff_modEq_mul (cop.pow_right e)]
    constructor
    · exact fun h ↦ (returns_at_prime_power hp h2 large front he n).1 h.2
    · intro h
      refine ⟨?_, (returns_at_prime_power hp h2 large front he _).2 h⟩
      obtain ⟨v, hv⟩ := (dvd_mul_right 2 _).trans h
      rw [hv, pow_mul]
      simpa only [one_pow] using base.pow v
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((test _).2 dvd_rfl))
    ((test _).1 (pow_orderOf_eq_one _))


private def address (t : ℕ) : ℕ := 157080 * 17 ^ t - 1
private def modulus (k : ℕ) : ℕ := 314160 * 17 ^ k

private theorem address_succ (t : ℕ) : address t + 1 = 157080 * 17 ^ t := by
  unfold address
  have pos : 0 < 157080 * 17 ^ t := by positivity
  omega

/-- The low class is fixed while the depth of the seventeens may be chosen. -/
private theorem address_low (t : ℕ) : address t ≡ 157079 [MOD 314160] := by
  have odd : Odd (17 ^ t) := (by decide : Odd (17 : ℕ)).pow
  obtain ⟨w, hw⟩ := odd
  have h := address_succ t
  rw [hw] at h
  change address t % 314160 = 157079 % 314160
  omega

private theorem address_unit (k t : ℕ) : (address t).Coprime (modulus k) := by
  have cop : (address t).Coprime (address t + 1) := by simp
  rw [address_succ] at cop
  have half : (address t).Coprime 157080 := cop.of_dvd_right (dvd_mul_right _ _)
  have two := half.of_dvd_right (by decide : 2 ∣ 157080)
  have odd := half.of_dvd_right (by decide : 17 ∣ 157080)
  exact (two.mul_right half).mul_right (odd.pow_right k)

private theorem read_depth {d k j : ℕ} (hj : j ≤ k)
    (cls : d ≡ address (k-j) [MOD modulus k]) :
    k + 1 - (d+1).factorization 17 = j := by
  let t := k - j + 1
  have ht : t ≤ k + 1 := by dsimp only [t]; omega
  have pw : 17 ^ (k+1) ∣ modulus k := by
    unfold modulus
    rw [pow_succ']
    exact Nat.mul_dvd_mul_right (by decide : 17 ∣ 314160) _
  have target : address (k-j) + 1 = 9240 * 17 ^ t := by
    rw [address_succ, show 17 ^ t = 17 * 17^(k-j) from _root_.pow_succ' ..]
    ring
  have eq : d + 1 ≡ 9240 * 17 ^ t [MOD 17 ^ (k+1)] := by
    simpa only [target] using (cls.of_dvd pw).add_right 1
  have lower : t ≤ (d+1).factorization 17 := by
    apply (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 17) (Nat.succ_ne_zero d)).1
    exact (eq.dvd_iff (pow_dvd_pow 17 ht)).2 (dvd_mul_left _ 9240)
  by_cases hj0 : j = 0
  · dsimp only [t] at lower
    omega
  · have ht' : t+1 ≤ k+1 := by dsimp only [t]; omega
    have missing : ¬ 17^(t+1) ∣ 9240 * 17^t := by
      intro h
      have deep := (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 17)
        (Nat.mul_ne_zero (by decide) (pow_ne_zero _ (by decide)))).1 h
      rw [Nat.factorization_mul (by decide : 9240 ≠ 0) (pow_ne_zero _ (by decide : 17 ≠ 0)),
        Finsupp.add_apply, Nat.factorization_pow_self (by decide : Nat.Prime 17),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬17 ∣ 9240), zero_add] at deep
      omega
    have upper : (d+1).factorization 17 ≤ t := by
      by_contra! deep
      apply missing
      exact (eq.dvd_iff (pow_dvd_pow 17 ht')).1
        ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 17) (Nat.succ_ne_zero d)).2 deep)
    dsimp only [t] at lower upper
    omega

/-- In one and the same class modulo 314160, every listed order can be imposed on arbitrarily
large primes having zero-free twists for every character of a separate level and a fixed box. -/
theorem choose_period (k j : ℕ) (hj : j ≤ k) (N : ℕ) [NeZero N] {β : ℝ} (hβ : 1/2 < β)
    (H : ℝ) (B : ℕ) :
    ∃ d : Nat.Primes, B < (d : ℕ) ∧ (d : ℕ) ≡ 157079 [MOD 314160] ∧
      orderOf ((d : ℕ) : ZMod (1680 * 17^(k+1))) = 2 * 17^j ∧ N.Coprime d ∧
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), β ≤ s.re → |s.im| ≤ H →
        entireL (quadTwist χ d) s ≠ 0 := by
  have : NeZero (modulus k) := ⟨Nat.mul_ne_zero (by decide) (pow_ne_zero _ (by decide))⟩
  have low := address_low (k-j)
  have seven : address (k-j) ≡ 7 [MOD 8] :=
    (low.of_dvd (by decide : 8 ∣ 314160)).trans (by decide : 157079 ≡ 7 [MOD 8])
  obtain ⟨d, hB, cls, _, cop, good⟩ := exists_seven_twist_in_class (N := N) (address_unit k (k-j))
    (seven.of_dvd (Nat.gcd_dvd_right _ _)) hβ H B
  have reading : (d : ℕ) ≡ 157079 [MOD 314160] :=
    (cls.of_dvd (dvd_mul_right _ (17^k))).trans low
  have front : 17 ∣ (d : ℕ) + 1 := Nat.modEq_zero_iff_dvd.1
    (((reading.of_dvd (by decide : 17 ∣ 314160)).add_right 1).trans
      (by decide : 157079+1 ≡ 0 [MOD 17]))
  have base : (d : ℕ)^2 ≡ 1 [MOD 1680] :=
    ((reading.of_dvd (by decide : 1680 ∣ 314160)).pow 2).trans (by decide : 157079^2 ≡ 1 [MOD 1680])
  have eq := order_over_base (by decide : Nat.Coprime 1680 17) (by decide : Nat.Prime 17)
    (by decide : (17:ℕ) ≠ 2) d.prop.one_lt front (Nat.succ_ne_zero k) base
  rw [read_depth hj cls] at eq
  exact ⟨d, hB, reading, eq, cop, good⟩

/-- Any prime in the same canonical class has one of exactly these periods at the geometric level. -/
theorem period_in_range (k : ℕ) {d : ℕ} (prime : d.Prime) (cls : d ≡ 157079 [MOD 314160]) :
    ∃ j ≤ k, orderOf (d : ZMod (1680 * 17^(k+1))) = 2 * 17^j := by
  have front : 17 ∣ d+1 := Nat.modEq_zero_iff_dvd.1
    (((cls.of_dvd (by decide : 17 ∣ 314160)).add_right 1).trans (by decide : 157079+1 ≡ 0 [MOD 17]))
  have v := ((by decide : Nat.Prime 17).dvd_iff_one_le_factorization (Nat.succ_ne_zero d)).1 front
  change 1 ≤ (d+1).factorization 17 at v
  exact ⟨k+1-(d+1).factorization 17, by omega, order_over_base (by decide : Nat.Coprime 1680 17) (by decide)
    (by decide) prime.one_lt front (Nat.succ_ne_zero k)
    (((cls.of_dvd (by decide : 1680 ∣ 314160)).pow 2).trans (by decide : 157079^2 ≡ 1 [MOD 1680]))⟩

end Hearthline.OrbitSpectrum
