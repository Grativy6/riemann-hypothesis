module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The arithmetic conditions for the geometric prime

A prime factor of the cyclotomic level must divide the norm (d + 1) / 4. One divisor of the
level must distinguish d from -1 while annihilating twice d + 1. The prime eleven must split.
The progression used to supply these conditions only needs the odd prime support of the level.
-/

@[expose] public section

open Nat Finset NumberTheorySymbols

namespace New

/-- Requirements on the auxiliary prime d at a geometric level q. -/
structure GeometricPrimeConditions (q d : ℕ) : Prop where
  /-- Every prime of the level divides the norm of (1 + √-d) / 2. -/
  norm_divisibility : ∀ p : ℕ, p.Prime → p ∣ q → 4 * p ∣ d + 1
  /-- Some divisor of the level detects a nonzero element of additive order two. -/
  separating_divisor : ∃ m : ℕ, m ∣ q ∧ m ∣ 2 * (d + 1) ∧ ¬ m ∣ d + 1
  /-- The fixed small-prime exclusion needs the splitting sign at eleven. -/
  eleven_splits : J(11 | d) = 1

/-- A single divisor can exclude -1 from every power, even when the order modulo the
full level exceeds two. Only oddness of the base is used. -/
theorem pow_ne_neg_one_of_separating_divisor {d q : ℕ} (odd : Odd d)
    (witness : ∃ m : ℕ, m ∣ q ∧ m ∣ 2 * (d + 1) ∧ ¬m ∣ d + 1) (n : ℕ) :
    (d : ZMod q) ^ n ≠ -1 := by
  obtain ⟨m, hm, h_half, h_ne_half⟩ := witness
  have on_divisor (k : ℕ) : (d : ZMod m) ^ k ≠ -1 := by
    obtain ⟨w, hw⟩ := odd
    have hd : (d : ZMod m) = 2 * w + 1 := by simp [hw]
    have h_zero : 2 * (d + 1 : ZMod m) = 0 :=
      mod_cast (ZMod.natCast_eq_zero_iff _ _).2 h_half
    have h_ne : (d + 1 : ZMod m) ≠ 0 :=
      mod_cast (ZMod.natCast_eq_zero_iff _ _).not.2 h_ne_half
    have h_sq : (d : ZMod m) ^ 2 = 1 := by linear_combination (d + 1) * hd + w * h_zero
    induction k using Nat.twoStepInduction with
    | zero =>
      -- If `1 = -1` then `2 = 0`, so `d + 1 = 2 (w + 1) = 0`.
      exact fun h_one ↦ h_ne (by linear_combination hd + (w + 1) * h_one)
    | one => exact fun h_one ↦ h_ne (by linear_combination h_one)
    | more n ih _ => simpa [pow_add, h_sq] using ih
  intro h
  apply on_divisor n
  simpa only [map_pow, map_neg, map_one, map_natCast] using congrArg (ZMod.castHom hm (ZMod m)) h

private lemma eleven_splits_of_dvd {d : ℕ} (h : 44 ∣ d + 1) : J(11 | d) = 1 := by
  have odd : Odd d := Nat.odd_iff.2 (by omega)
  change J(((11 : ℕ) : ℤ) | d) = 1
  rw [jacobiSym.mod_right' 11 odd, show d % (4 * 11) = 43 by omega]
  decide +kernel

/-- The original level and half-turn give all three conditions. -/
theorem geometricPrimeConditions_of_half_turn {q d : ℕ} (hq : 18480 ∣ q)
    (h : q ∣ 2 * (d + 1) ∧ ¬q ∣ d + 1) : GeometricPrimeConditions q d := by
  have h8 : 8 ∣ d + 1 := by
    have : 16 ∣ 2 * (d + 1) := (by decide : 16 ∣ 18480).trans (hq.trans h.1)
    omega
  have norm (p : ℕ) (hp : p.Prime) (hpq : p ∣ q) : 4 * p ∣ d + 1 := by
    have hdiv := hpq.trans h.1
    rw [show 2 * (d + 1) = 2 ^ 3 * ((d + 1) / 4) by omega] at hdiv
    have hodd : p ∣ (d + 1) / 4 := by
      rcases hp.dvd_mul.1 hdiv with h2 | hn
      · exact (hp.dvd_of_dvd_pow h2).trans (by omega)
      · exact hn
    exact Nat.mul_dvd_of_dvd_div (by omega) hodd
  exact ⟨norm, ⟨q, dvd_rfl, h⟩, eleven_splits_of_dvd (norm 11 (by decide)
    ((by decide : 11 ∣ 18480).trans hq))⟩

/-- Each odd prime dividing 11q occurs once. -/
def oddPrimeProduct (q : ℕ) : ℕ := ∏ p ∈ (11 * q).primeFactors.erase 2, p

/-- The simple search progression takes d = 8R - 1 modulo 16R. -/
def twistSearchModulus (q : ℕ) : ℕ := 16 * oddPrimeProduct q

/-- The residue halfway around the search modulus, less one. -/
def twistSearchResidue (q : ℕ) : ℕ := 8 * oddPrimeProduct q - 1

lemma odd_oddPrimeProduct (q : ℕ) : Odd (oddPrimeProduct q) := by
  unfold oddPrimeProduct
  apply Finset.prod_induction id (fun n : ℕ ↦ Odd n) (fun _ _ ↦ Odd.mul) odd_one
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (mem_of_mem_erase hp)).odd_of_ne_two (ne_of_mem_erase hp)

instance (q : ℕ) : NeZero (twistSearchModulus q) :=
  ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) (odd_oddPrimeProduct q).pos)⟩

theorem twistSearchResidue_coprime (q : ℕ) :
    (twistSearchResidue q).Coprime (twistSearchModulus q) := by
  have hpos := (odd_oddPrimeProduct q).pos
  have hodd : Odd (twistSearchResidue q) := Nat.odd_iff.2 (by unfold twistSearchResidue; omega)
  rw [show twistSearchModulus q = 2 * (twistSearchResidue q + 1) by
    unfold twistSearchModulus twistSearchResidue; omega]
  exact hodd.coprime_two_right.mul_right (by simp)

private lemma dvd_oddPrimeProduct {p q : ℕ} (hq : q ≠ 0) (hp : p.Prime) (h2 : p ≠ 2)
    (h : p ∣ 11 * q) : p ∣ oddPrimeProduct q := by
  exact Finset.dvd_prod_of_mem id (Finset.mem_erase.2 ⟨h2,
    Nat.mem_primeFactors.2 ⟨hp, h, Nat.mul_ne_zero (by decide) hq⟩⟩)

/-- The eight-fold midpoint of the search progression has every required norm divisor,
is distinguished from zero modulo sixteen and splits at eleven. -/
theorem geometricPrimeConditions_of_search {q d : ℕ} [NeZero q] (hq : 1680 ∣ q)
    (hd : d ≡ twistSearchResidue q [MOD twistSearchModulus q]) : GeometricPrimeConditions q d := by
  let R := oddPrimeProduct q
  have hodd : Odd R := odd_oddPrimeProduct q
  have hclass : d + 1 ≡ 8 * R [MOD 16 * R] := by
    have eq : twistSearchResidue q + 1 = 8 * R := by
      have := hodd.pos; unfold twistSearchResidue; dsimp only [R] at *; omega
    simpa only [twistSearchModulus, eq] using hd.add_right 1
  have half : 8 * R ∣ d + 1 := by
    apply Nat.modEq_zero_iff_dvd.1
    have div : 8 * R ∣ 16 * R := ⟨2, by ring⟩
    exact (hclass.of_dvd div).trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)
  have h16 : d + 1 ≡ 8 [MOD 16] := by
    have hsmall := hclass.of_dvd (dvd_mul_right 16 R)
    rcases hodd with ⟨v, hv⟩
    change (d + 1) % 16 = 8 % 16
    change (d + 1) % 16 = (8 * R) % 16 at hsmall
    omega
  have mult (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hdiv : p ∣ 11 * q) : 4 * p ∣ d + 1 :=
    (Nat.mul_dvd_mul (by decide : 4 ∣ 8) (dvd_oddPrimeProduct (NeZero.ne q) hp h2 hdiv)).trans half
  refine ⟨?_, ⟨16, (by decide : 16 ∣ 1680).trans hq, ?_, ?_⟩, ?_⟩
  · intro p hp hpq
    rcases eq_or_ne p 2 with rfl | h2
    · change (d + 1) % 16 = 8 % 16 at h16
      omega
    · exact mult p hp h2 (hpq.trans (dvd_mul_left q 11))
  · change (d + 1) % 16 = 8 % 16 at h16
    omega
  · change (d + 1) % 16 = 8 % 16 at h16
    omega
  · exact eleven_splits_of_dvd (mult 11 (by decide) (by decide) (dvd_mul_right 11 q))

end New
