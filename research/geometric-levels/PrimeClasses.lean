import New.Reduction.Data.FieldsAndPlaces
import New.Derivatives.Field.PrimeDecomposition
import Mathlib.Tactic

open Nat Finset New ZMod NumberTheorySymbols
namespace Hearthline.AdmissibleExamples

theorem eleven_table {d : ℕ} (h4 : d % 4 = 3) :
    J(11 | d) = 1 ↔ d % 11 = 2 ∨ d % 11 = 6 ∨ d % 11 = 7 ∨ d % 11 = 8 ∨ d % 11 = 10 := by
  have hodd : Odd d := Nat.odd_iff.2 (by omega)
  have lookup : ∀ t : Fin 44, t.val % 4 = 3 →
      (J(11 | t.val) = 1 ↔ t.val % 11 = 2 ∨ t.val % 11 = 6 ∨ t.val % 11 = 7 ∨
        t.val % 11 = 8 ∨ t.val % 11 = 10) := by decide +kernel
  change J(((11 : ℕ) : ℤ) | d) = 1 ↔ _
  rw [jacobiSym.mod_right' 11 hodd]
  have hmod : d % 11 = (d % 44) % 11 := by omega
  rw [hmod]
  exact lookup ⟨d % 44, Nat.mod_lt _ (by decide)⟩ (by dsimp; omega)

theorem two_trials : Nat.Prime 839 ∧ Nat.Prime 7559 ∧ 839 % 1680 = 839 ∧ 7559 % 1680 = 839 ∧
    J(11 | 839) = -1 ∧ J(11 | 7559) = 1 := by
  refine ⟨by norm_num1, by norm_num1, by decide, by decide, ?_, ?_⟩
  · change J(((11 : ℕ) : ℤ) | 839) = -1
    rw [jacobiSym.mod_right' 11 (by decide : Odd 839)]
    decide +kernel
  · exact (eleven_table (by decide : 7559 % 4 = 3)).2 (by decide)

theorem good_7559 : GeometricPrimeConditions 1680 7559 := by
  refine ⟨?_, ⟨16, by decide, by decide, by decide⟩, two_trials.2.2.2.2.2⟩
  intro p hp hd
  have hmem := Nat.mem_primeFactors.2 ⟨hp, hd, (by decide : (1680 : ℕ) ≠ 0)⟩
  have h : ∀ p ∈ (1680 : ℕ).primeFactors, 4 * p ∣ 7559 + 1 := by decide +kernel
  exact h p hmem

theorem bad_839 : ¬ GeometricPrimeConditions 1680 839 := by
  intro h
  have := h.eleven_splits
  exact (by decide +kernel : J(11 | 839) ≠ 1) this

def minimalParameters : Parameters where
  q₀ := 1680
  d := 7559
  dvd_q₀ := dvd_rfl
  d_prime := two_trials.2.1
  prime_conditions := good_7559

/-- The old geometric modulus with the input's repeated factors, the minimal levels and
their distinct cyclotomic degrees at the trivial conductor. -/
example : Nat.totient 18480 = 3840 ∧ Nat.totient 1680 = 384 ∧
    twistSearchModulus 1680 = 18480 ∧ twistSearchResidue 1680 = 9239 := by decide +kernel

/-- A nonnested pair. The selected prime has a 34-step orbit rather than an involution. -/
def longParameters : Parameters where
  q₀ := 485520
  d := 1099559
  dvd_q₀ := by decide
  d_prime := by norm_num1
  prime_conditions := geometricPrimeConditions_of_search (by decide) (by decide +kernel)

example : Nat.lcm 1680 (17^2) = 485520 ∧ twistSearchModulus 485520 = 314160 ∧
    twistSearchResidue 485520 = 157079 ∧ ¬ 485520 ∣ 314160 ∧ ¬ 314160 ∣ 485520 ∧
    ¬ 485520 ∣ 2 * (1099559 + 1) ∧ 1099559 ^ 2 % 485520 = 228481 := by decide +kernel

example (n : ℕ) : (1099559 : ZMod 485520) ^ n ≠ -1 :=
  longParameters.d_pow_ne_neg_one n

example : orderOf (1099559 : ZMod 485520) = 34 := by
  apply orderOf_eq_of_pow_and_pow_div_prime
  · decide +kernel
  · intro p hp h34
    have hmem := Nat.mem_primeFactors.2 ⟨hp, h34, (by decide : (34 : ℕ) ≠ 0)⟩
    have vals : ∀ p ∈ (34 : ℕ).primeFactors, (1099559 : ZMod 485520) ^ (34 / p) ≠ 1 := by
      decide +kernel
    exact vals p hmem

end Hearthline.AdmissibleExamples
