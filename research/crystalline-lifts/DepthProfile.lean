import LossOfLifts
import TauCeti.Algebra.Order.BigOperators.Sum.Min
import TauCeti.Algebra.Module.DiscreteValuationRing.ElementaryDivisors

noncomputable section
open Module Submodule IsLocalRing
open scoped Pointwise
namespace Hearthline.RelationLattices

variable {O Γ n : Type*} [CommRing O] [New.DVR O] [Fintype n] [DecidableEq n]
  (Z : Submodule O (Γ → n → O)) [Module.Finite O Z]

/-- A cyclic factor of exponent e in the saturation defect costs min(k,e) at precision k. -/
theorem precision_profile {ι : Type*} [Fintype ι] {e : ι → ℕ}
    (f : defect Z ≃ₗ[O] ∀ i, O ⧸ maximalIdeal O ^ e i) {π : O}
    (hπ : π ≠ 0) (uniformizer : Ideal.span {π} = maximalIdeal O) (k : ℕ) :
    New.relLength (New.obeying (New.relationsOn Z) (New.QuotSpan (π^k)))
      (Z.map (reduction (π^k))) = ∑ i, min k (e i) := by
  rw [length_lost Z (pow_ne_zero k hπ), TauCeti.range_lsmul_eq_smul_top,
      ← Submodule.ideal_span_singleton_smul, ← Ideal.span_singleton_pow, uniformizer]
  exact TauCeti.IsDiscreteValuationRing.length_quotient_pow_maximalIdeal_smul_top f k

/-- The increment at the next precision is the number of exponents that have not yet
been exhausted. The complete sequence identifies the multiset of positive exponents. -/
theorem next_layer {ι : Type*} [Fintype ι] {e : ι → ℕ}
    (f : defect Z ≃ₗ[O] ∀ i, O ⧸ maximalIdeal O ^ e i) {π : O}
    (hπ : π ≠ 0) (uniformizer : Ideal.span {π} = maximalIdeal O) (k : ℕ) :
    New.relLength (New.obeying (New.relationsOn Z) (New.QuotSpan (π^(k+1))))
        (Z.map (reduction (π^(k+1)))) =
      New.relLength (New.obeying (New.relationsOn Z) (New.QuotSpan (π^k)))
        (Z.map (reduction (π^k))) + (Finset.univ.filter (fun i ↦ k < e i)).card := by
  classical
  rw [precision_profile Z f hπ uniformizer, precision_profile Z f hπ uniformizer]
  exact_mod_cast Finset.sum_min_add_one Finset.univ e k

/-- For positive elementary divisors the entire depth profile determines their multiset.
Appending a zero exponent contributes a zero module at every precision. -/
theorem recover_positive_exponents {ι κ : Type*} [Fintype ι] [Fintype κ] {e : ι → ℕ} {e' : κ → ℕ}
    (he : ∀ i, 0 < e i) (he' : ∀ j, 0 < e' j)
    (reads : ∀ k : ℕ, ∑ i, min k (e i) = ∑ j, min k (e' j)) :
    ∃ σ : ι ≃ κ, ∀ i, e i = e' (σ i) :=
  Fintype.exists_equiv_of_forall_sum_min_eq he he' reads

example (k : ℕ) : min k 0 + min k 3 = min k 3 := by simp

example : [0,1,2,3,4].map (fun k : ℕ ↦ min k 1 + min k 3) = [0,2,3,4,4] := by decide

end Hearthline.RelationLattices
