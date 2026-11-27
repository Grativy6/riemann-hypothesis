module

public import New.Reduction.Zeros.SharedZeros
public import New.Reduction.Zeros.FifthStrip
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Meromorphic.Divisor
import Mathlib.Tactic

/-!
# Canceling the same zeros with their multiplicities

The character products can vanish together. Their logarithmic-derivative
difference then has a removable value. We use its analytic representative in
the contour integral and the values off the zeros in the Dirichlet series.
-/

@[expose] public section

open Complex Real Nat Filter Set Finset Topology MeromorphicOn
open scoped BigOperators
namespace New.PrimeCutoff

/-- At each point strictly right of θ the two products have the same zero order. -/
def matchedOrders (d q : ℕ) [Fact d.Prime] [NeZero q] (θ : ℝ) : Prop :=
  ∀ z : ℂ, θ < z.re →
    (∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL χ) z) =
     ∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL (quadTwist χ d)) z

/-- Analytic representative of the regular part after removing the main pole
from the coefficient series. -/
noncomputable def regularMean (d q : ℕ) [Fact d.Prime] [NeZero q] (s : ℂ) : ℂ :=
  toMeromorphicNFOn (logDerivMean d q) univ s + (q.totient : ℂ)⁻¹

lemma meromorphic_mean (d q : ℕ) [Fact d.Prime] [NeZero q] : Meromorphic (logDerivMean d q) :=
  fun _ ↦ by fun_prop [logDerivMean, logDeriv]

theorem regularMean_analytic {d q : ℕ} [Fact d.Prime] [NeZero q] {θ : ℝ}
    (matchOrd : matchedOrders d q θ) {s : ℂ} (hs : θ < s.re) :
    AnalyticAt ℂ (regularMean d q) s := by
  have e : (∑ χ : DirichletCharacter ℂ q, (analyticOrderNatAt (entireL χ) s : ℂ)) =
      ∑ χ : DirichletCharacter ℂ q, (analyticOrderNatAt (entireL (quadTwist χ d)) s : ℂ) := by
    exact_mod_cast matchOrd s hs
  have h := tendsto_sub_mul_logDerivMean (d := d) (q := q) s
  simp only [Finset.sum_sub_distrib, e, sub_self, zero_div] at h
  exact (analytic_fill_of_zero_residue (meromorphic_mean d q) h).add analyticAt_const

theorem regularMean_series {d q : ℕ} [Fact d.Prime] [NeZero q] (d₂ : d ≠ 2)
    (cop : q.Coprime d) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ ↦ (lambdaKResidueClass d q n : ℂ)) s =
      regularMean d q s + (q.totient : ℂ)⁻¹ / (s - 1) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
  have h₁ : s - 1 ≠ 0 := sub_ne_zero.2 (ne_of_apply_ne re (by simpa using hs.ne'))
  rw [regularMean, TauCeti.toMeromorphicNFOn_apply_of_analyticAt (meromorphic_mean d q)
    (analyticAt_logDerivMean_of_one_le_re d q hs.le), LSeries_lambdaKResidueClass_eq_add_logDerivMean d₂ cop hs]
  field_simp
  ring

noncomputable def familyProduct {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (κ : ι → DirichletCharacter ℂ N) : ℂ → ℂ := ∏ i, entireL (κ i)

lemma familyProduct_analytic {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (κ : ι → DirichletCharacter ℂ N) (z : ℂ) : AnalyticAt ℂ (familyProduct κ) z := by
  unfold familyProduct
  fun_prop

lemma familyProduct_order {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (κ : ι → DirichletCharacter ℂ N) (z : ℂ) :
    analyticOrderNatAt (familyProduct κ) z = ∑ i, analyticOrderNatAt (entireL (κ i)) z := by
  have e : analyticOrderAt (familyProduct κ) z = ((∑ i, analyticOrderNatAt (entireL (κ i)) z : ℕ) : WithTop ℕ) := by
    rw [familyProduct, TauCeti.analyticOrderAt_prod fun i _ ↦ analyticAt_entireL (κ i) z, Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (Nat.cast_analyticOrderNatAt (analyticOrderAt_entireL_ne_top (κ i) z)).symm
  change (analyticOrderAt (familyProduct κ) z).toNat = _
  rw [e]
  exact ENat.toNat_natCast _

lemma familyProduct_logDeriv {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    {κ : ι → DirichletCharacter ℂ N} {z : ℂ} (nz : ∀ i, entireL (κ i) z ≠ 0) :
    logDeriv (familyProduct κ) z = ∑ i, logDeriv (entireL (κ i)) z :=
  logDeriv_prod (fun i _ ↦ nz i) (fun i _ ↦ (analyticAt_entireL (κ i) z).differentiableAt)

lemma family_punctured_nonzero {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (κ : ι → DirichletCharacter ℂ N) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, ∀ i, entireL (κ i) w ≠ 0 := by
  apply Filter.eventually_all.2
  intro i
  have all : AnalyticOnNhd ℂ (entireL (κ i)) univ := fun w _ ↦ analyticAt_entireL _ w
  exact all.eventually_ne_zero_nhdsNE_of_preconnected isPreconnected_univ (mem_univ (1 : ℂ))
      (entireL_ne_zero (κ i) le_rfl) (mem_univ z)

/-- Matching total orders is exactly what allows both local polar sums to be
subtracted on a disk. Individual character zeros may occur on either side. -/
lemma family_divisors_eq {d q : ℕ} [Fact d.Prime] [NeZero q] {θ : ℝ} {U : Set ℂ}
    (matchOrd : matchedOrders d q θ) (inside : ∀ z ∈ U, θ < z.re) :
    divisor (familyProduct (fun χ : DirichletCharacter ℂ q ↦ quadTwist χ d)) U =
    divisor (familyProduct (id : DirichletCharacter ℂ q → _)) U := by
  ext z
  by_cases hz : z ∈ U
  · have div (N : ℕ) [NeZero N] (κ : DirichletCharacter ℂ q → DirichletCharacter ℂ N) :
        divisor (familyProduct κ) U z = (∑ i, analyticOrderNatAt (entireL (κ i)) z : ℕ) := by
      have hm : MeromorphicOn (familyProduct κ) U := fun s _ ↦ (familyProduct_analytic κ s).meromorphicAt
      rw [hm.divisor_eq_analyticOrderNatAt (familyProduct_analytic κ z) hz, familyProduct_order]
    rw [div, div]
    exact_mod_cast (matchOrd z (inside z hz)).symm
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

end New.PrimeCutoff
