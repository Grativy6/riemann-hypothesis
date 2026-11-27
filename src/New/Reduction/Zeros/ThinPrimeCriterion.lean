module

public import New.Reduction.Zeros.DyadicTwistSample
import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import Mathlib.Tactic

/-!
One fixed dyadic sample of an invertible refinement supplies every zero rectangle for the one-sided criterion. The final statement uses the stock Mathlib Riemann hypothesis and the explicit arithmetic hypothesis on just that sample.
-/

@[expose] public section

open Complex DirichletCharacter Filter Nat Set Asymptotics
open scoped Topology
namespace New.TwistSelection

/-- A fixed, explicitly ordered auxiliary-prime set. It selects one invertible
class modulo 314160, then applies the same finite quota in every dyadic block. -/
def seventeenPool : Set ℕ := thin (primeClass (194039 : ZMod 314160))

theorem summable_seventeenPool :
    Summable (weight ∘ (Subtype.val : seventeenPool → ℕ)) := summable_thin _

theorem seventeenPool_no_power_saving {α : ℝ} (hα : α < 1) :
    ¬ (count seventeenPool =O[atTop] fun x : ℕ ↦ (x:ℝ)^α) :=
  thin_no_power_saving (weight_diverges_primeClass
    ((ZMod.isUnit_iff_coprime 194039 314160).2 (by decide))) hα

theorem arithmetic_of_seventeenPool {n : ℕ} (hn : n ∈ seventeenPool) :
    n.Prime ∧ n ≡ 9239 [MOD 18480] ∧ n ≡ 1 [MOD 17] := by
  obtain ⟨hp,hclass⟩ := thin_subset (primeClass (194039 : ZMod 314160)) hn
  have fine := (ZMod.natCast_eq_natCast_iff n 194039 314160).1 hclass
  exact ⟨hp,(fine.of_dvd (by decide : 18480 ∣ 314160)).trans (by decide),
    (fine.of_dvd (by decide : 17 ∣ 314160)).trans (by decide)⟩

/-- Each selected prime and exponent has its own constant and eventual cutoff. -/
def remainderBoundsOn (pool : Set ℕ) : Prop :=
  ∀ d : Primes, (d : ℕ) ∈ pool → ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d 18480 x ≤ A*x^(-1/2+ε)

/-- The explicit prime list with its full collection of exponents. -/
abbrev selectedRemainderBounds := remainderBoundsOn seventeenPool

/-- The smaller fixed list suffices even for every character of the original modulus. -/
theorem LFunction_ne_zero_of_pool {pool : Set ℕ} (sub : pool ⊆ seventeenPool)
    (large : ∀ α : ℝ, α < 1 → ¬ (count pool =O[atTop] fun x : ℕ ↦ (x:ℝ)^α))
    (bounds : remainderBoundsOn pool)
    (χ : DirichletCharacter ℂ 18480) {ρ : ℂ} (h₁ : ρ ≠ 1) (hρ : 1/2 < ρ.re) :
    χ.LFunction ρ ≠ 0 := by
  obtain ⟨β,hβ,hβρ⟩ : ∃ β : ℝ, 1/2<β ∧ β<ρ.re := exists_between hρ
  apply nonvanishing_of_selected_count hβ pool (a := (9239 : ZMod 18480)) ?_ ?_
    (large _ (by linarith)) ?_ χ h₁ hβρ
  · intro n hn
    obtain ⟨hp,hq,_⟩ := arithmetic_of_seventeenPool (sub hn)
    exact ⟨hp,(ZMod.natCast_eq_natCast_iff n 9239 18480).2 hq⟩
  · intro d hd
    have hmod := (ZMod.natCast_eq_natCast_iff d 9239 18480).1 hd
    exact ⟨(hmod.of_dvd (by decide : 8 ∣ 18480)).trans (by decide : 9239 ≡ 7 [MOD 8]),
      Nat.Coprime.symm (hmod.gcd_eq.trans (by decide))⟩
  · intro d hd
    have eq : -(1:ℝ)/2+(β-1/2) = β-1 := by ring
    simpa only [eq] using bounds d hd (β-1/2) (sub_pos.2 hβ)

theorem LFunction_ne_zero_of_seventeenPool (bounds : selectedRemainderBounds)
    (χ : DirichletCharacter ℂ 18480) {ρ : ℂ} (h₁ : ρ ≠ 1) (hρ : 1/2 < ρ.re) :
    χ.LFunction ρ ≠ 0 :=
  LFunction_ne_zero_of_pool (fun _ hn ↦ hn) (fun _ h ↦ seventeenPool_no_power_saving h)
    bounds χ h₁ hρ

/-- The actual Mathlib Riemann hypothesis follows from the stated sparse family
of arithmetic bounds. This module does not import the community one-sided bound. -/
theorem riemannHypothesis_of_pool {pool : Set ℕ} (sub : pool ⊆ seventeenPool)
    (large : ∀ α : ℝ, α < 1 → ¬ (count pool =O[atTop] fun x : ℕ ↦ (x:ℝ)^α))
    (bounds : remainderBoundsOn pool) :
    RiemannHypothesis := by
  apply TauCeti.riemannHypothesis_iff_riemannZeta_ne_zero.mpr
  intro s hs
  obtain rfl | h₁ := eq_or_ne s 1
  · exact riemannZeta_one_ne_zero
  · let χ : DirichletCharacter ℂ 1 := 1
    have clear := LFunction_ne_zero_of_pool sub large bounds
      (χ.changeLevel (by decide : 1 ∣ 18480)) h₁ hs
    rw [LFunction_changeLevel _ χ (Or.inr h₁)] at clear
    simpa only [LFunction_modOne_eq] using (left_ne_zero_of_mul clear)

/-- The fixed finite-weight pool suffices for the stock proposition. -/
theorem riemannHypothesis_of_selected_remainders (bounds : selectedRemainderBounds) :
    RiemannHypothesis :=
  riemannHypothesis_of_pool (fun _ hn ↦ hn) (fun _ h ↦ seventeenPool_no_power_saving h) bounds

end New.TwistSelection
