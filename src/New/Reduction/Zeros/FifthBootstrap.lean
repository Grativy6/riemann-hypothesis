module

public import New.Reduction.Zeros.FifthGridCoarse
public import New.Reduction.Zeros.FifthTwistCounts
import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import Mathlib.Tactic

/-!
# Recovering the count from the fifth-power samples

First exclude untwisted zeros strictly to the right of 3/5. To test a point
farther left, choose one prime whose twists avoid its closed height box. At
that same prime the coarse multiplicity comparison excludes all twisted zeros
to the right of 3/5, even outside the box. The sharp counting theorem can now
supply the local fifth-cell bound at the prime actually used in the last step.
-/

@[expose] public section

open Nat Real Complex Set Filter Finset Asymptotics DirichletCharacter
namespace New.TwistSelection

/-- With every base order zero, real-axis clearance and a coarse one-sided bound
at one prime propagate nonvanishing to all heights for that prime's twists. -/
theorem clear_twists_of_coarse {q d : ℕ} [NeZero q] [Fact d.Prime] {θ A : ℝ}
    (pos : 0 < θ) (h8 : d % 8 = 7) (cop : q.Coprime d)
    (remainder : ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ A * x ^ (θ - 1))
    (base : ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), θ < s.re → entireL χ s ≠ 0)
    (axis : ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), θ < t → t < 1 → entireL (quadTwist χ d) t ≠ 0)
    (χ : DirichletCharacter ℂ q) (z : ℂ) (hz : θ < z.re) : entireL (quadTwist χ d) z ≠ 0 := by
  have eq := sum_entireL_orders_eq_twisted_of_primeRemainder_le h8 cop pos remainder
    (fun t ht ht₁ ↦ by
      rw [Finset.sum_eq_zero fun ψ _ ↦ (analyticOrderNatAt_entireL_eq_zero_iff _ _).2 (axis ψ t ht ht₁)]
      exact Nat.zero_le _) hz
  have zeroBase : (∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL ψ) z) = 0 :=
    Finset.sum_eq_zero fun ψ _ ↦ (analyticOrderNatAt_entireL_eq_zero_iff _ _).2 (base ψ z hz)
  exact (analyticOrderNatAt_entireL_eq_zero_iff _ _).1
    (Finset.sum_eq_zero_iff.1 (eq.symm.trans zeroBase) χ (Finset.mem_univ _))

/-- The sampled hypotheses on an admissible pool suffice throughout the open half-plane.
The prime chosen for the final point may depend on the point. -/
theorem LFunction_ne_zero_of_fifth_pool {q : ℕ} [NeZero q] (pool : Set ℕ) {a : ZMod q}
    (classmem : ∀ n ∈ pool, n.Prime ∧ (n : ZMod q) = a)
    (admissible : ∀ d : Primes, ((d : ℕ) : ZMod q) = a → (d : ℕ) % 8 = 7 ∧ q.Coprime d)
    (large : ∀ α : ℝ, α < 1 → ¬ (count pool =O[atTop] fun x : ℕ ↦ (x : ℝ) ^ α))
    (samples : ∀ d : Primes, (d : ℕ) ∈ pool → ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      primeRemainder d q ((n : ℝ) ^ 5) ≤ A * ((n : ℝ) ^ 5) ^ (-1 / 2 + ε))
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (h₁ : ρ ≠ 1) (hρ : 1 / 2 < ρ.re) :
    χ.LFunction ρ ≠ 0 := by
  have coarse (d : Primes) (hd : (d : ℕ) ∈ pool) :
      ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ C * x ^ ((3 / 5 : ℝ) - 1) := by
    obtain ⟨A, hA⟩ := samples d hd (1 / 10) (by norm_num)
    rw [show -(1 : ℝ) / 2 + 1 / 10 = -(2 / 5) by norm_num] at hA
    simpa only [show (3 / 5 : ℝ) - 1= -(2 / 5) by norm_num] using PrimeCutoff.real_two_fifths hA

  -- The first pass can select a different prime for each point in the coarse half-plane.
  have base (ψ : DirichletCharacter ℂ q) (s : ℂ) (hs : 3 / 5 < s.re) : entireL ψ s ≠ 0 := by
    obtain rfl | ne := eq_or_ne s 1
    · exact entireL_ne_zero _ le_rfl
    · apply (entireL_ne_zero_iff ψ ne).2
      exact nonvanishing_of_selected_count (β:= 3 / 5) (by norm_num) pool classmem admissible
        (large _ (by norm_num)) coarse ψ ne hs

  -- Now fix a target and one prime. The rest of the argument keeps that prime.
  obtain ⟨β, hβ, hβ'⟩ := exists_between (lt_min hρ (by norm_num : (1 / 2 : ℝ) < 3 / 5))
  have bρ := lt_of_lt_of_le hβ' (min_le_left _ _)
  have b₃ := lt_of_lt_of_le hβ' (min_le_right _ _)
  obtain ⟨d, hd, box⟩ := exists_clear_prime_of_count hβ pool classmem admissible
    (large _ (by linarith)) |ρ.im|
  obtain ⟨h8, cop⟩ := admissible d (classmem d hd).2
  have axis (ψ : DirichletCharacter ℂ q) (t : ℝ) (h : β ≤ t) :
      entireL (quadTwist ψ d) t ≠ 0 := box ψ t h (by simp)
  obtain ⟨C, hC⟩ := coarse d hd
  have twists := clear_twists_of_coarse (by norm_num : (0 : ℝ) < 3 / 5) h8 cop hC base
    (fun ψ t ht _ ↦ axis ψ t (b₃.trans ht).le)

  -- Global clearance at this prime supplies the missing count inside each gap.
  obtain ⟨B, hB⟩ := PrimeCutoff.count_of_clear_families (by omega : (d : ℕ) ≠ 2) cop base twists
  have counts := PrimeCutoff.local_fifths_of_count hB
  obtain ⟨A, hA⟩ := PrimeCutoff.real_of_fifths_and_counts counts (samples d hd) (β - 1 / 2) (sub_pos.2 hβ)
  rw [show -(1 : ℝ) / 2 + (β - 1 / 2) = β - 1 by ring] at hA
  have orders := sum_entireL_orders_eq_twisted_of_primeRemainder_le h8 cop (by linarith : 0 < β) hA
    (fun t ht _ ↦ by
      rw [Finset.sum_eq_zero fun ψ _ ↦ (analyticOrderNatAt_entireL_eq_zero_iff _ _).2 (axis ψ t ht.le)]
      exact Nat.zero_le _) bρ
  have zeroTwists : (∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL (quadTwist ψ d)) ρ) = 0 :=
    Finset.sum_eq_zero fun ψ _ ↦ (analyticOrderNatAt_entireL_eq_zero_iff _ _).2 (box ψ ρ bρ.le le_rfl)
  exact (entireL_ne_zero_iff χ h₁).1 ((analyticOrderNatAt_entireL_eq_zero_iff _ _).1
    (Finset.sum_eq_zero_iff.1 (orders.trans zeroTwists) χ (Finset.mem_univ _)))

/-- A single tail of arbitrarily small positive logarithmic weight works with
fifth-power samples alone. Each auxiliary prime and exponent owns its own cutoff. -/
theorem arbitrarily_light_fifth_power_RH {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, Summable (weight ∘ (Subtype.val : after seventeenPool K → ℕ)) ∧
      0 < (∑' d : after seventeenPool K, weight d) ∧
      (∑' d : after seventeenPool K, weight d) < η ∧
      (powerBoundsOn (fun _ ↦ 5) (after seventeenPool K) → RiemannHypothesis) := by
  obtain ⟨K, sums, cap, large⟩ := arbitrarily_small_budget hη
  refine ⟨K, sums, log_weight_pos (tail_nonempty K) (fun _ hd ↦ (arithmetic_of_seventeenPool hd.1).1) sums,
    cap,?_⟩
  intro samples
  apply TauCeti.riemannHypothesis_iff_riemannZeta_ne_zero.mpr
  intro s hs
  obtain rfl | h₁ := eq_or_ne s 1
  · exact riemannZeta_one_ne_zero
  · let χ : DirichletCharacter ℂ 1 := 1
    have clear := LFunction_ne_zero_of_fifth_pool (after seventeenPool K) (a := (9239 : ZMod 18480))
      (fun n hn ↦ ⟨(arithmetic_of_seventeenPool hn.1).1,
        (ZMod.natCast_eq_natCast_iff n 9239 18480).2 (arithmetic_of_seventeenPool hn.1).2.1⟩)
      (fun d hd ↦ by
        have hmod := (ZMod.natCast_eq_natCast_iff d 9239 18480).1 hd
        exact ⟨(hmod.of_dvd (by decide : 8 ∣ 18480)).trans (by decide : 9239 ≡ 7 [MOD 8]),
          Nat.Coprime.symm (hmod.gcd_eq.trans (by decide))⟩)
      large samples (χ.changeLevel (by decide : 1 ∣ 18480)) h₁ hs
    rw [LFunction_changeLevel _ χ (Or.inr h₁)] at clear
    simpa only [LFunction_modOne_eq] using (left_ne_zero_of_mul clear)

end New.TwistSelection
