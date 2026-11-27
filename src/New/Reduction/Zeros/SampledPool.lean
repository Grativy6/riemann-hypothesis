module

public import New.Reduction.Zeros.SampledOrders
public import New.Reduction.Zeros.PowerMesh
public import New.Reduction.Zeros.SmallPrimeBudget
import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import Mathlib.Tactic

/-!
# The height box can choose its own sampling grid

At a target ρ choose a prime with a clear finite box, then keep its modulus,
sample mesh and constants fixed throughout the one-prime comparison.
-/

@[expose] public section

open Complex Nat Real Filter Set Finset Asymptotics DirichletCharacter
namespace New.TwistSelection

/-- Each prime and exponent may have its own positive power saving in the
sample distance. There is no uniform lower bound on that saving. -/
theorem nonvanishing_of_nearby {q : ℕ} [NeZero q] (pool : Set ℕ) {a : ZMod q}
    (classmem : ∀ n ∈ pool, n.Prime ∧ (n : ZMod q) = a)
    (admissible : ∀ d : Primes, ((d : ℕ) : ZMod q) = a → (d : ℕ) % 8 = 7 ∧ q.Coprime d)
    (large : ∀ α : ℝ, α < 1 → ¬ (count pool =O[atTop] fun x : ℕ ↦ (x : ℝ) ^ α))
    (observed : ∀ d : Primes, (d : ℕ) ∈ pool → ∀ β : ℝ, 1 / 2 < β → β < 1 →
      ∃ δ > 0, PrimeCutoff.nearbyUpper d q β δ)
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (ne : ρ ≠ 1) (right : 1 / 2 < ρ.re) :
    χ.LFunction ρ ≠ 0 := by
  obtain ⟨β, hβ, upper⟩ := exists_between (lt_min right (by norm_num : (1 / 2 : ℝ) < 1))
  have bρ := lt_of_lt_of_le upper (min_le_left _ _)
  have b₁ := lt_of_lt_of_le upper (min_le_right _ _)
  obtain ⟨d, hd, box⟩ := exists_clear_prime_of_count hβ pool classmem admissible (large _ (by linarith)) |ρ.im|
  obtain ⟨h8, cop⟩ := admissible d (classmem d hd).2
  obtain ⟨δ, δp, hδ⟩ := observed d hd β hβ b₁
  have axis (t : ℝ) (ht : β < t) :
      (∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL (quadTwist ψ d)) t) = 0 :=
    Finset.sum_eq_zero fun ψ _ ↦ (analyticOrderNatAt_entireL_eq_zero_iff _ _).2 (box ψ t ht.le (by simp))
  have ord := PrimeCutoff.matched_of_nearby h8 cop hβ b₁ δp hδ (fun t ht _ ↦ (axis t ht) ▸ Nat.zero_le _) ρ bρ
  have ztw : (∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL (quadTwist ψ d)) ρ) = 0 :=
    Finset.sum_eq_zero fun ψ _ ↦ (analyticOrderNatAt_entireL_eq_zero_iff _ _).2 (box ψ ρ bρ.le le_rfl)
  exact (entireL_ne_zero_iff χ ne).1 ((analyticOrderNatAt_entireL_eq_zero_iff _ _).1
    (Finset.sum_eq_zero_iff.1 (ord.trans ztw) χ (Finset.mem_univ _)))

/-- Every auxiliary prime may select its own integer power for every requested
exponent. The numerical tail is chosen before the degree assignment. -/
theorem light_prime_arbitrary_powers {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, Summable (weight ∘ (Subtype.val : after seventeenPool K → ℕ)) ∧
      0 < (∑' d : after seventeenPool K, weight d) ∧
      (∑' d : after seventeenPool K, weight d) < η ∧
      ∀ k : ℕ → ℝ → ℕ,
        (∀ d : Primes, (d : ℕ) ∈ after seventeenPool K → ∀ ε : ℝ, 0 < ε → 0 < k d ε) →
        (∀ d : Primes, (d : ℕ) ∈ after seventeenPool K → ∀ ε : ℝ, 0 < ε →
          ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
            primeRemainder d 18480 ((n : ℝ) ^ (k d ε)) ≤ A * ((n : ℝ) ^ (k d ε)) ^ (-1 / 2 + ε)) →
        RiemannHypothesis := by
  obtain ⟨K, sums, cap, large⟩ := arbitrarily_small_budget hη
  refine ⟨K, sums, log_weight_pos (tail_nonempty K) (fun _ h ↦ (arithmetic_of_seventeenPool h.1).1) sums,
    cap,?_⟩
  intro k degrees samples
  apply TauCeti.riemannHypothesis_iff_riemannZeta_ne_zero.mpr
  intro s hs
  obtain rfl | h₁ := eq_or_ne s 1
  · exact riemannZeta_one_ne_zero
  · let χ : DirichletCharacter ℂ 1 := 1
    have obs (d : Primes) (hd : (d : ℕ) ∈ after seventeenPool K) (β : ℝ) (hβ : 1 / 2 < β) (_ : β < 1) :
        ∃ δ > 0, PrimeCutoff.nearbyUpper d 18480 β δ := by
      let ε := β - 1 / 2
      have ep : 0 < ε := sub_pos.2 hβ
      have kp := degrees d hd ε ep
      obtain ⟨A, hA⟩ := samples d hd ε ep
      rw [show -(1 : ℝ) / 2 + ε = β - 1 by dsimp [ε]; ring] at hA
      exact ⟨_, one_div_pos.2 (Nat.cast_pos.2 kp), PrimeCutoff.nearby_of_powers kp hA⟩
    have clear := nonvanishing_of_nearby (after seventeenPool K) (a := (9239 : ZMod 18480))
      (fun n hn ↦ ⟨(arithmetic_of_seventeenPool hn.1).1,
        (ZMod.natCast_eq_natCast_iff n 9239 18480).2 (arithmetic_of_seventeenPool hn.1).2.1⟩)
      (fun d hd ↦ by
        have hmod := (ZMod.natCast_eq_natCast_iff d 9239 18480).1 hd
        exact ⟨(hmod.of_dvd (by decide : 8 ∣ 18480)).trans (by decide : 9239 ≡ 7 [MOD 8]),
          Nat.Coprime.symm (hmod.gcd_eq.trans (by decide))⟩)
      large obs (χ.changeLevel (by decide : 1 ∣ 18480)) h₁ hs
    rw [LFunction_changeLevel _ χ (Or.inr h₁)] at clear
    simpa only [LFunction_modOne_eq] using (left_ne_zero_of_mul clear)

/-- Each auxiliary prime d can serve as the degree of its own test, even though
the retained list contains arbitrarily large primes. -/
theorem light_prime_own_degree_RH {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, Summable (weight ∘ (Subtype.val : after seventeenPool K → ℕ)) ∧
      0 < (∑' d : after seventeenPool K, weight d) ∧
      (∑' d : after seventeenPool K, weight d) < η ∧
      (∀ T : ℕ, ∃ d : Primes, (d : ℕ) ∈ after seventeenPool K ∧ T < (d : ℕ)) ∧
      ((∀ d : Primes, (d : ℕ) ∈ after seventeenPool K → ∀ ε : ℝ, 0 < ε →
        ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, primeRemainder d 18480 ((n : ℝ) ^ (d : ℕ)) ≤
          A * ((n : ℝ) ^ (d : ℕ)) ^ (-1 / 2 + ε)) → RiemannHypothesis) := by
  obtain ⟨K, sums, pos, cap, criterion⟩ := light_prime_arbitrary_powers hη
  refine ⟨K, sums, pos, cap,?_, criterion (fun d _ ↦ d) (fun d _ _ _ ↦ d.property.pos)⟩
  intro T
  obtain ⟨n, hn⟩ := tail_nonempty (max K (T + 1))
  exact ⟨⟨n,(arithmetic_of_seventeenPool hn.1).1⟩, ⟨hn.1,(le_max_left _ _).trans hn.2⟩,
    (Nat.lt_succ_self T).trans_le ((le_max_right _ _).trans hn.2)⟩

end New.TwistSelection
