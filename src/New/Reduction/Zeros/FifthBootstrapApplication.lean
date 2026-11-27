module

public import New.Reduction.Zeros.FifthBootstrap
import New.Reduction.Zeros.CommunityPowerSamples
import Mathlib.Tactic

/-!
# Applying the original integer estimate on fifth powers

The community's arithmetic enters through its estimate at natural numbers,
specialized immediately to N = n⁵. The conditional criterion lives in a
separate module.
-/

@[expose] public section

open Filter Nat Real
namespace New.TwistSelection

/-- The arithmetic input used by the application consists of the community's
integer estimate restricted to fifth powers of the selected primes' cutoffs. -/
theorem community_fifth_samples (d : Primes) (hd : (d : ℕ) ∈ seventeenPool) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      primeRemainder d 18480 ((n : ℝ) ^ 5) ≤ A * ((n : ℝ) ^ 5) ^ (-1 / 2 + ε) :=
  community_power_samples d hd ε hε (by decide)

/-- This application retains the original arithmetic at integer fifth powers. -/
theorem riemannHypothesis_via_fifth_power_tests : RiemannHypothesis := by
  obtain ⟨K, _, _, _, criterion⟩ := arbitrarily_light_fifth_power_RH (η:= 1 / 1000) (by norm_num)
  exact criterion (fun d hd ↦ community_fifth_samples d hd.1)

end New.TwistSelection
