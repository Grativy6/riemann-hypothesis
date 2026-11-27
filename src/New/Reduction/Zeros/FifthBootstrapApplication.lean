module

public import New.Reduction.Zeros.FifthBootstrap
import New.Reduction.OneSidedBound
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
      primeRemainder d 18480 ((n : ℝ) ^ 5) ≤ A * ((n : ℝ) ^ 5) ^ (-1 / 2 + ε) := by
  have hm := (arithmetic_of_seventeenPool hd).2.1
  let P : Parameters :=
    { q₀ := 18480
      d := d
      dvd_q₀ := dvd_rfl
      d_prime := d.property
      q₀_dvd_and_not_dvd := dvd_two_mul_succ_and_not_dvd_succ (by decide : 0 < 18480)
        (by decide) (show (d : ℕ) ≡ 18480 / 2 - 1 [MOD 18480] from hm) }
  let δ := min (1 / 200 : ℝ) (ε / 6)
  have δp : 0 < δ := lt_min (by norm_num) (by positivity)
  have δs : δ < 1 / 100 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have slack : 6 * δ ≤ ε := by dsimp [δ]; linarith [min_le_right (1 / 200 : ℝ) (ε / 6)]
  have seq : Tendsto (fun n : ℕ ↦ n ^ 5) atTop atTop := tendsto_pow_atTop (by decide : 5 ≠ 0)
  let C : ℝ := 64 * (18480 : ℕ).totient + 3
  refine ⟨C,?_⟩
  filter_upwards [seq.eventually (eventually_primeRemainder_natCast_le P δp δs),
    eventually_ge_atTop (1 : ℕ)] with n bound hn
  have at_n : primeRemainder d 18480 ((n : ℝ) ^ 5) ≤ C * ((n : ℝ) ^ 5) ^ (-1 / 2 + 6 * δ) := by
    simpa only [P, C, Nat.cast_pow] using bound
  exact at_n.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (one_le_pow₀ (by exact_mod_cast hn)) (by linarith only [slack])) (by dsimp [C]; positivity))

/-- This application retains the original arithmetic at integer fifth powers. -/
theorem riemannHypothesis_via_fifth_power_tests : RiemannHypothesis := by
  obtain ⟨K, _, _, _, criterion⟩ := arbitrarily_light_fifth_power_RH (η:= 1 / 1000) (by norm_num)
  exact criterion (fun d hd ↦ community_fifth_samples d hd.1)

end New.TwistSelection
