module

public import New.Reduction.Zeros.SmallPrimeBudget
import New.Reduction.OneSidedBound
import Mathlib.Tactic

/-!
# Restricting the community integer estimate to one chosen degree

The estimate on all natural numbers specializes directly to N=nᵏ for any
positive k. The degree is chosen after the auxiliary prime and the exponent.
-/

@[expose] public section

open Nat Real Filter
namespace New.TwistSelection

theorem community_power_samples (d : Primes) (hd : (d : ℕ) ∈ seventeenPool) (ε : ℝ) (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      primeRemainder d 18480 ((n : ℝ) ^ k) ≤ A * ((n : ℝ) ^ k) ^ (-1 / 2 + ε) := by
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
  have seq : Tendsto (fun n : ℕ ↦ n ^ k) atTop atTop := tendsto_pow_atTop hk.ne'
  let C : ℝ := 64 * (18480 : ℕ).totient + 3
  refine ⟨C,?_⟩
  filter_upwards [seq.eventually (eventually_primeRemainder_natCast_le P δp δs),
    eventually_ge_atTop (1 : ℕ)] with n bound hn
  have at_n : primeRemainder d 18480 ((n : ℝ) ^ k) ≤ C * ((n : ℝ) ^ k) ^ (-1 / 2 + 6 * δ) := by
    simpa only [P, C, Nat.cast_pow] using bound
  exact at_n.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (one_le_pow₀ (by exact_mod_cast hn)) (by linarith only [slack])) (by dsimp [C]; positivity))

end New.TwistSelection
