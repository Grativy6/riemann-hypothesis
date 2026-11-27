module

public import New.Reduction.Zeros.SampledPool
import New.Reduction.Zeros.CommunityPowerSamples
import Mathlib.Tactic

/-!
# Let each measuring prime supply its own degree

At auxiliary prime d, use only nᵈ. All uses of the original integer estimate
are confined to this application and its input module.
-/

@[expose] public section

open Nat Real Filter
namespace New.TwistSelection

/-- Feed the community's integer estimate into the personal power grids nᵈ. -/
theorem riemannHypothesis_via_prime_degrees : RiemannHypothesis := by
  obtain ⟨K, _, _, _, _, criterion⟩ := light_prime_own_degree_RH (η := 1 / 1000) (by norm_num)
  exact criterion (fun d hd ε ep ↦ community_power_samples d hd.1 ε ep d.property.pos)

end New.TwistSelection
