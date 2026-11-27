module

public import New.Reduction.Zeros.PowerGridCriterion
import New.Reduction.Zeros.ThinPrimeCommunityApplication
import Mathlib.Tactic

/-!
# Applying the community estimate to fourth-power observations
-/

@[expose] public section

namespace New.TwistSelection

/-- Apply the published arithmetic bound to the fourth-power tests only. -/
theorem riemannHypothesis_via_fourth_power_tests : RiemannHypothesis := by
  obtain ⟨K,_,_,_,criterion⟩ := arbitrarily_light_fourth_power_RH (η := 1/1000) (by norm_num)
  apply criterion
  apply (remainderBoundsOn_iff_powerBoundsOn (by intro d hd; exact ⟨by decide, le_rfl⟩)).1
  intro d hd
  exact community_selectedRemainderBounds d hd.1

end New.TwistSelection
