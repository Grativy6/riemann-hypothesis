module

public import New.Reduction.Zeros.ThinPrimeCriterion
import New.Reduction.OneSidedBound

/-!
Apply the independently stated reduction to the existing community remainder estimate. This file keeps the source of the hard arithmetic bound explicit.
-/

@[expose] public section

open Nat Filter
open scoped Topology
namespace New.TwistSelection

/-- The published community estimate applies prime by prime to the explicitly
selected set. It supplies the mathematical premise of the independent reduction. -/
theorem community_selectedRemainderBounds : selectedRemainderBounds := by
  intro d hd ε hε
  obtain ⟨_,hclass,_⟩ := arithmetic_of_seventeenPool hd
  exact ⟨128*(18480:ℕ).totient+32,
    eventually_primeRemainder_le_mul_rpow (by decide : 18480 ∣ 18480) hclass hε⟩

theorem riemannHypothesis_via_seventeenPool : RiemannHypothesis :=
  riemannHypothesis_of_selected_remainders community_selectedRemainderBounds

end New.TwistSelection
