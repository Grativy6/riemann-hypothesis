import LossOfLifts
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

noncomputable section
open Module LinearMap Submodule Ideal
namespace Hearthline.RelationLattices

variable {O Γ n : Type*} [CommRing O] [New.DVR O] [Fintype n] [DecidableEq n]
  (Z : Submodule O (Γ → n → O)) [Module.Finite O Z]

/-- The whole set of solutions at any one proper nonzero modulus detects whether Z
was saturated. This compares two submodules of readings, not just a single sample. -/
theorem all_lift_iff_saturated {a : O} (ha : a ≠ 0) (hn : ¬IsUnit a) :
    Z.map (reduction a) = New.obeying (New.relationsOn Z) (New.QuotSpan a) ↔
      Z = saturation Z := by
  rw [← read_saturation Z ha]
  refine ⟨fun eq ↦ (le_saturation Z).antisymm ?_, fun h ↦ congrArg _ h⟩
  have : Module.Finite O (saturation Z) := finite_saturation Z
  have small : Ideal.span {a} ≤ Ring.jacobson O := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal, Ideal.span_singleton_le_iff_mem]
    exact hn
  apply Submodule.le_of_le_smul_of_le_jacobson (Module.Finite.iff_fg.1 inferInstance) small
  intro z hz
  have mem : reduction a z ∈ Z.map (reduction a) := eq ▸ ⟨z, hz, rfl⟩
  obtain ⟨v, hv, equal⟩ := mem
  have zero : reduction a (z-v) = 0 := by rw [map_sub, equal, sub_self]
  have divides (g : Γ) (j : n) : a ∣ (z-v) g j :=
    (Ideal.Quotient.eq_zero_iff_dvd a _).1 (congrFun (congrFun zero g) j)
  choose w hw using divides
  have rem : z-v = a • w := funext fun g ↦ funext (hw g)
  have sw := divide_in_saturation ha w (rem ▸ (saturation Z).sub_mem hz (le_saturation Z hv))
  exact Submodule.mem_sup.2 ⟨v, hv, a • w,
    Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton a)) sw, by rw [← rem]; abel⟩

variable (O) in
/-- Multiplying every integral reading by one nonzero scalar preserves all the homogeneous
relations of the full one-coordinate lattice. Reduction at that scalar wipes out its whole image. -/
theorem scaled_single_reading (a : O) (ha : a ≠ 0) :
    let W := (lsmul O (Unit → Unit → O) a).range
    W.map (reduction a) = ⊥ ∧ New.obeying (New.relationsOn W) (New.QuotSpan a) = ⊤ := by
  intro W
  have ss : saturation W = ⊤ := top_unique fun x _ ↦ ⟨a, ha, x, rfl⟩
  constructor
  · refine eq_bot_iff.2 ?_
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact funext fun i ↦ funext fun j ↦ (Ideal.Quotient.eq_zero_iff_dvd a _).2 ⟨x i j, rfl⟩
  · rw [← read_saturation W ha, ss, Submodule.map_top, LinearMap.range_eq_top]
    exact (Ideal.Quotient.mk_surjective (I := Ideal.span {a})).comp_left.comp_left

section
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩
local instance : New.DVR ℤ_[17] := {}
/-- The surviving residue 1 passes all the equations of the scaled 17-adic line,
while no integral vector in that line reduces to 1. -/
example :
    let W := (lsmul ℤ_[17] (Unit → Unit → ℤ_[17]) 17).range
    let one : Unit → Unit → New.QuotSpan (17 : ℤ_[17]) := fun _ _ ↦ 1
    one ∈ New.obeying (New.relationsOn W) (New.QuotSpan (17 : ℤ_[17])) ∧
      one ∉ W.map (reduction (17 : ℤ_[17])) := by
  intro W one
  obtain ⟨lost, full⟩ := scaled_single_reading ℤ_[17] 17 (by norm_num)
  rw [full, lost]
  refine ⟨Submodule.mem_top, fun zero ↦ ?_⟩
  have wrong : (1 : New.QuotSpan (17 : ℤ_[17])) = 0 := congrFun (congrFun (show one = 0 from zero) ()) ()
  exact (PadicInt.prime_p (p := 17)).not_isUnit <| isUnit_of_dvd_one <|
    (Ideal.Quotient.eq_zero_iff_dvd 17 (1 : ℤ_[17])).1 (by simpa)
/-- A unit modulus identifies every reading with zero, even for a nonsaturated lattice. -/
example :
    let W := (lsmul ℤ_[17] (Unit → Unit → ℤ_[17]) 17).range
    W.map (reduction (1 : ℤ_[17])) = New.obeying (New.relationsOn W) (New.QuotSpan (1 : ℤ_[17])) ∧
      W ≠ saturation W := by
  intro W
  have : Subsingleton (New.QuotSpan (1 : ℤ_[17])) := Submodule.Quotient.subsingleton_iff.2
    (by exact Ideal.span_singleton_one)
  refine ⟨Subsingleton.elim _ _, fun same ↦ ?_⟩
  let v : Unit → Unit → ℤ_[17] := fun _ _ ↦ 1
  have live : v ∈ saturation W := ⟨17, by norm_num, v, rfl⟩
  obtain ⟨x, hx⟩ := (same ▸ live : v ∈ W)
  exact (PadicInt.prime_p (p := 17)).not_isUnit (isUnit_of_dvd_one
    ⟨x () (), (congrFun (congrFun hx ()) ()).symm⟩)

end

end Hearthline.RelationLattices
