import Lib.General.Algebra.FittingIdealsAndLengths
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.Tactic

noncomputable section
open Module LinearMap Submodule Ideal

namespace Hearthline.RelationLattices

variable {O V : Type*} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]

/-- The integral vectors that enter the lattice after multiplication by a nonzero scalar. -/
def saturation (Z : Submodule O V) : Submodule O V where
  carrier := {w | ∃ a : O, a ≠ 0 ∧ a • w ∈ Z}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a*b, mul_ne_zero ha hb, ?_⟩
    simpa [smul_add, smul_smul, mul_comm b a] using Z.add_mem (Z.smul_mem b hx) (Z.smul_mem a hy)
  smul_mem' := by
    rintro b x ⟨a, ha, hx⟩
    exact ⟨a, ha, (smul_comm a b x).symm ▸ Z.smul_mem b hx⟩

theorem le_saturation (Z : Submodule O V) : Z ≤ saturation Z :=
  fun _ hx ↦ ⟨1, one_ne_zero, by simpa using hx⟩

theorem divide_in_saturation {Z : Submodule O V} {a : O} (ha : a ≠ 0) (w : V)
    (hw : a • w ∈ saturation Z) : w ∈ saturation Z := by
  obtain ⟨b, hb, h⟩ := hw
  exact ⟨b*a, mul_ne_zero hb ha, by simpa only [mul_smul] using h⟩

variable {Γ n : Type*} (Z : Submodule O (Γ → n → O))

/-- Homogeneous integral matrix relations detect no difference between Z and its saturation. -/
theorem relations_saturation [Fintype n] [DecidableEq n] :
    New.relationsOn (saturation Z) = New.relationsOn Z := by
  ext f
  constructor
  · exact fun hf z hz ↦ hf z (le_saturation Z hz)
  · intro hf w hw
    obtain ⟨a, ha, hz⟩ := hw
    have zero := hf (a • w) hz
    change New.relEval O f (a • w) = 0 at zero
    rw [map_smul] at zero
    exact (smul_eq_zero.mp zero).resolve_left ha

section Finite
variable [IsPrincipalIdealRing O] [Module.Finite O Z]

/-- Finitely many coordinate readings separate the vectors in the saturation. Choose
coordinates spanning the evaluations on Z and clear the denominator of the vector being read. -/
theorem finite_saturation : Module.Finite O (saturation Z) := by
  classical
  let coord (i : Γ × n) : Module.Dual O Z := (proj i.2 ∘ₗ proj i.1) ∘ₗ Z.subtype
  obtain ⟨s, hs, eq⟩ :=
    (fg_span_iff_fg_span_finset_subset (R := O) (Set.range coord)).1 (IsNoetherian.noetherian _)
  choose index hindex using fun k : s ↦ hs k.property
  let read : saturation Z →ₗ[O] (s → O) :=
    pi fun k ↦ (proj (index k).2 ∘ₗ proj (index k).1) ∘ₗ (saturation Z).subtype
  apply Module.Finite.of_injective read
  apply LinearMap.ker_eq_bot.1
  apply eq_bot_iff.2
  intro w hw
  obtain ⟨a, ha, hz⟩ := w.property
  let z : Z := ⟨a • w.val, hz⟩
  have vanish : span O (Set.range coord) ≤ (Module.Dual.eval O Z z).ker := by
    rw [eq, Submodule.span_le]
    intro v hv
    change v z = 0
    let k : s := ⟨v, hv⟩
    have hzero : read w k = 0 := congrFun (show read w = 0 from hw) k
    rw [← show coord (index k) = v from hindex k]
    change a * (read w k) = 0
    rw [hzero, mul_zero]
  apply Subtype.ext
  ext g j
  have h := vanish (subset_span (Set.mem_range_self (g,j)))
  exact (mul_eq_zero.mp (show a * w.val g j = 0 from h)).resolve_left ha

theorem finrank_saturation : finrank O (saturation Z) = finrank O Z := by
  let S := saturation Z
  have : Module.Finite O S := finite_saturation Z
  let Q := Z.submoduleOf S
  have tor : Module.IsTorsion O (S ⧸ Q) := by
    intro y
    obtain ⟨w, rfl⟩ := Q.mkQ_surjective y
    obtain ⟨a, ha, hz⟩ := w.property
    refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
    change a • Q.mkQ w = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 hz
  have zero := (Module.finrank_eq_zero_iff_isTorsion (R := O) (M := S ⧸ Q)).2 tor
  have eq := Q.finrank_quotient_add_finrank
  rw [zero, zero_add, (Submodule.submoduleOfEquivOfLe (le_saturation Z)).finrank_eq] at eq
  exact eq.symm

end Finite

variable {R : Type*} [CommRing R] [New.DVR R] (L : Submodule R (Γ → n → R))
  [Fintype n] [DecidableEq n] [Module.Finite R L]

/-- Every solution of the integral equations modulo a nonzero scalar lifts to an integral
vector after saturating the original lattice. -/
theorem read_saturation {a : R} (ha : a ≠ 0) :
    (saturation L).map (((Ideal.span {a}).mkQ.compLeft n).compLeft Γ) =
      New.obeying (New.relationsOn L) (New.QuotSpan a) := by
  have := finite_saturation L
  rw [← relations_saturation L]
  exact New.map_mkQ_eq_obeying_relationsOn (saturation L) ha (divide_in_saturation ha)

/-- The whole solution set of the relations has exactly rank times coefficient length. The
ambient relation bound is sharp at every finite nonzero modulus, even for nonsaturated L. -/
theorem length_readings {a : R} (ha : a ≠ 0) :
    length R (New.obeying (New.relationsOn L) (New.QuotSpan a)) =
      finrank R L * length R (New.QuotSpan a) := by
  have := finite_saturation L
  rw [← read_saturation L ha, New.length_map_mkQ_of_saturated (saturation L) ha
    (divide_in_saturation ha), finrank_saturation]

end Hearthline.RelationLattices
