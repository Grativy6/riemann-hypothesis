module

public import Lib.Weil.Construction.ThetaPhaseSelector
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# The actual theta translates form a basis at the scaled lattice

The inversion theorem supplies spanning. Character orthogonality supplies
independence and a concrete way of recovering each component before summing.
-/

@[expose] public section

open NumberField Complex Pointwise Set Finset Module
namespace New.ThetaCoordinates

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
local notation "𝓕" => ((InfinitePlace E × n → ℂ) → ℂ)

/-- All entire functions fixed by the signed shifts of H. -/
def thetaFunctions (H : AddSubgroup (n → E)) : Submodule ℂ 𝓕 where
  carrier := {F | IsThetaFunction H F}
  zero_mem' := ⟨differentiable_const _, fun _ _ ↦ map_zero _⟩
  add_mem' := fun {F G} hF hG ↦ ⟨hF.differentiable.add hG.differentiable,
    fun g hg ↦ by rw [map_add, hF.signedShift_eq g hg, hG.signedShift_eq g hg]⟩
  smul_mem' := fun c {F} hF ↦ ⟨hF.differentiable.const_smul c,
    fun g hg ↦ by rw [map_smul, hF.signedShift_eq g hg]⟩

variable {ε : n → ℤˣ} (V : Space E n ε) [V.IsStd] {δ : E} {N : ℕ}
  {Y Γ : Type} [Fintype Y] [Fintype Γ] {y : Y → n → E} {γ : Γ → n → E}

/-- The theta functions centered at the representatives of the larger lattice. -/
noncomputable def vacuumTranslate (v : n → E) : 𝓕 := ratShift (-v) (Space.entireTheta V.vacElem)

lemma vacuumTranslate_mem {v : n → E} (hv : v ∈ δ⁻¹ • idealLattice E n)
    (hδ : (δ : 𝔸f E) ∈ Ô E) (dn : δ ≠ 0) :
    vacuumTranslate V v ∈ thetaFunctions (star δ • idealLattice E n) := by
  have base : IsThetaFunction (star δ • idealLattice E n) (Space.entireTheta V.vacElem) :=
    ⟨V.isThetaFunction_vacElem.differentiable,
      fun g hg ↦ V.isThetaFunction_vacElem.signedShift_eq _ (star_smul_idealLattice_le hδ hg)⟩
  exact base.ratShift (fun g hg ↦ (mem_star_smul_idealLattice_iff dn).1 hg (-v) (neg_mem hv))

theorem thetaFunctions_eq_span (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N) :
    thetaFunctions (star δ • idealLattice E n) =
      Submodule.span ℂ (Set.range (fun i : Y ↦ vacuumTranslate V (y i))) := by
  have dn := ne_zero_of_mul_star_eq hN norm
  refine le_antisymm (fun F hF ↦ ?_) (Submodule.span_le.2 (Set.range_subset_iff.2 (fun i ↦
    vacuumTranslate_mem V (hy.mem i) hδ dn)))
  obtain ⟨c, _, hc⟩ := V.exists_smul_entireTheta_vacElem_eq hy hγ hδ hN norm hF
  let t : ℂ := (N : ℂ) ^ Fintype.card (InfinitePlace E × n)
  have tn : t ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN)
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).2
  refine ⟨fun i ↦ t⁻¹ * c i, ?_⟩
  calc _ = t⁻¹ • ∑ i, c i • vacuumTranslate V (y i) := by simp only [Finset.smul_sum, smul_smul]
       _ = t⁻¹ • (t • F) := by rw [show ∑ i, c i • vacuumTranslate V (y i) = t • F from hc]
       _ = F := by rw [smul_smul, inv_mul_cancel₀ tn, one_smul]

/-- An actual basis of the scaled theta space, indexed by the chosen representatives. -/
noncomputable def vacuumBasis (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N) :
    Module.Basis Y ℂ (thetaFunctions (star δ • idealLattice E n)) :=
  let independent : LinearIndependent ℂ (fun i : Y ↦ vacuumTranslate V (y i)) :=
    independent_translates hy hγ (ne_zero_of_mul_star_eq hN norm) V.isThetaFunction_vacElem V.entireTheta_vacElem_ne_zero
  (Module.Basis.span independent).map (LinearEquiv.ofEq _ _ (thetaFunctions_eq_span V hy hγ hδ hN norm).symm)

@[simp] theorem vacuumBasis_apply (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N) (i : Y) :
    ((vacuumBasis V hy hγ hδ hN norm i : thetaFunctions _) : 𝓕) = vacuumTranslate V (y i) := by
  simp [vacuumBasis]
  exact Module.Basis.coe_span_apply _ _

/-- The usual Frobenius count here has an explicit independent spanning family:
one translated vacuum per class, with N^r classes. -/
theorem finrank_thetaFunctions (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N) :
    Module.finrank ℂ (thetaFunctions (n := n) (star δ • idealLattice E n)) =
      N ^ Fintype.card (InfinitePlace E × n) := by
  obtain ⟨Y, _, y, hy⟩ := exists_isRepresentativeSystem_inv_smul (n := n) hδ hN norm
  obtain ⟨Γ, _, γ, hγ⟩ := exists_isRepresentativeSystem_star_smul (n := n) hδ hN norm
  let V := stdSpace E n
  exact (Module.finrank_eq_card_basis (vacuumBasis V hy hγ hδ hN norm)).trans
    (card_representatives_idealLattice hy hγ hδ hN norm).1

/-- The scalars in the unnormalized expansion are unique. -/
theorem existsUnique_coordinates (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N)
    {F : 𝓕} (hF : IsThetaFunction (star δ • idealLattice E n) F) :
    ∃! c : Y → ℂ, ∑ i, c i • vacuumTranslate V (y i) = F := by
  have mem : F ∈ thetaFunctions (star δ • idealLattice E n) := hF
  rw [thetaFunctions_eq_span V hy hγ hδ hN norm] at mem
  obtain ⟨c, ec⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 mem
  refine ⟨c, ec,?_⟩
  intro b eb
  have ind := independent_translates hy hγ (ne_zero_of_mul_star_eq hN norm)
    V.isThetaFunction_vacElem V.entireTheta_vacElem_ne_zero
  have e : ∑ i, (b i - c i) • vacuumTranslate V (y i) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, eb, ec, sub_self]
  exact funext fun i ↦ sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 ind) _ e i)

omit [Fintype Y] in
/-- If one observation is missing, its basis vector and zero give the same
remaining readings although they are different theta functions. -/
theorem omitted_coordinate (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (dn : δ ≠ 0) (i : Y) :
    ∃ F ∈ thetaFunctions (star δ • idealLattice E n), F ≠ 0 ∧
      (∀ k, k ≠ i → selector γ (y k) F = 0) ∧ selector γ (y i) F ≠ 0 := by
  classical
  let V := stdSpace E n
  refine ⟨vacuumTranslate V (y i), vacuumTranslate_mem V (hy.mem i) hδ dn,
    translate_ne_zero V.entireTheta_vacElem_ne_zero _,?_,?_⟩
  · intro k ne
    simp only [vacuumTranslate, selector_at_rep hy hγ dn V.isThetaFunction_vacElem, ne, ite_false]
  · simp only [vacuumTranslate, selector_at_rep hy hγ dn V.isThetaFunction_vacElem, ite_true]
    exact smul_ne_zero (characterCount_ne_zero hγ) (translate_ne_zero V.entireTheta_vacElem_ne_zero _)

end New.ThetaCoordinates
