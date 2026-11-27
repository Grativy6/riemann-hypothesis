module

public import Lib.Weil.Construction.ThetaPhaseBasis
import Mathlib.Tactic

/-!
# Adding the phase readings back

On the scaled theta space the normalized selectors are idempotent and have
pairwise zero products. Their sum returns the original theta function.
-/

@[expose] public section

open NumberField Complex Pointwise Finset
namespace New.ThetaCoordinates

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
local notation "𝓕" => ((InfinitePlace E × n → ℂ) → ℂ)
variable {Y Γ : Type} [Fintype Y] [Fintype Γ] {y : Y → n → E} {γ : Γ → n → E} {δ : E} {N : ℕ}

/-- Divide a selector by the number of signed shifts used to form it. -/
noncomputable def projection (γ : Γ → n → E) (u : n → E) : Module.End ℂ 𝓕 :=
  (Fintype.card Γ : ℂ)⁻¹ • selector γ u

theorem read_expansion (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n)) (dn : δ ≠ 0)
    {F : 𝓕} (hF : IsThetaFunction (idealLattice E n) F) (c : Y → ℂ) (i : Y) :
    projection γ (y i) (∑ k, c k • ratShift (-y k) F) = c i • ratShift (-y i) F := by
  simp only [projection, LinearMap.smul_apply, selector_sum hy hγ dn hF, smul_smul]
  congr 1
  field_simp [characterCount_ne_zero hγ]

theorem sum_projections (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N)
    {F : 𝓕} (hF : IsThetaFunction (star δ • idealLattice E n) F) :
    ∑ i : Y, projection γ (y i) F = F := by
  let V := stdSpace E n
  obtain ⟨c, hc, _⟩ := existsUnique_coordinates V hy hγ hδ hN norm hF
  rw [← hc]
  exact Finset.sum_congr rfl fun i _ ↦
    read_expansion hy hγ (ne_zero_of_mul_star_eq hN norm) V.isThetaFunction_vacElem c i

theorem projection_projection (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N)
    {F : 𝓕} (hF : IsThetaFunction (star δ • idealLattice E n) F) (i k : Y) [DecidableEq Y] :
    projection γ (y i) (projection γ (y k) F) = if i = k then projection γ (y k) F else 0 := by
  let V := stdSpace E n
  have dn := ne_zero_of_mul_star_eq hN norm
  obtain ⟨c, hc, _⟩ := existsUnique_coordinates V hy hγ hδ hN norm hF
  have one : projection γ (y k) F = c k • ratShift (-y k) (Space.entireTheta V.vacElem) := by
    rw [← hc]
    exact read_expansion hy hγ dn V.isThetaFunction_vacElem c k
  rw [one, map_smul]
  simp only [projection, LinearMap.smul_apply, selector_at_rep hy hγ dn V.isThetaFunction_vacElem]
  split_ifs <;> simp [smul_smul, characterCount_ne_zero hγ]

end New.ThetaCoordinates
