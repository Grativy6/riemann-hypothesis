module

public import Lib.Weil.Construction.ThetaPhaseProjection
public import Lib.Weil.Construction.ThetaPhaseObservations
import Lib.Shimura.ComplexTheta.AppellHumbertData
import Mathlib.Tactic

/-!
# A complex number from each phase selector

The theta projection returns a whole function on a known line. A scalar
reading at z sees that line precisely when its basis function is nonzero at z.
One nonzero anchor of the original vacuum supplies calibrated sites for every
class by moving the evaluation point together with the translate.
-/

@[expose] public section

open NumberField Complex Pointwise Finset
namespace New.ThetaCoordinates

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
local notation "𝓦" => (InfinitePlace E × n → ℂ)
local notation "𝓕" => (𝓦 → ℂ)
variable {Y Γ : Type} [Fintype Y] [Fintype Γ] {y : Y → n → E} {γ : Γ → n → E} {δ : E} {N : ℕ}
  {ε : n → ℤˣ} (V : Space E n ε) [V.IsStd]

omit [V.IsStd] in
/-- When the probe follows the basis translate, the vacuum is evaluated at
the same anchor in every class. The exponential multiplier never vanishes. -/
theorem following_anchor {z₀ : 𝓦} (hz : Space.entireTheta V.vacElem z₀ ≠ 0) (v : n → E) :
    vacuumTranslate V v (z₀ + realImage v) ≠ 0 := by
  rw [vacuumTranslate, ratShift, thetaShift_apply_apply, realImage_neg]
  apply mul_ne_zero (Complex.exp_ne_zero _)
  simpa using hz

omit [V.IsStd] in
theorem exists_anchor : ∃ z₀ : 𝓦, Space.entireTheta V.vacElem z₀ ≠ 0 := by
  by_contra! zero
  exact V.entireTheta_vacElem_ne_zero (funext zero)

/-- Divide the projected scalar reading by the calibrated basis value. -/
noncomputable def scalarCoordinate (γ : Γ → n → E) (u : n → E) (z₀ : 𝓦) (F : 𝓕) : ℂ :=
  (projection γ u F) (z₀ + realImage u) / vacuumTranslate V u (z₀ + realImage u)

theorem scalarCoordinate_expansion (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n)) (dn : δ ≠ 0)
    {z₀ : 𝓦} (hz : Space.entireTheta V.vacElem z₀ ≠ 0) (c : Y → ℂ) (i : Y) :
    scalarCoordinate V γ (y i) z₀ (∑ k, c k • vacuumTranslate V (y k)) = c i := by
  have read := read_expansion hy hγ dn V.isThetaFunction_vacElem c i
  rw [scalarCoordinate]
  change (projection γ (y i) (∑ k, c k • ratShift (-y k) (Space.entireTheta V.vacElem))) _ / _ = _
  rw [read]
  change (c i * vacuumTranslate V (y i) _) / vacuumTranslate V (y i) _ = c i
  exact mul_div_cancel_right₀ _ (following_anchor V hz (y i))

theorem scalar_reconstruction (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N)
    {z₀ : 𝓦} (hz : Space.entireTheta V.vacElem z₀ ≠ 0)
    {F : 𝓕} (hF : IsThetaFunction (star δ • idealLattice E n) F) :
    ∑ i : Y, scalarCoordinate V γ (y i) z₀ F • vacuumTranslate V (y i) = F := by
  obtain ⟨c, hc, _⟩ := existsUnique_coordinates V hy hγ hδ hN norm hF
  rw [← hc]
  simp only [scalarCoordinate_expansion V hy hγ (ne_zero_of_mul_star_eq hN norm) hz]

/-- A scalar observation must both select the class and evaluate its basis
function at a nonzero site. This gives an exact test for any survey of probes. -/
theorem injective_scalar_iff_visible {A : Type*} (u : A → n → E) (z : A → 𝓦)
    (hu : ∀ a, u a ∈ δ⁻¹ • idealLattice E n)
    (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N) :
    Function.Injective (fun F : thetaFunctions (star δ • idealLattice E n) ↦
      fun a ↦ projection γ (u a) (F : 𝓕) (z a)) ↔
      ∀ k : Y, ∃ a : A, u a - y k ∈ idealLattice E n ∧ vacuumTranslate V (y k) (z a) ≠ 0 := by
  classical
  have dn := ne_zero_of_mul_star_eq hN norm
  have vac := V.isThetaFunction_vacElem
  have nz := V.entireTheta_vacElem_ne_zero
  let H := thetaFunctions (star δ • idealLattice E n)
  constructor
  · intro inj k
    by_contra! missing
    let f := vacuumTranslate V (y k)
    have fm : f ∈ H := vacuumTranslate_mem V (hy.mem k) hδ dn
    have eq : (fun a ↦ projection γ (u a) f (z a)) = fun a ↦ projection γ (u a) ((0 : H) : 𝓕) (z a) := by
      funext a
      simp only [f, vacuumTranslate, projection, LinearMap.smul_apply,
        selector_translate (hu a) (hy.mem k) dn hγ vac, ZeroMemClass.coe_zero, map_zero, Pi.zero_apply]
      by_cases hit : u a - y k ∈ idealLattice E n
      · rw [ite_eq_left hit, smul_smul, inv_mul_cancel₀ (characterCount_ne_zero hγ), one_smul]
        exact missing a hit
      · simp [hit]
    have equal : (⟨f, fm⟩ : H) = 0 := inj eq
    exact (translate_ne_zero nz (y k)) (congrArg Subtype.val equal)
  · intro covers F G data_eq
    have mem : (F : 𝓕) - (G : 𝓕) ∈ H := H.sub_mem F.property G.property
    obtain ⟨c, hc, _⟩ := existsUnique_coordinates V hy hγ hδ hN norm mem
    have zero (k : Y) : c k = 0 := by
      obtain ⟨a, hit, visible⟩ := covers k
      have pick := (selector_eq_iff (hu a) (hy.mem k) dn hγ vac nz).2 hit
      have eq := congrFun data_eq a
      change projection γ (u a) (F : 𝓕) (z a) = projection γ (u a) (G : 𝓕) (z a) at eq
      have same : projection γ (u a) = projection γ (y k) := by simp only [projection, pick]
      rw [same] at eq
      have diff : projection γ (y k) ((F : 𝓕) - (G : 𝓕)) (z a) = 0 := by
        rw [map_sub, Pi.sub_apply, eq, sub_self]
      rw [← hc] at diff
      change projection γ (y k) (∑ i, c i • ratShift (-y i) (Space.entireTheta V.vacElem)) (z a) = 0 at diff
      rw [read_expansion hy hγ dn vac c k] at diff
      exact (mul_eq_zero.1 (show c k * vacuumTranslate V (y k) (z a) = 0 from diff)).resolve_right visible
    exact Subtype.ext (sub_eq_zero.1 (hc.symm.trans (by simp [zero])))

end New.ThetaCoordinates
