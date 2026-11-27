module

public import Lib.Weil.Construction.ThetaScalarReadings
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import Mathlib.Topology.Baire.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Tactic

/-!
# How many actual point values suffice?

At one anchor z, all the phase projections use the same ordinary point values
at z + realImage (γ j). The resulting evaluation map is bijective exactly
when every vacuum translate is nonzero at z. Such anchors form an open dense
set, and the number of point values equals the dimension.
-/

@[expose] public section

open NumberField Complex Pointwise Finset Set Module
namespace New.ThetaCoordinates

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
local notation "𝓦" => (InfinitePlace E × n → ℂ)
local notation "𝓕" => (𝓦 → ℂ)
variable {Y Γ : Type} [Fintype Y] [Fintype Γ] {y : Y → n → E} {γ : Γ → n → E} {δ : E} {N : ℕ}
variable {ε : n → ℤˣ} (V : Space E n ε) [V.IsStd]

/-- Read raw values of the input theta function, without doing any Fourier
averaging first. The number of slots is the size of the γ representative set. -/
noncomputable def orbitSamples (H : AddSubgroup (n → E)) (γ : Γ → n → E) (z : 𝓦) :
    thetaFunctions H →ₗ[ℂ] (Γ → ℂ) where
  toFun F j := (F : 𝓕) (z + realImage (γ j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The complete row multiplier at the archimedean evaluation site. The
exponential in this factor can change the magnitude of a raw point value. -/
noncomputable def signedMultiplier (a : n → E) (z : 𝓦) : ℂ :=
  let B := fockForm (InfinitePlace E × n)
  let r := realImage a
  stdLattice.semichar (finiteImage a) * Complex.exp (-(B r z + B r r / 2))

omit [DecidableEq n] in
lemma signedMultiplier_ne_zero (a : n → E) (z : 𝓦) : signedMultiplier a z ≠ 0 := by
  simp [signedMultiplier, Space.semichar_ne_zero]

omit [DecidableEq n] in
lemma signedShift_evaluate (a : n → E) (F : 𝓕) (z : 𝓦) :
    signedShift a F z = signedMultiplier a z * F (z + realImage a) := by
  simp [signedShift_apply, ratShift, thetaShift_apply_apply, Pi.smul_apply, smul_eq_mul, signedMultiplier, mul_assoc]

omit [DecidableEq n] in
lemma signed_value_zero_iff (a : n → E) (F : 𝓕) (z : 𝓦) :
    signedShift a F z = 0 ↔ F (z + realImage a) = 0 := by
  rw [signedShift_evaluate, mul_eq_zero, or_iff_right (signedMultiplier_ne_zero a z)]

omit [DecidableEq n] in
/-- All filtered scalar readings at the same anchor use the same Γ raw values. -/
lemma projected_value_eq_sum (F : 𝓕) (z : 𝓦) (γ : Γ → n → E) (u : n → E) :
    projection γ u F z = (Fintype.card Γ : ℂ)⁻¹ *
      ∑ j, ratPhase (γ j) u * signedMultiplier (γ j) z * F (z + realImage (γ j)) := by
  simp only [projection, selector, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, signedShift_evaluate, mul_assoc]

omit [DecidableEq n] in
/-- Equal ordinary values on the orbit give equal filtered values at the anchor. -/
lemma projected_value_of_orbit {F G : 𝓕} {z : 𝓦} (γ : Γ → n → E)
    (same : ∀ j, F (z + realImage (γ j)) = G (z + realImage (γ j))) (u : n → E) :
    projection γ u F z = projection γ u G z := by
  simp only [projected_value_eq_sum, same]

omit [Fintype Γ] in
/-- A zero of a vacuum translate at the anchor repeats on every signed lattice
shift used by the measurement. -/
theorem basis_zero_on_orbit (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (v : n → E) (z : 𝓦) (zero : vacuumTranslate V v z = 0) (j : Γ) :
    vacuumTranslate V v (z + realImage (γ j)) = 0 := by
  apply (signed_value_zero_iff (γ j) _ z).1
  change signedShift (γ j) (ratShift (-v) (Space.entireTheta V.vacElem)) z = 0
  rw [signedShift_ratShift, V.isThetaFunction_vacElem.signedShift_eq _ (hγ.mem j)]
  change ratPhase (γ j) (-v) * vacuumTranslate V v z = 0
  rw [zero, mul_zero]

/-- At a fixed anchor a basis channel is invisible at every orbit point if it
vanishes at the anchor itself. -/
theorem orbit_injective_iff (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N) (z : 𝓦) :
    Function.Injective (orbitSamples (star δ • idealLattice E n) γ z) ↔
      ∀ i : Y, vacuumTranslate V (y i) z ≠ 0 := by
  classical
  let H := thetaFunctions (star δ • idealLattice E n)
  have dn := ne_zero_of_mul_star_eq hN norm
  constructor
  · intro inj i missing
    let f := vacuumTranslate V (y i)
    have fm : f ∈ H := vacuumTranslate_mem V (hy.mem i) hδ dn
    have data : orbitSamples (star δ • idealLattice E n) γ z (⟨f, fm⟩ : H) =
        orbitSamples (star δ • idealLattice E n) γ z 0 := by
      funext j
      change f (z + realImage (γ j)) = 0
      exact basis_zero_on_orbit V hγ (y i) z missing j
    exact (translate_ne_zero V.entireTheta_vacElem_ne_zero (y i)) (congrArg Subtype.val (inj data))
  · intro good F G eq
    have reads := (injective_scalar_iff_visible V y (fun _ ↦ z) hy.mem hy hγ hδ hN norm).2
      (fun i ↦ ⟨i, by simp, good i⟩)
    apply reads
    funext i
    exact projected_value_of_orbit γ (fun j ↦ congrFun eq j) (y i)

/-- There is an open dense set of locations where all the translates can be
read at the same anchor. This includes the singleton ambient space in rank zero. -/
theorem open_dense_good_anchors :
    IsOpen {z : 𝓦 | ∀ i : Y, vacuumTranslate V (y i) z ≠ 0} ∧
    Dense {z : 𝓦 | ∀ i : Y, vacuumTranslate V (y i) z ≠ 0} := by
  classical
  have fDiff (i : Y) : Differentiable ℂ (vacuumTranslate V (y i)) :=
    differentiable_thetaShift _ _ V.isThetaFunction_vacElem.differentiable
  have op (i : Y) : IsOpen {z : 𝓦 | vacuumTranslate V (y i) z ≠ 0} :=
    isOpen_ne_fun (fDiff i).continuous continuous_const
  obtain ⟨anchor, nonzero⟩ := exists_anchor V
  have dense (i : Y) : Dense {z : 𝓦 | vacuumTranslate V (y i) z ≠ 0} := by
    have analytic := (fDiff i).differentiableOn.analyticOnNhd_of_finiteDimensional isOpen_univ
    exact analytic.dense_setOf_ne_zero (following_anchor V nonzero (y i))
  have eq : {z : 𝓦 | ∀ i : Y, vacuumTranslate V (y i) z ≠ 0} =
      ⋂ i : Y, {z : 𝓦 | vacuumTranslate V (y i) z ≠ 0} := by ext; simp
  rw [eq]
  exact ⟨isOpen_iInter_of_finite op, dense_iInter_of_isOpen op dense⟩

/-- The M ordinary samples interpolate arbitrary M complex data on a dense open
set of anchors. A nodal anchor is detected by the precise nonvanishing condition. -/
theorem orbit_bijective_iff (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N) (z : 𝓦) :
    Function.Bijective (orbitSamples (star δ • idealLattice E n) γ z) ↔
      ∀ i : Y, vacuumTranslate V (y i) z ≠ 0 := by
  let H := thetaFunctions (star δ • idealLattice E n)
  let _ : Module.Finite ℂ H := Module.Finite.of_basis (vacuumBasis V hy hγ hδ hN norm)
  have dim : Module.finrank ℂ H = Module.finrank ℂ (Γ → ℂ) := by
    rw [Module.finrank_pi]
    exact (finrank_thetaFunctions (n := n) hδ hN norm).trans (card_representatives_idealLattice hy hγ hδ hN norm).2.symm
  have inj := orbit_injective_iff V hy hγ hδ hN norm z
  exact ⟨fun bi ↦ inj.1 bi.1, fun good ↦
    ⟨inj.2 good, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).1 (inj.2 good)⟩⟩

/-- Both invertibility and the openness/density conclusion hold for ordinary
point evaluations, without exposing a projected function as the data. -/
theorem open_dense_interpolation (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N) :
    IsOpen {z : 𝓦 | Function.Bijective (orbitSamples (star δ • idealLattice E n) γ z)} ∧
    Dense {z : 𝓦 | Function.Bijective (orbitSamples (star δ • idealLattice E n) γ z)} := by
  let V := stdSpace E n
  have eq : {z : 𝓦 | Function.Bijective (orbitSamples (star δ • idealLattice E n) γ z)} =
      {z : 𝓦 | ∀ i : Y, vacuumTranslate V (y i) z ≠ 0} :=
    Set.ext (fun z ↦ orbit_bijective_iff V hy hγ hδ hN norm z)
  rw [eq]
  exact open_dense_good_anchors V

/-- Fewer than N^r scalar linear readings cannot distinguish the whole space,
even when the measurements are allowed to be arbitrary linear functionals. -/
theorem scalar_count_lower_bound {A : Type*} [Fintype A]
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N)
    (L : thetaFunctions (star δ • idealLattice E n) →ₗ[ℂ] (A → ℂ)) (injective : Function.Injective L) :
    N ^ Fintype.card (InfinitePlace E × n) ≤ Fintype.card A := by
  have dim := LinearMap.finrank_le_finrank_of_injective injective
  rw [finrank_thetaFunctions (n := n) hδ hN norm, Module.finrank_pi] at dim
  exact dim

end New.ThetaCoordinates
