module

public import Lib.Weil.Construction.ThetaOrbitInterpolation
import Mathlib.Tactic

/-!
# Explicit interpolation from the shared point values

The inverse is a finite character transform. First apply the signed-shift
row multiplier to the raw samples. The resulting Fourier coefficient must
then be divided by the value of its own translated vacuum at the anchor.
-/

@[expose] public section

open NumberField Complex Pointwise Finset Module Filter Topology Set
namespace New.ThetaCoordinates

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
local notation "𝓦" => (InfinitePlace E × n → ℂ)
local notation "𝓕" => (𝓦 → ℂ)
variable {Y Γ : Type} [Fintype Y] [Fintype Γ] {y : Y → n → E} {γ : Γ → n → E} {δ : E} {N : ℕ}
  {ε : n → ℤˣ} (V : Space E n ε) [V.IsStd]

omit [Fintype Γ] in
/-- On the orbit of an anchor, the matrix entry of a basis mode is the
character entry times the basis value, divided by the signed row multiplier. -/
theorem sample_matrix_entry (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (v : n → E) (z : 𝓦) (j : Γ) :
    signedMultiplier (γ j) z * vacuumTranslate V v (z + realImage (γ j)) =
      ratPhase (γ j) (-v) * vacuumTranslate V v z := by
  rw [← signedShift_evaluate, vacuumTranslate, signedShift_ratShift,
    V.isThetaFunction_vacElem.signedShift_eq _ (hγ.mem j)]
  rfl

/-- Decode one coordinate from the raw orbit samples. Its interpretation as
a coordinate requires the corresponding vacuum translate to be nonzero at z. -/
noncomputable def decode (γ : Γ → n → E) (u : n → E) (z : 𝓦) (data : Γ → ℂ) : ℂ :=
  (∑ j, ratPhase (γ j) u * signedMultiplier (γ j) z * data j) /
    ((Fintype.card Γ : ℂ) * vacuumTranslate V u z)

theorem decode_expansion (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n)) (dn : δ ≠ 0)
    (z : 𝓦) (k : Y) (hk : vacuumTranslate V (y k) z ≠ 0) (c : Y → ℂ) :
    decode V γ (y k) z (fun j ↦ (∑ i, c i • vacuumTranslate V (y i)) (z + realImage (γ j))) = c k := by
  let F := ∑ i, c i • vacuumTranslate V (y i)
  have read : projection γ (y k) F z = c k * vacuumTranslate V (y k) z :=
    congrFun (read_expansion hy hγ dn V.isThetaFunction_vacElem c k) z
  rw [projected_value_eq_sum] at read
  change (∑ j, _ * _ * F (z + realImage (γ j))) / _ = _
  apply (div_eq_iff (mul_ne_zero (characterCount_ne_zero hγ) hk)).2
  field_simp [characterCount_ne_zero hγ] at read
  linear_combination read

/-- Synthesizing with the decoded coefficients gives the unique theta function
taking arbitrary prescribed complex values on the orbit of a good anchor. -/
theorem interpolate_raw_data (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N)
    (z : 𝓦) (good : ∀ i : Y, vacuumTranslate V (y i) z ≠ 0) (data : Γ → ℂ) :
    ∀ j, (∑ i, decode V γ (y i) z data • vacuumTranslate V (y i)) (z + realImage (γ j)) = data j := by
  obtain ⟨F, hdata⟩ := ((orbit_bijective_iff V hy hγ hδ hN norm z).2 good).2 data
  obtain ⟨c, hc, _⟩ := existsUnique_coordinates V hy hγ hδ hN norm F.property
  have coeff (i : Y) : decode V γ (y i) z data = c i := by
    rw [← hdata]
    change decode V γ (y i) z (fun j ↦ (F : 𝓕) (z + realImage (γ j))) = c i
    rw [← hc]
    exact decode_expansion V hy hγ (ne_zero_of_mul_star_eq hN norm) z i (good i) c
  intro j
  simp only [coeff, hc]
  exact congrFun hdata j

omit [V.IsStd] in
/-- A perturbation of the raw samples is weighted by the actual row magnitudes
and divided by the actual column magnitude. Unit modulus belongs to ratPhase. -/
theorem decode_error_bound (γ : Γ → n → E) (u : n → E) (z : 𝓦) (data other : Γ → ℂ) :
    ‖decode V γ u z data - decode V γ u z other‖ ≤
      (∑ j, ‖signedMultiplier (γ j) z‖ * ‖data j - other j‖) /
        ((Fintype.card Γ : ℝ) * ‖vacuumTranslate V u z‖) := by
  have unit (j : Γ) : ‖ratPhase (γ j) u‖ = 1 := by
    simp [ratPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have algebra : decode V γ u z data - decode V γ u z other =
      (∑ j, ratPhase (γ j) u * signedMultiplier (γ j) z * (data j - other j)) /
        ((Fintype.card Γ : ℂ) * vacuumTranslate V u z) := by
    simp only [decode, mul_sub, sum_sub_distrib, sub_div]
  rw [algebra, norm_div, norm_mul, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ ↦ by rw [norm_mul, norm_mul, unit, one_mul])

/-- Near a nodal anchor, invertible measurements can make every raw reading
of the same unit-coordinate basis vector arbitrarily small. -/
theorem near_node_weak_readings (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N)
    (i : Y) {z₀ : 𝓦} (node : vacuumTranslate V (y i) z₀ = 0)
    {U : Set 𝓦} (nbhd : U ∈ 𝓝 z₀) {τ : ℝ} (τp : 0 < τ) :
    ∃ z ∈ U, Function.Bijective (orbitSamples (star δ • idealLattice E n) γ z) ∧
      ∀ j : Γ, ‖vacuumTranslate V (y i) (z + realImage (γ j))‖ < τ := by
  have cont : Continuous (vacuumTranslate V (y i)) :=
    (differentiable_thetaShift _ _ V.isThetaFunction_vacElem.differentiable).continuous
  have small : ∀ᶠ z in 𝓝 z₀, ∀ j : Γ, ‖vacuumTranslate V (y i) (z + realImage (γ j))‖ < τ := by
    apply Filter.eventually_all.2
    intro j
    have pos : ‖vacuumTranslate V (y i) (z₀ + realImage (γ j))‖ < τ := by
      rwa [basis_zero_on_orbit V hγ (y i) z₀ node j, norm_zero]
    exact ((cont.comp (continuous_id.add_const (realImage (γ j)))).norm.continuousAt).eventually_lt_const pos
  have dense := (open_dense_interpolation hy hγ hδ hN norm).2
  obtain ⟨z,⟨zU, weak⟩, good⟩ := mem_closure_iff_nhds.1 (dense z₀) _ (Filter.inter_mem nbhd small)
  exact ⟨z, zU, good, weak⟩

end New.ThetaCoordinates
