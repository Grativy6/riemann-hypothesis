module

public import New.Reduction.Zeros.PrimeCutoffChord
public import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

/-!
# The two endpoint probability laws

The logarithmic correction equals Mathlib's measure-theoretic KL divergence.
Subtracting the actual weighted interior tents gives the full remainder reading.
-/

@[expose] public section

open Filter Set Finset Real MeasureTheory InformationTheory
open scoped ENNReal Topology
namespace New.PrimeCutoff

/-- The two endpoint masses, in lower/upper order. -/
noncomputable def endpointLaw (a b : ℝ) : Measure Bool :=
  ENNReal.ofReal a • Measure.dirac false + ENNReal.ofReal b • Measure.dirac true

noncomputable instance (a b : ℝ) : IsFiniteMeasure (endpointLaw a b) := by
  constructor
  simp [endpointLaw,smul_eq_mul]

lemma endpoint_probability {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (total : a+b=1) :
    IsProbabilityMeasure (endpointLaw a b) := by
  constructor
  simp [endpointLaw,smul_eq_mul,← ENNReal.ofReal_add ha hb,total]

lemma lintegral_endpointLaw (f : Bool → ℝ≥0∞) (a b : ℝ) :
    (∫⁻ t, f t ∂endpointLaw a b) = ENNReal.ofReal a * f false + ENNReal.ofReal b * f true := by
  simp [endpointLaw,lintegral_add_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]

lemma endpoint_reweight {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (u v : ℝ) :
    endpointLaw (a*u) (b*v) =
      (endpointLaw a b).withDensity (fun t : Bool ↦ ENNReal.ofReal (if t then v else u)) := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs, lintegral_endpointLaw]
  by_cases h₀ : false∈s <;> by_cases h₁ : true∈s <;>
    simp [endpointLaw,Measure.dirac_apply',Set.indicator,
      h₀,h₁,smul_eq_mul,ENNReal.ofReal_mul ha,ENNReal.ofReal_mul hb]

/-- The actual measure-theoretic KL divergence under a two-point reweighting. -/
theorem klDiv_endpoint_reweight {a b u v : ℝ} (ha : 0≤a) (hb : 0≤b) (hu : 0≤u) (hv : 0≤v) :
    klDiv (endpointLaw (a*u) (b*v)) (endpointLaw a b) =
      ENNReal.ofReal (a*klFun u+b*klFun v) := by
  let f (t : Bool) := ENNReal.ofReal (if t then v else u)
  have eq : endpointLaw (a*u) (b*v) = (endpointLaw a b).withDensity f := endpoint_reweight ha hb u v
  have ac : endpointLaw (a*u) (b*v) ≪ endpointLaw a b := eq ▸ withDensity_absolutelyContinuous _ _
  have rn : (endpointLaw (a*u) (b*v)).rnDeriv (endpointLaw a b) =ᵐ[endpointLaw a b] f := by
    rw [eq]; exact Measure.rnDeriv_withDensity _ (measurable_of_finite f)
  rw [klDiv_eq_lintegral_klFun_of_ac ac]
  calc _ = ∫⁻ t, ENNReal.ofReal (klFun (f t).toReal) ∂endpointLaw a b :=
        lintegral_congr_ae (rn.mono fun t ht ↦ by rw [ht])
    _ = _ := by
      rw [lintegral_endpointLaw,ENNReal.ofReal_add (mul_nonneg ha (klFun_nonneg hu)) (mul_nonneg hb (klFun_nonneg hv)),
        ENNReal.ofReal_mul ha,ENNReal.ofReal_mul hb]
      simp [f,ENNReal.toReal_ofReal hu,ENNReal.toReal_ofReal hv]

/-- The logarithmic chord correction is the relative entropy of the reciprocal
endpoint weights with respect to the ordinary endpoint weights. -/
theorem entropy_of_chord {a b y x z : ℝ} (hy : 0<y) (hz : 0<z) (hx : 0<x)
    (ha : 0≤a) (hb : 0≤b) (weights : a+b=1) (mix : a*y+b*z=x) :
    let P := endpointLaw (a*(y/x)) (b*(z/x))
    let Q := endpointLaw a b
    IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      (klDiv P Q).toReal = (a*y*Real.log (y/x) + b*z*Real.log (z/x))/x := by
  dsimp only
  have hu := (div_pos hy hx).le
  have hv := (div_pos hz hx).le
  have mass : a*(y/x)+b*(z/x)=1 := by
    calc _ = (a*y+b*z)/x := by ring
      _ = 1 := by rw [mix,div_self hx.ne']
  refine ⟨endpoint_probability (mul_nonneg ha hu) (mul_nonneg hb hv) mass,
    endpoint_probability ha hb weights,?_⟩
  rw [klDiv_endpoint_reweight ha hb hu hv,
    ENNReal.toReal_ofReal (add_nonneg (mul_nonneg ha (klFun_nonneg hu)) (mul_nonneg hb (klFun_nonneg hv)))]
  unfold klFun
  linear_combination weights-mass

theorem exact_chord_with_entropy {d q : ℕ} [Fact d.Prime] [NeZero q] {a b y x z : ℝ}
    (hy : 0<y) (ha : 0≤a) (hb : 0≤b) (weights : a+b=1) (mix : a*y+b*z=x)
    (left : y≤x) (right : x≤z) :
    primeRemainder d q x - (a*(y/x)*primeRemainder d q y + b*(z/x)*primeRemainder d q z) =
      (klDiv (endpointLaw (a*(y/x)) (b*(z/x))) (endpointLaw a b)).toReal / q.totient -
      (∑ n ∈ Finset.Icc 1 ⌊z⌋₊, lambdaKResidueClass d q n/n *
        min (a*((n:ℝ)-y)⁺) (b*(z-n)⁺))/x := by
  have hx := hy.trans_le left
  have hz := hx.trans_le right
  rw [(entropy_of_chord hy hz hx ha hb weights mix).2.2,
    ← integrated_chord_defect hy ha hb weights mix left right]
  unfold integrated
  rw [Real.log_div hy.ne' hx.ne', Real.log_div hz.ne' hx.ne']
  field_simp [hx.ne']
  linear_combination ((logDerivMean d q 1).re + Real.log x/q.totient) * mix

end New.PrimeCutoff
