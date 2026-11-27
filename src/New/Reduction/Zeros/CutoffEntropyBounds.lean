module

public import New.Reduction.Zeros.CutoffEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Curvature bounds for the two-point relative entropy

On [y,z] the second derivative of u log u lies between 1/z and 1/y.
Subtracting quadratics gives explicit lower and upper bounds on the exact entropy charge.
-/

@[expose] public section

open Real Set Filter InformationTheory
open scoped Topology
namespace New.PrimeCutoff

/-- Subtract a quadratic of curvature 1/c from u log u. Its signed curvature
is σ(1/u−1/c) on a positive interval. -/
lemma log_quadratic_convex {y z c σ : ℝ} (hy : 0<y) (hc : 0<c)
    (curvature : ∀ t∈Set.Icc y z, 0≤σ*(t⁻¹-c⁻¹)) :
    ConvexOn ℝ (Set.Icc y z) (fun t ↦ σ*(t*Real.log t-t^2/(2*c))) := by
  let f (t : ℝ) := σ*(t*Real.log t-t^2/(2*c))
  let slope (t : ℝ) := σ*(Real.log t+1 - t/c)
  have df (t : ℝ) (ht : 0<t) : HasDerivAt f (slope t) t := by
    have d := ((Real.hasDerivAt_mul_log ht.ne').sub
      (((hasDerivAt_id t).pow 2).div_const (2*c))).const_mul σ
    convert d using 1 <;> dsimp [f,slope,id]; field
  have dd (t : ℝ) (ht : 0<t) : HasDerivAt (deriv f) (σ*(t⁻¹-c⁻¹)) t := by
    have d := (((Real.hasDerivAt_log ht.ne').add_const 1).sub ((hasDerivAt_id t).div_const c)).const_mul σ
    have local_slope : deriv f =ᶠ[𝓝 t] slope := by
      filter_upwards [lt_mem_nhds ht] with u hu using (df u hu).deriv
    apply HasDerivAt.congr_of_eventuallyEq (f := slope) _ local_slope
    simpa [slope,one_div] using d
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · intro t ht
    exact (df t (hy.trans_le ht.1)).continuousAt.continuousWithinAt
  · intro t ht
    exact (df t (hy.trans_le (interior_subset ht).1)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact (dd t (hy.trans_le (interior_subset ht).1)).differentiableAt.differentiableWithinAt
  · intro t ht
    change 0 ≤ deriv (deriv f) t
    rw [(dd t (hy.trans_le (interior_subset ht).1)).deriv]
    exact curvature t (interior_subset ht)

lemma log_chord_quadratic {a b y x z c σ : ℝ} (hy : 0<y) (hc : 0<c)
    (ha : 0≤a) (hb : 0≤b) (weights : a+b=1) (mix : a*y+b*z=x) (ends : y≤z)
    (curvature : ∀ t∈Set.Icc y z, 0≤σ*(t⁻¹-c⁻¹)) :
    0≤σ*((a*y*Real.log y+b*z*Real.log z-x*Real.log x) - (x-y)*(z-x)/(2*c)) := by
  have cvx := log_quadratic_convex hy hc curvature
  have chord := cvx.2 (Set.left_mem_Icc.2 ends) (Set.right_mem_Icc.2 ends) ha hb weights
  simp only [smul_eq_mul,mix] at chord
  have var : a*y^2+b*z^2-x^2=(x-y)*(z-x) := by linear_combination (y+z)*mix-y*z*weights
  rw [← var]
  calc 0 ≤ a*(σ*(y*Real.log y-y^2/(2*c))) + b*(σ*(z*Real.log z-z^2/(2*c))) -
      σ*(x*Real.log x-x^2/(2*c)) := sub_nonneg.2 chord
    _ = _ := by ring

/-- The exact natural-log correction is trapped between two parabolic errors.
The two denominators approach each other as a gap shrinks. -/
theorem relative_entropy_sandwich {a b y x z : ℝ} (hy : 0<y) (ha : 0≤a) (hb : 0≤b)
    (weights : a+b=1) (mix : a*y+b*z=x) (left : y≤x) (right : x≤z) :
    let J := (klDiv (endpointLaw (a*(y/x)) (b*(z/x))) (endpointLaw a b)).toReal
    (x-y)*(z-x)/(2*x*z) ≤ J ∧ J ≤ (x-y)*(z-x)/(2*x*y) := by
  dsimp only
  have hx := hy.trans_le left
  have hz := hx.trans_le right
  rw [(entropy_of_chord hy hz hx ha hb weights mix).2.2]
  have numerator : a*y*Real.log (y/x)+b*z*Real.log (z/x) =
      a*y*Real.log y+b*z*Real.log z-x*Real.log x := by
    rw [Real.log_div hy.ne' hx.ne',Real.log_div hz.ne' hx.ne']
    linear_combination -Real.log x * mix
  rw [numerator]
  have low := log_chord_quadratic (σ:=1) hy hz ha hb weights mix (left.trans right) (fun t ht ↦ by
    rw [one_mul]; exact sub_nonneg.2 (inv_anti₀ (hy.trans_le ht.1) ht.2))
  have high := log_chord_quadratic (σ:=-1) hy hy ha hb weights mix (left.trans right) (fun t ht ↦ by
    rw [neg_one_mul,neg_nonneg]; exact sub_nonpos.2 (inv_anti₀ hy ht.1))
  have normalize (c : ℝ) : (x-y)*(z-x)/(2*x*c) = ((x-y)*(z-x)/(2*c))/x := by ring
  rw [normalize z,normalize y]
  exact ⟨div_le_div_of_nonneg_right (by linarith only [low]) hx.le,
    div_le_div_of_nonneg_right (by linarith only [high]) hx.le⟩

end New.PrimeCutoff
