module

public import TauCeti.Analysis.Meromorphic.Continuation
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

/-!
# The value left after a pole cancels

All normal forms below use the punctured germ. The two polynomials at the end
give an explicit instance in which the isolated point value changes.
-/

@[expose] public section

open Complex Filter Set Topology

namespace New.PrimeCutoff

/-- A meromorphic function with at most a simple pole has an analytic normal
form at a point where its residue vanishes. The limit assumption includes the
at-most-simple condition. -/
theorem analytic_fill_of_zero_residue {f : ℂ → ℂ} (hm : Meromorphic f) {s : ℂ}
    (zero : Tendsto (fun z ↦ (z - s) * f z) (𝓝[≠] s) (𝓝 0)) :
    AnalyticAt ℂ (toMeromorphicNFOn f univ) s := by
  have hlin : MeromorphicAt (fun z : ℂ ↦ z - s) s := by fun_prop
  have h := (tendsto_zero_iff_meromorphicOrderAt_pos (hlin.mul (hm s))).1 zero
  rw [meromorphicOrderAt_mul hlin (hm s), meromorphicOrderAt_id_sub_const] at h
  have nn : 0 ≤ meromorphicOrderAt f s := by
    cases eq : meromorphicOrderAt f s with
    | top => simp
    | coe m =>
      rw [eq] at h
      have pos : ((0 : ℤ) : WithTop ℤ) < ((1 + m : ℤ) : WithTop ℤ) := by simpa using h
      have : 0 < 1 + m := by exact_mod_cast pos
      exact_mod_cast (show 0 ≤ m by omega)
  apply ((meromorphicNFOn_toMeromorphicNFOn f univ) (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.1
  rwa [meromorphicOrderAt_congr (hm.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s))]

/-- Two simple zeros leave a nonzero regular term: for F(z)=z(1+z), G(z)=z,
the pointwise log-derivative difference at zero is 0 and its continuation is 1. -/
theorem shared_zero_example :
    let f := fun z : ℂ ↦ z * (1 + z)
    let g := fun z : ℂ ↦ z
    let h := fun z ↦ logDeriv f z - logDeriv g z
    h 0 = 0 ∧ Tendsto h (𝓝[≠] 0) (𝓝 1) ∧ toMeromorphicNFOn h univ 0 = 1 := by
  intro f g h
  let k := fun z : ℂ ↦ 1 / (1 + z)
  have ha : AnalyticAt ℂ k 0 := by dsimp [k]; fun_prop (disch := norm_num)
  have raw : h =ᶠ[𝓝[≠] (0 : ℂ)] k := by
    have hn : ∀ᶠ z : ℂ in 𝓝 0, 1 + z ≠ 0 := (continuous_const.add continuous_id).continuousAt.eventually_ne (by norm_num)
    filter_upwards [self_mem_nhdsWithin, hn.filter_mono nhdsWithin_le_nhds] with z hz h₁
    have nz : z ≠ 0 := hz
    dsimp [h, f, g, k]
    rw [logDeriv_apply, logDeriv_apply, deriv_fun_mul (by fun_prop) (by fun_prop)]
    have d₁ : deriv (fun w : ℂ ↦ 1 + w) z = 1 := ((hasDerivAt_id z).const_add (1 : ℂ)).deriv
    simp only [deriv_id'', d₁, one_mul, mul_one]
    field_simp
    ring
  have hm : Meromorphic h := fun _ ↦ by dsimp [h, f, g]; fun_prop [logDeriv]
  have value : k 0 = 1 := by norm_num [k]
  have same := (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hm.meromorphicOn (mem_univ (0 : ℂ))).trans
    ((toMeromorphicNFAt_eventuallyEq_nhds_congr raw).trans ((toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt).eventuallyEq))
  refine ⟨by simp [h, f, g, logDeriv_apply], ?_, same.eq_of_nhds.trans value⟩
  exact value ▸ (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' raw.symm

end New.PrimeCutoff
