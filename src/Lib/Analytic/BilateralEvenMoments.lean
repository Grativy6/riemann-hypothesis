module

public import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

/-!
# Both endpoints of an exponential moment

The nonnegative even terms of the tilted moment-generating function count the two
reflected real endpoints together. Their integral identity remains valid at infinity.
The later ordinary-Taylor comparison uses a centre in the interior of convergence.
-/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat Topology

namespace BilateralMoments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- Twice the even Taylor term of the exponential, tilted at the real centre z. -/
noncomputable def term (z h x : ℝ) (k : ℕ) : ℝ :=
  2 * ((h*x)^(2*k) / (2*k)!) * Real.exp (z*x)

lemma term_nonneg (z h x : ℝ) (k : ℕ) : 0 ≤ term z h x k := by
  have pos : 0 ≤ (h*x)^(2*k) := by rw [pow_mul]; positivity
  unfold term
  positivity

/-- Pointwise, retaining just the even terms gives the sum of both real endpoints. -/
lemma hasSum_term (z h x : ℝ) :
    HasSum (term z h x) (Real.exp ((z+h)*x) + Real.exp ((z-h)*x)) := by
  have S := ((Real.hasSum_cosh (h*x)).mul_left 2).mul_right (Real.exp (z*x))
  have value : Real.exp ((z+h)*x) + Real.exp ((z-h)*x) =
      2 * Real.cosh (h*x) * Real.exp (z*x) := by
    rw [Real.cosh_eq, add_mul, sub_mul, Real.exp_add, Real.exp_sub, Real.exp_neg]
    ring_nf
  rw [value]
  exact S

/-- The even moments record both tails, with the equality valid also when either side is infinite. -/
theorem endpoint_mass_eq_even (hX : Measurable X) (z h : ℝ) :
    (∫⁻ w, ENNReal.ofReal (Real.exp ((z+h)*X w)) ∂μ) +
      (∫⁻ w, ENNReal.ofReal (Real.exp ((z-h)*X w)) ∂μ) =
    ∑' k : ℕ, ∫⁻ w, ENNReal.ofReal (term z h (X w) k) ∂μ := by
  rw [← lintegral_add_left (by fun_prop), ← lintegral_tsum (by intro k; fun_prop [term])]
  apply lintegral_congr
  intro w
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
    ← ENNReal.ofReal_tsum_of_nonneg (term_nonneg z h (X w)) (hasSum_term z h (X w)).summable,
    (hasSum_term z h (X w)).tsum_eq]

lemma mem_iff_finite_mass (hX : Measurable X) (s : ℝ) :
    s ∈ integrableExpSet X μ ↔ (∫⁻ w, ENNReal.ofReal (Real.exp (s*X w)) ∂μ) < ⊤ := by
  change Integrable (fun w ↦ Real.exp (s*X w)) μ ↔ _
  have nonneg : 0 ≤ᵐ[μ] fun w ↦ Real.exp (s*X w) :=
    Filter.Eventually.of_forall fun w ↦ (Real.exp_pos _).le
  rw [← hasFiniteIntegral_iff_ofReal nonneg]
  exact ⟨Integrable.hasFiniteIntegral, fun h ↦ ⟨by fun_prop, h⟩⟩

theorem even_mass_lt_top_iff (hX : Measurable X) (z h : ℝ) :
    (∑' k : ℕ, ∫⁻ w, ENNReal.ofReal (term z h (X w) k) ∂μ) < ⊤ ↔
      z+h ∈ integrableExpSet X μ ∧ z-h ∈ integrableExpSet X μ := by
  rw [← endpoint_mass_eq_even hX, ENNReal.add_lt_top,
    mem_iff_finite_mass hX, mem_iff_finite_mass hX]


/-- Even Taylor coefficients at a real centre, with the real displacement h included. -/
noncomputable def moment (X : Ω → ℝ) (μ : Measure Ω) (z h : ℝ) (k : ℕ) : ℝ :=
  h^(2*k) / (2*k)! * ∫ w, X w^(2*k) * Real.exp (z*X w) ∂μ

lemma moment_nonneg (z h : ℝ) (k : ℕ) : 0 ≤ moment X μ z h k := by
  have hn (x : ℝ) : 0 ≤ x^(2*k) := by rw [pow_mul]; positivity
  exact mul_nonneg (div_nonneg (hn h) (by positivity)) (integral_nonneg fun w ↦
    mul_nonneg (hn (X w)) (Real.exp_pos _).le)

lemma term_factor (z h x : ℝ) (k : ℕ) :
    term z h x k = (2*(h^(2*k)/(2*k)!)) * (x^(2*k) * Real.exp (z*x)) := by
  unfold term
  rw [mul_pow]
  ring

lemma lintegral_term_eq_moment {z : ℝ} (hz : z ∈ interior (integrableExpSet X μ)) (h : ℝ) (k : ℕ) :
    (∫⁻ w, ENNReal.ofReal (term z h (X w) k) ∂μ) = ENNReal.ofReal (2*moment X μ z h k) := by
  have hint : Integrable (fun w ↦ term z h (X w) k) μ := by
    simp only [term_factor]
    exact (integrable_pow_mul_exp_of_mem_interior_integrableExpSet hz (2*k)).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun w ↦ term_nonneg z h (X w) k)]
  simp only [term_factor, moment, integral_const_mul, mul_assoc]

lemma tsum_ofReal_finite_iff {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) :
    (∑' k, ENNReal.ofReal (f k)) < ⊤ ↔ Summable f := by
  let g (k : ℕ) : ℝ≥0 := ⟨f k, hf k⟩
  have same (k : ℕ) : ENNReal.ofReal (f k) = (g k : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal (hf k)
  simp only [same, lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
  rfl

/-- At an interior point, summability of just the even Taylor coefficients is equivalent
to exponential integrability at both reflected endpoints, including boundary points. -/
theorem summable_even_iff_endpoints (hX : Measurable X) {z : ℝ}
    (hz : z ∈ interior (integrableExpSet X μ)) (h : ℝ) :
    Summable (moment X μ z h) ↔ z+h ∈ integrableExpSet X μ ∧ z-h ∈ integrableExpSet X μ := by
  rw [← even_mass_lt_top_iff hX]
  simp_rw [lintegral_term_eq_moment hz]
  rw [tsum_ofReal_finite_iff (fun k ↦ mul_nonneg (by norm_num) (moment_nonneg z h k))]
  exact ⟨fun s ↦ s.mul_left _, fun s ↦ by
    simpa using s.mul_left (2⁻¹ : ℝ)⟩

/-- The moment used above is the actual Taylor term of any germ agreeing with the MGF. -/
lemma moment_eq_even_derivative {z h : ℝ} (hz : z ∈ interior (integrableExpSet X μ))
    {g : ℂ → ℂ} (hg : g =ᶠ[𝓝 (z:ℂ)] complexMGF X μ) (k : ℕ) :
    moment X μ z h k =
      ((((2*k)!:ℂ)⁻¹ • (h:ℂ)^(2*k) • iteratedDeriv (2*k) g z):ℂ).re := by
  simp_rw [moment, hg.iteratedDeriv_eq, iteratedDeriv_complexMGF (z := z) hz,
    smul_eq_mul, ← Complex.ofReal_natCast]
  norm_cast
  ring

/-- Full Taylor summability in a real direction also controls its reflection. -/
theorem endpoints_of_summable_taylor (hX : Measurable X) {z h : ℝ}
    (hz : z ∈ interior (integrableExpSet X μ)) {g : ℂ → ℂ}
    (hg : g =ᶠ[𝓝 (z:ℂ)] complexMGF X μ)
    (hs : Summable fun k : ℕ ↦ ((k ! : ℂ)⁻¹ • (h:ℂ)^k • iteratedDeriv k g z : ℂ)) :
    z+h ∈ integrableExpSet X μ ∧ z-h ∈ integrableExpSet X μ := by
  apply (summable_even_iff_endpoints hX hz h).1
  have hsub := (Complex.hasSum_re hs.hasSum).summable.comp_injective
    (i := fun k : ℕ ↦ 2*k) (by intro x y eq; change 2*x=2*y at eq; omega)
  exact hsub.congr (fun k ↦ (moment_eq_even_derivative hz hg k).symm)


/-- An analytic continuation agreeing with the MGF in true convergence neighbourhoods
accumulating at a real point forces that point into the interior of exponential
integrability. The approach may come from either side. -/
theorem interior_of_continued_germ (hX : Measurable X) {a : ℝ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g (a:ℂ))
    (hnear : ∃ᶠ z : ℝ in 𝓝 a, z ∈ interior (integrableExpSet X μ) ∧
      g =ᶠ[𝓝 (z:ℂ)] complexMGF X μ) : a ∈ interior (integrableExpSet X μ) := by
  obtain ⟨ε, hε, analytic⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨z, ⟨hz,agree⟩, close⟩ := (hnear.and_eventually
    (Metric.ball_mem_nhds a (by positivity : (0:ℝ) < ε/4))).exists
  rw [mem_interior_iff_mem_nhds]
  refine Metric.mem_nhds_iff.2 ⟨ε/4, by positivity, fun s hs ↦ ?_⟩
  have za : dist (z:ℂ) (a:ℂ) < ε/4 := by
    simpa [Complex.isometry_ofReal.dist_eq] using (Metric.mem_ball.1 close)
  have sa : dist (s:ℂ) (a:ℂ) < ε/4 := by
    simpa [Complex.isometry_ofReal.dist_eq] using (Metric.mem_ball.1 hs)
  have sz : dist (s:ℂ) (z:ℂ) < ε/2 := by
    linarith [dist_triangle (s:ℂ) (a:ℂ) (z:ℂ),dist_comm (a:ℂ) (z:ℂ)]
  have series := (Complex.hasSum_taylorSeries_on_ball
    (analytic.mono (Metric.ball_half_subset _ (show dist (z:ℂ) (a:ℂ) < ε/2 by linarith))).differentiableOn
    (Metric.mem_ball.2 sz)).summable
  have hsum : Summable fun k : ℕ ↦ ((k !:ℂ)⁻¹ • ((s-z:ℝ):ℂ)^k • iteratedDeriv k g z : ℂ) := by
    simpa using series
  simpa using (endpoints_of_summable_taylor hX hz agree hsum).1

end BilateralMoments
