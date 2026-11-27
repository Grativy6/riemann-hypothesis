module

import Mathlib.Data.Rat.Cast.OfScientific
public import New.Reduction.PrimeSums
import New.Determinant.Twist.LongForms
import New.Reduction.ShortAndEnough

/-!
# The main inequality

One covolume, corrected by an index, is bounded from both sides. Write `dim` for the dimension of
the target (`targetDim`), `mainAmount` for the main amount and `rem` for the total remainder
(`totalRemainder`), weighted sums over primes less their expected values. Theorems A and B give a
family of `n ≤ dim` target forms, a bound `V` for the logarithm of the squared covolume of its lifts
(`TwistedLattice.CovolumeLe`) and a bound `δ` for its index (`TwistedLattice.IndexLe`). Up to
errors,

    mainAmount ≤ (V + 2 δ) / dim ≤ mainAmount - (n / dim) m rem,

where the lower bound is Theorem C. The main amount cancels.

Notions from other files:

* `Data P`: the data for the parameters `P` (a modulus `q₀` and a prime `d`). They bundle
  scales `x`, `x₁`, `b` in prescribed ranges (`D.logB = log b`), the number `D.m` of lifts, a set
  of places of the CM field `D.E`, the `b`-places, which carry the weight `b`, and primes for the
  levels. `D.a = x b`, and `D.f` is the number of infinite places of `D.E`.
* `D.normalizedPoincare g`: the translate `g 𝔭` by `g : D.chosenGL` of a fixed linear map `𝔭` from
  the source `D.ramifiedSourceForms` to the target `D.targetForms`.
* `D.integralRamified`: the source forms that are integral at every `ι : PrimePadicIso`.
* `D.errorUnit`: the unit of loss `f a log³ b`.

## The inputs

* Theorem A: (a) `span_short_integralRamified_eq_top` (size) and (b) `indexLe_normalizedPoincare`
  (index), both in `New.Reduction.ShortAndEnough`.
* Theorem B: `enough_forms` in `New.Reduction.ShortAndEnough`.
* Theorem C: `integral_forms_long` in `New.Determinant.Twist.LongForms`, from a twist for each prime
  (`TwistedLattice.covolume_add_index_nonneg`) and the height of `Z(1) / Z(ξ_ι)`
  (`heightLe_chainDeterminant_one_div`).
* Hadamard's bound for the covolume: `TwistedLattice.covolumeLe_of_normSqAt_le`.
* The sign of the main amount: `mainAmount_nonneg`.

## What cancels, and where

* The main amount, between the upper and the lower bound: the comparison step of
  `remainder_with_rank_share`.
* The gains `∑ gain_l log l` in the size of the chain, against `log c_B`:
  `span_short_integralRamified_eq_top`.
* The constant `c₁ = (logDerivMean d 1 1).re`, between the period and the expected value
  `a (log (a / κ̄) + c₁)` of the prime sums:
  `jetSize_sub_mainPrimeSum_le`.
* The excesses `a log (κ̄ M rd_E / 2π)` of the `m` lifts, against `a log N`, up to `O(a log b)`.
  Here `κ̄` is the geometric mean of the weights `κ` over the `f` places and `rd_E` is the root
  discriminant of `E`:
  `mul_jetSize_sub_mainPrimeSum_sub_le`.
* The main terms `log x`, `log x₁` and `c₁` of the prime sums, against their expected value:
  `totalRemainder_eq`.
* A constant that depends on `q₀`, between the two cut-offs: `sum_aPlaces_primeSum`.

## The errors per dimension

| source   | where             | amount                              |
|----------|-------------------|-------------------------------------|
| size     | Theorem A (a)     | `f a log⁴ b`                        |
| index    | Theorems A (b), B | `320 log (1 + 2 b²) · #aPlaces · a · log x₁`    |
| covolume | Theorem C         | `3 f a log⁴ b`                      |

The doubled index is the amount in the table. The family has at least `(1 - 4/b²) dim` members.
Keeping this share yields `m rem ≤ 5 f a log⁴ b` at the given scales. The scales
are listed in `New.Reduction.Data.Sizes`.

## Relation to the literature

Earlier bounds for sums over primes by size against divisibility: Pritsker, The Gelfond–Schnirelman
method in prime number theory, 2005; Granville–Stark, ABC implies no Siegel zeros for L-functions of
characters with negative discriminant, 2000; Bombieri, Counting points on curves over finite fields,
Sém. Bourbaki 430, 1973; van Frankenhuijsen, The Riemann hypothesis for function fields over a
finite field, 2008.
-/

@[expose] public section

namespace New

open Real Finset Data Module Submodule

/-- The error after cancellation retains the lower bound on the rank share and the separate
determinant cost. -/
theorem remainder_with_rank_share {P : Parameters} (D : Data P) :
    (1 - 4 / D.b^2) * (D.m * D.totalRemainder) ≤ 4 * (D.f * D.a * D.logB^4) +
      320 * log (1 + 2 * D.b^2) * #D.aPlaces * D.a * D.logX₁ := by
  -- Choose many independent images of short integral forms, bound their covolume and index from
  -- above, and compare with the lower bound `integral_forms_long`.
  obtain ⟨h_dim_pos, t, h_translate_budget, h_span_dimension⟩ :
      0 < D.targetDim ∧ ∃ t : Finset D.chosenGL,
      #t * finrank ℂ D.ramifiedSourceForms ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2) ∧
      (1 - 4 / D.b ^ 2) * D.targetDim ≤ finrank ℂ ↥(⨆ g ∈ t, (D.normalizedPoincare g).range) :=
    D.enough_forms
  let sizeError : ℝ := D.f * D.a * D.logB ^ 4
  let logNormBound : ℝ := D.mainAmount - D.m * D.totalRemainder + sizeError
  let indexBudgetPerDim : ℝ := 160 * log (1 + 2 * D.b ^ 2) * #D.aPlaces * D.a * D.logX₁
  let short : Set D.ramifiedSourceForms :=
    {φ ∈ D.integralRamified | ∀ (g : D.chosenGL) (σ : ℂ ≃+* ℂ),
      (D.Θ 1 (D.normalizedPoincare g φ)).normSqAt σ ≤ exp logNormBound}
  have h_short_span : span ℂ short = ⊤ := D.span_short_integralRamified_eq_top
  -- A + B: take a basis from the images of short source forms under the chosen translates.
  obtain ⟨n, y, h_indep, h_near_full_rank, h_image_short⟩ : ∃ (n : ℕ) (y : Fin n → D.targetForms),
      LinearIndependent ℂ y ∧ (1 - 4 / D.b ^ 2) * D.targetDim ≤ n ∧
      ∀ i : Fin n, ∃ g ∈ t, y i ∈ D.normalizedPoincare g '' short := by
    let images : Set D.targetForms := ⋃ g ∈ t, D.normalizedPoincare g '' short
    have span_eq : span ℂ images = ⨆ g ∈ t, (D.normalizedPoincare g).range := by
      simp only [images, span_iUnion₂, span_image, h_short_span, Submodule.map_top]
    obtain ⟨y, hy_mem, -, h_indep⟩ := exists_fun_fin_finrank_span_eq ℂ images
    refine ⟨finrank ℂ (span ℂ images), y, h_indep, by rwa [span_eq], fun i ↦ ?_⟩
    simpa only [images, Set.mem_iUnion, exists_prop] using hy_mem i
  have hn_le : (n : ℝ) ≤ D.targetDim := by simpa using h_indep.fintype_card_le_finrank
  -- Covolume: each form has squared length at most `exp logNormBound`.
  have h_covolume_upper : D.targetLattice.CovolumeLe y (n * logNormBound) := by
    refine TwistedLattice.covolumeLe_of_normSqAt_le fun i σ ↦ ?_
    obtain ⟨g, -, φ, ⟨-, hφ_short⟩, hφ_eq⟩ := h_image_short i
    rw [normSqAt_targetLattice, ← hφ_eq]
    exact hφ_short g σ
  -- Each translate contributes `32 · #aPlaces · a · log x₁` per dimension of the ramified source.
  have h_index_upper : D.targetLattice.IndexLe y (D.targetDim * indexBudgetPerDim) := by
    have hL : 0 ≤ D.logX₁ := (HasLogBound.pos D).le
    have hy_int (i : Fin n) : ∃ g ∈ t, y i ∈ D.normalizedPoincare g '' D.integralRamified := by
      obtain ⟨g, hg, φ, ⟨hφ_int, -⟩, hφ_eq⟩ := h_image_short i
      exact ⟨g, hg, φ, hφ_int, hφ_eq⟩
    refine (D.indexLe_normalizedPoincare t hy_int).mono ?_
    calc #t * finrank ℂ D.ramifiedSourceForms * (32 * #D.aPlaces * D.a * D.logX₁)
        ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2) * (32 * #D.aPlaces * D.a * D.logX₁) := by
          grw [h_translate_budget]
      _ = D.targetDim * indexBudgetPerDim := by ring
  -- C: apply the lower bound to the same family. The index is counted twice (the two Gram
  -- variables); the nonnegative main amount cancels using `n ≤ targetDim`.
  have h_volume_index_lower :
      D.targetDim * (D.mainAmount - 3 * sizeError) ≤
        n * logNormBound + 2 * (D.targetDim * indexBudgetPerDim) :=
    integral_forms_long h_indep h_near_full_rank h_index_upper h_covolume_upper
  have h_loss_pos : 0 < sizeError := HasLogBound.pos D
  have h_main_comparison :
      n * (D.mainAmount + sizeError) ≤ D.targetDim * (D.mainAmount + sizeError) :=
    mul_le_mul_of_nonneg_right hn_le (add_nonneg D.mainAmount_nonneg h_loss_pos.le)
  let totalErrorPerDim : ℝ := 4 * sizeError + 2 * indexBudgetPerDim
  have h_main_cancelled : n * (D.m * D.totalRemainder) ≤ D.targetDim * totalErrorPerDim := by
    simp only [logNormBound, totalErrorPerDim] at h_volume_index_lower ⊢
    linarith only [h_volume_index_lower, h_main_comparison]
  have hL : 0 ≤ D.logX₁ := (HasLogBound.pos D).le
  have hlog : 0 ≤ Real.log (1 + 2 * D.b^2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg D.b])
  have hidx : 0 ≤ indexBudgetPerDim := by dsimp [indexBudgetPerDim]; positivity
  have htotal : 0 ≤ totalErrorPerDim := by dsimp [totalErrorPerDim]; positivity
  have hq : 0 < 1 - 4 / D.b^2 := by
    have h : 4 / D.b^2 ≤ (2 : ℝ)⁻¹ := D.le_of_hasLogBound
    linarith
  have hn : (0 : ℝ) < n := (mul_pos hq (Nat.cast_pos.2 h_dim_pos)).trans_le h_near_full_rank
  apply le_of_mul_le_mul_left (a := (n : ℝ)) _ hn
  calc
    _ = (1 - 4 / D.b^2) * (n * (D.m * D.totalRemainder)) := by ring
    _ ≤ (1 - 4 / D.b^2) * (D.targetDim * totalErrorPerDim) :=
      mul_le_mul_of_nonneg_left h_main_cancelled hq.le
    _ = ((1 - 4 / D.b^2) * D.targetDim) * totalErrorPerDim := by ring
    _ ≤ n * totalErrorPerDim := mul_le_mul_of_nonneg_right h_near_full_rank htotal
    _ = _ := by dsimp [totalErrorPerDim, indexBudgetPerDim, sizeError]; ring

/-- A coarse constant of five suffices at the fourth logarithmic power for these data. -/
theorem star_inequality_five {P : Parameters} (D : Data P) :
    D.m * D.totalRemainder ≤ 5 * D.f * D.a * D.logB^4 := by
  have hB : 0 < D.logB := HasLogBound.pos D
  have hb : 10 ≤ D.b := by
    change 10 ≤ Real.exp D.logB
    linarith [Real.add_one_le_exp D.logB, Real.log_le_sub_one_of_pos hB, D.constantBound_le,
      (Data.le_constantBound (P := P)).1]
  have hB3 : 3 ≤ D.logB := by
    linarith [Real.log_le_sub_one_of_pos hB, D.constantBound_le, (Data.le_constantBound (P := P)).1]
  have hL : 0 ≤ D.logX₁ := (HasLogBound.pos D).le
  have hpoly : 1 + 2 * D.b^2 ≤ D.b^3 := by
    nlinarith [mul_nonneg (show 0 ≤ D.b - 3 by linarith) (sq_nonneg D.b), sq_nonneg (D.b-1)]
  have hl : Real.log (1 + 2 * D.b^2) ≤ 3 * D.logB := by
    calc _ ≤ Real.log (D.b^3) := Real.log_le_log (by positivity) hpoly
         _ = _ := by rw [Real.log_pow]; simp [Data.b]
  have hlog0 : 0 ≤ Real.log (1 + 2 * D.b^2) := Real.log_nonneg (by nlinarith [sq_nonneg D.b])
  have hcb : 640 * Real.log (1 + 2 * D.b^2) * D.logX₁ ≤ D.logB^4 := by
    calc _ ≤ 640 * (3 * D.logB) * D.logX₁ := by gcongr
         _ = D.logB * (1920 * D.logX₁) := by ring
         _ ≤ D.logB * D.logB :=
           mul_le_mul_of_nonneg_left (by linarith only [D.logX₁_le_logB, hL]) hB.le
         _ ≤ D.logB^4 := by
           have h := le_mul_of_one_le_right (sq_nonneg D.logB)
             (show 1 ≤ D.logB^2 from one_le_pow₀ (by linarith))
           nlinarith only [h]
  have hcount : (#D.aPlaces : ℝ) ≤ D.f := by
    exact_mod_cast (show #D.aPlaces ≤ D.f from Finset.card_le_univ _)
  have hi : 2 * (320 * Real.log (1 + 2 * D.b^2) * #D.aPlaces * D.a * D.logX₁) ≤
      D.f * D.a * D.logB^4 := by
    calc _ = ((#D.aPlaces : ℝ) * D.a) * (640 * Real.log (1 + 2 * D.b^2) * D.logX₁) := by ring
         _ ≤ _ := by gcongr
  have hshare : (9 / 10 : ℝ) ≤ 1 - 4 / D.b^2 := by
    have h : 4 / D.b^2 ≤ (1 / 10 : ℝ) :=
      (div_le_iff₀ (by positivity)).2 (by nlinarith [sq_nonneg (D.b-10)])
    linarith
  by_cases hpos : 0 ≤ (D.m : ℝ) * D.totalRemainder
  · have h := (mul_le_mul_of_nonneg_right hshare hpos).trans (remainder_with_rank_share D)
    nlinarith only [h, hi]
  · exact (le_of_lt (lt_of_not_ge hpos)).trans (by positivity)

/-- The published right-hand side follows at the original scales. -/
theorem star_inequality {P : Parameters} (D : Data P) :
    D.m * D.totalRemainder ≤ D.f * D.a * D.logB ^ 5 := by
  have hB : 0 < D.logB := HasLogBound.pos D
  have h5 : 5 ≤ D.logB := by
    linarith [Real.log_le_sub_one_of_pos hB, D.constantBound_le, (Data.le_constantBound (P := P)).1]
  apply (star_inequality_five D).trans
  calc _ = ((D.f : ℝ) * D.a * D.logB^4) * 5 := by ring
       _ ≤ ((D.f : ℝ) * D.a * D.logB^4) * D.logB :=
         mul_le_mul_of_nonneg_left h5 (by positivity)
       _ = _ := by ring

end New
