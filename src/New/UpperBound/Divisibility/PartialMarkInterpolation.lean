module

public import New.UpperBound.Divisibility.FiniteMarkedCollisions
import New.UpperBound.Divisibility.ChainDatumExpansion
import Mathlib.Tactic

/-!
# A common local witness at every marked fraction

Each selected pair carries its fraction of the index and transfer prices. The remaining fraction
carries the unmarked collision deficit. Interpolation gives one local submodule and an exact
criterion for its displayed bound to reach the full-mark target.
-/

@[expose] public section

namespace New.Data

open Finset Real
variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]
  {Λ : Finset (FinPlace D.E)}

lemma IsMarked.deficit_eq_unmarkedShare (h : D.IsMarked Λ) :
    D.collisionDeficit p (placesInducing Λ) = (1 - D.markedShare p Λ) * D.collisionDeficit p ∅ := by
  have hg : (D.returnPairCount p : ℝ) ≠ 0 := by exact_mod_cast (D.returnPairCount_pos p).ne'
  calc D.collisionDeficit p (placesInducing Λ) =
      ((D.returnPairCount p : ℝ) * D.collisionDeficit p (placesInducing Λ)) / D.returnPairCount p := by field_simp
    _ = ((D.returnPairCount p - (#Λ : ℝ)) * D.collisionDeficit p ∅) / D.returnPairCount p := by
      rw [h.collisionDeficit_return_share]
    _ = _ := by unfold markedShare; field_simp

/-- The valuation allowance is the affine interpolation between the unmarked and full-mark
allowances, with the actual fraction of marked pairs as coefficient. -/
theorem IsMarked.gauge_exponent_interpolation (h : D.IsMarked Λ) :
    D.m * D.collisionDeficit p (placesInducing Λ) + (1 + D.markedShare p Λ)*D.loss p - D.gain p =
      (1 - D.markedShare p Λ)*(D.m * D.collisionDeficit p ∅ + D.loss p - D.gain p) +
        D.markedShare p Λ*(2*D.loss p - D.gain p) := by
  rw [h.deficit_eq_unmarkedShare]
  ring

/-- For this bound, an incomplete mark reaches the full-mark target exactly when the
unmarked deficit is already paid. -/
theorem IsMarked.gauge_exponent_le_target_iff (h : D.IsMarked Λ) :
    D.m * D.collisionDeficit p (placesInducing Λ) + (1+D.markedShare p Λ)*D.loss p - D.gain p ≤
      2*D.loss p - D.gain p ↔ D.IsFullMark Λ ∨ D.collisionClearance p = 0 := by
  have cutoff : D.collisionClearance p = 0 ↔ D.m * D.collisionDeficit p ∅ ≤ D.loss p := by
    rw [← Nat.le_zero, collisionClearance_le_iff]
    simp
  have diff :
      (D.m * D.collisionDeficit p (placesInducing Λ) + (1+D.markedShare p Λ)*D.loss p - D.gain p) -
        (2*D.loss p - D.gain p) =
          (1-D.markedShare p Λ)*(D.m*D.collisionDeficit p ∅ - D.loss p) := by
    rw [h.deficit_eq_unmarkedShare]
    ring
  rw [← sub_nonpos, diff, cutoff]
  constructor
  · intro hbudget
    by_cases full : D.IsFullMark Λ
    · exact Or.inl full
    · have hstrict : D.markedShare p Λ < 1 := lt_of_le_of_ne h.share_le_one (fun hx ↦ full (h.share_eq_one_iff.1 hx))
      exact Or.inr (sub_nonpos.1 (nonpos_of_mul_nonpos_right hbudget (sub_pos.2 hstrict)))
  · rintro (full | paid)
    · rw [h.share_eq_one_iff.2 full, sub_self, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 h.share_le_one) (sub_nonpos.2 paid)

end New.Data

namespace New.Data

open Finset Real Submodule Module
open scoped Pointwise
variable {P : Parameters} (D : Data P) (p : ℕ) (Λ : Finset (FinPlace D.E))

open scoped Classical in
/-- Select the first `k` canonical offsets. -/
noncomputable def markPrefix [Fact p.Prime] [PadicPlace p] (k : ℕ) : Finset (FinPlace D.E) :=
  (range k).image fun i ↦ inducedPlace (D.distinguishedLift i)

/-- Every numerator from zero through the number of pairs is realized by a concrete marked set. -/
theorem IsExceptional.markPrefix_spec {D : Data P} {p : ℕ}
    [Fact p.Prime] [PadicPlace p] (he : D.IsExceptional p) (hs : D.IsSmallNonsplit p)
    {k : ℕ} (hk : k ≤ D.returnPairCount p) :
    D.IsMarked (D.markPrefix p k) ∧ #(D.markPrefix p k) = k := by
  classical
  constructor
  · apply (he.isFullMark_arithmeticMark hs).toIsMarked.of_subset
    intro l hl
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hl
    exact mem_image_of_mem _ (mem_range.2 ((mem_range.1 hi).trans_le hk))
  · rw [markPrefix, card_image_of_injOn, card_range]
    intro i hi j hj eq
    exact he.distinguish_lift_pair ((mem_range.1 hi).trans_le hk) ((mem_range.1 hj).trans_le hk) (.inl eq)

/-- Least natural scalar exponent needed to match the interpolated marked-product allowance. -/
noncomputable def partialClearance : ℕ :=
  ⌈D.markedShare p Λ * (D.m * D.collisionDeficit p ∅ - D.loss p)⌉₊

variable {D p Λ} [hp : Fact p.Prime] [PadicPlace p]

lemma IsFullMark.partialClearance_eq (h : D.IsFullMark Λ) : D.partialClearance p Λ = D.collisionClearance p := by
  simp only [partialClearance, h.toIsMarked.share_eq_one_iff.2 h, one_mul, collisionClearance]

/-- A single submodule input for both the determinant and the valuation at a partial mark. -/
noncomputable def IsMarked.commonModule (h : D.IsMarked Λ) (j : ℕ) : Submodule embValRing D.SourceForm :=
  D.integralSourceForms.map ((Λ.attach.toList.map h.scaledHeckeOperator).prod ^ D.m) ⊔
    (p : embValRing)^j • D.integralSourceForms

/-- The marked product, together with any scalar covering its partial clearance, has the
interpolated gauge bound on the whole common module. -/
theorem IsChainDatum.gaugeLe_compositeLift_partial {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}
    (hΨ : IsChainDatum ϑ Ψ) (hQ : p.Coprime ϑ.normQ) (h : D.IsMarked Λ)
    {j : ℕ} (hj : D.partialClearance p Λ ≤ j) {φ : D.SourceForm} (hφ : φ ∈ h.commonModule j) :
    GaugeLe 1 (p ^ ((1-D.markedShare p Λ)*(D.m*D.collisionDeficit p ∅+D.loss p-D.gain p) +
        D.markedShare p Λ*(2*D.loss p-D.gain p))) (compositeLift ϑ Ψ φ) := by
  obtain ⟨Ψ', hΨ', heq⟩ : ∃ Ψ' : D.Translations →₀ ℂ, IsWeakChainDatum ϑ Ψ' ∧
      ∀ φ : D.SourceForm, compositeLift ϑ Ψ φ = restrictedChain ϑ Ψ' φ :=
    hΨ.exists_isWeakChainDatum_compositeLift_eq
  obtain ⟨u, hu, v, hv, rfl⟩ : ∃ u ∈ D.integralSourceForms, ∃ v ∈ D.integralSourceForms,
      ((Λ.attach.toList.map h.scaledHeckeOperator).prod ^ D.m) u + (p : ℂ)^j • v = φ := by
    obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, hs⟩ := mem_sup.1 hφ
    exact ⟨u,hu,v,hv,hs⟩
  rw [heq, map_add]
  have product := hΨ'.gaugeLe_restrictedChain_markedShare hQ hu h
  rw [h.gauge_exponent_interpolation] at product
  apply product.add
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have norm : ‖ιₚ ((p : ℂ)^j)‖ = (p : ℝ)^(-(j : ℝ)) := by simp [norm_p_eq_inv, rpow_neg]
  have scalar := (hΨ'.gaugeLe_restrictedChain_collisionDeficit hQ hv h.isSmallNonsplit).smul ((p : ℂ)^j)
  rw [norm, ← rpow_add hp0] at scalar
  rw [map_smul]
  refine scalar.rpow_mono ?_
  have paid : D.markedShare p Λ * (D.m * D.collisionDeficit p ∅ - D.loss p) ≤ j := Nat.ceil_le.1 hj
  linarith

/-- Each partial mark has its own joint witness. Both bounds use the same marked set and
the same least scalar exponent. The index price is the corresponding share of the full price
evaluated at that exponent. -/
theorem IsMarked.partial_common_witness (h : D.IsMarked Λ) :
    let j := D.partialClearance p Λ
    ∃ c : ℕ, c ≤ D.markedShare p Λ * D.fullReturnIndexCost p j * finrank ℂ D.SourceForm ∧
      ColengthDvd D.integralSourceForms (h.commonModule j) (p^c) ∧
      ∀ (ϑ : D.Twist) (Ψ : D.Translations →₀ ℂ), IsChainDatum ϑ Ψ → p.Coprime ϑ.normQ →
        ∀ φ ∈ h.commonModule j, GaugeLe 1
          (p ^ ((1-D.markedShare p Λ)*(D.m*D.collisionDeficit p ∅+D.loss p-D.gain p) +
            D.markedShare p Λ*(2*D.loss p-D.gain p))) (compositeLift ϑ Ψ φ) := by
  intro j
  obtain ⟨_, c, hc, index⟩ := h.isOntoUpToColength_prod_scaledHeckeOperator_pow_return j
  refine ⟨c, by simpa only [h.returnProductIndexCost_eq_share] using hc, index, ?_⟩
  exact fun ϑ Ψ hΨ hQ φ hφ ↦ hΨ.gaugeLe_compositeLift_partial hQ h le_rfl hφ

end New.Data
