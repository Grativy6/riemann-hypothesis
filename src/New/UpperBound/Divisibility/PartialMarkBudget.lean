module

public import New.UpperBound.Divisibility.MarkedResidues
import New.Reduction.Data.Sizes
import Mathlib.Tactic

/-!
# Low-column and transfer allowances for partial marks

The finite-prime fiber is a coset of the even powers of the global Frobenius element.
Every selected finite prime has the same number of places and all those places have the off
weight. The transfer and low-column inequality therefore scales by the marked fraction.
-/

@[expose] public section

namespace New.Data

open Finset
variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]

/-- The image of a translated cyclic subgroup has its order as cardinality. -/
private lemma card_translated_powers {H : Type*} [Group H] [Fintype H] (u x : H) :
    Nat.card {y : H // ∃ n : ℕ, y = u^n*x} = orderOf u := by
  let e : Submonoid.powers u ≃ {y : H // ∃ n : ℕ, y = u^n*x} := {
    toFun := fun y ↦ ⟨y.val * x, by obtain ⟨n, hn⟩ := y.property; exact ⟨n, congrArg (· * x) hn.symm⟩⟩
    invFun := fun z ↦ ⟨z.val / x, by obtain ⟨n, hn⟩ := z.property; exact ⟨n, by simp [hn]⟩⟩
    left_inv := fun y ↦ Subtype.ext (by simp)
    right_inv := fun z ↦ Subtype.ext (by simp) }
  calc _ = Nat.card (Submonoid.powers u) := Nat.card_congr e.symm
    _ = orderOf u := by
      have e' := finEquivPowers (isOfFinOrder_of_finite u)
      simpa using (Nat.card_congr e').symm

open scoped Classical in
/-- Over all infinite places, a single induced prime is visited by the even powers. -/
lemma card_all_inducing_prime (hi : chiK P.d p = -1) (τ : D.Φ) :
    #{σ : D.Φ | inducedPlace σ = inducedPlace τ} =
      orderOf ((D.placeOfInt (-(p : ℤ)))^2) := by
  classical
  let g := D.placeOfInt (-(p : ℤ))
  have eq (σ : D.Φ) : inducedPlace σ = inducedPlace τ ↔ ∃ n : ℕ, σ = (g^2)^n*τ := by
    simpa only [g, pow_mul] using inducedPlace_eq_iff_even_powers hi σ τ
  calc #{σ : D.Φ | inducedPlace σ = inducedPlace τ} =
      Nat.card {σ : D.Φ // ∃ n : ℕ, σ = (g^2)^n*τ} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        simp only [eq]
    _ = _ := card_translated_powers (g^2) τ

/-- Each selected finite prime contributes exactly half of the global Frobenius cycle. -/
lemma IsMarked.card_placesInducing_eq {Λ : Finset (FinPlace D.E)} (h : D.IsMarked Λ) :
    #(placesInducing Λ) = #Λ * (orderOf (D.placeOfInt (-(p : ℤ))) / 2) := by
  classical
  have h2 := D.m_even.two_dvd.trans h.isExceptional.m_dvd_orderOf
  have fiber (l : FinPlace D.E) (hl : l ∈ Λ) :
      #{σ : D.Φ | inducedPlace σ = l} = orderOf (D.placeOfInt (-(p : ℤ))) / 2 := by
    obtain ⟨τ, _, rfl⟩ := h.induced_by_aPlace l hl
    rw [card_all_inducing_prime h.isExceptional.chiK_eq_neg_one, orderOf_pow_of_dvd (by decide : 2 ≠ 0) h2]
  calc #(placesInducing Λ) = ∑ l ∈ Λ, #{σ : D.Φ | inducedPlace σ = l} := by
          simpa only [placesInducing] using (sum_card_fiberwise_eq_card_filter univ Λ inducedPlace).symm
    _ = _ := by rw [sum_congr rfl fiber, sum_const, nsmul_eq_mul]; simp

/-- The low columns discard height one, so their count depends on the place only through its weight. -/
lemma lowColumns_congr_weight (j : ℕ) {σ τ : D.Φ} (h : D.weight σ = D.weight τ) :
    D.lowColumns j σ = D.lowColumns j τ := by
  unfold lowColumns
  apply sum_congr rfl
  intro i hi
  by_cases h1 : i = 1 <;> simp [h1, columnCount, liftWeight_eq, h]

open scoped Classical in
/-- Marked places have the off weight, as does the identity a-place. All their low columns
can therefore be counted from one diagram. -/
lemma IsMarked.sum_lowColumns_eq {Λ : Finset (FinPlace D.E)} (h : D.IsMarked Λ) (j : ℕ) :
    ∑ σ ∈ placesInducing Λ, D.lowColumns j σ =
      (#Λ * (orderOf (D.placeOfInt (-(p : ℤ))) / 2)) * D.lowColumns j 1 := by
  have hone : (1 : D.Φ) ∉ D.bPlaces := by
    intro h1
    have hz := D.placeClass_of_mem_bPlaces 1 h1
    have hbad : (1 : ZMod P.q₀) = -1 := by simpa using congrArg (fun z : (ZMod P.q₀)ˣ ↦ (z : ZMod P.q₀)) hz
    exact P.d_pow_ne_neg_one 0 (by simpa using hbad)
  have term (σ : D.Φ) (hσ : σ ∈ placesInducing Λ) : D.lowColumns j σ = D.lowColumns j 1 := by
    apply lowColumns_congr_weight j
    rw [D.weight_eq_ite, D.weight_eq_ite, ite_eq_right hone, ite_eq_right (h.notMem_bPlaces σ (.inl (by simpa using hσ)))]
  rw [sum_congr rfl term, sum_const, h.card_placesInducing_eq, nsmul_eq_mul]
  simp

end New.Data

namespace New.Data

open Finset Real
variable {P : Parameters} (D : Data P)

/-- Fraction of conjugate-prime pairs selected by a mark at the given prime. -/
noncomputable def markedShare (p : ℕ) (Λ : Finset (FinPlace D.E)) : ℝ := (#Λ : ℝ) / D.returnPairCount p

variable {D} {p : ℕ} [Fact p.Prime] [PadicPlace p] {Λ : Finset (FinPlace D.E)}

lemma IsMarked.card_le_pairCount (h : D.IsMarked Λ) : #Λ ≤ D.returnPairCount p := by
  have hd : D.o₀ p ∣ orderOf (D.placeOfInt (-(p : ℤ))) := orderOf_map_dvd _ _
  have hn := Nat.div_pos (Nat.le_of_dvd (orderOf_pos _) hd) h.isExceptional.odd_o₀.pos
  apply Nat.le_of_mul_le_mul_right _ hn
  rw [returnPairCount_mul_period h.isExceptional.chiK_eq_neg_one h.isExceptional.odd_o₀]
  have := h.card_uncovered_add_card_mul_pair
  omega

lemma IsMarked.share_le_one (h : D.IsMarked Λ) : D.markedShare p Λ ≤ 1 := by
  have hg : 0 < (D.returnPairCount p : ℝ) := by exact_mod_cast D.returnPairCount_pos p
  exact (div_le_one hg).2 (by exact_mod_cast h.card_le_pairCount)

lemma IsMarked.share_eq_one_iff (h : D.IsMarked Λ) : D.markedShare p Λ = 1 ↔ D.IsFullMark Λ := by
  have hg : (D.returnPairCount p : ℝ) ≠ 0 := by exact_mod_cast (D.returnPairCount_pos p).ne'
  rw [markedShare, div_eq_one_iff_eq hg, Nat.cast_inj, h.full_iff_card_returnPairCount]

/-- Twice the selected distinguished places equal the mark count times the first-return period. -/
lemma IsMarked.twice_selected_eq (h : D.IsMarked Λ) :
    2 * #(D.aPlaces ∩ placesInducing Λ) = #Λ * (orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p) := by
  have h₁ := h.card_uncovered_add_card_mul_pair
  have h₂ := h.card_uncovered_add_twice
  omega

/-- The low-column and transfer allowance scales with the fraction of pairs marked. All places
inducing a marked prime have the same weight; each selected prime has a whole even-power orbit. -/
theorem IsMarked.transfer_lowColumns_le_share (h : D.IsMarked Λ) {j : ℕ} (hj : j < D.m) :
    (#Λ : ℝ) * D.transferExponent p + D.ceilLogLifts p *
        (∑ σ ∈ placesInducing Λ, D.lowColumns j σ : ℕ) ≤
      D.markedShare p Λ * (D.loss p / D.m) + #(D.aPlaces ∩ placesInducing Λ) * (D.a / D.x₁) := by
  classical
  let u := orderOf (D.placeOfInt (-(p : ℤ))) / 2
  let v := orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p
  let E : ℝ := D.transferExponent p + D.ceilLogLifts p * (u : ℝ) * D.lowColumns j 1 -
    (v : ℝ)/2 * (D.a/D.x₁)
  have price (Γ : Finset (FinPlace D.E)) (hΓ : D.IsMarked Γ) :
      (#Γ : ℝ) * D.transferExponent p + D.ceilLogLifts p *
          (∑ σ ∈ placesInducing Γ, D.lowColumns j σ : ℕ) -
        #(D.aPlaces ∩ placesInducing Γ) * (D.a / D.x₁) = (#Γ : ℝ) * E := by
    have hc : 2 * (#(D.aPlaces ∩ placesInducing Γ) : ℝ) = (#Γ : ℝ) * (v : ℝ) := by
      exact_mod_cast hΓ.twice_selected_eq
    rw [hΓ.sum_lowColumns_eq]
    push_cast
    dsimp only [E, u]
    linear_combination -(D.a / D.x₁) / 2 * hc
  let F := D.arithmeticMark p
  have full := h.isExceptional.isFullMark_arithmeticMark h.isSmallNonsplit
  have bound : (D.returnPairCount p : ℝ)*E ≤ D.loss p / D.m := by
    rw [← full.card_eq_returnPairCount, ← price F full.toIsMarked]
    have hb := full.card_mul_transferExponent_add_sum_lowColumns_le hj
    dsimp only [F] at *
    linarith
  have hk : 0 ≤ D.markedShare p Λ := by unfold markedShare; positivity
  have hG : (D.returnPairCount p : ℝ) ≠ 0 := by exact_mod_cast (D.returnPairCount_pos p).ne'
  have mulE : (#Λ : ℝ)*E = D.markedShare p Λ*((D.returnPairCount p : ℝ)*E) := by
    unfold markedShare
    field_simp
  have paid := (mul_le_mul_of_nonneg_left bound hk)
  linarith [price Λ h, mulE]

end New.Data
