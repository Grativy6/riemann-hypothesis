module

public import New.UpperBound.Divisibility.ValuationAtNonSplitPrimes
import Lib.ClassField.HeckeCharacter.AlgebraicValues
import Lib.General.NumberTheory.ConjugateFiberParity
import Mathlib.Tactic

/-!
# The signed high-place count of a local chain character

A Frobenius step matches the sizes of the two full fibers at an inert prime. Only the
difference between the numbers of high places survives in the p-adic norm. At an exceptional
prime an odd total high-place count forces a nonunit outside every mark.
-/

@[expose] public section

open NumberField Finset Real
namespace New.Data

variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]

open scoped Classical in
/-- At an inert prime Frobenius pairs the two fibers, including when the finite prime is fixed. -/
lemma inert_equal_fiber_sizes (hi : chiK P.d p = -1) (l : FinPlace D.E) :
    #{τ : D.Φ | inducedPlace τ = l} = #{τ : D.Φ | star (inducedPlace τ) = l} := by
  classical
  apply card_equiv (Equiv.mulLeft (D.placeOfInt (-(p : ℤ))))
  intro τ
  have step : inducedPlace (D.placeOfInt (-(p : ℤ)) * τ) = star (inducedPlace τ) := by
    simpa using D.inducedPlace_neg_pow_mul_of_odd hi odd_one τ
  simp [step]

open scoped Classical in
/-- An arbitrary set of places pays the common lift weight once per place and the extra
height once per high place. Integer coefficients also retain the sign after subtraction. -/
lemma sum_liftWeight_by_high_places (D : Data P) (j : ℕ) (S : Finset D.Φ) :
    (∑ τ ∈ S, (D.liftWeight j τ : ℤ)) =
      (#S : ℤ)*(D.offWeight + j*D.gap + D.halfGap : ℕ) +
        (#(S ∩ D.bPlaces) : ℤ)*((D.natB : ℤ)-D.offWeight) := by
  classical
  have weight (τ : D.Φ) : (D.liftWeight j τ : ℤ) =
      (D.offWeight + j*D.gap + D.halfGap : ℕ) +
        if τ ∈ D.bPlaces then (D.natB : ℤ)-D.offWeight else 0 := by
    rw [liftWeight_eq, D.weight_eq_ite]
    split_ifs <;> push_cast <;> ring
  simp_rw [weight]
  rw [sum_add_distrib, ← sum_filter, sum_const, sum_const]
  simp [filter_mem_eq_inter]

open scoped Classical in
/-- Above an inert prime the entire residual slope of a chain character is its excess
height times the difference between the numbers of high places on the two sides. -/
theorem inert_liftWeight_difference (hi : chiK P.d p = -1) (l : FinPlace D.E) (j : ℕ) :
    (∑ τ : D.Φ with star (inducedPlace τ) = l, (D.liftWeight j τ : ℤ)) -
        (∑ τ : D.Φ with inducedPlace τ = l, (D.liftWeight j τ : ℤ)) =
      ((#((univ.filter fun τ : D.Φ ↦ star (inducedPlace τ) = l) ∩ D.bPlaces) : ℤ) -
        #((univ.filter fun τ : D.Φ ↦ inducedPlace τ = l) ∩ D.bPlaces)) * ((D.natB : ℤ) - D.offWeight) := by
  rw [D.sum_liftWeight_by_high_places, D.sum_liftWeight_by_high_places,
    inert_equal_fiber_sizes hi l]
  ring

end New.Data

namespace New.Data

open NumberField Finset Real Parameters
variable {P : Parameters} (D : Data P) (p : ℕ) [Fact p.Prime] [PadicPlace p]

open scoped Classical in
/-- The number of high-weight infinite places inducing a specified finite prime. -/
noncomputable def highCount (l : FinPlace D.E) : ℕ :=
  #{τ ∈ D.bPlaces | inducedPlace τ = l}

/-- The signed exponent seen by a chain character at the prime. -/
noncomputable def highSlope (l : FinPlace D.E) : ℤ :=
  ((D.highCount p (star l) : ℤ) - D.highCount p l) * ((D.natB : ℤ) - D.offWeight)

variable {D p}

lemma highSlope_star (l : FinPlace D.E) : D.highSlope p (star l) = -D.highSlope p l := by
  simp only [highSlope, star_star]
  ring

omit [Fact p.Prime] [PadicPlace p] in
lemma offWeight_lt_high (D : Data P) : D.offWeight < D.natB := by
  have hlog : 0 < D.logX := by
    linarith [D.mul_log_logB_le_logX, D.constantBound_le, (le_constantBound (P := P)).1]
  have hX : D.x < D.x₁ := exp_lt_exp.2 (by linarith [D.logX_le_logX₁])
  have h : (D.offWeight : ℝ) < D.natB := by
    rw [D.cast_offWeight, D.cast_natB, D.cast_a, div_lt_iff₀ (exp_pos _), mul_comm D.b]
    exact mul_lt_mul_of_pos_right hX (exp_pos _)
  exact_mod_cast h

/-- The finite prime induced by the infinite place named by the negative unit. -/
noncomputable def negativeUnitPrime (D : Data P) (p : ℕ) [Fact p.Prime] [PadicPlace p] : FinPlace D.E :=
  inducedPlace (D.placeOfInt (-1))

/-- The entire excess over the off weight, summed over the chosen high places. -/
def totalHighExcess (D : Data P) : ℤ := (#D.bPlaces : ℤ) * ((D.natB : ℤ) - D.offWeight)

lemma totalHighExcess_pos (D : Data P) : 0 < totalHighExcess D := by
  have pos : 0 < #D.bPlaces := by
    by_contra! hz
    have hd := D.towerDeg_le_card_bPlaces_mul
    rw [Nat.eq_zero_of_le_zero hz, Nat.cast_zero, zero_mul] at hd
    exact (show 0 < (towerDeg D.towerExp : ℝ) by
      exact_mod_cast (show 0 < towerDeg D.towerExp by unfold towerDeg; positivity)).not_ge hd
  exact mul_pos (by exact_mod_cast pos) (sub_pos.2 (by exact_mod_cast offWeight_lt_high D))

/-- No individual finite prime can see more than the total available high-place excess. -/
theorem abs_highSlope_le_total (l : FinPlace D.E) :
    |D.highSlope p l| ≤ D.totalHighExcess := by
  classical
  have size (w : FinPlace D.E) : D.highCount p w ≤ #D.bPlaces :=
    card_le_card (filter_subset _ _)
  have bound : |(D.highCount p (star l) : ℤ) - D.highCount p l| ≤ #D.bPlaces := by
    have h₁ := size l
    have h₂ := size (star l)
    exact abs_le.2 ⟨by omega, by omega⟩
  have gap : (0 : ℤ) ≤ (D.natB : ℤ) - D.offWeight := sub_nonneg.2 (by exact_mod_cast (offWeight_lt_high D).le)
  rw [highSlope, abs_mul, abs_of_nonneg gap, totalHighExcess]
  exact mul_le_mul_of_nonneg_right bound gap

/-- The common background and the added lift weight cancel at every inert prime above p. -/
theorem norm_atUniformizer_eq_highSlope (hi : chiK P.d p = -1) {l : FinPlace D.E}
    (hl : (p : 𝓞 D.E) ∈ l.asIdeal) (ϑ : D.TameChar) (j : ℕ) :
    ‖ιₚ ((D.chainChar ϑ j).baseChange.atUniformizer l)‖ = (p : ℝ)^(D.highSlope p l) := by
  classical
  have uniform : l.valuation D.E p = WithZero.exp (-1) := by
    rw [← map_natCast (algebraMap (NumberField.RingOfIntegers D.E) D.E), l.valuation_of_algebraMap]
    exact intValuation_natCast_eq_exp_neg_one hl (not_dvd_q₁_mul_d_of_inert hi)
  have hv : Valued.v (uniformizer l : LocField l) = Valued.v (p : LocField l) := by
    simp [← uniform, ← v_algebraMap_eq_valuation]
  change ‖ιₚ ((D.chainChar ϑ j).baseChange.finPart (locIdele l (uniformizer l)) : ℂ)‖ = _
  rw [D.hasWeight_liftChar.norm_baseChange_locIdele_of_valuation_eq_p ιₚ l (uniformizer l) hv]
  change (p : ℝ)^((∑ τ : D.Φ with inducedPlace τ = l, -(D.liftWeight j τ : ℤ)) -
      ∑ τ : D.Φ with star (inducedPlace τ) = l, -(D.liftWeight j τ : ℤ)) = _
  congr 1
  have sel : (univ.filter (fun τ : D.Φ ↦ inducedPlace τ = l)) ∩ D.bPlaces =
      D.bPlaces.filter (fun τ ↦ inducedPlace τ = l) := by ext τ; simp [and_comm]
  have opp : (univ.filter (fun τ : D.Φ ↦ star (inducedPlace τ) = l)) ∩ D.bPlaces =
      D.bPlaces.filter (fun τ ↦ inducedPlace τ = star l) := by
    ext τ
    simp [and_comm, star_eq_iff_star_eq, eq_comm (a := star l)]
  have slope := inert_liftWeight_difference (D := D) hi l j
  rw [sel, opp] at slope
  rw [sum_neg_distrib, sum_neg_distrib]
  unfold highSlope highCount
  linarith only [slope]

theorem norm_atUniformizer_eq_one_iff (hi : chiK P.d p = -1) {l : FinPlace D.E}
    (hl : (p : 𝓞 D.E) ∈ l.asIdeal) (ϑ : D.TameChar) (j : ℕ) :
    ‖ιₚ ((D.chainChar ϑ j).baseChange.atUniformizer l)‖ = 1 ↔
      D.highCount p l = D.highCount p (star l) := by
  rw [norm_atUniformizer_eq_highSlope hi hl]
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have inj := zpow_right_injective₀ (zero_lt_one.trans hp1) hp1.ne'
  have positive : (0 : ℤ) < (D.natB : ℤ) - D.offWeight := by
    exact sub_pos.2 (by exact_mod_cast offWeight_lt_high D)
  rw [← zpow_zero (p : ℝ), inj.eq_iff, highSlope, mul_eq_zero, or_iff_left positive.ne',
    sub_eq_zero, Nat.cast_inj, eq_comm]

lemma IsMarked.highCount_eq_zero {Λ : Finset (FinPlace D.E)} (h : D.IsMarked Λ)
    {l : FinPlace D.E} (hl : l ∈ Λ ∨ star l ∈ Λ) : D.highCount p l = 0 := by
  classical
  apply card_eq_zero.2
  apply filter_eq_empty_iff.2
  intro τ hτ eq
  exact h.notMem_bPlaces τ (by rw [eq]; exact hl) hτ

/-- At an exceptional prime, an odd total number of high places forces some unmarked
conjugate pair to have unequal high counts and nonunit character norm at every lift. -/
theorem IsExceptional.exists_unmarked_nonunit (he : D.IsExceptional p) (odd : Odd #D.bPlaces) :
    ∃ l : FinPlace D.E, (p : 𝓞 D.E) ∈ l.asIdeal ∧
      (D.highCount p l : ZMod 2) ≠ (D.highCount p (star l) : ZMod 2) ∧
      (∀ Λ : Finset (FinPlace D.E), D.IsMarked Λ → l ∉ Λ ∧ star l ∉ Λ) ∧
      ∀ (ϑ : D.TameChar) (j : ℕ), ‖ιₚ ((D.chainChar ϑ j).baseChange.atUniformizer l)‖ ≠ 1 := by
  classical
  obtain ⟨l, hmem, mismatch⟩ := Finset.exists_unmatched_mod_two D.bPlaces
    (inducedPlace (D := D) (p := p)) odd (fun τ _ ↦ he.star_ne (D.p_mem_inducedPlace τ))
  have counts : (D.highCount p l : ZMod 2) ≠ (D.highCount p (star l) : ZMod 2) := mismatch
  have ne : D.highCount p l ≠ D.highCount p (star l) := fun eq ↦ counts (congrArg Nat.cast eq)
  have above : (p : 𝓞 D.E) ∈ l.asIdeal := by
    rcases mem_union.1 hmem with h | h
    · obtain ⟨τ,_,rfl⟩ := mem_image.1 h
      exact D.p_mem_inducedPlace τ
    · obtain ⟨r, hr, rfl⟩ := mem_image.1 h
      obtain ⟨τ, _, rfl⟩ := mem_image.1 hr
      rw [mem_star_place, star_natCast]
      exact D.p_mem_inducedPlace τ
  refine ⟨l, above, counts, ?_, fun ϑ j ↦ mt (norm_atUniformizer_eq_one_iff he.chiK_eq_neg_one above ϑ j).1 ne⟩
  intro Λ hΛ
  have outside (m : l ∈ Λ ∨ star l ∈ Λ) : False := by
    apply ne
    rw [hΛ.highCount_eq_zero m, hΛ.highCount_eq_zero (l := star l) (by simpa [or_comm] using m)]
  exact ⟨fun hl ↦ outside (.inl hl), fun hs ↦ outside (.inr hs)⟩

open scoped Classical in
/-- Counting a set of high places that all induce the same finite prime. -/
lemma highCount_of_single_prime {v : FinPlace D.E}
    (packed : ∀ τ ∈ D.bPlaces, inducedPlace τ = v) (l : FinPlace D.E) :
    D.highCount p l = if l = v then #D.bPlaces else 0 := by
  classical
  unfold highCount
  split_ifs with h
  · subst l
    rw [filter_eq_self.2 packed]
  · exact card_eq_zero.2 (filter_eq_empty_iff.2 fun τ hτ eq ↦ h (eq.symm.trans (packed τ hτ)))

open scoped Classical in
/-- Concentration at one member of a split pair attains the full possible magnitude on
that pair; the other places above p have norm one. -/
theorem norm_profile_of_single_prime (he : D.IsExceptional p)
    (v : FinPlace D.E) (hv : (p : 𝓞 D.E) ∈ v.asIdeal)
    (packed : ∀ σ ∈ D.bPlaces, inducedPlace σ = v)
    (l : FinPlace D.E) (hl : (p : 𝓞 D.E) ∈ l.asIdeal) (ϑ : D.TameChar) (j : ℕ) :
    ‖ιₚ ((D.chainChar ϑ j).baseChange.atUniformizer l)‖ =
      if l = v then (p : ℝ)^(-D.totalHighExcess)
      else if l = star v then (p : ℝ)^D.totalHighExcess else 1 := by
  classical
  have apart := he.star_ne hv
  rw [norm_atUniformizer_eq_highSlope he.chiK_eq_neg_one hl]
  by_cases left : l = v
  · subst l
    simp [highSlope, highCount_of_single_prime packed, apart, totalHighExcess]
  by_cases right : l = star v
  · subst l
    simp [highSlope, highCount_of_single_prime packed, apart, totalHighExcess]
  have hstar : star l ≠ v := fun e ↦ right (by simpa using congrArg star e)
  simp [highSlope, highCount_of_single_prime packed, left, right, hstar]

end New.Data
