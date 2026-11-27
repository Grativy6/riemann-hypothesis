module

public import New.Reduction.Data.SparseFiber
public import New.UpperBound.Divisibility.HighPlaceNorm
public import New.UpperBound.Divisibility.SixPairsAt479
import New.UpperBound.Divisibility.OrientedPrime
import New.Reduction.Data.Existence
import Mathlib.Tactic

/-!
# The full local norm profile above 479

For every sufficiently large integer scale the high places can be concentrated at the
finite prime induced by the negative unit in the tower. This prime and its conjugate realize
opposite slopes of full magnitude. All other finite primes over 479 give norm one.
-/

@[expose] public section

namespace New.Data.CollisionPrimeExample

open NumberField Finset Real Filter
local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩

lemma highPlace_induces_negativePrime (D : Data params) (ι : PadicPlace 479)
    (hf : params.NegOneFiber D.towerExp 12 D.bPlaces) {σ : D.Φ} (hσ : σ ∈ D.bPlaces) :
    inducedPlace σ = D.negativeUnitPrime 479 := by
  obtain ⟨hd,h⟩ := hf
  let he := exceptional_479 D
  have same_mod : 2 * D.returnModulus 479 = 12 * params.q₀ := by
    rw [returnModulus, returnPairCount_479]
    ring
  have at_place (n : ℕ) (hn : n = 12*params.q₀) (hn' : n ∣ D.q₁) :
      params.placeClass hn' σ = -1 := by subst n; exact h σ hσ
  have at_anchor : he.inducedPrimeClass (D.placeOfInt (-1)) = -1 := by
    apply Units.ext
    simpa [IsExceptional.inducedPrimeClass] using
      (params.placeClass_placeOfInt (s := D.towerExp) (ν := -1) (h_dvd := he.twice_returnModulus_dvd_tower)
        (show IsCoprime (-1 : ℤ) params.q₀ from ⟨-1,0,by ring⟩))
  have eq : he.inducedPrimeClass σ = he.inducedPrimeClass (D.placeOfInt (-1)) :=
    (at_place _ same_mod _).trans at_anchor.symm
  apply (he.inducedPlace_eq_iff_phase σ (D.placeOfInt (-1))).2
  exact ⟨0, he.odd_o₀.pos, by simpa using eq⟩

open scoped Classical in
/-- Only the prime at the negative unit and its conjugate carry a nonzero slope. Their
slopes have opposite signs and attain the full high-place excess. -/
theorem norm_profile_479 (D : Data params) (ι : PadicPlace 479)
    (hf : params.NegOneFiber D.towerExp 12 D.bPlaces) (l : FinPlace D.E)
    (hl : (479 : 𝓞 D.E) ∈ l.asIdeal) (ϑ : D.TameChar) (j : ℕ) :
    ‖ιₚ ((D.chainChar ϑ j).baseChange.atUniformizer l)‖ =
      if l = D.negativeUnitPrime 479 then (479 : ℝ)^(-totalHighExcess D)
      else if l = star (D.negativeUnitPrime 479) then (479 : ℝ)^(totalHighExcess D) else 1 :=
  norm_profile_of_single_prime (exceptional_479 D) (D.negativeUnitPrime 479)
    (D.p_mem_inducedPlace _) (fun _ hτ ↦ highPlace_induces_negativePrime D ι hf hτ) l hl ϑ j

/-- Arbitrarily far up the actual construction, the whole high-place excess can be
confined to this prescribed conjugate pair without disturbing the six marked units. -/
theorem eventually_single_pair_479 :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX = x ∧ Odd #D.bPlaces ∧
      params.NegOneFiber D.towerExp 12 D.bPlaces ∧
      ∀ _ι : PadicPlace 479, ∃ Λ : Finset (FinPlace D.E), D.IsFullMark (p := 479) Λ ∧ #Λ = 6 ∧
        D.negativeUnitPrime 479 ∉ Λ ∧ star (D.negativeUnitPrime 479) ∉ Λ := by
  filter_upwards [New.eventually_exists_data_focused params (ε := 1/200) (by norm_num) (by norm_num)] with x hx
  obtain ⟨D, hX, _, _, _, _, _, _, ho, hf⟩ := hx
  refine ⟨D, hX, ho, hf, fun ι ↦ ?_⟩
  obtain ⟨Λ, hΛ, _⟩ := exists_nonempty_fullMark_479 D ι
  have nonzero : D.highCount 479 (D.negativeUnitPrime 479) ≠ 0 := by
    rw [highCount_of_single_prime (v := D.negativeUnitPrime 479)
      (fun _ hτ ↦ highPlace_induces_negativePrime D ι hf hτ), ite_eq_left rfl]
    obtain ⟨k, hk⟩ := ho
    omega
  have outside (h : D.negativeUnitPrime 479 ∈ Λ ∨ star (D.negativeUnitPrime 479) ∈ Λ) : False :=
    nonzero (hΛ.toIsMarked.highCount_eq_zero h)
  exact ⟨Λ, hΛ, fullMark_card_479 D ι hΛ, fun hl ↦ outside (.inl hl), fun hl ↦ outside (.inr hl)⟩

private lemma anchor_base (D : Data params) :
    params.placeClass (params.q₀.dvd_mul_right (towerDeg D.towerExp)) (D.placeOfInt (-1)) = -1 :=
  Units.ext (by simp)

/-- Translate the high places so that the old negative-unit address moves to v. -/
noncomputable def placeHighAt (D : Data params) (v : D.Φ)
    (hv : params.placeClass (params.q₀.dvd_mul_right (towerDeg D.towerExp)) v = -1) : Data params :=
  D.translateHighPlaces (v / D.placeOfInt (-1)) (by rw [map_div, hv, anchor_base]; simp)

/-- Moving the packet preserves the three scales, both ranks, tower, level primes, chosen
level and number of high places. -/
theorem placeHighAt_fields (D : Data params) (v : D.Φ) (hv) :
    let D' := placeHighAt D v hv
    D'.natX = D.natX ∧ D'.natX₁ = D.natX₁ ∧ D'.natB = D.natB ∧
      D'.m = D.m ∧ D'.r = D.r ∧ D'.towerExp = D.towerExp ∧
      D'.levelPrime = D.levelPrime ∧ D'.N = D.N ∧ #D'.bPlaces = #D.bPlaces :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,D.card_translateHighPlaces _ _⟩

/-- The canonical six finite primes used by the proof are the same after the move. -/
lemma placeHighAt_arithmeticMark (D : Data params) (v : D.Φ) (hv) (_ι : PadicPlace 479) :
    (placeHighAt D v hv).arithmeticMark 479 = D.arithmeticMark 479 := rfl

open scoped Classical in
/-- With the same field and scalar data, the maximal slope can be placed above any
chosen place of base class minus one. -/
theorem moved_norm_profile_479 (D : Data params) (ι : PadicPlace 479)
    (hf : params.NegOneFiber D.towerExp 12 D.bPlaces) (v : D.Φ)
    (hv : params.placeClass (params.q₀.dvd_mul_right (towerDeg D.towerExp)) v = -1) :
    let D' := placeHighAt D v hv
    ∀ (l : FinPlace D.E), (479 : 𝓞 D.E) ∈ l.asIdeal → ∀ (ϑ : D'.TameChar) (j : ℕ),
      ‖ιₚ ((D'.chainChar ϑ j).baseChange.atUniformizer l)‖ =
        if l = inducedPlace v then (479 : ℝ)^(-D.totalHighExcess)
        else if l = star (inducedPlace v) then (479 : ℝ)^D.totalHighExcess else 1 := by
  intro D' l hl ϑ j
  have packed (σ : D'.Φ) (hσ : σ ∈ D'.bPlaces) : inducedPlace σ = inducedPlace v := by
    change inducedPlace (D := D) (p := 479) σ = inducedPlace (D := D) (p := 479) v
    change σ ∈ D.bPlaces.image (fun z ↦ (v / D.placeOfInt (-1))*z) at hσ
    obtain ⟨τ, hτ, rfl⟩ := mem_image.1 hσ
    have base : inducedPlace (D := D) (p := 479) τ = inducedPlace (D := D) (p := 479) (D.placeOfInt (-1)) :=
      highPlace_induces_negativePrime D ι hf hτ
    calc inducedPlace ((v / D.placeOfInt (-1))*τ)
        = (v / D.placeOfInt (-1)) • inducedPlace (D := D) (p := 479) τ := by rw [mul_comm, inducedPlace_mul]
      _ = (v / D.placeOfInt (-1)) • inducedPlace (D := D) (p := 479) (D.placeOfInt (-1)) := by rw [base]
      _ = inducedPlace (D := D) (p := 479) v := by
        rw [← inducedPlace_mul]
        simp
  have mass : D'.totalHighExcess = D.totalHighExcess := by
    unfold totalHighExcess
    change (#(D.translateHighPlaces _ _).bPlaces : ℤ) * ((D.natB : ℤ)-D.offWeight) = _
    rw [D.card_translateHighPlaces]
  rw [← mass]
  exact norm_profile_of_single_prime (exceptional_479 D') (inducedPlace v)
    (D.p_mem_inducedPlace v) packed l hl ϑ j

/-- The first full return to the negative base class has odd length fifteen. -/
noncomputable def oppositeAddress479 (D : Data params) : D.Φ :=
  D.placeOfInt (-(479 : ℤ))^15 * D.placeOfInt (-1)

lemma oppositeAddress_base (D : Data params) :
    params.placeClass (params.q₀.dvd_mul_right (towerDeg D.towerExp)) (oppositeAddress479 D) = -1 := by
  have order : orderOf (params.placeClass (params.q₀.dvd_mul_right (towerDeg D.towerExp))
      (D.placeOfInt (-(479 : ℤ)))) = 15 := order_479 D
  rw [oppositeAddress479, map_mul, map_pow, ← order, pow_orderOf_eq_one, one_mul, anchor_base]

lemma oppositeAddress_prime (D : Data params) (ι : PadicPlace 479) :
    inducedPlace (oppositeAddress479 D) = star (D.negativeUnitPrime 479) := by
  have he := exceptional_479 D
  simpa [oppositeAddress479, negativeUnitPrime, order_479] using
    (inducedPlace_after_returns (D := D) he.chiK_eq_neg_one he.odd_o₀ 1 (D.placeOfInt (-1)))

/-- At the same finite prime of the same field, the two admissible choices of high places
give inverse, nonunit norms. Their levels, ranks, scale and weight multiset agree. -/
theorem exact_reversal_at_fixed_prime (D : Data params) (ι : PadicPlace 479)
    (hf : params.NegOneFiber D.towerExp 12 D.bPlaces) :
    let D' := placeHighAt D (oppositeAddress479 D) (oppositeAddress_base D)
    let w := D.negativeUnitPrime 479
    ∀ (ϑ : D.TameChar) (ϑ' : D'.TameChar) (i j : ℕ),
      ‖ιₚ ((D.chainChar ϑ i).baseChange.atUniformizer w)‖ = (479 : ℝ)^(-D.totalHighExcess) ∧
      ‖ιₚ ((D'.chainChar ϑ' j).baseChange.atUniformizer w)‖ = (479 : ℝ)^D.totalHighExcess := by
  classical
  intro D' w ϑ ϑ' i j
  have hw : (479 : 𝓞 D.E) ∈ w.asIdeal := D.p_mem_inducedPlace (D.placeOfInt (-1))
  have apart := (exceptional_479 D).star_ne hw
  dsimp only [w] at apart
  constructor
  · simpa [w] using norm_profile_479 D ι hf w hw ϑ i
  · have exactValue := moved_norm_profile_479 D ι hf (oppositeAddress479 D) (oppositeAddress_base D) w hw ϑ' j
    rw [oppositeAddress_prime D ι] at exactValue
    simpa [D', w, apart.symm] using exactValue

end New.Data.CollisionPrimeExample
