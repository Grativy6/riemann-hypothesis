module

public import New.Reduction.Data.SparseFiber
public import New.UpperBound.Divisibility.HighPlaceOffsets
public import New.UpperBound.Divisibility.OneAndThirtySix
public import New.UpperBound.Divisibility.SixPairsAt479
import New.Reduction.Data.Existence
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# The exact convex envelope of three local character readings

Every high place contributes one of six sign triples. The four extreme triples occur in
admissible data at every sufficiently large integer scale. The convex hull of the normalized
local exponents is therefore the tetrahedron spanned by these four points.
-/

@[expose] public section

open NumberField Finset Real
namespace New.Data

variable {P : Parameters} (D : Data P)

lemma bPlaces_nonempty : D.bPlaces.Nonempty := by
  by_contra! empty
  have h := D.totalHighExcess_pos
  simp [totalHighExcess, empty] at h

/-- The local exponent divided by the total available high-weight excess. The p-adic
embedding is an explicit input when several rational primes are read together. -/
noncomputable def normalizedProbe (p : ℕ) [Fact p.Prime] (ι : PadicPlace p) : ℝ :=
  (D.highSlope p (D.negativeUnitPrime p) : ℝ) / D.totalHighExcess

lemma normalizedProbe_is_rat (p : ℕ) [Fact p.Prime] (ι : PadicPlace p) :
    ∃ q : ℚ, (q : ℝ) = D.normalizedProbe p ι :=
  ⟨(D.highSlope p (D.negativeUnitPrime p) : ℚ) / D.totalHighExcess, by simp [normalizedProbe]⟩

lemma IsExceptional.normalizedProbe_eq_mean {p : ℕ} [Fact p.Prime] (ι : PadicPlace p)
    {D : Data P} (he : D.IsExceptional p) :
    D.normalizedProbe p ι =
      (∑ σ ∈ D.bPlaces, (ThreePrimeEnvelope.signAt (D.returnPairCount p) (D.negativeOffset σ) : ℝ)) /
        #D.bPlaces := by
  rw [normalizedProbe, he.highSlope_eq_offsetSum, totalHighExcess]
  push_cast
  exact mul_div_mul_right _ _ (sub_ne_zero.2 (by exact_mod_cast (offWeight_lt_high D).ne'))

/-- The local character norm itself, with the p-adic embedding explicitly selected. -/
noncomputable def measuredNorm (p : ℕ) [Fact p.Prime] (ι : PadicPlace p) (ϑ : D.TameChar) (j : ℕ) : ℝ :=
  ‖ιₚ ((D.chainChar ϑ j).baseChange.atUniformizer (D.negativeUnitPrime p))‖

lemma IsExceptional.measuredNorm_eq {p : ℕ} [Fact p.Prime] (ι : PadicPlace p)
    {D : Data P} (he : D.IsExceptional p) (ϑ : D.TameChar) (j : ℕ) :
    D.measuredNorm p ι ϑ j = (p : ℝ)^((D.totalHighExcess : ℝ)*D.normalizedProbe p ι) := by
  have above : (p : 𝓞 D.E) ∈ (D.negativeUnitPrime p).asIdeal := D.p_mem_inducedPlace (D.placeOfInt (-1))
  rw [measuredNorm, norm_atUniformizer_eq_highSlope (l := D.negativeUnitPrime p) he.chiK_eq_neg_one above ϑ j,
    normalizedProbe, ← Real.rpow_intCast]
  congr 1
  field_simp [(by exact_mod_cast D.totalHighExcess_pos.ne' : (D.totalHighExcess : ℝ) ≠ 0)]

/-- A common translation by the offset t. The translated data carry the original levels,
ranks and multiset of weights. -/
noncomputable def translateOffset (t : ℕ) : Data P :=
  D.translateHighPlaces (D.distinguishedLift t) (by simpa [aPlaces] using D.distinguishedLift_mem t)

theorem translateOffset_fields (t : ℕ) :
    let D' := D.translateOffset t
    D'.natX = D.natX ∧ D'.natX₁ = D.natX₁ ∧ D'.natB = D.natB ∧ D'.m = D.m ∧ D'.r = D.r ∧
      D'.towerExp = D.towerExp ∧ D'.levelPrime = D.levelPrime ∧ D'.N = D.N ∧ #D'.bPlaces = #D.bPlaces :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,D.card_translateHighPlaces _ _⟩

/-- If the high places start in the negative unit class at modulus kM, then their new
offsets are all t modulo k. This statement is independent of the rational prime. -/
theorem offset_after_translation {k : ℕ} (hf : P.NegOneFiber D.towerExp k D.bPlaces) (t : ℕ)
    (σ : (D.translateOffset t).Φ) (hσ : σ ∈ (D.translateOffset t).bPlaces) :
    (D.translateOffset t).negativeOffset σ ≡ t [MOD k] := by
  classical
  obtain ⟨hd, hcenter⟩ := hf
  let read := P.placeClass hd
  let anchor := D.placeOfInt (-1)
  have base : read anchor = -1 := Units.ext (by
    simpa [read,anchor] using (P.placeClass_placeOfInt (s := D.towerExp) (ν := -1) (h_dvd := hd)
      (show IsCoprime (-1 : ℤ) P.q₀ from ⟨-1,0,by ring⟩)))
  have hbase := (D.translateOffset t).placeClass_of_mem_bPlaces σ hσ
  have representation := (D.translateOffset t).negativePlace_eq_offset hbase
  change σ = D.distinguishedLift (D.negativeOffset σ)*anchor at representation
  change σ ∈ D.bPlaces.image (fun z ↦ D.distinguishedLift t*z) at hσ
  obtain ⟨z,hz,hmove⟩ := mem_image.1 hσ
  have left : read σ = read (D.distinguishedLift t)*(-1) := by rw [← hmove, map_mul]; exact congrArg _ (hcenter z hz)
  have right : read σ = read (D.distinguishedLift (D.negativeOffset σ))*(-1) := by
    conv_lhs => rw [representation]
    rw [map_mul, base]
  have same := mul_right_cancel (right.symm.trans left)
  have val := congrArg (fun r : (ZMod (k*P.q₀))ˣ ↦ (r : ZMod (k*P.q₀))) same
  change (P.placeClass hd (D.distinguishedLift (D.negativeOffset σ)) : ZMod (k*P.q₀)) =
      (P.placeClass hd (D.distinguishedLift t) : ZMod (k*P.q₀)) at val
  rw [D.distinguishedLift_val, D.distinguishedLift_val, ZMod.natCast_eq_natCast_iff, mul_comm k] at val
  exact (lifted_offsets_modEq (P := P) k _ t).1 val

end New.Data

namespace New.Data.CollisionPrimeExample

open Finset Real Filter ThreePrimeEnvelope
local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 535919) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 665279) := ⟨by norm_num1⟩

/-- Local exponents at the three negative-unit primes divided by the same total high-place excess. -/
noncomputable def readings (D : Data params) (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919)
    (ι₂ : PadicPlace 665279) : Point :=
  ![D.normalizedProbe 479 ι₀, D.normalizedProbe 535919 ι₁, D.normalizedProbe 665279 ι₂]

/-- All three coordinates are averages of the same finite list of offsets. -/
theorem readings_eq_centerMass (D : Data params) (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919)
    (ι₂ : PadicPlace 665279) :
    readings D ι₀ ι₁ ι₂ = D.bPlaces.centerMass (fun _ ↦ (1 : ℝ))
      (fun σ ↦ row (D.negativeOffset σ)) := by
  classical
  have both := singleton_and_thirty_six D ι₁ ι₂
  have h₁ : D.IsExceptional 535919 := by
    let : PadicPlace 535919 := ι₁
    exact both.1.toIsMarked.isExceptional
  have h₂ : D.IsExceptional 665279 := by
    let : PadicPlace 665279 := ι₂
    obtain ⟨_,full⟩ := both.2.1
    exact full.toIsMarked.isExceptional
  have a := (exceptional_479 D).normalizedProbe_eq_mean ι₀
  have b := h₁.normalizedProbe_eq_mean ι₁
  have c := h₂.normalizedProbe_eq_mean ι₂
  rw [returnPairCount_479] at a
  rw [(first_return_counts D).2.2] at b
  rw [(second_return_counts D).2.2] at c
  funext i
  fin_cases i <;> simp [readings,row,centerMass,a,b,c, Finset.sum_apply, div_eq_inv_mul]

theorem inside_for_every_data (D : Data params) (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919)
    (ι₂ : PadicPlace 665279) : readings D ι₀ ι₁ ι₂ ∈ tetrahedron := by
  rw [readings_eq_centerMass]
  apply (convex_convexHull ℝ (Set.range corner)).centerMass_mem
  · simp
  · simpa using (show (0 : ℝ) < #D.bPlaces by exact_mod_cast card_pos.2 D.bPlaces_nonempty)
  · exact fun σ _ ↦ row_mem _

/-- In the concentrated construction every translated high place has the same 72-residue,
so the average is exactly the one-offset reading. -/
theorem readings_translate_fiber (D : Data params) (hf : params.NegOneFiber D.towerExp 72 D.bPlaces)
    (t : ℕ) (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    readings (D.translateOffset t) ι₀ ι₁ ι₂ = row t := by
  classical
  let S := (D.translateOffset t).bPlaces
  have same (σ) (hσ : σ ∈ S) : row ((D.translateOffset t).negativeOffset σ) = row t :=
    row_congr (D.offset_after_translation hf t σ hσ)
  rw [readings_eq_centerMass]
  change S.centerMass _ _ = _
  calc S.centerMass (fun _ ↦ (1:ℝ)) (fun σ ↦ row ((D.translateOffset t).negativeOffset σ)) =
      S.centerMass (fun _ ↦ (1:ℝ)) (Function.const _ (row t)) := by
        unfold Finset.centerMass
        congr 1
        exact sum_congr rfl fun σ hσ ↦ congrArg ((1:ℝ) • ·) (same σ hσ)
    _ = row t := centerMass_const (by
      have nonempty : S.Nonempty := (D.translateOffset t).bPlaces_nonempty
      simp [card_ne_zero.mpr nonempty]) _

/-- Every base-trivial translation has an offset representative. Equality of its residue
modulo 72 times the base determines the simultaneous reading. -/
theorem readings_at_unit (D : Data params) (hf : params.NegOneFiber D.towerExp 72 D.bPlaces)
    (g : D.Φ) (hg : params.placeClass (params.q₀.dvd_mul_right (towerDeg D.towerExp)) g = 1)
    (t : ℕ) (hread : params.placeClass hf.choose g =
      params.placeClass hf.choose (D.distinguishedLift t))
    (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    readings (D.translateHighPlaces g hg) ι₀ ι₁ ι₂ = row t := by
  obtain ⟨n,_,rfl⟩ := D.exists_distinguishedLift (by simpa [aPlaces] using hg)
  have val := congrArg (fun v : (ZMod (72*params.q₀))ˣ ↦ (v : ZMod (72*params.q₀))) hread
  rw [D.distinguishedLift_val, D.distinguishedLift_val, ZMod.natCast_eq_natCast_iff, mul_comm 72] at val
  exact (readings_translate_fiber D hf n ι₀ ι₁ ι₂).trans
    (row_congr ((lifted_offsets_modEq (P := params) 72 n t).1 val))

/-- The original fifteen-step return at 479 is offset 66 on this board. It reverses the
first negative-unit reading, keeps the second, and clears the third. -/
theorem first_return_joint_reading (D : Data params)
    (hf : params.NegOneFiber D.towerExp 72 D.bPlaces) (ι₀ : PadicPlace 479)
    (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    let g := D.placeOfInt (-(479 : ℤ))^15
    ∃ hg : params.placeClass (params.q₀.dvd_mul_right (towerDeg D.towerExp)) g = 1,
      readings (D.translateHighPlaces g hg) ι₀ ι₁ ι₂ = ![1,-1,0] := by
  intro g
  have ord : orderOf (params.placeClass (params.q₀.dvd_mul_right (towerDeg D.towerExp))
    (D.placeOfInt (-(479 : ℤ)))) = 15 := order_479 D
  have base : params.placeClass (params.q₀.dvd_mul_right (towerDeg D.towerExp)) g = 1 := by
    rw [show g = D.placeOfInt (-(479 : ℤ))^15 from rfl, map_pow, ← ord, pow_orderOf_eq_one]
  have euclid : IsCoprime (-(479 : ℤ)) (params.q₀ : ℤ) := ⟨4321,112,by decide⟩
  have same : params.placeClass hf.choose g = params.placeClass hf.choose (D.distinguishedLift 66) := by
    apply Units.ext
    rw [show g = D.placeOfInt (-(479 : ℤ))^15 from rfl, map_pow, Units.val_pow_eq_pow_val,
      params.placeClass_placeOfInt euclid, D.distinguishedLift_val]
    decide
  refine ⟨base, (readings_at_unit D hf g base 66 same ι₀ ι₁ ι₂).trans ?_⟩
  funext i
  fin_cases i <;> norm_num [row, signAt]

/-- Evaluate the actual character at the three fixed measuring primes after the fifteen-step
return. The same input data, twist and lift are used in all three coordinates. -/
theorem first_return_character_norms (D : Data params)
    (hf : params.NegOneFiber D.towerExp 72 D.bPlaces) (ι₀ : PadicPlace 479)
    (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    let g := D.placeOfInt (-(479 : ℤ))^15
    ∃ hg : params.placeClass (params.q₀.dvd_mul_right (towerDeg D.towerExp)) g = 1,
      let d := D.translateHighPlaces g hg
      ∀ (ϑ : d.TameChar) (j : ℕ),
        d.measuredNorm 479 ι₀ ϑ j = (479 : ℝ)^D.totalHighExcess ∧
        d.measuredNorm 535919 ι₁ ϑ j = (535919 : ℝ)^(-D.totalHighExcess) ∧
        d.measuredNorm 665279 ι₂ ϑ j = 1 := by
  intro g
  obtain ⟨hg, reading⟩ := first_return_joint_reading D hf ι₀ ι₁ ι₂
  refine ⟨hg, ?_⟩
  intro d ϑ j
  have mass : d.totalHighExcess = D.totalHighExcess := by
    change (D.translateHighPlaces g hg).totalHighExcess = _
    unfold totalHighExcess
    rw [D.card_translateHighPlaces]
    rfl
  have h₀ : d.normalizedProbe 479 ι₀ = 1 := congrFun reading 0
  have h₁ : d.normalizedProbe 535919 ι₁ = -1 := congrFun reading 1
  have h₂ : d.normalizedProbe 665279 ι₂ = 0 := congrFun reading 2
  have both := singleton_and_thirty_six d ι₁ ι₂
  have he₁ : d.IsExceptional 535919 := by
    let : PadicPlace 535919 := ι₁
    exact both.1.toIsMarked.isExceptional
  have he₂ : d.IsExceptional 665279 := by
    let : PadicPlace 665279 := ι₂
    obtain ⟨_,full⟩ := both.2.1
    exact full.toIsMarked.isExceptional
  rw [(exceptional_479 d).measuredNorm_eq ι₀, he₁.measuredNorm_eq ι₁, he₂.measuredNorm_eq ι₂,
    h₀, h₁, h₂, mass]
  simp [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 535919), zpow_neg]

/-- A single model at every large scale reaches all 72 offsets by translations, with
the same ranks, field, level primes, chosen level and number of high places. -/
theorem eventually_all_offsets :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX = x ∧ params.NegOneFiber D.towerExp 72 D.bPlaces ∧
      ∀ t ι₀ ι₁ ι₂, readings (D.translateOffset t) ι₀ ι₁ ι₂ = row t := by
  filter_upwards [New.eventually_exists_data_in_fixed_fiber params 3 2 (ε := 1/200)
    (by norm_num) (by norm_num)] with x hx
  obtain ⟨D, hx, _, _, _, _, _, _, _, hf⟩ := hx
  have focus : params.NegOneFiber D.towerExp 72 D.bPlaces := by
    simpa only [show 2^3*3^2 = 72 by decide] using hf
  exact ⟨D,hx,focus,readings_translate_fiber D focus⟩

/-- The complete convex envelope at every sufficiently large scale. Every admissible
reading lies within the tetrahedron and a single family realizes all four vertices. -/
theorem eventually_convexHull_readings (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919)
    (ι₂ : PadicPlace 665279) :
    ∀ᶠ x : ℕ in atTop, convexHull ℝ {v | ∃ D : Data params, D.natX = x ∧ readings D ι₀ ι₁ ι₂ = v}
      = tetrahedron := by
  filter_upwards [eventually_all_offsets] with x hx
  obtain ⟨D, hx, _, all⟩ := hx
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ (Set.range corner))
    rintro _ ⟨d,_,rfl⟩
    exact inside_for_every_data d ι₀ ι₁ ι₂
  · apply convexHull_mono
    rintro _ ⟨i,rfl⟩
    exact ⟨D.translateOffset (cornerOffset i), hx, (all _ ι₀ ι₁ ι₂).trans (row_cornerOffset i)⟩

/-- An explicit point that lies strictly inside the four faces but cannot be a single
normalized arithmetic reading, since its third coordinate is irrational. -/
theorem irrational_interior (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919)
    (ι₂ : PadicPlace 665279) :
    let v : Point := ![0, 0, √2 / 8]
    v ∈ tetrahedron ∧ ∀ D : Data params, readings D ι₀ ι₁ ι₂ ≠ v := by
  intro v
  constructor
  · apply (inside_iff_mem _).1
    have sq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have pos := Real.sqrt_nonneg 2
    have small : √(2:ℝ) ≤ 2 := by nlinarith only [sq, sq_nonneg (√(2:ℝ)-1)]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [v] <;> linarith
  · intro D eq
    obtain ⟨q,hq⟩ := D.normalizedProbe_is_rat 665279 ι₂
    have hy : D.normalizedProbe 665279 ι₂ = √2/8 := congrFun eq 2
    apply irrational_sqrt_two
    refine ⟨q*8, ?_⟩
    push_cast
    linarith

end New.Data.CollisionPrimeExample
