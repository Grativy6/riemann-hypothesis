module

public import New.UpperBound.Divisibility.HighPlaceNorm
public import New.UpperBound.Divisibility.OrientedPrime
public import New.UpperBound.Divisibility.ThreePrimeGeometry
import New.Reduction.PrimeSums
import Mathlib.Tactic

/-!
# A common integer offset for every rational-prime probe

Every high place has one offset from the negative base unit. Its contribution at p is
negative at multiples of 2G, positive at the other multiples of G, and zero elsewhere.
-/

@[expose] public section

open NumberField Finset Real
namespace New.Data

variable {P : Parameters} (D : Data P)

lemma distinguishedLift_zero : D.distinguishedLift 0 = 1 := by
  simp [distinguishedLift, placeOfInt, Parameters.placeOfInt]

/-- Read the offset of a negative base place from the full unit address after division by
the negative unit. The residue representative is taken before the integer division. -/
noncomputable def negativeOffset (σ : D.Φ) : ℕ :=
  ((P.placeMulEquiv D.towerExp (σ / D.placeOfInt (-1)) : ZMod D.q₁).val / P.q₀)

lemma offset_of_negative_lift (t : ℕ) (ht : t < towerDeg D.towerExp) :
    D.negativeOffset (D.distinguishedLift t * D.placeOfInt (-1)) = t := by
  have hm : 1 < P.q₀ := by have := Nat.le_of_dvd (NeZero.pos P.q₀) P.dvd_q₀; omega
  have small : 1 + P.q₀*t < D.q₁ := by
    change 1 + P.q₀*t < P.q₀*towerDeg D.towerExp
    have := Nat.mul_le_mul_left P.q₀ (Nat.succ_le_of_lt ht)
    rw [Nat.mul_succ] at this
    omega
  have addr : (P.placeMulEquiv D.towerExp (D.distinguishedLift t) : ZMod D.q₁) = (1+P.q₀*t : ℕ) := by
    have cop : IsCoprime ((1+P.q₀*t : ℕ) : ℤ) (P.q₀ : ℤ) := ⟨1,-(t : ℤ),by push_cast; ring⟩
    simpa [distinguishedLift] using (P.placeMulEquiv_placeOfInt (s := D.towerExp) cop)
  simp only [negativeOffset, mul_div_cancel_right, addr, ZMod.val_natCast, Nat.mod_eq_of_lt small]
  rw [Nat.add_mul_div_left _ _ (NeZero.pos _), Nat.div_eq_of_lt hm, zero_add]

lemma exists_distinguishedLift {σ : D.Φ} (hσ : σ ∈ D.aPlaces) :
    ∃ t < towerDeg D.towerExp, D.distinguishedLift t = σ := by
  classical
  let T := towerDeg D.towerExp
  let S := (range T).image D.distinguishedLift
  have sub : S ⊆ D.aPlaces := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := mem_image.1 hz
    exact D.distinguishedLift_mem i
  have size : #S = T := by
    change #((range T).image D.distinguishedLift) = T
    rw [card_image_of_injOn, card_range]
    intro a ha b hb eq
    have hread := congrArg (fun τ ↦ D.negativeOffset (τ * D.placeOfInt (-1))) eq
    simpa only [D.offset_of_negative_lift _ (mem_range.1 ha), D.offset_of_negative_lift _ (mem_range.1 hb)] using hread
  have all : S = D.aPlaces := eq_of_subset_of_card_le sub (by rw [size,D.card_aPlaces])
  obtain ⟨i,hi,eq⟩ := mem_image.1 (show σ ∈ S by rwa [all])
  exact ⟨i,mem_range.1 hi,eq⟩

lemma negativePlace_eq_offset {σ : D.Φ}
    (hσ : P.placeClass (P.q₀.dvd_mul_right (towerDeg D.towerExp)) σ = -1) :
    σ = D.distinguishedLift (D.negativeOffset σ) * D.placeOfInt (-1) := by
  have base : P.placeClass (P.q₀.dvd_mul_right (towerDeg D.towerExp)) (D.placeOfInt (-1)) = -1 := by
    apply Units.ext
    simp
  have ha : σ / D.placeOfInt (-1) ∈ D.aPlaces := by simp [aPlaces, map_div, hσ, base]
  obtain ⟨t,ht,h⟩ := D.exists_distinguishedLift ha
  have assemble : σ = D.distinguishedLift t * D.placeOfInt (-1) := by rw [h, div_mul_cancel]
  rw [assemble, D.offset_of_negative_lift t ht]

variable {D} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]

/-- Moving both infinite places by a common group element preserves equality of the finite
primes they induce and preserves membership in the same unordered conjugate pair. -/
lemma same_read_after_translation (hi : chiK P.d p = -1) (a b w : D.Φ) :
    (inducedPlace (a*w) = inducedPlace (b*w) ↔ inducedPlace a = inducedPlace b) ∧
    ((inducedPlace (a*w) = inducedPlace (b*w) ∨ inducedPlace (a*w) = star (inducedPlace (b*w))) ↔
      (inducedPlace a = inducedPlace b ∨ inducedPlace a = star (inducedPlace b))) := by
  constructor
  · rw [inducedPlace_eq_iff_even_powers hi, inducedPlace_eq_iff_even_powers hi]
    simp only [← mul_assoc, mul_left_inj]
  · rw [D.inducedPlace_eq_or_star_iff hi, D.inducedPlace_eq_or_star_iff hi]
    simp only [← mul_assoc, mul_left_inj]

/-- Offset t leaves the individual prime unchanged precisely at multiples of 2G.
It stays in the unordered pair precisely at multiples of G. -/
theorem IsExceptional.offset_return_tests (he : D.IsExceptional p) (t : ℕ) (w : D.Φ) :
    (inducedPlace (D.distinguishedLift t*w) = inducedPlace w ↔ 2*D.returnPairCount p ∣ t) ∧
    ((inducedPlace (D.distinguishedLift t*w) = inducedPlace w ∨
        inducedPlace (D.distinguishedLift t*w) = star (inducedPlace w)) ↔ D.returnPairCount p ∣ t) := by
  let z := D.distinguishedLift 0
  have z0 : z = 1 := D.distinguishedLift_zero
  have transport := same_read_after_translation he.chiK_eq_neg_one (D.distinguishedLift t) z w
  have inF := he.mem_aPlaces_and_prime_iff_primeClass z (D.distinguishedLift_mem 0) (D.distinguishedLift t)
  have inP := mem_aPlaces_and_pair_iff_pairClass he.chiK_eq_neg_one he.odd_o₀ z
    (D.distinguishedLift_mem 0) (D.distinguishedLift t)
  simp only [D.distinguishedLift_mem t, true_and] at inF inP
  have ind := transport.1.trans (inF.trans ((he.primeClass_offset_iff t 0).trans Nat.modEq_zero_iff_dvd))
  have pair := transport.2.trans (inP.trans ((D.pairClass_distinguishedLift_iff p t 0).trans Nat.modEq_zero_iff_dvd))
  simpa only [z0,one_mul] using And.intro ind pair

end New.Data

namespace New.Data

open NumberField Finset Real
variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]

open ThreePrimeEnvelope

/-- One prime-independent integer index locates each high place. Different rational primes
read that same index at different periods. -/
theorem IsExceptional.highSlope_eq_offsetSum (he : D.IsExceptional p) :
    D.highSlope p (D.negativeUnitPrime p) =
      (∑ σ ∈ D.bPlaces, signAt (D.returnPairCount p) (D.negativeOffset σ)) *
        ((D.natB : ℤ)-D.offWeight) := by
  classical
  let w := D.placeOfInt (-1)
  let l := inducedPlace (p := p) w
  have apart : star l ≠ l := he.star_ne (D.p_mem_inducedPlace w)
  have count (u : FinPlace D.E) : (D.highCount p u : ℤ) =
      ∑ σ ∈ D.bPlaces, if inducedPlace σ = u then (1 : ℤ) else 0 := by
    rw [← sum_filter]; simp [highCount]
  unfold highSlope
  rw [count, count, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun σ hσ ↦ ?_
  let t := D.negativeOffset σ
  have pos := D.negativePlace_eq_offset (D.placeClass_of_mem_bPlaces _ hσ)
  have tests := he.offset_return_tests t w
  have eq : (inducedPlace (p := p) σ = l ↔ 2*D.returnPairCount p ∣ t) := by
    change σ = D.distinguishedLift t * w at pos
    rw [← pos] at tests
    exact tests.1
  have pair : ((inducedPlace σ = l ∨ inducedPlace σ = star l) ↔ D.returnPairCount p ∣ t) := by
    change σ = D.distinguishedLift t * w at pos
    rw [← pos] at tests
    exact tests.2
  change (if inducedPlace σ = star l then (1 : ℤ) else 0) -
    (if inducedPlace σ = l then (1 : ℤ) else 0) = signAt _ t
  by_cases hi : 2*D.returnPairCount p ∣ t
  · simp [eq.2 hi, apart.symm, signAt, hi]
  by_cases hp : D.returnPairCount p ∣ t
  · have hs := (pair.2 hp).resolve_left (mt eq.1 hi)
    simp [hs, apart, signAt, hi, hp]
  · have hn : inducedPlace σ ≠ star l := fun h ↦ hp (pair.1 (.inr h))
    simp [hn, mt eq.1 hi, signAt, hi, hp]

end New.Data
