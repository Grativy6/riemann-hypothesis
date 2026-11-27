module

public import New.UpperBound.Divisibility.CommonOrbitProfiles
import Mathlib.Tactic

/-!
# Reading the conjugate pair at any finite prime

The prime induced by offset a sees exactly the high places at a modulo 2G, and its conjugate
sees those at a+G. The four-slot construction preserves the two exchanges at every one of
these references. Outside their union both high-place counts are zero.
-/

@[expose] public section

open Finset NumberField ThreePrimeEnvelope
namespace New.SixSignatures

/-- Contribution of offset u at the pair oriented from a toward a+G. -/
def referenceSign (G a u : ℕ) : ℤ :=
  (if u ≡ a+G [MOD 2*G] then 1 else 0) - (if u ≡ a [MOD 2*G] then 1 else 0)

lemma referenceSign_input {G a u v : ℕ} (h : u ≡ v [MOD 2*G]) :
    referenceSign G a u = referenceSign G a v := by
  have test (j : ℕ) : (u ≡ j [MOD 2*G]) ↔ v ≡ j [MOD 2*G] :=
    ⟨fun e ↦ h.symm.trans e, fun e ↦ h.trans e⟩
  exact congrArg₂ (fun x y : ℤ ↦ x-y) (if_congr (test _) rfl rfl) (if_congr (test _) rfl rfl)

lemma referenceSign_anchor {G a b u : ℕ} (h : a ≡ b [MOD 2*G]) :
    referenceSign G a u = referenceSign G b u := by
  have test {a b : ℕ} (e : a ≡ b [MOD 2*G]) : (u ≡ a [MOD 2*G]) ↔ u ≡ b [MOD 2*G] :=
    ⟨fun t ↦ t.trans e, fun t ↦ t.trans e.symm⟩
  exact congrArg₂ (fun x y : ℤ ↦ x-y) (if_congr (test (h.add_right G)) rfl rfl)
    (if_congr (test h) rfl rfl)

/-- Four-slot contribution for an arbitrary oriented pair period. -/
def slotsAt (G a : ℕ) (c : Fin 6) : ℤ :=
  ∑ j : Fin 4, referenceSign G a (microRow c j)

abbrev atReference (a : ℕ) (c : Fin 6) (i : Fin 3) : ℤ := slotsAt (probePeriod i) a c

lemma atReference_period (a : ℕ) (c : Fin 6) (i : Fin 3) :
    atReference (a%72) c i = atReference a c i := by
  have period : ∀ j : Fin 3, 2*probePeriod j ∣ 72 := by decide
  apply sum_congr rfl
  exact fun _ _ ↦ referenceSign_anchor ((Nat.mod_modEq a 72).of_dvd (period i))

set_option maxRecDepth 4096 in
lemma exchanges_at_reference (a : ℕ) (i : Fin 3) :
    atReference a 0 i+atReference a 1 i=2*atReference a 2 i ∧
    atReference a 2 i+atReference a 3 i=2*atReference a 4 i := by
  have table : ∀ t : Fin 72, ∀ j : Fin 3,
      atReference t 0 j+atReference t 1 j=2*atReference t 2 j ∧
      atReference t 2 j+atReference t 3 j=2*atReference t 4 j := by decide
  simpa only [atReference_period] using table ⟨a%72,Nat.mod_lt _ (by decide)⟩ i

end New.SixSignatures

namespace New.Data
open SixSignatures
variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- The actual finite prime induced by the negative-unit lift at the specified offset. -/
noncomputable def anchorPrime (D : Data P) (p : ℕ) [Fact p.Prime] (ι : PadicPlace p) (a : ℕ) : FinPlace D.E :=
  D.inducedPlace (D.distinguishedLift a*D.placeOfInt (-1))

/-- The chosen finite prime at two offsets agrees exactly modulo the oriented period. -/
theorem IsExceptional.anchorPrime_eq_iff (he : D.IsExceptional p) (a b : ℕ) :
    D.anchorPrime p inferInstance a = D.anchorPrime p inferInstance b ↔
      a ≡ b [MOD 2*D.returnPairCount p] := by
  have moved := (same_read_after_translation he.chiK_eq_neg_one
    (D.distinguishedLift a) (D.distinguishedLift b) (D.placeOfInt (-1))).1
  have tested := he.mem_aPlaces_and_prime_iff_primeClass (D.distinguishedLift b)
    (D.distinguishedLift_mem b) (D.distinguishedLift a)
  simp only [D.distinguishedLift_mem,true_and] at tested
  exact moved.trans (tested.trans (he.primeClass_offset_iff a b))

theorem IsExceptional.anchorPrime_conjugate (he : D.IsExceptional p) (a : ℕ) :
    D.anchorPrime p inferInstance (a+D.returnPairCount p) = star (D.anchorPrime p inferInstance a) := by
  let G := D.returnPairCount p
  have moved := same_read_after_translation he.chiK_eq_neg_one (D.distinguishedLift (a+G))
    (D.distinguishedLift a) (D.placeOfInt (-1))
  have other := he.offset_add_pairCount_conjugates a
  refine (moved.2.2 (.inr other)).resolve_left fun same ↦ ?_
  exact he.star_ne (D.p_mem_inducedPlace (D.distinguishedLift a)) (other.symm.trans (moved.1.1 same))

/-- The difference of the two unweighted counts underlying the local exponent. -/
noncomputable def signedCount (D : Data P) (p : ℕ) [Fact p.Prime] (ι : PadicPlace p) (l : FinPlace D.E) : ℤ :=
  (D.highCount p (star l) : ℤ) - D.highCount p l

open scoped Classical in
lemma signedCount_sum (D : Data P) (p : ℕ) [Fact p.Prime] (ι : PadicPlace p) (l : FinPlace D.E) :
    D.signedCount p ι l = ∑ z ∈ D.bPlaces,
      ((if D.inducedPlace (p := p) z = star l then (1:ℤ) else 0) -
        if D.inducedPlace (p := p) z = l then (1:ℤ) else 0) := by
  classical
  have count (v : FinPlace D.E) : (D.highCount p v : ℤ) =
      ∑ z ∈ D.bPlaces, if D.inducedPlace (p := p) z = v then (1:ℤ) else 0 := by
    rw [← sum_filter]; simp [highCount]
  rw [signedCount,count,count,sum_sub_distrib]

theorem IsExceptional.signedCount_anchor (he : D.IsExceptional p) (a : ℕ) :
    D.signedCount p inferInstance (D.anchorPrime p inferInstance a) =
    ∑ z ∈ D.bPlaces, referenceSign (D.returnPairCount p) a (D.negativeOffset z) := by
  classical
  rw [signedCount_sum]
  apply sum_congr rfl
  intro z hz
  have source : D.inducedPlace (p := p) z = D.anchorPrime p inferInstance (D.negativeOffset z) :=
    congrArg (D.inducedPlace (p := p)) (D.negativePlace_eq_offset (D.placeClass_of_mem_bPlaces _ hz))
  simp only [referenceSign,source,← he.anchorPrime_conjugate,he.anchorPrime_eq_iff]

/-- An arbitrary finite prime outside the negative-unit orbit and its conjugates has zero
signed count for any choice of high places on this frame. -/
theorem IsExceptional.signedCount_off_orbit (he : D.IsExceptional p) (l : FinPlace D.E)
    (outside : ∀ a, D.anchorPrime p inferInstance a ≠ l) : D.signedCount p inferInstance l = 0 := by
  classical
  rw [signedCount_sum]
  apply sum_eq_zero
  intro z hz
  have source : D.inducedPlace (p := p) z = D.anchorPrime p inferInstance (D.negativeOffset z) :=
    congrArg (D.inducedPlace (p := p)) (D.negativePlace_eq_offset (D.placeClass_of_mem_bPlaces _ hz))
  have other : D.inducedPlace (p := p) z ≠ star l := by
    intro equal
    apply outside (D.negativeOffset z+D.returnPairCount p)
    rw [he.anchorPrime_conjugate,← source,equal,star_star]
  simp [other,source.trans_ne (outside _)]

end New.Data
