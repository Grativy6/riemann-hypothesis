module

public import New.UpperBound.Divisibility.OrientedPrime
import Mathlib.Tactic

/-!
# The two residue tables for the canonical mark

Start with the explicit representatives 1+q₀ i and traverse the o possible phases of each parity.
The two resulting lists read membership in the selected and conjugate sets on all infinite places.
-/

@[expose] public section

namespace New.Data

open Finset Real
variable {P : Parameters} (D : Data P)

/-- The arithmetic class of the ith marked representative after 2j or 2j+1 Frobenius steps. -/
noncomputable def phaseResidue (p : ℕ) (ε : Fin 2) (i j : ℕ) : ZMod (2*D.returnModulus p) :=
  (-(p : ZMod (2*D.returnModulus p)))^(2*j+ε.val) * (1+P.q₀*i : ℕ)

/-- Finite lists of reduced residues for the selected and conjugate orientations. -/
noncomputable def markedResidues (p : ℕ) (ε : Fin 2) : Finset (ZMod (2*D.returnModulus p)) :=
  (range (D.returnPairCount p)).biUnion fun i ↦ (range (D.o₀ p)).image (D.phaseResidue p ε i)

variable {D} {p : ℕ} [hp : Fact p.Prime]

lemma IsExceptional.primeClass_frobenius_val (he : D.IsExceptional p) :
    (he.inducedPrimeClass (D.placeOfInt (-(p : ℤ))) : ZMod (2*D.returnModulus p)) = -(p : ZMod _) := by
  have hnd : ¬p ∣ P.q₁ D.towerExp := fun h ↦ by
    have := P.chiK_eq_one_of_dvd hp.out h
    have := he.chiK_eq_neg_one
    omega
  have hc : IsCoprime (-(p : ℤ)) P.q₀ := (Parameters.isCoprime_q₀_of_not_dvd hnd).neg_left
  simpa [IsExceptional.inducedPrimeClass] using
    (P.placeClass_placeOfInt (s := D.towerExp) (h_dvd := he.twice_returnModulus_dvd_tower) hc)

lemma IsExceptional.phase_class_iff (he : D.IsExceptional p) (σ : D.Φ) (ε : Fin 2) (i j : ℕ) :
    he.inducedPrimeClass σ = (he.inducedPrimeClass (D.placeOfInt (-(p : ℤ))))^(2*j+ε.val) *
        he.inducedPrimeClass (D.distinguishedLift i) ↔
    (he.inducedPrimeClass σ : ZMod _) = D.phaseResidue p ε i j := by
  rw [Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val, he.primeClass_frobenius_val]
  have hv : (he.inducedPrimeClass (D.distinguishedLift i) : ZMod (2*D.returnModulus p)) =
      ((1+P.q₀*i : ℕ) : ZMod (2*D.returnModulus p)) :=
    D.distinguishedLift_val he.twice_returnModulus_dvd_tower i
  rw [hv, phaseResidue]

variable [PadicPlace p]

theorem IsExceptional.inducedPlace_eq_lift_iff_residue (he : D.IsExceptional p) (σ : D.Φ) (i : ℕ) :
    inducedPlace σ = inducedPlace (D.distinguishedLift i) ↔
      ∃ j < D.o₀ p, (he.inducedPrimeClass σ : ZMod _) = D.phaseResidue p 0 i j := by
  rw [he.inducedPlace_eq_iff_phase]
  refine exists_congr fun j ↦ and_congr_right fun _ ↦ ?_
  simpa using he.phase_class_iff σ 0 i j

theorem IsExceptional.inducedPlace_eq_conj_lift_iff_residue (he : D.IsExceptional p) (σ : D.Φ) (i : ℕ) :
    inducedPlace σ = star (inducedPlace (D.distinguishedLift i)) ↔
      ∃ j < D.o₀ p, (he.inducedPrimeClass σ : ZMod _) = D.phaseResidue p 1 i j := by
  rw [he.inducedPlace_eq_star_iff_phase]
  refine exists_congr fun j ↦ and_congr_right fun _ ↦ ?_
  simpa using he.phase_class_iff σ 1 i j

/-- Reading the even table is equivalent to membership in the actual selected-place set
for the explicit mark, including places outside the distinguished fiber. -/
theorem IsExceptional.selected_places_iff_residue (he : D.IsExceptional p) (σ : D.Φ) :
    σ ∈ placesInducing (D.arithmeticMark p) ↔
      (he.inducedPrimeClass σ : ZMod _) ∈ D.markedResidues p 0 := by
  classical
  simp only [placesInducing, mem_filter, mem_univ, true_and, arithmeticMark, markedResidues,
    mem_biUnion, mem_image, mem_range]
  constructor
  · rintro ⟨i, hi, eq⟩
    obtain ⟨j,hj,read⟩ := (he.inducedPlace_eq_lift_iff_residue σ i).1 eq.symm
    exact ⟨i,hi,j,hj,read.symm⟩
  · rintro ⟨i,hi,j,hj,read⟩
    exact ⟨i,hi,((he.inducedPlace_eq_lift_iff_residue σ i).2 ⟨j,hj,read.symm⟩).symm⟩

/-- The odd table reads the conjugate side of the explicit mark. -/
theorem IsExceptional.conjugate_places_iff_residue (he : D.IsExceptional p) (σ : D.Φ) :
    σ ∈ placesInducingConj (D.arithmeticMark p) ↔
      (he.inducedPrimeClass σ : ZMod _) ∈ D.markedResidues p 1 := by
  classical
  simp only [placesInducingConj, mem_filter, mem_univ, true_and, arithmeticMark, markedResidues,
    mem_biUnion, mem_image, mem_range]
  constructor
  · rintro ⟨i, hi, eq⟩
    have swap : inducedPlace σ = star (inducedPlace (D.distinguishedLift i)) := by rw [eq, star_star]
    obtain ⟨j,hj,read⟩ := (he.inducedPlace_eq_conj_lift_iff_residue σ i).1 swap
    exact ⟨i,hi,j,hj,read.symm⟩
  · rintro ⟨i,hi,j,hj,read⟩
    have eq := (he.inducedPlace_eq_conj_lift_iff_residue σ i).2 ⟨j,hj,read.symm⟩
    exact ⟨i,hi,by rw [eq, star_star]⟩

open scoped Classical in
/-- The weighted balance used by the marked operators can be indexed by the two integer tables. -/
theorem IsExceptional.balance_by_residues {B : Type*} [AddCommMonoid B] (he : D.IsExceptional p)
    (hs : D.IsSmallNonsplit p) (j : ℕ) (F : ℕ → FinPlace D.E → B) :
    ∑ τ : D.Φ with (he.inducedPrimeClass τ : ZMod _) ∈ D.markedResidues p 0,
        F (D.liftWeight j τ) (inducedPlace τ) =
      ∑ τ : D.Φ with (he.inducedPrimeClass τ : ZMod _) ∈ D.markedResidues p 1,
        F (D.liftWeight j τ) (star (inducedPlace τ)) := by
  have even : placesInducing (D.arithmeticMark p) =
      univ.filter (fun τ ↦ (he.inducedPrimeClass τ : ZMod _) ∈ D.markedResidues p 0) := by
    ext τ
    simpa only [mem_filter, mem_univ, true_and] using he.selected_places_iff_residue τ
  have odd : placesInducingConj (D.arithmeticMark p) =
      univ.filter (fun τ ↦ (he.inducedPrimeClass τ : ZMod _) ∈ D.markedResidues p 1) := by
    ext τ
    simpa only [mem_filter, mem_univ, true_and] using he.conjugate_places_iff_residue τ
  rw [← even, ← odd]
  exact (he.isFullMark_arithmeticMark hs).toIsMarked.sum_placesInducing_eq_sum_placesInducingConj j F

end New.Data
