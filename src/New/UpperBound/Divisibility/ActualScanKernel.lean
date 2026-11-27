module

public import New.UpperBound.Divisibility.ScanKernelAt72
import Mathlib.Tactic

/-!
# What every compatible local norm scan can recover

The observed 72-bin histogram comes from actual high places. Three genuine primes force
its difference from any other histogram on the same frame to be constant in each
residue class modulo nine. This condition in turn gives equal local norms at every
exceptional prime whose oriented period divides 72.
-/

@[expose] public section
open Finset Filter NumberField ThreePrimeEnvelope ColoredSparse
namespace New.SixSignatures

def boardIndex (u : ℕ) : Fin 9 × Fin 8 :=
  (⟨u%9,Nat.mod_lt _ (by decide)⟩,⟨(u/9)%8,Nat.mod_lt _ (by decide)⟩)

lemma boardIndex_address (b : Fin 9) (j : Fin 8) : boardIndex (address72 b j)=(b,j) := by
  apply Prod.ext <;> apply Fin.ext
  · change (b.val+9*j.val)%9=b.val;omega
  · change ((b.val+9*j.val)/9)%8=j.val;omega

lemma address_boardIndex (u : ℕ) : address72 (boardIndex u).1 (boardIndex u).2 ≡ u [MOD 72] := by
  change (u%9+9*((u/9)%8))%72=u%72
  omega

lemma boardIndex_congr {u v : ℕ} (eq : u ≡ v [MOD 72]) : boardIndex u=boardIndex v := by
  change u%72=v%72 at eq
  apply Prod.ext <;> apply Fin.ext
  · change u%9=v%9;omega
  · change (u/9)%8=(v/9)%8;omega

end New.SixSignatures

namespace New.Data.CollisionPrimeExample
open SixSignatures OrbitProbes

/-- The full residue histogram of the actual high places, written in nine columns of eight. -/
noncomputable def residueBoard (D : Data params) : Board72 := fun b j ↦
  (#{z ∈ D.bPlaces | boardIndex (D.negativeOffset z)=(b,j)} : ℕ)

theorem residueBoard_sum (D : Data params) (F : Fin 9 × Fin 8 → ℤ) :
    (∑ z ∈ D.bPlaces,F (boardIndex (D.negativeOffset z))) =
      ∑ b,∑ j,residueBoard D b j*F (b,j) := by
  classical
  have h := (sum_fiberwise_of_maps_to' (g := fun z ↦ boardIndex (D.negativeOffset z))
    (s := D.bPlaces) (t := univ) (fun _ _ ↦ mem_univ _) F).symm
  simpa only [sum_const,Fintype.sum_prod_type,nsmul_eq_mul,residueBoard] using h

theorem residueBoard_at_finite_prime (D : Data params) {p : ℕ} [Fact p.Prime] (ι : PadicPlace p)
    (he : D.IsExceptional p) (fits : 2*D.returnPairCount p ∣ 72) (a : ℕ) :
    D.signedCount p ι (D.anchorPrime p ι a) = boardScan (residueBoard D) (D.returnPairCount p) a := by
  rw [he.signedCount_anchor]
  let F := fun v : Fin 9 × Fin 8 ↦ referenceSign (D.returnPairCount p) a (address72 v.1 v.2)
  calc (∑ z ∈ D.bPlaces, _) = ∑ z ∈ D.bPlaces,F (boardIndex (D.negativeOffset z)) := by
        apply sum_congr rfl
        intro z _
        exact (referenceSign_input ((address_boardIndex (D.negativeOffset z)).of_dvd fits)).symm
    _ = _ := residueBoard_sum D F

theorem equalProfile_of_board_agreement {D : Data params} (c e : HighPlaceChoice D)
    {p : ℕ} [Fact p.Prime] (ι : PadicPlace p) (he : D.IsExceptional p)
    (fits : 2*D.returnPairCount p ∣ 72)
    (same : ∀ a,boardScan (residueBoard c.toData) (D.returnPairCount p) a =
                boardScan (residueBoard e.toData) (D.returnPairCount p) a) : EqualPrimeProfile c e p ι := by
  apply equalPrimeProfile_of_anchors c e ι he
  intro a
  change c.toData.signedCount p ι (c.toData.anchorPrime p ι a) =
      e.toData.signedCount p ι (e.toData.anchorPrime p ι a)
  exact (residueBoard_at_finite_prime c.toData ι he fits a).trans
    ((same a).trans (residueBoard_at_finite_prime e.toData ι he fits a).symm)

/-- The complete family of local comparisons at exceptional primes whose half-periods
occur on the board. All finite places and all twists at each such prime are included. -/
def AllCompatibleProfiles {D : Data params} (c e : HighPlaceChoice D) : Prop :=
  ∀ p : ℕ, ∀ [_hp : Fact p.Prime], ∀ ι : PadicPlace p,
    D.IsExceptional p → 2*D.returnPairCount p ∣ 72 → EqualPrimeProfile c e p ι

/-- Transfer the two actual anchor counts to the half-period in the prime table. -/
theorem boards_agree_at_probe {D : Data params} (c e : HighPlaceChoice D) (i : Fin 9)
    (ι : PadicPlace (rationalPrime i))
    (agree : ∀ a,c.toData.signedCount _ ι (D.anchorPrime _ ι a)=e.toData.signedCount _ ι (D.anchorPrime _ ι a)) :
    ∀ a,boardScan (residueBoard c.toData) (halfPeriod i) a =
      boardScan (residueBoard e.toData) (halfPeriod i) a := by
  intro a
  obtain ⟨he,_,_,G⟩ := period_and_exceptional D i
  have fits : 2*D.returnPairCount (rationalPrime i) ∣ 72 := by
    rw [G];exact Nat.mul_dvd_mul_left 2 (arithmetic i).2.1
  have signed := agree a
  change c.toData.signedCount _ ι (c.toData.anchorPrime _ ι a) =
    e.toData.signedCount _ ι (e.toData.anchorPrime _ ι a) at signed
  rw [residueBoard_at_finite_prime c.toData ι he fits a,
    residueBoard_at_finite_prime e.toData ι he fits a] at signed
  have rc : c.toData.returnPairCount (rationalPrime i)=D.returnPairCount (rationalPrime i) := rfl
  have re : e.toData.returnPairCount (rationalPrime i)=D.returnPairCount (rationalPrime i) := rfl
  rw [rc,re,G] at signed
  exact signed

theorem allCompatibleProfiles_iff {D : Data params} (c e : HighPlaceChoice D)
    (ι₉ : PadicPlace (rationalPrime 5)) (ι₁₈ : PadicPlace (rationalPrime 7))
    (ι₃₆ : PadicPlace (rationalPrime 8)) :
    AllCompatibleProfiles c e ↔
    ∀ b j, residueBoard c.toData b j-residueBoard e.toData b j =
             residueBoard c.toData b 0-residueBoard e.toData b 0 := by
  constructor
  · intro profiles
    have atProbe (i : Fin 9) (ι : PadicPlace (rationalPrime i)) :=
      boards_agree_at_probe c e i ι (fun a ↦ (profiles _ ι (period_and_exceptional D i).1
        (by rw [(period_and_exceptional D i).2.2.2]; exact Nat.mul_dvd_mul_left 2 (arithmetic i).2.1)
        (D.anchorPrime _ ι a)).1)
    exact flat_difference_of_three _ _ (atProbe 8 ι₃₆) (atProbe 7 ι₁₈) (atProbe 5 ι₉)
  · intro flat p hp ι he fits
    exact equalProfile_of_board_agreement c e ι he fits
      ((equal_scans_iff _ _).2 flat _ fits)

end New.Data.CollisionPrimeExample
