module

public import New.UpperBound.Divisibility.FlatColumnProfiles
import Mathlib.Tactic

/-!
# Transporting the unsigned mass between periods

Each old G-residue is the disjoint union of its two lifts modulo 2G. For an exceptional
prime the two finer residues are the actual conjugate prime ideals. Counting over the
common modulus first prevents the two measuring grids from being implicitly identified.
-/

@[expose] public section

open Finset NumberField ThreePrimeEnvelope
namespace New.SixSignatures

lemma either_half {G a u : ℕ} (h : u ≡ a [MOD G]) :
    u ≡ a [MOD 2*G] ∨ u ≡ a+G [MOD 2*G] := by
  obtain ⟨q,hq⟩ := h.dvd
  rcases Int.even_or_odd q with ⟨k,hk⟩ | ⟨k,hk⟩
  · left
    apply Nat.modEq_of_dvd
    refine ⟨k,?_⟩
    push_cast
    rw [hq,hk]
    ring
  · right
    apply Nat.modEq_of_dvd
    refine ⟨k+1,?_⟩
    push_cast
    rw [show (a:ℤ)+G-u=(a-u)+G by ring,hq,hk]
    ring

lemma halves_disjoint {G a u : ℕ} (hg : 0<G) (h : u ≡ a [MOD 2*G]) :
    ¬u ≡ a+G [MOD 2*G] := by
  intro other
  have eq : a+0 ≡ a+G [MOD 2*G] := by simpa using h.symm.trans other
  have div : 2*G ∣ G := Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_left_cancel' a eq).symm
  have := Nat.le_of_dvd hg div
  omega

lemma half_indicator {G : ℕ} (hg : 0<G) (a u : ℕ) :
    (if u ≡ a [MOD 2*G] then (1:ℕ) else 0)+(if u ≡ a+G [MOD 2*G] then 1 else 0) =
      if u ≡ a [MOD G] then 1 else 0 := by
  have down : G ∣ 2*G := dvd_mul_left _ _
  by_cases old : u ≡ a [MOD G]
  · obtain l|r := either_half old
    · simp [l,halves_disjoint hg l,old]
    · have nl : ¬u ≡ a [MOD 2*G] := fun l ↦ halves_disjoint hg l r
      simp [nl,r,old]
  · have nl : ¬u ≡ a [MOD 2*G] := fun l ↦ old (l.of_dvd down)
    have nr : ¬u ≡ a+G [MOD 2*G] := fun r ↦ old ((r.of_dvd down).trans (by simp [Nat.ModEq]))
    simp [nl,nr,old]

end New.SixSignatures

namespace New.Data
open SixSignatures
variable {P : Parameters}

/-- The number of actual high places in an offset class at any modulus. -/
noncomputable def offsetMass (D : Data P) (m a : ℕ) : ℕ :=
  #{z ∈ D.bPlaces | D.negativeOffset z ≡ a [MOD m]}

theorem offsetMass_split (D : Data P) {G : ℕ} (hg : 0<G) (a : ℕ) :
    D.offsetMass (2*G) a + D.offsetMass (2*G) (a+G) = D.offsetMass G a := by
  classical
  simp only [offsetMass,card_filter,← sum_add_distrib]
  exact sum_congr rfl fun z _ ↦ half_indicator hg a (D.negativeOffset z)

theorem IsExceptional.highCount_at_anchor {D : Data P} {p : ℕ} [Fact p.Prime] (ι : PadicPlace p)
    (he : D.IsExceptional p) (a : ℕ) :
    D.highCount p (D.anchorPrime p ι a) = D.offsetMass (2*D.returnPairCount p) a := by
  classical
  unfold highCount offsetMass
  congr 1
  apply filter_congr
  intro z hz
  have orig : D.inducedPlace (p := p) z=D.anchorPrime p ι (D.negativeOffset z) :=
    congrArg (D.inducedPlace (p := p)) (D.negativePlace_eq_offset (D.placeClass_of_mem_bPlaces _ hz))
  rw [orig,he.anchorPrime_eq_iff]

/-- Both finer counts together equal the original half-period class. -/
theorem IsExceptional.total_at_pair {D : Data P} {p : ℕ} [Fact p.Prime] (ι : PadicPlace p)
    (he : D.IsExceptional p) (a : ℕ) :
    let l := D.anchorPrime p ι a
    D.highCount p l + D.highCount p (star l) = D.offsetMass (D.returnPairCount p) a := by
  intro l
  change D.highCount p (D.anchorPrime p ι a) + D.highCount p (star (D.anchorPrime p ι a)) = _
  rw [← he.anchorPrime_conjugate, he.highCount_at_anchor,he.highCount_at_anchor]
  exact D.offsetMass_split (D.returnPairCount_pos _) _

end New.Data

namespace New.Data.CollisionPrimeExample
open SixSignatures OrbitProbes

lemma index_eq_iff_mod72 (u v : ℕ) : boardIndex u=boardIndex v ↔ u ≡ v [MOD 72] := by
  constructor
  · intro same
    have h := address_boardIndex u
    rw [same] at h
    exact h.symm.trans (address_boardIndex v)
  · exact boardIndex_congr

theorem offsetMass_of_board (D : Data params) {m : ℕ} (hm : m ∣ 72) (a : ℕ) :
    (D.offsetMass m a : ℤ) =
      ∑ b,∑ j,residueBoard D b j * (if address72 b j ≡ a [MOD m] then 1 else 0) := by
  classical
  let F := fun r : Fin 9 × Fin 8 ↦ if address72 r.1 r.2 ≡ a [MOD m] then (1:ℤ) else 0
  calc (D.offsetMass m a : ℤ) = ∑ z ∈ D.bPlaces, if D.negativeOffset z ≡ a [MOD m] then (1:ℤ) else 0 := by
        unfold offsetMass;rw [← sum_filter];simp
    _ = ∑ z ∈ D.bPlaces,F (boardIndex (D.negativeOffset z)) := by
      apply sum_congr rfl;intro z _
      have eq := (address_boardIndex (D.negativeOffset z)).of_dvd hm
      exact if_congr ⟨fun h ↦ eq.trans h, fun h ↦ eq.symm.trans h⟩ rfl rfl
    _ = _ := residueBoard_sum D F

/-- At a uniform column, its eight slots visit exactly the eight residues of its base
class modulo three on the common 24-slot grid. -/
theorem uniform_mass_at_24 (D : Data params) {k : ℕ} {c : Fin 9}
    (board : ∀ b j,residueBoard D b j=if b=c then (k:ℤ) else 0) (a : ℕ) :
    D.offsetMass 24 a = if a%3=c.val%3 then k else 0 := by
  classical
  have table : ∀ b : Fin 9, ∀ r : Fin 24,
      (∑ j : Fin 8, if address72 b j ≡ r.val [MOD 24] then (1:ℤ) else 0) =
          if r.val%3=b.val%3 then 1 else 0 := by decide
  have reduced (u : ℕ) : (u ≡ a [MOD 24]) ↔ u ≡ a%24 [MOD 24] :=
    ⟨fun h ↦ h.trans (Nat.mod_modEq a 24).symm,fun h ↦ h.trans (Nat.mod_modEq a 24)⟩
  have eq := table c ⟨a%24,Nat.mod_lt _ (by decide)⟩
  have small : (a%24)%3=a%3 := Nat.mod_mod_of_dvd a (by decide)
  change (∑ j : Fin 8, if address72 c j ≡ a%24 [MOD 24] then (1:ℤ) else 0) =
      (if (a%24)%3=c.val%3 then 1 else 0) at eq
  rw [small] at eq
  have h := offsetMass_of_board D (show 24∣72 by decide) a
  rw [sum_eq_single c] at h
  · simp only [board,← mul_sum] at h
    simp only [reduced] at h
    rw [eq] at h
    split_ifs at h ⊢ <;> simp_all
  · intro b _ ne
    simp [board,ne]
  · simp

lemma offsetMass_at_boardIndex (D : Data params) (a : ℕ) :
    (D.offsetMass 72 a:ℤ)=residueBoard D (boardIndex a).1 (boardIndex a).2 := by
  unfold offsetMass residueBoard
  congr 2
  apply filter_congr
  intro z _
  exact (index_eq_iff_mod72 _ _).symm

theorem uniform_mass_at_72 (D : Data params) {k : ℕ} {c : Fin 9}
    (board : ∀ b j,residueBoard D b j=if b=c then (k:ℤ) else 0) (a : ℕ) :
    D.offsetMass 72 a = if a%9=c.val then k else 0 := by
  have mass := offsetMass_at_boardIndex D a
  rw [board] at mass
  by_cases same : (boardIndex a).1=c
  · have v : a%9=c.val := congrArg Fin.val same
    rw [ite_eq_left same] at mass
    simpa [v] using (show D.offsetMass 72 a=k by exact_mod_cast mass)
  · have v : a%9≠c.val := fun eq ↦ same (Fin.ext eq)
    rw [ite_eq_right same] at mass
    simpa [v] using (show D.offsetMass 72 a=0 by exact_mod_cast mass)

end New.Data.CollisionPrimeExample
