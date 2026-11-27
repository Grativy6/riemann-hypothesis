module

public import New.UpperBound.Divisibility.ReturnQuotient
import New.Derivatives.Field.PrimeDecomposition
import Mathlib.Tactic

/-!
# Reading and choosing a marked prime pair by its residue

The modulus q₀ gcd(T,b) distinguishes the unordered pairs. Taking the places of 1+q₀ i at
offsets from zero up to the pair count chooses a full mark explicitly. Both membership
directions use the actual induced-prime map.
-/

@[expose] public section

namespace New.Data

open Finset

variable {P : Parameters} (D : Data P)

/-- The modulus at which the unordered induced-prime pair has its own class. -/
noncomputable def returnModulus (p : ℕ) : ℕ := P.q₀ * D.returnPairCount p

lemma returnModulus_dvd_tower (p : ℕ) : D.returnModulus p ∣ D.q₁ :=
  Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_left _ _)

/-- Reduce the multiplicative place to the intermediate modulus determined by the return carry. -/
noncomputable def inducedPairClass (p : ℕ) : D.Φ →* (ZMod (D.returnModulus p))ˣ :=
  P.placeClass (D.returnModulus_dvd_tower p)

variable {D} {p : ℕ} [hp : Fact p.Prime]

lemma first_return_pairClass_one (hi : chiK P.d p = -1) (ho : Odd (D.o₀ p)) :
    D.inducedPairClass p (D.placeOfInt (-(p : ℤ)) ^ D.o₀ p) = 1 := by
  have hnd : ¬p ∣ P.q₁ D.towerExp := fun hd ↦ by
    have := P.chiK_eq_one_of_dvd hp.out hd
    omega
  have cop : IsCoprime (-(p : ℤ)) P.q₀ := (Parameters.isCoprime_q₀_of_not_dvd hnd).neg_left
  have hd : D.returnModulus p ∣ p^(D.o₀ p)+1 := by
    rw [← mul_returnQuotient hi ho]
    exact Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_right _ _)
  have hz := (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at hz
  rw [inducedPairClass, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
    P.placeClass_placeOfInt cop]
  push_cast
  rw [ho.neg_pow]
  linear_combination -hz

open scoped Classical in
/-- Among the distinguished places, reducing modulo q₀ gcd(T,b) reads the entire unordered
pair of induced primes. The reduction is also sufficient for being distinguished once it
agrees with a distinguished place. -/
theorem mem_aPlaces_and_pair_iff_pairClass [PadicPlace p] (hi : chiK P.d p = -1)
    (ho : Odd (D.o₀ p)) (τ : D.Φ) (hτ : τ ∈ D.aPlaces) (σ : D.Φ) :
    (σ ∈ D.aPlaces ∧ (inducedPlace σ = inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ))) ↔
      D.inducedPairClass p σ = D.inducedPairClass p τ := by
  classical
  let g := D.placeOfInt (-(p : ℤ))
  let π := P.placeClass (P.q₀.dvd_mul_right (towerDeg D.towerExp))
  let T := towerDeg D.towerExp
  let G := D.returnPairCount p
  let B := D.aPlaces.filter fun z ↦ inducedPlace z = inducedPlace τ ∨
    inducedPlace z = star (inducedPlace τ)
  let F := (univ : Finset D.Φ).filter fun z ↦ D.inducedPairClass p z = D.inducedPairClass p τ
  let v (z : D.Φ) : ZMod D.q₁ := P.placeMulEquiv D.towerExp z
  let cast := ZMod.castHom (D.returnModulus_dvd_tower p) (ZMod (D.returnModulus p))
  let V := (univ : Finset (ZMod D.q₁)).filter fun z ↦ cast z = cast (v τ)
  have ht : π τ = 1 := by simpa [π, aPlaces] using hτ
  have sub : B ⊆ F := by
    intro z hz
    obtain ⟨ha, hpair⟩ := mem_filter.1 hz
    obtain ⟨i, rfl⟩ := (D.inducedPlace_eq_or_star_iff hi z τ).1 hpair
    have hpi : (π g)^i = 1 := by simpa [aPlaces, π, g, ht] using ha
    obtain ⟨j, hj⟩ := orderOf_dvd_iff_pow_eq_one.2 hpi
    change i = D.o₀ p * j at hj
    apply mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [hj, pow_mul, map_mul, map_pow, first_return_pairClass_one hi ho, one_pow, one_mul]
  have hval (z : D.Φ) : cast (v z) = (D.inducedPairClass p z : ZMod (D.returnModulus p)) := by
    simp [cast, v, inducedPairClass, Parameters.placeClass, ZMod.unitsMap_val, ZMod.castHom_apply]
  have vinj : Function.Injective v :=
    Units.val_injective.comp (P.placeMulEquiv D.towerExp).injective
  have cap : #F ≤ #V := card_le_card_of_injOn v (fun z hz ↦ mem_filter.2
    ⟨mem_univ _, by rw [hval, hval, (mem_filter.1 hz).2]⟩) vinj.injOn
  have hT : 0 < T := by dsimp [T, towerDeg]; positivity
  have hG : 0 < G := Nat.gcd_pos_of_pos_left _ hT
  have hR : 0 < D.returnModulus p := Nat.mul_pos (NeZero.pos _) hG
  have : NeZero (D.returnModulus p) := ⟨hR.ne'⟩
  have vb : #V * D.returnModulus p = D.q₁ :=
    ReturnQuotient.card_cast_fiber_mul (D.returnModulus_dvd_tower p) (cast (v τ))
  have hg : G * (T/G) = T := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have exact_cap : #V = T/G := by
    apply Nat.eq_of_mul_eq_mul_right hR
    calc #V * D.returnModulus p = D.q₁ := vb
      _ = (T/G) * (P.q₀*G) := by change P.q₀*T = _; nth_rw 1 [← hg]; ring
  have bsize : #B = T/G := (card_aPlaces_inducing_pair hi τ hτ).trans (pair_size_eq_tower_div_returnPairCount hi ho)
  have eq : B = F := eq_of_subset_of_card_le sub (cap.trans_eq (exact_cap.trans bsize.symm))
  simpa [B,F] using Finset.ext_iff.1 eq σ

end New.Data

namespace New.Data

open Finset
variable {P : Parameters} (D : Data P)

/-- The place of the integer 1+q₀ i is distinguished. The nonnegative offset i serves as an
ordinary coordinate on lifts of the identity residue. -/
noncomputable def distinguishedLift (i : ℕ) : D.Φ := D.placeOfInt ((1 + P.q₀*i : ℕ) : ℤ)

lemma distinguishedLift_val {m : ℕ} (d : m ∣ D.q₁) (i : ℕ) :
    (P.placeClass d (D.distinguishedLift i) : ZMod m) = (1 + P.q₀*i : ℕ) := by
  have cop : IsCoprime ((1+P.q₀*i : ℕ) : ℤ) (P.q₀ : ℤ) := by
    exact ⟨1, -(i : ℤ), by push_cast; ring⟩
  simpa [distinguishedLift] using (P.placeClass_placeOfInt (s := D.towerExp) (h_dvd := d) cop)

lemma distinguishedLift_mem (i : ℕ) : D.distinguishedLift i ∈ D.aPlaces := by
  simp only [aPlaces, mem_filter, mem_univ, true_and, Units.ext_iff, Units.val_one]
  rw [D.distinguishedLift_val]
  push_cast
  simp [ZMod.natCast_self]

/-- Integers from 0 up to the number of pairs have distinct intermediate residue classes. -/
lemma pairClass_distinguishedLift_inj (p : ℕ) {i j : ℕ}
    (hi : i < D.returnPairCount p) (hj : j < D.returnPairCount p)
    (he : D.inducedPairClass p (D.distinguishedLift i) = D.inducedPairClass p (D.distinguishedLift j)) :
    i = j := by
  let G := D.returnPairCount p
  have hM : 1 < P.q₀ := lt_of_lt_of_le (by decide : 1 < 18480) (Nat.le_of_dvd (NeZero.pos _) P.dvd_q₀)
  have small (v : ℕ) (hv : v < G) : 1 + P.q₀*v < P.q₀*G := calc
    1 + P.q₀*v < P.q₀ + P.q₀*v := Nat.add_lt_add_right hM _
    _ = P.q₀*(v+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hv
  have hz : ((1+P.q₀*i : ℕ) : ZMod (D.returnModulus p)) = ((1+P.q₀*j : ℕ) : ZMod (D.returnModulus p)) :=
    (D.distinguishedLift_val (D.returnModulus_dvd_tower p) i).symm.trans
      ((congrArg (fun z : (ZMod (D.returnModulus p))ˣ ↦ (z : ZMod (D.returnModulus p))) he).trans
        (D.distinguishedLift_val (D.returnModulus_dvd_tower p) j))
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).1 hz
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos _) <| Nat.add_left_cancel
    (hmod.eq_of_lt_of_lt (small i hi) (small j hj))

open scoped Classical in
/-- One explicit finite prime per arithmetic pair class. Offset i names the place of 1+q₀ i. -/
noncomputable def arithmeticMark (p : ℕ) [Fact p.Prime] [PadicPlace p] : Finset (FinPlace D.E) :=
  (range (D.returnPairCount p)).image fun i ↦ inducedPlace (D.distinguishedLift i)

variable {D} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]

/-- At each exceptional small prime the integer representatives form a full mark. -/
theorem IsExceptional.isFullMark_arithmeticMark (he : D.IsExceptional p) (hs : D.IsSmallNonsplit p) :
    D.IsFullMark (D.arithmeticMark p) := by
  classical
  have distinguish {i j : ℕ} (hi : i < D.returnPairCount p) (hj : j < D.returnPairCount p)
      (same : inducedPlace (D.distinguishedLift i) = inducedPlace (D.distinguishedLift j) ∨
        inducedPlace (D.distinguishedLift i) = star (inducedPlace (D.distinguishedLift j))) : i = j :=
    D.pairClass_distinguishedLift_inj p hi hj ((mem_aPlaces_and_pair_iff_pairClass
      he.chiK_eq_neg_one he.odd_o₀ (D.distinguishedLift j) (D.distinguishedLift_mem j) _).1
        ⟨D.distinguishedLift_mem i, same⟩)
  have hm : D.IsMarked (D.arithmeticMark p) := {
    star_notMem := by
      intro l hl hs'
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hl
      obtain ⟨j, hj, eq⟩ := mem_image.1 hs'
      obtain rfl := distinguish (mem_range.1 hj) (mem_range.1 hi) (.inr eq)
      exact he.star_ne (D.p_mem_inducedPlace _) eq.symm
    isExceptional := he
    induced_by_aPlace := by
      intro l hl
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hl
      exact ⟨_, D.distinguishedLift_mem i, rfl⟩
    isSmallNonsplit := hs }
  apply hm.full_iff_card_returnPairCount.2
  rw [arithmeticMark, card_image_of_injOn, card_range]
  exact fun i hi j hj eq ↦ distinguish (mem_range.1 hi) (mem_range.1 hj) (.inl eq)

end New.Data
