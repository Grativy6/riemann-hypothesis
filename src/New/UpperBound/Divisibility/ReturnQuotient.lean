module

public import Lib.General.NumberTheory.FirstReturn
public import New.UpperBound.Divisibility.MarkOperator
import New.Derivatives.Field.PrimeDecomposition
import New.Reduction.PrimeSums
import Mathlib.Tactic

/-!
# The integer left by the first return

A distinguished place has residue 1 modulo the base modulus M. For an inert prime with odd
local order o, write b = (pᵒ + 1) / M and let T be the tower factor. The first-return period is
the additive order of b modulo T. Each unordered pair of induced primes therefore accounts for
T / gcd(T,b) distinguished places. The number of selected primes and the number of uncovered places obey the same arithmetic count.
-/

@[expose] public section

open Finset


namespace New.Data
variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime]

/-- Inert primes act by their actual residue modulo every divisor of the fixed modulus. -/
lemma placeClass_neg_prime_val (h : chiK P.d p = -1) {n : ℕ} (hn : n ∣ P.q₀) :
    (P.placeClass (hn.trans (dvd_mul_right _ _)) (D.placeOfInt (-(p : ℤ))) : ZMod n) =
      -(p : ZMod n) := by
  have hcop : p.Coprime P.q₀ := hp.out.coprime_iff_not_dvd.2 fun hd ↦ by
    have hs := P.chiK_eq_one_of_dvd (s := D.towerExp) hp.out (hd.trans (dvd_mul_right _ _))
    omega
  have hi : IsCoprime (-(p : ℤ)) (P.q₀ : ℤ) :=
    (Nat.isCoprime_iff_coprime.2 hcop).neg_left
  simpa using (P.placeClass_placeOfInt (s := D.towerExp) (m := n)
    (h_dvd := hn.trans (dvd_mul_right _ _)) hi)

/-- For an inert prime, the divisibility condition on the place order is an ordinary modular power. -/
lemma dvd_iff_neg_prime_pow (h : chiK P.d p = -1) (e : ℕ) :
    D.o₀ p ∣ e ↔ (-(p : ZMod P.q₀))^e = 1 := by
  rw [o₀, orderOf_dvd_iff_pow_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val,
    Units.val_one, placeClass_neg_prime_val h dvd_rfl]

end New.Data

namespace New.Data

variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]
  {Λ : Finset (FinPlace D.E)}

open scoped Classical in
/-- Counting the marked, conjugate-marked and uncovered places partitions all a-places. -/
theorem IsMarked.card_uncovered_add_twice (h : D.IsMarked Λ) :
    #{τ ∈ D.aPlaces | inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ} +
      2 * #(D.aPlaces ∩ placesInducing Λ) = #D.aPlaces := by
  classical
  let S := D.aPlaces ∩ placesInducing Λ
  let C := D.aPlaces ∩ placesInducingConj Λ
  let shift := Equiv.mulLeft (D.placeOfInt (-p ^ D.o₀ p))
  have toA (τ : D.Φ) (hτ : τ ∈ D.aPlaces) : shift τ ∈ D.aPlaces :=
    (D.placeOfInt_mul_mem_aPlaces_iff h.isExceptional.odd_o₀ τ hτ).2 dvd_rfl
  have sc : Set.MapsTo shift (↑S) (↑C) := by
    intro τ hτ
    exact mem_inter.2 ⟨toA _ (mem_inter.1 hτ).1,
      (h.neg_pow_mul_mem_placesInducingConj_iff h.isExceptional.odd_o₀ τ).2 (mem_inter.1 hτ).2⟩
  have cs : Set.MapsTo shift (↑C) (↑S) := by
    intro τ hτ
    exact mem_inter.2 ⟨toA _ (mem_inter.1 hτ).1,
      (h.neg_pow_mul_mem_placesInducing_iff h.isExceptional.odd_o₀ τ).2 (mem_inter.1 hτ).2⟩
  have eqcard : #S = #C := le_antisymm (card_le_card_of_injOn _ sc shift.injective.injOn)
    (card_le_card_of_injOn _ cs shift.injective.injOn)
  have disjoint : Disjoint S C := by
    rw [Finset.disjoint_left]
    intro τ hs hc
    exact h.star_notMem (inducedPlace τ) (by simpa [placesInducing] using (mem_inter.1 hs).2)
      (by simpa [placesInducingConj] using (mem_inter.1 hc).2)
  have outside : D.aPlaces.filter (fun τ ↦ inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ) =
      D.aPlaces \ (S ∪ C) := by
    ext τ
    simp [S, C, placesInducing, placesInducingConj]
    tauto
  have sub : S ∪ C ⊆ D.aPlaces := union_subset inter_subset_left inter_subset_left
  have le := card_le_card sub
  rw [card_union_of_disjoint disjoint] at le
  rw [outside, card_sdiff_of_subset sub, card_union_of_disjoint disjoint]
  change #D.aPlaces - (#S + #C) + 2 * #S = #D.aPlaces
  omega

open scoped Classical in
/-- A full mark covers every distinguished place in at least one orientation. -/
theorem IsMarked.isFullMark_iff_no_uncovered (h : D.IsMarked Λ) :
    D.IsFullMark Λ ↔
      D.aPlaces.filter (fun τ ↦ inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ) = ∅ := by
  classical
  constructor
  · intro full
    apply eq_empty_iff_forall_notMem.2
    intro τ hτ
    obtain ⟨ha, hn, hc⟩ := mem_filter.1 hτ
    exact (full.mem_or_star_mem τ ha).elim hn hc
  · intro empty
    refine ⟨h, fun τ ha ↦ ?_⟩
    by_contra! bad
    have mem : τ ∈ D.aPlaces.filter (fun z ↦ inducedPlace z ∉ Λ ∧ star (inducedPlace z) ∉ Λ) :=
      mem_filter.2 ⟨ha, bad⟩
    simp [empty] at mem

end New.Data

namespace New.Data

open Finset
variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]

open scoped Classical in
/-- Counting the image of the indexed orbit gives the number of distinguished places
that induce either orientation of the prime of τ. -/
theorem card_aPlaces_inducing_pair (hinert : chiK P.d p = -1) (τ : D.Φ) (hτ : τ ∈ D.aPlaces) :
    #{σ ∈ D.aPlaces | inducedPlace σ = inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ)} =
      orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p := by
  classical
  let g := D.placeOfInt (-(p : ℤ))
  let N := orderOf (g^D.o₀ p)
  have : NeZero N := .of_pos (orderOf_pos _)
  obtain ⟨t, ht, _, hrange⟩ := D.exists_orbit_of_mem_aPlaces hinert hτ
  have image_eq : D.aPlaces.filter
      (fun σ ↦ inducedPlace σ = inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ)) =
      (univ : Finset (ZMod N)).image t := by
    ext σ
    simpa only [mem_filter, mem_image, mem_univ, true_and, Set.mem_range] using (hrange σ).symm
  rw [image_eq, card_image_of_injective _ ht, card_univ, ZMod.card]
  exact orderOf_pow_of_dvd (orderOf_pos _).ne' (orderOf_map_dvd _ _)

end New.Data

namespace New.Data

open Finset
variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]
  {Λ : Finset (FinPlace D.E)}

open scoped Classical in
/-- The chosen primes cover disjoint orbits, each with the same number of distinguished places. -/
theorem IsMarked.card_uncovered_add_card_mul_pair (h : D.IsMarked Λ) :
    #{σ ∈ D.aPlaces | inducedPlace σ ∉ Λ ∧ star (inducedPlace σ) ∉ Λ} +
      #Λ * (orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p) = #D.aPlaces := by
  classical
  let U := D.aPlaces.filter fun σ ↦ inducedPlace σ ∉ Λ ∧ star (inducedPlace σ) ∉ Λ
  let fiber (l : FinPlace D.E) :=
    D.aPlaces.filter fun σ ↦ inducedPlace σ = l ∨ star (inducedPlace σ) = l
  have hmem (σ : D.Φ) (l : FinPlace D.E) :
      σ ∈ fiber l ↔ σ ∈ D.aPlaces ∧ (inducedPlace σ = l ∨ star (inducedPlace σ) = l) :=
    mem_filter
  have disj : (Λ : Set (FinPlace D.E)).PairwiseDisjoint fiber := by
    intro l hl w hw hn
    rw [Function.onFun, disjoint_left]
    intro σ hs ht
    obtain ⟨_, hl' | hl'⟩ := (hmem σ l).1 hs <;>
      obtain ⟨_, hw' | hw'⟩ := (hmem σ w).1 ht <;> grind [h.star_notMem, star_star]
  have hcard (l : FinPlace D.E) (hl : l ∈ Λ) :
      #(fiber l) = orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p := by
    obtain ⟨τ, hτ, rfl⟩ := h.induced_by_aPlace l hl
    simpa only [fiber, star_eq_iff_star_eq, eq_comm (a := star (inducedPlace τ))] using
      card_aPlaces_inducing_pair h.isExceptional.chiK_eq_neg_one τ hτ
  have hcover : U = D.aPlaces \ Λ.biUnion fiber := by
    ext σ
    simp only [U, mem_filter, mem_sdiff, mem_biUnion, hmem]
    grind
  have sub : Λ.biUnion fiber ⊆ D.aPlaces := biUnion_subset.2 fun l _ ↦ filter_subset _ _
  have hc : #(Λ.biUnion fiber) = #Λ * (orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p) := by
    rw [card_biUnion disj, sum_congr rfl hcard, sum_const, nsmul_eq_mul]
    simp
  change #U + _ = _
  rw [hcover, ← hc, card_sdiff_of_subset sub, Nat.sub_add_cancel (card_le_card sub)]

end New.Data

namespace New.Data

open Finset

variable {P : Parameters} (D : Data P)

/-- At an inert prime of odd local order o, pᵒ+1 is a multiple of q₀. This is its quotient. -/
noncomputable def returnQuotient (p : ℕ) : ℕ := (p^(D.o₀ p)+1)/P.q₀

/-- The arithmetic count of unordered prime pairs over the distinguished places. -/
noncomputable def returnPairCount (p : ℕ) : ℕ := (towerDeg D.towerExp).gcd (D.returnQuotient p)

variable {D} {p : ℕ} [hp : Fact p.Prime]

lemma mul_returnQuotient (hi : chiK P.d p = -1) (ho : Odd (D.o₀ p)) :
    P.q₀ * D.returnQuotient p = p^(D.o₀ p) + 1 := by
  have hpow := (dvd_iff_neg_prime_pow (D := D) hi (D.o₀ p)).1 dvd_rfl
  rw [ho.neg_pow] at hpow
  have hdvd : P.q₀ ∣ p^(D.o₀ p)+1 := (ZMod.natCast_eq_zero_iff _ _).1 <| by
    push_cast
    linear_combination -hpow
  exact Nat.mul_div_cancel' hdvd

/-- On the distinguished fiber the first return has the same period as addition of its
ordinary return quotient in the cyclic group modulo the tower factor. -/
theorem order_first_return_eq_addOrder (hi : chiK P.d p = -1) (ho : Odd (D.o₀ p)) :
    orderOf (D.placeOfInt (-(p : ℤ)) ^ D.o₀ p) =
      addOrderOf ((D.returnQuotient p : ℕ) : ZMod (towerDeg D.towerExp)) := by
  let g := D.placeOfInt (-(p : ℤ))
  let o := D.o₀ p
  let b := D.returnQuotient p
  have h12 : 12 ∣ P.q₀ := (by decide : 12 ∣ 18480).trans P.dvd_q₀
  have hnd : ¬p ∣ P.q₁ D.towerExp := fun h ↦ by
    have hs := P.chiK_eq_one_of_dvd hp.out h
    omega
  have hcop : IsCoprime (-(p : ℤ)) P.q₀ := (Parameters.isCoprime_q₀_of_not_dvd hnd).neg_left
  have hg : ((P.placeMulEquiv D.towerExp g) : ZMod D.q₁) = -(p : ZMod D.q₁) := by
    simpa [g] using (P.placeMulEquiv_placeOfInt (s := D.towerExp) hcop)
  have hb : (P.q₀ : ℤ)*b = (p : ℤ)^o + 1 := by exact_mod_cast mul_returnQuotient hi ho
  have hz : (-(p : ℤ))^o = 1 + P.q₀ * (-(b : ℤ)) := by
    change (-(p : ℤ))^(D.o₀ p) = _
    rw [ho.neg_pow]
    dsimp [o] at hb
    linarith
  calc orderOf (g^o) = orderOf ((P.placeMulEquiv D.towerExp) (g^o)) :=
        ((P.placeMulEquiv D.towerExp).orderOf_eq _).symm
    _ = orderOf ((-(p : ZMod D.q₁))^o) := by
      rw [map_pow, ← orderOf_units, Units.val_pow_eq_pow_val, hg]
    _ = orderOf (((1 + P.q₀ * (-(b : ℤ)) : ℤ) : ZMod D.q₁)) := by
      congr 1
      simpa only [Int.cast_pow, Int.cast_neg, Int.cast_natCast] using
        congrArg (fun z : ℤ ↦ (z : ZMod D.q₁)) hz
    _ = addOrderOf ((-(b : ℤ)) : ZMod (towerDeg D.towerExp)) := by
      unfold q₁ Parameters.q₁ towerDeg
      rw [Nat.mul_comm (3 ^ _) (2 ^ _)]
      simpa only [Int.cast_neg, Int.cast_natCast] using
        ReturnQuotient.order_eq_addOrder P.q₀ (NeZero.ne _) h12 (-(b : ℤ)) D.towerExp
          (Nat.log 3 D.towerExp + 5)
    _ = _ := by simp [b]

/-- The number of distinguished places in one unordered induced-prime pair is T/gcd(T,b),
where T is the tower factor and b is the return quotient. -/
theorem pair_size_eq_tower_div_returnPairCount (hi : chiK P.d p = -1) (ho : Odd (D.o₀ p)) :
    orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p = towerDeg D.towerExp / D.returnPairCount p := by
  have hd : D.o₀ p ∣ orderOf (D.placeOfInt (-(p : ℤ))) := orderOf_map_dvd _ _
  have ht : 0 < towerDeg D.towerExp := by unfold towerDeg; positivity
  rw [← orderOf_pow_of_dvd ho.pos.ne' hd, order_first_return_eq_addOrder hi ho,
    ZMod.addOrderOf_coe _ ht.ne', returnPairCount]

variable [PadicPlace p] {Λ : Finset (FinPlace D.E)}

/-- Every full mark has exactly gcd(T,b) members, independently of orientation and of the
chosen p-adic embedding. -/
theorem IsFullMark.card_eq_returnPairCount (h : D.IsFullMark Λ) : #Λ = D.returnPairCount p := by
  have hi := h.isExceptional.chiK_eq_neg_one
  have ho := h.isExceptional.odd_o₀
  let T := towerDeg D.towerExp
  let G := D.returnPairCount p
  have ht : 0 < T := by dsimp [T, towerDeg]; positivity
  have hd : G ∣ T := Nat.gcd_dvd_left _ _
  have hg : 0 < G := Nat.gcd_pos_of_pos_left _ ht
  have hperiod : 0 < T/G := Nat.div_pos (Nat.le_of_dvd ht hd) hg
  have hc := h.toIsMarked.card_uncovered_add_card_mul_pair
  rw [h.toIsMarked.isFullMark_iff_no_uncovered.1 h, card_empty, zero_add,
    pair_size_eq_tower_div_returnPairCount hi ho, D.card_aPlaces] at hc
  exact Nat.eq_of_mul_eq_mul_right hperiod (hc.trans (Nat.mul_div_cancel' hd).symm)

end New.Data

namespace New.Data

open Finset Real
variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime]

/-- The count times the common orbit length is the size of the distinguished fiber. -/
lemma returnPairCount_mul_period (hi : chiK P.d p = -1) (ho : Odd (D.o₀ p)) :
    D.returnPairCount p * (orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p) = #D.aPlaces := by
  rw [pair_size_eq_tower_div_returnPairCount hi ho, D.card_aPlaces]
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

/-- The power-of-two lift count divides the length of every exceptional first-return orbit.
Dividing by the odd local order preserves all those factors of two. -/
theorem IsExceptional.m_dvd_pair_size (h : D.IsExceptional p) :
    D.m ∣ orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p := by
  have hd : D.o₀ p ∣ orderOf (D.placeOfInt (-(p : ℤ))) := orderOf_map_dvd _ _
  have hcop : D.m.Coprime (D.o₀ p) := by
    obtain ⟨e, hm, _⟩ := D.exists_m_eq_two_pow
    rw [hm]
    exact (Nat.coprime_two_right.2 h.odd_o₀).symm.pow_left _
  exact hcop.dvd_of_dvd_mul_left ((Nat.mul_div_cancel' hd).symm ▸ h.m_dvd_orderOf)

variable [PadicPlace p] {Λ : Finset (FinPlace D.E)}

/-- A mark is full precisely when its number of selected primes reaches the arithmetic count. -/
theorem IsMarked.full_iff_card_returnPairCount (h : D.IsMarked Λ) :
    D.IsFullMark Λ ↔ #Λ = D.returnPairCount p := by
  refine ⟨fun f ↦ f.card_eq_returnPairCount, fun hk ↦ h.isFullMark_iff_no_uncovered.2 ?_⟩
  apply card_eq_zero.1
  have balance := h.card_uncovered_add_card_mul_pair
  rw [hk, returnPairCount_mul_period h.isExceptional.chiK_eq_neg_one h.isExceptional.odd_o₀] at balance
  omega

/-- Distinct marked primes each account for at least m distinguished places. -/
theorem IsMarked.mul_card_le_aPlaces (h : D.IsMarked Λ) : D.m * #Λ ≤ #D.aPlaces := by
  have hd : D.o₀ p ∣ orderOf (D.placeOfInt (-(p : ℤ))) := orderOf_map_dvd _ _
  have hpos : 0 < orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p :=
    Nat.div_pos (Nat.le_of_dvd (orderOf_pos _) hd) h.isExceptional.odd_o₀.pos
  have hm := Nat.le_of_dvd hpos h.isExceptional.m_dvd_pair_size
  calc D.m * #Λ ≤ #Λ * (orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p) := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ hm
    _ ≤ #D.aPlaces := by have := h.card_uncovered_add_card_mul_pair; omega

open scoped Classical in
/-- The arithmetic pair count determines how many distinguished places remain uncovered. -/
theorem IsMarked.uncovered_share (h : D.IsMarked Λ) :
    (D.returnPairCount p : ℝ) *
      (#{σ ∈ D.aPlaces | inducedPlace σ ∉ Λ ∧ star (inducedPlace σ) ∉ Λ} : ℝ) =
      ((D.returnPairCount p : ℝ) - #Λ) * #D.aPlaces := by
  let n := orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p
  let U := D.aPlaces.filter fun σ ↦ inducedPlace σ ∉ Λ ∧ star (inducedPlace σ) ∉ Λ
  have hc : (#U : ℝ) + (#Λ : ℝ)*n = #D.aPlaces := by exact_mod_cast h.card_uncovered_add_card_mul_pair
  have ht : (D.returnPairCount p : ℝ)*n = #D.aPlaces := by
    exact_mod_cast returnPairCount_mul_period h.isExceptional.chiK_eq_neg_one h.isExceptional.odd_o₀
  change (D.returnPairCount p : ℝ) * (#U : ℝ) = _
  linear_combination (D.returnPairCount p : ℝ) * hc - (#Λ : ℝ) * ht

open scoped Classical in
/-- When the carry is coprime to the tower factor, the prime of any distinguished place gives
an explicit singleton full mark. -/
theorem IsExceptional.fullMark_singleton (he : D.IsExceptional p) (hs : D.IsSmallNonsplit p)
    (hc : D.returnPairCount p = 1) (τ : D.Φ) (hτ : τ ∈ D.aPlaces) :
    D.IsFullMark (p := p) {inducedPlace τ} := by
  classical
  have hm : D.IsMarked (p := p) {inducedPlace τ} := {
    star_notMem := by
      intro l hl
      obtain rfl := Finset.mem_singleton.1 hl
      simpa using he.star_ne (D.p_mem_inducedPlace τ)
    isExceptional := he
    induced_by_aPlace := by
      intro l hl
      exact ⟨τ, hτ, (Finset.mem_singleton.1 hl).symm⟩
    isSmallNonsplit := hs }
  exact hm.full_iff_card_returnPairCount.2 (by simp [hc])

end New.Data
