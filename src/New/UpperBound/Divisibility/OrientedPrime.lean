module

public import New.UpperBound.Divisibility.ArithmeticMark
import New.Derivatives.Field.PrimeDecomposition
import New.Reduction.PrimeSums
import Mathlib.Tactic

/-!
# The individual prime and the doubled modulus

Doubling the pair modulus distinguishes the two orientations on the distinguished fiber.
On the whole place group, the equal-prime condition permits all even Frobenius phases and
the conjugate-prime condition all odd phases. There are exactly o phases of each kind.
-/

@[expose] public section

namespace New.Parameters

/-- Reducing a named place in two stages agrees with reducing it directly. -/
lemma reduce_placeClass {P : New.Parameters} {s a b : ℕ} (hab : a ∣ b) (hb : b ∣ P.q₁ s) (σ : P.Φ s) :
    ZMod.unitsMap hab (P.placeClass hb σ) = P.placeClass (hab.trans hb) σ := by
  exact DFunLike.congr_fun (ZMod.unitsMap_comp hab hb) (P.placeMulEquiv s σ)

end New.Parameters

namespace New.Data
open Finset
variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime]

/-- The first-return cycle has even length at an exceptional prime, so twice the number
of pairs still divides the distinguished tower factor. -/
theorem IsExceptional.twice_pairCount_dvd_tower (he : D.IsExceptional p) :
    2 * D.returnPairCount p ∣ towerDeg D.towerExp := by
  have htwo := D.m_even.two_dvd.trans he.m_dvd_pair_size
  obtain ⟨k, hk⟩ := htwo
  have ht := returnPairCount_mul_period he.chiK_eq_neg_one he.odd_o₀
  rw [D.card_aPlaces, hk] at ht
  exact ⟨k, by rw [← ht]; ring⟩

theorem IsExceptional.twice_pairCount_not_dvd_quotient (he : D.IsExceptional p) :
    ¬ 2 * D.returnPairCount p ∣ D.returnQuotient p := by
  intro hd
  have qpos : 0 < towerDeg D.towerExp := by unfold towerDeg; positivity
  have hG : 0 < D.returnPairCount p := Nat.gcd_pos_of_pos_left _ qpos
  have h : 2 * D.returnPairCount p ∣ D.returnPairCount p := Nat.dvd_gcd he.twice_pairCount_dvd_tower hd
  have := Nat.le_of_dvd hG h
  omega

theorem IsExceptional.twice_returnModulus_dvd_tower (he : D.IsExceptional p) :
    2 * D.returnModulus p ∣ D.q₁ := by
  simpa only [returnModulus, mul_left_comm] using Nat.mul_dvd_mul_left P.q₀ he.twice_pairCount_dvd_tower

/-- The refined unit residue that separates the two orientations above a distinguished pair. -/
noncomputable def IsExceptional.inducedPrimeClass (he : D.IsExceptional p) :
    D.Φ →* (ZMod (2 * D.returnModulus p))ˣ :=
  P.placeClass he.twice_returnModulus_dvd_tower

theorem IsExceptional.reduce_inducedPrimeClass (he : D.IsExceptional p) (σ : D.Φ) :
    ZMod.unitsMap (dvd_mul_left (D.returnModulus p) 2) (he.inducedPrimeClass σ) = D.inducedPairClass p σ :=
  Parameters.reduce_placeClass _ _ _

/-- The first return has exact order two after the modulus that reads the pair is doubled. -/
theorem IsExceptional.primeClass_first_return_order (he : D.IsExceptional p) :
    orderOf (he.inducedPrimeClass (D.placeOfInt (-(p : ℤ))^D.o₀ p)) = 2 := by
  let o := D.o₀ p
  let R := D.returnModulus p
  let z : ℤ := (-(p : ℤ))^o
  have val : (he.inducedPrimeClass (D.placeOfInt (-(p : ℤ))^o) : ZMod (2*R)) = z := by
    have hnd : ¬p ∣ P.q₁ D.towerExp := fun h ↦ by
      have := P.chiK_eq_one_of_dvd hp.out h
      have := he.chiK_eq_neg_one
      omega
    have hc : IsCoprime (-(p : ℤ)) P.q₀ := (Parameters.isCoprime_q₀_of_not_dvd hnd).neg_left
    rw [IsExceptional.inducedPrimeClass, map_pow, Units.val_pow_eq_pow_val, P.placeClass_placeOfInt hc]
    simp only [z, Int.cast_pow]
  have sign : z-1 = -((p^o+1 : ℕ) : ℤ) := by
    dsimp only [z, o]
    rw [he.odd_o₀.neg_pow]
    push_cast
    ring
  have divR : R ∣ p^o+1 := by
    rw [show p^o+1 = P.q₀*D.returnQuotient p from
      (mul_returnQuotient he.chiK_eq_neg_one he.odd_o₀).symm]
    exact Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_right _ _)
  have notDouble : ¬2*R ∣ p^o+1 := by
    intro h
    rw [show p^o+1 = P.q₀*D.returnQuotient p from
      (mul_returnQuotient he.chiK_eq_neg_one he.odd_o₀).symm] at h
    have hd : P.q₀ * (2 * D.returnPairCount p) ∣ P.q₀ * D.returnQuotient p := by
      simpa only [R, returnModulus, mul_left_comm] using h
    exact he.twice_pairCount_not_dvd_quotient ((Nat.mul_dvd_mul_iff_left (NeZero.pos _)).1 hd)
  have h2 : 2 ∣ R := P.two_dvd_q₀.mul_right _
  have hz : (R : ℤ) ∣ z-1 := by rw [sign, dvd_neg]; exact_mod_cast divR
  have hn : ¬ (2*(R : ℤ)) ∣ z-1 := by rw [sign, dvd_neg]; exact_mod_cast notDouble
  rw [← orderOf_units, val]
  exact ReturnOrientation.square_period_two h2 z hz hn

end New.Data

namespace New.Data

variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- Counting first-return steps keeps the orientation bit on the actual induced finite prime. -/
theorem inducedPlace_after_returns (hi : chiK P.d p = -1) (ho : Odd (D.o₀ p))
    (n : ℕ) (τ : D.Φ) :
    inducedPlace ((D.placeOfInt (-(p : ℤ)) ^ D.o₀ p)^n * τ) =
      if Even n then inducedPlace τ else star (inducedPlace τ) := by
  have step (σ : D.Φ) : inducedPlace ((D.placeOfInt (-(p : ℤ)) ^ D.o₀ p) * σ) =
      star (inducedPlace σ) := by
    simpa only [Parameters.placeOfInt_pow, ho.neg_pow] using
      D.inducedPlace_neg_pow_mul_of_odd hi ho σ
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, step, ih]
      by_cases hn : Even n <;> simp [Nat.even_add_one, hn]

/-- At an exceptional prime the two orientations are distinct; precisely the even
number of return steps preserves the finite prime of the starting place. -/
theorem IsExceptional.prime_preserved_iff_even (he : D.IsExceptional p) (n : ℕ) (τ : D.Φ) :
    inducedPlace ((D.placeOfInt (-(p : ℤ)) ^ D.o₀ p)^n * τ) = inducedPlace τ ↔ Even n := by
  rw [inducedPlace_after_returns he.chiK_eq_neg_one he.odd_o₀]
  by_cases hn : Even n <;> simp [hn, he.star_ne (D.p_mem_inducedPlace τ)]

end New.Data


namespace New.Data

open Finset
variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime]

/-- A ratio of two places has trivial pair class exactly when it is a power of the first return. -/
theorem IsExceptional.pairClass_eq_iff_returns [PadicPlace p] (he : D.IsExceptional p) (σ τ : D.Φ) :
    D.inducedPairClass p σ = D.inducedPairClass p τ ↔
      ∃ n : ℕ, σ = (D.placeOfInt (-(p : ℤ))^D.o₀ p)^n * τ := by
  let g := D.placeOfInt (-(p : ℤ))
  let π := P.placeClass (P.q₀.dvd_mul_right (towerDeg D.towerExp))
  constructor
  · intro h
    have hv : D.inducedPairClass p (σ/τ) = D.inducedPairClass p 1 := by simp [map_div, h]
    obtain ⟨ha, hpair⟩ := (mem_aPlaces_and_pair_iff_pairClass he.chiK_eq_neg_one he.odd_o₀ 1
      (by simp [aPlaces]) (σ/τ)).2 hv
    obtain ⟨i, hi⟩ := (D.inducedPlace_eq_or_star_iff he.chiK_eq_neg_one (σ/τ) 1).1 hpair
    have hvpow : σ/τ = g^i := by simpa [g] using hi
    have hvone : π (σ/τ) = 1 := by simpa only [aPlaces, mem_filter, mem_univ, true_and, π] using ha
    rw [hvpow, map_pow] at hvone
    obtain ⟨n, hn⟩ := orderOf_dvd_iff_pow_eq_one.2 hvone
    change i = D.o₀ p * n at hn
    exact ⟨n, div_eq_iff_eq_mul.1 (by simpa [hn, pow_mul, g] using hvpow)⟩
  · rintro ⟨n,rfl⟩
    rw [map_mul, map_pow, first_return_pairClass_one he.chiK_eq_neg_one he.odd_o₀, one_pow, one_mul]

/-- Equality of refined residues picks the even first-return steps on the whole group of places. -/
theorem IsExceptional.primeClass_eq_iff_even_returns [PadicPlace p] (he : D.IsExceptional p) (σ τ : D.Φ) :
    he.inducedPrimeClass σ = he.inducedPrimeClass τ ↔
      ∃ n : ℕ, σ = (D.placeOfInt (-(p : ℤ))^D.o₀ p)^(2*n) * τ := by
  let u := D.placeOfInt (-(p : ℤ))^D.o₀ p
  have ht : orderOf (he.inducedPrimeClass u) = 2 := he.primeClass_first_return_order
  constructor
  · intro eq
    have hred := congrArg (ZMod.unitsMap (dvd_mul_left (D.returnModulus p) 2)) eq
    rw [he.reduce_inducedPrimeClass, he.reduce_inducedPrimeClass] at hred
    obtain ⟨n, hn⟩ := (he.pairClass_eq_iff_returns σ τ).1 hred
    have hper : (he.inducedPrimeClass u)^n = 1 := by
      rw [hn, map_mul, map_pow] at eq
      exact mul_right_cancel (eq.trans (one_mul _).symm)
    have h2 : 2 ∣ n := ht ▸ (orderOf_dvd_iff_pow_eq_one.2 hper)
    obtain ⟨k,hk⟩ := h2
    exact ⟨k,hk ▸ hn⟩
  · rintro ⟨n,rfl⟩
    have hpow : (he.inducedPrimeClass u)^2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by simp [ht])
    rw [map_mul, map_pow, pow_mul]
    change ((he.inducedPrimeClass u)^2)^n * _ = _
    rw [hpow, one_pow, one_mul]

/-- For a distinguished starting place the refined residue identifies the individual finite prime. -/
theorem IsExceptional.mem_aPlaces_and_prime_iff_primeClass [PadicPlace p] (he : D.IsExceptional p)
    (τ : D.Φ) (hτ : τ ∈ D.aPlaces) (σ : D.Φ) :
    (σ ∈ D.aPlaces ∧ inducedPlace σ = inducedPlace τ) ↔ he.inducedPrimeClass σ = he.inducedPrimeClass τ := by
  constructor
  · rintro ⟨ha, hprime⟩
    have hpair := (mem_aPlaces_and_pair_iff_pairClass he.chiK_eq_neg_one he.odd_o₀ τ hτ σ).1
      ⟨ha, Or.inl hprime⟩
    obtain ⟨n, hn⟩ := (he.pairClass_eq_iff_returns σ τ).1 hpair
    have even : Even n := (he.prime_preserved_iff_even n τ).1 (hn ▸ hprime)
    obtain ⟨k, hk⟩ := even_iff_two_dvd.1 even
    exact (he.primeClass_eq_iff_even_returns σ τ).2 ⟨k, hk ▸ hn⟩
  · intro hclass
    have hred := congrArg (ZMod.unitsMap (dvd_mul_left (D.returnModulus p) 2)) hclass
    rw [he.reduce_inducedPrimeClass, he.reduce_inducedPrimeClass] at hred
    have ha := ((mem_aPlaces_and_pair_iff_pairClass he.chiK_eq_neg_one he.odd_o₀ τ hτ σ).2 hred).1
    obtain ⟨k, rfl⟩ := (he.primeClass_eq_iff_even_returns σ τ).1 hclass
    exact ⟨ha, (he.prime_preserved_iff_even (2*k) τ).2 (even_two_mul k)⟩

/-- The even powers of the refined Frobenius residue give a cycle of length o. -/
theorem IsExceptional.order_primeClass_even_frobenius (he : D.IsExceptional p) :
    orderOf ((he.inducedPrimeClass (D.placeOfInt (-(p : ℤ))))^2) = D.o₀ p := by
  let g := D.placeOfInt (-(p : ℤ))
  let v := he.inducedPrimeClass g
  have hM : P.q₀ ∣ 2*D.returnModulus p :=
    (dvd_mul_right P.q₀ (D.returnPairCount p)).trans (dvd_mul_left (D.returnModulus p) 2)
  have hd : D.o₀ p ∣ orderOf v := by
    have h := orderOf_map_dvd (ZMod.unitsMap hM) v
    simpa only [v, IsExceptional.inducedPrimeClass, Parameters.reduce_placeClass, o₀, g] using h
  have ht : orderOf (v^(D.o₀ p)) = 2 := by simpa only [map_pow, v, g] using he.primeClass_first_return_order
  rw [orderOf_pow_of_dvd he.odd_o₀.pos.ne' hd] at ht
  have hall : orderOf v = 2 * D.o₀ p := calc
    _ = D.o₀ p * (orderOf v / D.o₀ p) := (Nat.mul_div_cancel' hd).symm
    _ = _ := by rw [ht, mul_comm]
  have h2 : 2 ∣ orderOf v := hall ▸ dvd_mul_right _ _
  change orderOf (v^2) = _
  rw [orderOf_pow_of_dvd (by decide : 2 ≠ 0) h2, hall, Nat.mul_div_cancel_left _ (by decide)]

end New.Data


namespace New.Data

open Finset
variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]

/-- For an inert prime, equality of two induced finite primes is an even Frobenius translation. -/
lemma inducedPlace_eq_iff_even_powers (hi : chiK P.d p = -1) (σ τ : D.Φ) :
    inducedPlace σ = inducedPlace τ ↔ ∃ n : ℕ, σ = D.placeOfInt (-(p : ℤ))^(2*n)*τ := by
  have hdiv : inducedPlace σ = (σ / τ) • inducedPlace τ := by rw [← inducedPlace_mul, mul_div_cancel]
  rw [hdiv, Parameters.smul_eq_self_iff_of_inert (D.p_mem_inducedPlace τ) hi]
  constructor
  · rintro ⟨i, hpow, hpar⟩
    obtain ⟨n, hn⟩ := even_iff_two_dvd.1 hpar
    exact ⟨n, div_eq_iff_eq_mul.1 (hn ▸ hpow)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨2*n, by simp, even_two_mul n⟩

/-- For arbitrary places the full readout allows o even Frobenius phases in the refined
residue. On the distinguished fiber only the identity phase can match. -/
theorem IsExceptional.inducedPlace_eq_iff_phase (he : D.IsExceptional p) (σ τ : D.Φ) :
    inducedPlace σ = inducedPlace τ ↔ ∃ j < D.o₀ p,
      he.inducedPrimeClass σ =
        (he.inducedPrimeClass (D.placeOfInt (-(p : ℤ))))^(2*j) * he.inducedPrimeClass τ := by
  let g := D.placeOfInt (-(p : ℤ))
  let v := he.inducedPrimeClass g
  have ord : orderOf (v^2) = D.o₀ p := he.order_primeClass_even_frobenius
  constructor
  · intro eq
    obtain ⟨j, rfl⟩ := (inducedPlace_eq_iff_even_powers he.chiK_eq_neg_one σ τ).1 eq
    refine ⟨j % D.o₀ p, Nat.mod_lt _ he.odd_o₀.pos, ?_⟩
    rw [map_mul, map_pow]
    have h := pow_mod_orderOf (v^2) j
    rw [ord] at h
    simp only [pow_mul, v, g, h]
  · rintro ⟨j, hj, read⟩
    have equal : he.inducedPrimeClass σ = he.inducedPrimeClass (g^(2*j)*τ) := by
      simpa only [map_mul, map_pow, g] using read
    obtain ⟨n, hn⟩ := (he.primeClass_eq_iff_even_returns _ _).1 equal
    have hsame := (he.prime_preserved_iff_even (2*n) (g^(2*j)*τ)).2 (even_two_mul _)
    rw [hn]
    exact hsame.trans ((inducedPlace_eq_iff_even_powers he.chiK_eq_neg_one _ τ).2 ⟨j,rfl⟩)

/-- The conjugate prime is read by the odd phases in the same finite residue ring. -/
theorem IsExceptional.inducedPlace_eq_star_iff_phase (he : D.IsExceptional p) (σ τ : D.Φ) :
    inducedPlace σ = star (inducedPlace τ) ↔ ∃ j < D.o₀ p,
      he.inducedPrimeClass σ =
        (he.inducedPrimeClass (D.placeOfInt (-(p : ℤ))))^(2*j+1) * he.inducedPrimeClass τ := by
  have step : inducedPlace (D.placeOfInt (-(p : ℤ))*τ) = star (inducedPlace τ) := by
    simpa using D.inducedPlace_neg_pow_mul_of_odd he.chiK_eq_neg_one odd_one τ
  rw [← step, he.inducedPlace_eq_iff_phase σ _]
  simp only [map_mul, pow_succ, mul_assoc]

omit [PadicPlace p] in
/-- At a distinguished pair even the direction of a single first return has a visible residue. -/
theorem IsExceptional.first_return_changes_primeClass (he : D.IsExceptional p) (τ : D.Φ) :
    D.inducedPairClass p ((D.placeOfInt (-(p : ℤ)) ^ D.o₀ p)*τ) = D.inducedPairClass p τ ∧
      he.inducedPrimeClass ((D.placeOfInt (-(p : ℤ)) ^ D.o₀ p)*τ) ≠ he.inducedPrimeClass τ := by
  rw [map_mul, first_return_pairClass_one he.chiK_eq_neg_one he.odd_o₀, one_mul, map_mul]
  refine ⟨rfl, fun h ↦ ?_⟩
  have hone := mul_right_cancel (h.trans (one_mul _).symm)
  have ht := he.primeClass_first_return_order
  rw [hone, orderOf_one] at ht
  omega

end New.Data

namespace New.Data

open Finset
variable {P : Parameters} (D : Data P)
variable {D} {p : ℕ} [Fact p.Prime]

lemma IsExceptional.primeClass_offset_iff (he : D.IsExceptional p) (i j : ℕ) :
    he.inducedPrimeClass (D.distinguishedLift i) = he.inducedPrimeClass (D.distinguishedLift j) ↔
      i ≡ j [MOD 2*D.returnPairCount p] := by
  rw [IsExceptional.inducedPrimeClass, Units.ext_iff, D.distinguishedLift_val,
    D.distinguishedLift_val, ZMod.natCast_eq_natCast_iff, returnModulus, mul_left_comm]
  exact lifted_offsets_modEq (P := P) _ _ _

/-- Adding a full block of pair labels interchanges the actual finite prime and its conjugate. -/
theorem IsExceptional.offset_add_pairCount_conjugates [PadicPlace p] (he : D.IsExceptional p) (i : ℕ) :
    inducedPlace (D.distinguishedLift (i + D.returnPairCount p)) = star (inducedPlace (D.distinguishedLift i)) := by
  let G := D.returnPairCount p
  have same := (D.pairClass_distinguishedLift_iff p (i+G) i).2 (by simp [Nat.ModEq, G])
  have both := (mem_aPlaces_and_pair_iff_pairClass he.chiK_eq_neg_one he.odd_o₀
    (D.distinguishedLift i) (D.distinguishedLift_mem i) (D.distinguishedLift (i+G))).2 same
  apply both.2.resolve_left
  intro eq
  have read := (he.mem_aPlaces_and_prime_iff_primeClass (D.distinguishedLift i) (D.distinguishedLift_mem i)
    (D.distinguishedLift (i+G))).1 ⟨both.1,eq⟩
  have hm := (he.primeClass_offset_iff (i+G) i).1 read
  have h0 : G ≡ 0 [MOD 2*G] := Nat.ModEq.add_left_cancel' i (by simpa using hm)
  have hd := (Nat.modEq_zero_iff_dvd).1 h0
  have hpG : 0 < G := D.returnPairCount_pos p
  have := Nat.le_of_dvd hpG hd
  omega

/-- Away from the distinguished fiber the refined residue can change even though the
individual finite prime stays fixed. The phase criterion retains these cases. -/
theorem IsExceptional.two_steps_same_prime_new_phase [PadicPlace p] (he : D.IsExceptional p)
    (ho : 1 < D.o₀ p) (τ : D.Φ) :
    inducedPlace (D.placeOfInt (-(p : ℤ))^2 * τ) = inducedPlace τ ∧
      he.inducedPrimeClass (D.placeOfInt (-(p : ℤ))^2 * τ) ≠ he.inducedPrimeClass τ := by
  constructor
  · apply (inducedPlace_eq_iff_even_powers he.chiK_eq_neg_one _ τ).2
    exact ⟨1,by simp⟩
  · intro hbad
    rw [map_mul, map_pow] at hbad
    have hone := mul_right_cancel (hbad.trans (one_mul _).symm)
    have horder := he.order_primeClass_even_frobenius
    rw [hone, orderOf_one] at horder
    omega

end New.Data
