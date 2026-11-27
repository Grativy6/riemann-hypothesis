module

public import New.UpperBound.Divisibility.LocalDivisibility
import New.UpperBound.Divisibility.ChainDatumExpansion
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# The collision mass of a partial mark

The marked places exclude both orientations of an induced prime pair from the collision count.
The surviving exponents at each uncovered distinguished place are the positive odd multiples
of the order of the place of −p modulo q₀. Reindexing gives a convergent geometric series.

Erasing one prime from a full mark uncovers a whole orbit. Its number of places is the
order of the place of −p divided by its order modulo q₀. The final estimates apply the
computed mass to the restricted chain and the composite lift.
-/

@[expose] public section

open Function

/-! ## The geometric series -/

namespace New.CollisionArithmetic

/-- The positive odd multiples of an odd natural number form one convergent geometric series. -/
theorem hasSum_odd_multiples {x : ℝ} (hx : 1 < x) (a : ℝ) {o : ℕ} (ho : Odd o) :
    HasSum (fun e : ℕ ↦ if Odd e ∧ o ∣ e then a / x^e else 0)
      (a * x^o / ((x^o)^2 - 1)) := by
  let next (j : ℕ) := o * (2*j+1)
  have hinj : Injective next := by
    intro j k heq
    have := Nat.eq_of_mul_eq_mul_left ho.pos heq
    omega
  have range_of {e : ℕ} (he : Odd e ∧ o ∣ e) : e ∈ Set.range next := by
    obtain ⟨d, hd⟩ := he.2
    subst e
    obtain ⟨j, hj⟩ := (Nat.odd_mul.1 he.1).2
    exact ⟨j, by simp [next, hj]⟩
  have he (j : ℕ) : Odd (next j) ∧ o ∣ next j :=
    ⟨Nat.odd_mul.2 ⟨ho, ⟨j, rfl⟩⟩, dvd_mul_right ..⟩
  apply (hinj.hasSum_iff (fun e h ↦ ite_eq_right (fun hc ↦ h (range_of hc)))).1
  let q := x^o
  have hq : 1 < q := one_lt_pow₀ hx ho.pos.ne'
  have hs : 1 < q^2 := one_lt_pow₀ hq (by decide)
  have hsum := (hasSum_geometric_of_lt_one (by positivity : 0 ≤ (q^2)⁻¹)
    (inv_lt_one_of_one_lt₀ hs)).mul_left (a/q)
  have value : a / q * (1 - (q^2)⁻¹)⁻¹ = a * q / (q^2 - 1) := by
    have hq0 : q ≠ 0 := by linarith
    have hs0 : q^2 - 1 ≠ 0 := by linarith
    field_simp
  rw [value] at hsum
  refine hsum.congr_fun fun j ↦ ?_
  change (if Odd (next j) ∧ o ∣ next j then a / x^(next j) else 0) = _
  rw [ite_eq_left (he j)]
  simp only [next, pow_mul, pow_succ, ← inv_pow, div_eq_mul_inv, mul_inv_rev, q]
  ring

end New.CollisionArithmetic

open Finset

namespace New.Data

variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]
  {Λ : Finset (FinPlace D.E)}

/-! ## Which places contribute -/

/-- A collision survives exactly at an uncovered conjugate pair and an odd multiple of
the order of the place of -p modulo the fixed modulus. -/
theorem IsMarked.collision_iff_uncovered (h : D.IsMarked Λ) (τ : D.Φ) (e : ℕ) :
    D.IsCollision p (placesInducing Λ) τ e ↔
      (τ ∈ D.aPlaces ∧ inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ) ∧
        Odd e ∧ D.o₀ p ∣ e := by
  constructor
  · intro hc
    obtain ⟨_, he, ho⟩ := hc.ne_and_odd_and_dvd
    obtain ⟨_, hτ, hpartner⟩ := hc
    obtain ⟨ha, hn⟩ := mem_sdiff.1 hτ
    have h1 : inducedPlace τ ∉ Λ := by simpa [placesInducing] using hn
    have h2 : star (inducedPlace τ) ∉ Λ := by
      simpa [placesInducing,
        D.inducedPlace_neg_pow_mul_of_odd h.isExceptional.chiK_eq_neg_one he] using
        (mem_sdiff.1 hpartner).2
    exact ⟨⟨ha, h1, h2⟩, he, ho⟩
  · rintro ⟨⟨ha, h1, h2⟩, he, ho⟩
    refine ⟨mem_positivePartnerExponents.2
      ⟨he.pos, mem_partnerExponents.2 (.inr ⟨h.isExceptional.chiK_eq_neg_one, he⟩)⟩,
      mem_sdiff.2 ⟨ha, by simpa [placesInducing] using h1⟩, mem_sdiff.2 ⟨?_, ?_⟩⟩
    · exact (D.placeOfInt_mul_mem_aPlaces_iff he τ ha).2 ho
    · simpa [placesInducing,
        D.inducedPlace_neg_pow_mul_of_odd h.isExceptional.chiK_eq_neg_one he] using h2

open scoped Classical in
theorem IsMarked.collisionSum_eq_uncovered_mul_tail (h : D.IsMarked Λ) :
    D.collisionSum p (placesInducing Λ) =
      (#{τ ∈ D.aPlaces | inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ} : ℝ) *
        ∑' e : ℕ, if Odd e ∧ D.o₀ p ∣ e then (D.a / p^e : ℝ) else 0 := by
  classical
  let U := D.aPlaces.filter fun τ ↦ inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ
  let T := ∑' e : ℕ, if Odd e ∧ D.o₀ p ∣ e then (D.a / p^e : ℝ) else 0
  have hterm (τ : D.Φ) :
      (∑' e : ℕ, if D.IsCollision p (placesInducing Λ) τ e then (D.a / p^e : ℝ) else 0) =
        if τ ∈ U then T else 0 := by
    by_cases hτ : τ ∈ U
    · have hu : τ ∈ D.aPlaces ∧ inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ :=
        Finset.mem_filter.1 hτ
      simp [h.collision_iff_uncovered, hu, hτ, T]
    · have hu : ¬ (τ ∈ D.aPlaces ∧ inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ) :=
        fun hx ↦ hτ (Finset.mem_filter.2 hx)
      simp [h.collision_iff_uncovered, hu, hτ]
  unfold collisionSum
  simp_rw [hterm]
  change (∑ τ : D.Φ, if τ ∈ U then T else 0) = (#U : ℝ) * T
  rw [← Finset.sum_filter]
  simp [nsmul_eq_mul]

end New.Data

open Finset

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

variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]
  {Λ : Finset (FinPlace D.E)}

open scoped Classical in
/-- Each uncovered a-place contributes one geometric tail of ratio p^(-2o), with o the order
of -p modulo the fixed modulus. -/
theorem IsMarked.collisionSum_eq_uncovered (h : D.IsMarked Λ) :
    D.collisionSum p (placesInducing Λ) =
      (#{τ ∈ D.aPlaces | inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ} : ℝ) *
        (D.a * (p : ℝ) ^ D.o₀ p / (((p : ℝ) ^ D.o₀ p)^2 - 1)) := by
  rw [h.collisionSum_eq_uncovered_mul_tail,
    (CollisionArithmetic.hasSum_odd_multiples (by exact_mod_cast hp.out.one_lt)
      (D.a : ℝ) h.isExceptional.odd_o₀).tsum_eq]

/-- Marking c of the A distinguished places accounts for exactly 2c places in the
collision count, including the conjugate-induced places. -/
theorem IsMarked.collisionSum_placesInducing_eq (h : D.IsMarked Λ) :
    D.collisionSum p (placesInducing Λ) =
      ((#D.aPlaces : ℝ) - 2 * #(D.aPlaces ∩ placesInducing Λ)) *
        (D.a * (p : ℝ) ^ D.o₀ p / (((p : ℝ) ^ D.o₀ p)^2 - 1)) := by
  classical
  have hc : (#{τ ∈ D.aPlaces | inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ} : ℝ) +
      2 * #(D.aPlaces ∩ placesInducing Λ) = #D.aPlaces := by
    exact_mod_cast h.card_uncovered_add_twice
  rw [h.collisionSum_eq_uncovered]
  congr 1
  linarith

/-- A marked set removes the entire collision sum exactly when it covers every
conjugate pair of induced primes. -/
theorem IsMarked.collisionSum_placesInducing_eq_zero_iff (h : D.IsMarked Λ) :
    D.collisionSum p (placesInducing Λ) = 0 ↔ D.IsFullMark Λ := by
  classical
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hq := one_lt_pow₀ hp1 h.isExceptional.odd_o₀.pos.ne'
  have hden : 0 < ((p : ℝ)^D.o₀ p)^2 - 1 := sub_pos.2 (one_lt_pow₀ hq (by decide))
  have ha : 0 < (D.a : ℝ) := HasLogBound.pos D
  have cost : 0 < D.a * (p : ℝ)^D.o₀ p / (((p : ℝ)^D.o₀ p)^2 - 1) := by positivity
  rw [h.collisionSum_eq_uncovered, h.isFullMark_iff_no_uncovered]
  simp [cost.ne']

end New.Data

namespace New.Data
variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]

/-! ## The orbit uncovered by one erasure -/

open scoped Classical in
/-- The distinguished places inducing the same unordered pair of primes as τ form one coset
of the subgroup generated by g^o, for g the place of -p and o its order modulo q₀. -/
theorem card_aPlaces_inducing_pair (hinert : chiK P.d p = -1) (τ : D.Φ) (hτ : τ ∈ D.aPlaces) :
    #{σ ∈ D.aPlaces | inducedPlace σ = inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ)} =
      orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p := by
  classical
  let g := D.placeOfInt (-(p : ℤ))
  let π := P.placeClass (P.q₀.dvd_mul_right (towerDeg D.towerExp))
  let a := g ^ D.o₀ p
  have ht : π τ = 1 := by simpa [aPlaces, π] using hτ
  have ord : D.o₀ p = orderOf (π g) := rfl
  have hg : π a = 1 := by simp [a, ord, map_pow, pow_orderOf_eq_one]
  let orbit := (range (orderOf a)).image fun j ↦ a^j * τ
  have orbit_eq : D.aPlaces.filter
      (fun σ ↦ inducedPlace σ = inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ)) = orbit := by
    ext σ
    constructor
    · intro h
      obtain ⟨hσ, hpair⟩ := mem_filter.1 h
      obtain ⟨i, hi⟩ := (D.inducedPlace_eq_or_star_iff hinert σ τ).1 hpair
      have hσ' : π σ = 1 := by simpa [aPlaces, π] using hσ
      have hi' : (π g)^i = 1 := by simpa [hi, g, map_mul, map_pow, ht] using hσ'
      obtain ⟨j, rfl⟩ := orderOf_dvd_iff_pow_eq_one.2 hi'
      exact mem_image.2 ⟨j % orderOf a, mem_range.2 (Nat.mod_lt _ (orderOf_pos a)), by
        rw [pow_mod_orderOf]; simpa [a, ord, g, pow_mul] using hi.symm⟩
    · intro h
      obtain ⟨j, _, rfl⟩ := mem_image.1 h
      refine mem_filter.2 ⟨?_, (D.inducedPlace_eq_or_star_iff hinert _ τ).2 ?_⟩
      · have hm : π (a^j * τ) = 1 := by simp [map_mul, map_pow, ht, hg]
        simpa [aPlaces, π] using hm
      · exact ⟨D.o₀ p * j, by simp [g, a, pow_mul]⟩
  rw [orbit_eq, card_image_of_injOn, card_range]
  · exact orderOf_pow_of_dvd (by rw [ord]; exact (orderOf_pos _).ne') (ord ▸ orderOf_map_dvd π g)
  · intro j hj k hk h
    exact pow_injOn_Iio_orderOf (mem_range.1 hj) (mem_range.1 hk) (mul_right_cancel h)

variable {Λ : Finset (FinPlace D.E)}

open scoped Classical in
/-- Any subset obtained by erasing one chosen prime is still a mark. -/
theorem IsMarked.erase (h : D.IsMarked Λ) (l : FinPlace D.E) : D.IsMarked (Λ.erase l) where
  star_notMem w hw hw' := h.star_notMem w (mem_of_mem_erase hw) (mem_of_mem_erase hw')
  isExceptional := h.isExceptional
  induced_by_aPlace w hw := h.induced_by_aPlace w (mem_of_mem_erase hw)
  isSmallNonsplit := h.isSmallNonsplit

open scoped Classical in
/-- Erasing one prime from a full mark leaves exactly one orbit of distinguished places.
Its size is the global place order divided by the order modulo the fixed modulus. -/
theorem IsFullMark.collisionSum_erase (h : D.IsFullMark Λ) {l : FinPlace D.E} (hl : l ∈ Λ) :
    D.collisionSum p (placesInducing (Λ.erase l)) =
      ((orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p : ℕ) : ℝ) *
        (D.a * (p : ℝ) ^ D.o₀ p / (((p : ℝ) ^ D.o₀ p)^2 - 1)) := by
  classical
  have hm := h.toIsMarked.erase l
  obtain ⟨τ, hτ, ht⟩ := h.induced_by_aPlace l hl
  have heq : D.aPlaces.filter (fun σ ↦ inducedPlace σ ∉ Λ.erase l ∧ star (inducedPlace σ) ∉ Λ.erase l) =
      D.aPlaces.filter (fun σ ↦ inducedPlace σ = inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ)) := by
    refine filter_congr fun σ hσ ↦ ?_
    rw [ht]
    have hbar := h.star_notMem l hl
    constructor
    · intro hu
      rcases h.mem_or_star_mem σ hσ with hw | hw
      · exact Or.inl (by by_contra hn; exact hu.1 (mem_erase.2 ⟨hn, hw⟩))
      · have he : star (inducedPlace σ) = l := by
          by_contra hn
          exact hu.2 (mem_erase.2 ⟨hn, hw⟩)
        exact Or.inr (by simpa using congrArg star he)
    · rintro (he | he) <;> simp [he, hbar]
  rw [hm.collisionSum_eq_uncovered, heq, card_aPlaces_inducing_pair h.isExceptional.chiK_eq_neg_one τ hτ]

end New.Data

namespace New.Data

open Finset

variable {P : Parameters} (D : Data P) {p : ℕ} [hp : Fact p.Prime]

/-! ## The value with no exclusions -/

omit hp in
/-- Without marks the only tests on a place and an exponent are membership in the distinguished
places, inertness, odd parity and divisibility by the local order. -/
lemma collision_empty_iff (τ : D.Φ) (e : ℕ) :
    D.IsCollision p ∅ τ e ↔ τ ∈ D.aPlaces ∧ chiK P.d p = -1 ∧ Odd e ∧ D.o₀ p ∣ e := by
  constructor
  · intro hc
    obtain ⟨hd, he, ho⟩ := hc.ne_and_odd_and_dvd
    exact ⟨(mem_sdiff.1 hc.2.1).1,
      ((mem_partnerExponents.1 (mem_positivePartnerExponents.1 hc.1).2).resolve_left hd).1, he, ho⟩
  · rintro ⟨ha, hi, he, ho⟩
    refine ⟨mem_positivePartnerExponents.2 ⟨he.pos, mem_partnerExponents.2 (.inr ⟨hi, he⟩)⟩,
      by simpa using ha, ?_⟩
    simpa using (D.placeOfInt_mul_mem_aPlaces_iff he τ ha).2 ho

/-- Exact collision mass with no excluded places, at every prime of any admissible data. -/
theorem collisionSum_empty_value :
    D.collisionSum p ∅ =
      if chiK P.d p = -1 ∧ Odd (D.o₀ p) then
        (#D.aPlaces : ℝ) * (D.a * (p : ℝ)^D.o₀ p / (((p : ℝ)^D.o₀ p)^2 - 1)) else 0 := by
  classical
  by_cases h : chiK P.d p = -1 ∧ Odd (D.o₀ p)
  · rw [ite_eq_left h]
    let c := D.a * (p : ℝ)^D.o₀ p / (((p : ℝ)^D.o₀ p)^2 - 1)
    have hx : 1 < (p : ℝ) := by exact_mod_cast hp.out.one_lt
    have ht := (CollisionArithmetic.hasSum_odd_multiples hx (D.a : ℝ) h.2).tsum_eq
    have term (τ : D.Φ) :
        (∑' e : ℕ, if D.IsCollision p ∅ τ e then (D.a / p^e : ℝ) else 0) =
          if τ ∈ D.aPlaces then c else 0 := by
      by_cases ha : τ ∈ D.aPlaces
      · simpa [D.collision_empty_iff, ha, h.1, c] using ht
      · simp [D.collision_empty_iff, ha]
    unfold collisionSum
    simp_rw [term]
    rw [← Finset.sum_filter]
    simp [nsmul_eq_mul, c]
  · have hn (τ : D.Φ) (e : ℕ) : ¬D.IsCollision p ∅ τ e := by
      intro hc
      obtain ⟨_, hi, he, ho⟩ := (D.collision_empty_iff τ e).1 hc
      exact h ⟨hi, Odd.of_dvd_nat he ho⟩
    simp [h, collisionSum, hn]

end New.Data

open Finset Real

namespace New.Data

variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]
  {Λ : Finset (FinPlace D.E)} {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}

/-! ## Consequences for the lifts -/

/-- A scalar that absorbs the collision excess gives the same target gauge as a full mark. -/
theorem IsWeakChainDatum.gaugeLe_scalar_of_collision_budget (hΨ : IsWeakChainDatum ϑ Ψ)
    (hQ : p.Coprime ϑ.normQ) {v : D.SourceForm} (hv : v ∈ D.integralSourceForms)
    (hs : D.IsSmallNonsplit p) {j : ℕ} (hj : D.m * D.collisionSum p ∅ ≤ D.loss p + j) :
    GaugeLe 1 (p ^ (2 * D.loss p - D.gain p))
      (restrictedChain ϑ Ψ ((p : ℂ)^j • v)) := by
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hnorm : ‖ιₚ ((p : ℂ)^j)‖ = (p : ℝ)^(-(j : ℝ)) := by
    simp [norm_p_eq_inv, rpow_neg]
  have h := (hΨ.gaugeLe_restrictedChain_collisionSum hQ hv hs).smul ((p : ℂ)^j)
  rw [hnorm, ← rpow_add hp_pos] at h
  rw [map_smul]
  exact h.rpow_mono (by linarith)

omit hp [PadicPlace p] in
/-- The least natural scalar exponent allowed by the collision budget, including a zero or
negative excess. -/
theorem least_collision_excess_iff (j : ℕ) :
    ⌈D.m * D.collisionSum p ∅ - D.loss p⌉₊ ≤ j ↔ D.m * D.collisionSum p ∅ ≤ D.loss p + j := by
  rw [Nat.ceil_le]
  constructor <;> intro h <;> linarith

end New.Data

namespace New.Data

open Finset Real Submodule
open scoped Pointwise

variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]
  {Λ : Finset (FinPlace D.E)} {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}

open scoped Classical in
/-- Removing a single chosen prime from a full mark increases the exponent in the proved gauge
bound by m times the mass of its orbit. This is an upper bound on the gauge of the actual lift. -/
theorem IsWeakChainDatum.gaugeLe_restrictedChain_erase (hΨ : IsWeakChainDatum ϑ Ψ)
    (hQ : p.Coprime ϑ.normQ) {v : D.SourceForm} (hv : v ∈ D.integralSourceForms)
    (hΛ : D.IsFullMark Λ) {l : FinPlace D.E} (hl : l ∈ Λ) :
    ∃ hm : D.IsMarked (Λ.erase l),
      GaugeLe 1 (p ^ (D.m * (((orderOf (D.placeOfInt (-(p : ℤ))) / D.o₀ p : ℕ) : ℝ) *
        (D.a * (p : ℝ)^D.o₀ p / (((p : ℝ)^D.o₀ p)^2 - 1))) + 2 * D.loss p - D.gain p))
        (restrictedChain ϑ Ψ ((((Λ.erase l).attach.toList.map hm.scaledHeckeOperator).prod ^ D.m) v)) := by
  have hm := hΛ.toIsMarked.erase l
  exact ⟨hm, by simpa only [hΛ.collisionSum_erase hl] using
    hΨ.gaugeLe_restrictedChain_of_isMarked hQ hv hm⟩

/-- In the scalar summand of the marked submodule, any natural exponent covering the excess
above loss gives the required composite-lift valuation. The least exponent is allowed as well. -/
theorem IsChainDatum.gaugeLe_compositeLift_of_collision_excess (hΨ : IsChainDatum ϑ Ψ)
    (hQ : p.Coprime ϑ.normQ) (hΛ : D.IsFullMark Λ) {j : ℕ}
    (hj : ⌈D.m * D.collisionSum p ∅ - D.loss p⌉₊ ≤ j) {φ : D.SourceForm}
    (hφ : φ ∈ D.integralSourceForms.map ((Λ.attach.toList.map hΛ.scaledHeckeOperator).prod ^ D.m) ⊔
      (p : embValRing)^j • D.integralSourceForms) :
    GaugeLe 1 (p ^ (2 * D.loss p - D.gain p)) (compositeLift ϑ Ψ φ) := by
  obtain ⟨Ψ', hΨ', heq⟩ : ∃ Ψ' : D.Translations →₀ ℂ, IsWeakChainDatum ϑ Ψ' ∧
      ∀ φ : D.SourceForm, compositeLift ϑ Ψ φ = restrictedChain ϑ Ψ' φ :=
    hΨ.exists_isWeakChainDatum_compositeLift_eq
  obtain ⟨u, hu, v, hv, rfl⟩ : ∃ u ∈ D.integralSourceForms, ∃ v ∈ D.integralSourceForms,
      ((Λ.attach.toList.map hΛ.scaledHeckeOperator).prod ^ D.m) u + (p : ℂ)^j • v = φ := by
    obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, hsum⟩ := mem_sup.1 hφ
    exact ⟨u, hu, v, hv, hsum⟩
  rw [heq, map_add]
  have hmark := hΨ'.gaugeLe_restrictedChain_of_isMarked hQ hu hΛ.toIsMarked
  rw [hΛ.collisionSum_placesInducing_eq_zero, mul_zero, zero_add] at hmark
  exact hmark.add (hΨ'.gaugeLe_scalar_of_collision_budget hQ hv hΛ.isSmallNonsplit
    ((least_collision_excess_iff j).1 hj))

end New.Data
