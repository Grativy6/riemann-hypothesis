module

public import New.UpperBound.Divisibility.EveryFinitePrime
import Mathlib.Tactic

/-!
# Identical local norm profiles on one arithmetic frame

The per-word construction fixes all three measurements after every common translation.
It also fixes the signed count, and hence the norm of a chain character, at every actual
finite place above each of the three primes. The number field, level and weights are fixed.
-/

@[expose] public section

open Finset Filter NumberField ThreePrimeEnvelope ColoredSparse
namespace New.Data.CollisionPrimeExample
open SixSignatures
local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 535919) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 665279) := ⟨by norm_num1⟩

/-- The sum over the true tower places inducing a prescribed member of a conjugate pair. -/
theorem signed_profile_at_period (D : Data params) {p : ℕ} [Fact p.Prime] (ι : PadicPlace p)
    (he : D.IsExceptional p) {G : ℕ} (period : D.returnPairCount p=G) (per : 2*G ∣ 72)
    {w : Fin 6 → ℕ} {k : ℕ} (positive : 0<∑ c,w c)
    (card : #D.bPlaces = (4*k)*(∑ c,w c))
    (wit : HasPopulation orbitAddress D.towerExp D.bPlaces (orbitWord w)) (a : ℕ) :
    D.signedCount p ι (D.anchorPrime p ι a) = (k:ℤ)*∑ c,(w c:ℤ)*slotsAt G a c := by
  classical
  obtain ⟨hd,j,_,f,B,addr⟩ := wit
  have actual : #D.bPlaces = (4*j)*(∑ c,w c) := by
    rw [B,card_map,card_univ,sample_card,orbitWord_sum];ring
  have eq : j=k := by have v := Nat.eq_of_mul_eq_mul_right positive (actual.symm.trans card); omega
  subst j
  rw [he.signedCount_anchor,period]
  simpa only [slotsAt,nsmul_eq_mul] using orbit_sum_of_slots D f hd B addr
    (referenceSign G a) (fun _ _ m ↦ referenceSign_input (m.of_dvd per))

/-- Specialization to the three original probes. -/
theorem signed_profile_of_orbit_word (D : Data params) {p : ℕ} [Fact p.Prime] (ι : PadicPlace p)
    (he : D.IsExceptional p) {i : Fin 3} (period : D.returnPairCount p=probePeriod i)
    {w : Fin 6 → ℕ} {k : ℕ} (positive : 0<∑ c,w c)
    (card : #D.bPlaces = (4*k)*(∑ c,w c))
    (wit : HasPopulation orbitAddress D.towerExp D.bPlaces (orbitWord w)) (a : ℕ) :
    D.signedCount p ι (D.anchorPrime p ι a) = (k:ℤ)*∑ c,(w c:ℤ)*atReference a c i :=
  signed_profile_at_period D ι he period ((by decide : ∀ j,2*probePeriod j ∣ 72) i) positive card wit a

/-- Equality of the integer signed counts everywhere, and equality of all local character
norms at places over the rational prime. Twists and lift indices may be chosen separately. -/
def EqualPrimeProfile {D : Data params} (c e : HighPlaceChoice D) (p : ℕ) [Fact p.Prime]
    (ι : PadicPlace p) : Prop :=
  ∀ l : FinPlace D.E, c.toData.signedCount p ι l = e.toData.signedCount p ι l ∧
    ((p : 𝓞 D.E) ∈ l.asIdeal → ∀ (θ : c.toData.TameChar) (η : e.toData.TameChar) (j b : ℕ),
      ‖ιₚ ((c.toData.chainChar θ j).baseChange.atUniformizer l)‖ =
        ‖ιₚ ((e.toData.chainChar η b).baseChange.atUniformizer l)‖)

/-- The negative-unit reference primes cover the support of the signed counts. Agreement
there gives the full local norm comparison for any two assignments on the same field. -/
theorem equalPrimeProfile_of_anchors {D : Data params} (c e : HighPlaceChoice D)
    {p : ℕ} [Fact p.Prime] (ι : PadicPlace p) (he : D.IsExceptional p)
    (same : ∀ a, c.toData.signedCount p ι (D.anchorPrime p ι a) =
      e.toData.signedCount p ι (D.anchorPrime p ι a)) : EqualPrimeProfile c e p ι := by
  intro l
  have counts : c.toData.signedCount p ι l = e.toData.signedCount p ι l := by
    by_cases seen : ∃ a, D.anchorPrime p ι a=l
    · obtain ⟨a,rfl⟩ := seen;exact same a
    · have absent : ∀ a,D.anchorPrime p ι a≠l := fun a h ↦ seen ⟨a,h⟩
      rw [IsExceptional.signedCount_off_orbit (D := c.toData) he l absent,
        IsExceptional.signedCount_off_orbit (D := e.toData) he l absent]
  refine ⟨counts,?_⟩
  intro above θ η j b
  rw [norm_atUniformizer_eq_highSlope (D := c.toData) he.chiK_eq_neg_one above θ j,
    norm_atUniformizer_eq_highSlope (D := e.toData) he.chiK_eq_neg_one above η b]
  have slopes : c.toData.highSlope p l = e.toData.highSlope p l :=
    congrArg (fun z : ℤ ↦ z * ((D.natB:ℤ)-D.offWeight)) counts
  rw [slopes]

theorem equalPrimeProfile_of_report {D : Data params} (c e : HighPlaceChoice D)
    {p : ℕ} [Fact p.Prime] (ι : PadicPlace p) (he : D.IsExceptional p)
    {i : Fin 3} (per : D.returnPairCount p=probePeriod i) {w v : Fin 6 → ℕ}
    (positive : 0<∑ j,w j) (eq : observed w=observed v) {k : ℕ}
    (card : #D.bPlaces=(4*k)*(∑ j,w j))
    (cw : HasPopulation orbitAddress c.toData.towerExp c.toData.bPlaces (orbitWord w))
    (ev : HasPopulation orbitAddress e.toData.towerExp e.toData.bPlaces (orbitWord v)) :
    EqualPrimeProfile c e p ι := by
  have h := congrFun eq 0
  rw [observed_total,observed_total] at h
  have size : (∑ j,w j)=(∑ j,v j) := by exact_mod_cast h
  have ccard : #c.toData.bPlaces=(4*k)*(∑ j,w j) := c.same_card.trans card
  have ecard : #e.toData.bPlaces=(4*k)*(∑ j,v j) := e.same_card.trans (size ▸ card)
  have same (a : ℕ) : c.toData.signedCount p ι (D.anchorPrime p ι a) =
      e.toData.signedCount p ι (D.anchorPrime p ι a) := by
    change c.toData.signedCount p ι (c.toData.anchorPrime p ι a) = e.toData.signedCount p ι (e.toData.anchorPrime p ι a)
    rw [signed_profile_of_orbit_word c.toData ι he per positive ccard cw a,
      signed_profile_of_orbit_word e.toData ι he per (size ▸ positive) ecard ev a]
    rw [weighted_sum_eq_of_exchanges (a := fun j ↦ (w j:ℤ)) (b := fun j ↦ (v j:ℤ)) eq _
      (exchanges_at_reference a i).1 (exchanges_at_reference a i).2]
  exact equalPrimeProfile_of_anchors c e ι he same

/-- At every sufficiently large scale, every six-bin word in the same integer report
has an assignment on this single frame. All the assignments agree after every shift and
at every finite place over 479, 535919 and 665279. -/
theorem eventually_full_prime_profiles (w : Fin 6 → ℕ) (positive : 0<∑ i,w i) :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ) (initial : HighPlaceChoice D),
      D.natX=x ∧ 0<k ∧ #D.bPlaces=(4*k)*(∑ i,w i) ∧ census initial.toData=(fun i ↦ (4*k)*w i) ∧
      ∀ v : Fin 6 → ℕ, observed w=observed v → ∃ c : HighPlaceChoice D,
        census c.toData=(fun i ↦ (4*k)*v i) ∧ ∀ (ι₀ : PadicPlace 479)
        (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279),
        (∀ t, readings (initial.toData.translateOffset t) ι₀ ι₁ ι₂ =
          readings (c.toData.translateOffset t) ι₀ ι₁ ι₂) ∧
        EqualPrimeProfile initial c 479 ι₀ ∧ EqualPrimeProfile initial c 535919 ι₁ ∧
        EqualPrimeProfile initial c 665279 ι₂ := by
  filter_upwards [eventually_orbit_menu _ positive] with x result
  obtain ⟨D,k,scale,hk,card,menu⟩ := result
  obtain ⟨initial,first,firstHist,start⟩ := menu w rfl
  refine ⟨D,k,initial,scale,hk,card,firstHist,?_⟩
  intro v eq
  obtain ⟨size,_⟩ := (observed_eq_iff_count_and_point positive).1 eq.symm
  obtain ⟨c,second,hist,sweep⟩ := menu v size
  refine ⟨c,hist,?_⟩
  intro a b m
  have sel := singleton_and_thirty_six D b m
  have middle : D.IsExceptional 535919 := by
    let : PadicPlace 535919 := b
    exact sel.1.toIsMarked.isExceptional
  have last : D.IsExceptional 665279 := by
    let : PadicPlace 665279 := m
    obtain ⟨_,full⟩ := sel.2.1
    exact full.toIsMarked.isExceptional
  exact ⟨fun t ↦ (start t a b m).trans ((orbitPoint_eq_of_report eq t).trans (sweep t a b m).symm),
    equalPrimeProfile_of_report initial c a (exceptional_479 D) (i := 0) (returnPairCount_479 D)
      positive eq card first second,
    equalPrimeProfile_of_report initial c b middle (i := 1) (first_return_counts D).2.2
      positive eq card first second,
    equalPrimeProfile_of_report initial c m last (i := 2) (second_return_counts D).2.2
      positive eq card first second⟩

end New.Data.CollisionPrimeExample
