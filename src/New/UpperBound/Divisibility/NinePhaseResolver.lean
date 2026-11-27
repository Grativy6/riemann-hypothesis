module

public import New.UpperBound.Divisibility.OrbitProbeTable
import Mathlib.Tactic

/-!
# A fourth prime recovers the six counts in the four-slot encoding

At 1,829,519 the half-period is nine. The signed counts at references 0 and 1 read
-4k(A+B) and 4k(F-D). The first three prime profiles are insensitive to the two elementary
exchanges in this encoding. The new pair separates them.
-/

@[expose] public section
open Finset Filter NumberField ThreePrimeEnvelope ColoredSparse
namespace New.SixSignatures

lemma ninth_sums (w : Fin 6 → ℕ) :
    (∑ c,(w c:ℤ)*slotsAt 9 0 c) = -4*((w 0:ℤ)+w 1) ∧
    (∑ c,(w c:ℤ)*slotsAt 9 1 c) = 4*((w 4:ℤ)-w 5) := by
  have zero : ∀ c : Fin 6, slotsAt 9 0 c = (![-4,-4,0,0,0,0] : Fin 6 → ℤ) c := by decide
  have one : ∀ c : Fin 6, slotsAt 9 1 c = (![0,0,0,0,4,-4] : Fin 6 → ℤ) c := by decide
  simp only [zero,one]
  simp [Fin.sum_univ_succ]
  constructor <;> ring

/-- On each original report, the two signed sums at half-period nine determine the word. -/
lemma recovered_at_nine {w v : Fin 6 → ℕ} (eq : observed w=observed v)
    (zero : (w 0:ℤ)+w 1 = (v 0:ℤ)+v 1) (one : (w 4:ℤ)-w 5 = (v 4:ℤ)-v 5) : w=v := by
  obtain ⟨t,u,h₀,h₁,h₂,h₃,h₄,h₅⟩ := (same_report_iff _ _).1 eq
  have ht : t=0 := by omega
  have hu : u=0 := by omega
  subst t;subst u
  simp only [add_zero,sub_zero,mul_zero] at h₀ h₁ h₂ h₃ h₄ h₅
  funext i
  fin_cases i
  · exact_mod_cast h₀.symm
  · exact_mod_cast h₁.symm
  · exact_mod_cast h₂.symm
  · exact_mod_cast h₃.symm
  · exact_mod_cast h₄.symm
  · exact_mod_cast h₅.symm

end New.SixSignatures

namespace New.Data.CollisionPrimeExample
open SixSignatures OrbitProbes

/-- On an actual four-slot population these signed counts are measured at two specific
finite primes over 1,829,519. -/
theorem resolver_measurements (D : Data params) (ι : PadicPlace (rationalPrime 5)) {w : Fin 6 → ℕ}
    (pos : 0<∑ j,w j) {k : ℕ} (card : #D.bPlaces=(4*k)*(∑ j,w j))
    (pop : HasPopulation orbitAddress D.towerExp D.bPlaces (orbitWord w)) :
    D.signedCount (rationalPrime 5) ι (D.anchorPrime (rationalPrime 5) ι 0) = (k:ℤ)*(-4*((w 0:ℤ)+w 1)) ∧
    D.signedCount (rationalPrime 5) ι (D.anchorPrime (rationalPrime 5) ι 1) = (k:ℤ)*(4*((w 4:ℤ)-w 5)) := by
  have facts := period_and_exceptional D 5
  have G : D.returnPairCount (rationalPrime 5) = 9 := facts.2.2.2
  have per : 2*9 ∣ 72 := by decide
  rw [signed_profile_at_period D ι facts.1 G per pos card pop 0,
    signed_profile_at_period D ι facts.1 G per pos card pop 1,(ninth_sums w).1,(ninth_sums w).2]
  exact ⟨rfl,rfl⟩

theorem equal_at_two_resolver_primes_iff {D : Data params} (c e : HighPlaceChoice D)
    (ι : PadicPlace (rationalPrime 5)) {w v : Fin 6 → ℕ} {k : ℕ} (hk : 0<k)
    (positive : 0<∑ j,w j) (eq : observed w=observed v)
    (card : #D.bPlaces=(4*k)*(∑ j,w j))
    (cw : HasPopulation orbitAddress c.toData.towerExp c.toData.bPlaces (orbitWord w))
    (ev : HasPopulation orbitAddress e.toData.towerExp e.toData.bPlaces (orbitWord v)) :
    ((∀ a : Fin 2, c.toData.signedCount (rationalPrime 5) ι (D.anchorPrime (rationalPrime 5) ι a) =
      e.toData.signedCount (rationalPrime 5) ι (D.anchorPrime (rationalPrime 5) ι a)) ↔ w=v) := by
  have hmass := congrFun eq 0
  rw [observed_total,observed_total] at hmass
  have size : (∑ j,w j)=(∑ j,v j) := by exact_mod_cast hmass
  have ec := resolver_measurements e.toData ι (size ▸ positive) (e.same_card.trans (size ▸ card)) ev
  have cc := resolver_measurements c.toData ι positive (c.same_card.trans card) cw
  have nz : (k:ℤ)≠0 := by exact_mod_cast hk.ne'
  constructor
  · intro agree
    have a : c.toData.signedCount _ ι (c.toData.anchorPrime _ ι 0) =
        e.toData.signedCount _ ι (e.toData.anchorPrime _ ι 0) := agree 0
    have b : c.toData.signedCount _ ι (c.toData.anchorPrime _ ι 1) =
        e.toData.signedCount _ ι (e.toData.anchorPrime _ ι 1) := agree 1
    rw [cc.1,ec.1] at a
    rw [cc.2,ec.2] at b
    apply recovered_at_nine eq
    · linarith only [mul_left_cancel₀ nz a]
    · linarith only [mul_left_cancel₀ nz b]
  · rintro rfl i
    fin_cases i
    · exact cc.1.trans ec.1.symm
    · exact cc.2.trans ec.2.symm

/-- At a prime over p the magnitude of the local character determines the signed count
on this fixed frame, since the positive prime power is strictly increasing in the
integral exponent and the excess high weight is positive. -/
theorem local_norm_eq_iff_signed_eq {D : Data params} (c e : HighPlaceChoice D) {p : ℕ}
    [hp : Fact p.Prime] (ι : PadicPlace p) (he : D.IsExceptional p) {l : FinPlace D.E}
    (hl : (p : 𝓞 D.E) ∈ l.asIdeal) (θ : c.toData.TameChar) (η : e.toData.TameChar) (j b : ℕ) :
    (‖ιₚ ((c.toData.chainChar θ j).baseChange.atUniformizer l)‖ =
      ‖ιₚ ((e.toData.chainChar η b).baseChange.atUniformizer l)‖) ↔
      c.toData.signedCount p ι l = e.toData.signedCount p ι l := by
  rw [norm_atUniformizer_eq_highSlope (D := c.toData) he.chiK_eq_neg_one hl θ j,
    norm_atUniformizer_eq_highSlope (D := e.toData) he.chiK_eq_neg_one hl η b]
  have gt : (1:ℝ)<p := by exact_mod_cast hp.out.one_lt
  rw [(zpow_right_strictMono₀ gt).injective.eq_iff]
  let gap := (D.natB:ℤ)-D.offWeight
  have nz : gap≠0 := sub_ne_zero.2 (by exact_mod_cast (offWeight_lt_high D).ne')
  change c.toData.signedCount p ι l*gap = e.toData.signedCount p ι l*gap ↔ _
  exact ⟨fun eq ↦ mul_right_cancel₀ nz eq, fun eq ↦ congrArg (·*gap) eq⟩

/-- These are two actual absolute values at uniformizers, for arbitrarily chosen twists and
lifts. On the four-slot encoding they separate every pair of distinct words in one report. -/
theorem two_local_norms_recover_word {D : Data params} (c e : HighPlaceChoice D)
    (ι : PadicPlace (rationalPrime 5)) {w v : Fin 6 → ℕ} {k : ℕ} (hk : 0<k)
    (positive : 0<∑ j,w j) (eq : observed w=observed v)
    (card : #D.bPlaces=(4*k)*(∑ j,w j))
    (cw : HasPopulation orbitAddress c.toData.towerExp c.toData.bPlaces (orbitWord w))
    (ev : HasPopulation orbitAddress e.toData.towerExp e.toData.bPlaces (orbitWord v))
    (θ : c.toData.TameChar) (η : e.toData.TameChar) (j j' : ℕ) :
    (∀ a : Fin 2, let l := D.anchorPrime (rationalPrime 5) ι a
      ‖ιₚ ((c.toData.chainChar θ j).baseChange.atUniformizer l)‖ =
        ‖ιₚ ((e.toData.chainChar η j').baseChange.atUniformizer l)‖) ↔ w=v := by
  rw [← equal_at_two_resolver_primes_iff c e ι hk positive eq card cw ev]
  apply forall_congr'
  intro a
  exact local_norm_eq_iff_signed_eq c e ι (period_and_exceptional D 5).1 (D.p_mem_inducedPlace _) θ η j j'

end New.Data.CollisionPrimeExample
