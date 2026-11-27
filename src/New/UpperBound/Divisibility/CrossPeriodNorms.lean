module

public import New.UpperBound.Divisibility.SmallerOrbitPrimes
import Mathlib.Tactic

/-!
# The first incompatible and first doubled periods on the same arithmetic frame

For half-period 48, two pairs cover one common class modulo 24. For half-period 72,
one pair covers one original slot. Odd mass forces a nonunit within the indicated
finite sets of reference positions, independent of the finer lift counts.
-/

@[expose] public section
open Finset Filter NumberField Real ThreePrimeEnvelope ColoredSparse
namespace New.Data
variable {P : Parameters}

/-- Magnitude of the chain character at the actual finite prime indexed by offset a. -/
noncomputable def referenceNorm (D : Data P) (p : ℕ) [Fact p.Prime] (ι : PadicPlace p)
    (θ : D.TameChar) (j a : ℕ) : ℝ :=
  ‖ιₚ ((D.chainChar θ j).baseChange.atUniformizer (D.anchorPrime p ι a))‖

theorem IsExceptional.referenceNorm_eq_one {D : Data P} {p : ℕ} [Fact p.Prime] (ι : PadicPlace p)
    (he : D.IsExceptional p) (θ : D.TameChar) (j a : ℕ) :
    D.referenceNorm p ι θ j a=1 ↔
    D.highCount p (D.anchorPrime p ι a)=D.highCount p (star (D.anchorPrime p ι a)) :=
  norm_atUniformizer_eq_one_iff he.chiK_eq_neg_one
    (D.p_mem_inducedPlace (D.distinguishedLift a*D.placeOfInt (-1))) θ j

theorem IsExceptional.referenceNorm_power {D : Data P} {p : ℕ} [Fact p.Prime] (ι : PadicPlace p)
    (he : D.IsExceptional p) (θ : D.TameChar) (j a : ℕ) :
    D.referenceNorm p ι θ j a =
      (p:ℝ)^(D.signedCount p ι (D.anchorPrime p ι a)*((D.natB:ℤ)-D.offWeight)) :=
  norm_atUniformizer_eq_highSlope he.chiK_eq_neg_one
    (D.p_mem_inducedPlace (D.distinguishedLift a*D.placeOfInt (-1))) θ j

end New.Data
namespace New.Data.CollisionPrimeExample
open SixSignatures

/-- An odd count in one mod-24 class forces at least one of its two new pairs to
have unequal counts. Empty classes give unit norm at both. -/
theorem two_norms_at_96 (D : Data params) {k : ℕ} {b : Fin 9} (odd : Odd k)
    (board : ∀ c j,residueBoard D c j=if c=b then (k:ℤ) else 0)
    {p : ℕ} [Fact p.Prime] (ι : PadicPlace p) (he : D.IsExceptional p) (period : D.returnPairCount p=48)
    (θ : D.TameChar) (j a : ℕ) :
    (D.referenceNorm p ι θ j a=1 ∧ D.referenceNorm p ι θ j (a+24)=1) ↔ a%3≠b.val%3 := by
  have s := D.offsetMass_split (show 0<24 by decide) a
  have first := he.total_at_pair ι a
  have second := he.total_at_pair ι (a+24)
  dsimp only at first second
  rw [period] at first second
  have value := uniform_mass_at_24 D board a
  rw [he.referenceNorm_eq_one,he.referenceNorm_eq_one]
  by_cases same : a%3=b.val%3
  · rw [ite_eq_left same] at value
    obtain ⟨v,hv⟩ := odd
    change D.offsetMass 48 a+D.offsetMass 48 (a+24)=D.offsetMass 24 a at s
    omega
  · rw [ite_eq_right same] at value
    change D.offsetMass 48 a+D.offsetMass 48 (a+24)=D.offsetMass 24 a at s
    omega

theorem norm_at_doubled_period (D : Data params) {k : ℕ} {b : Fin 9} (odd : Odd k)
    (board : ∀ c j,residueBoard D c j=if c=b then (k:ℤ) else 0)
    {p : ℕ} [Fact p.Prime] (ι : PadicPlace p) (he : D.IsExceptional p) (period : D.returnPairCount p=72)
    (θ : D.TameChar) (j a : ℕ) :
    D.referenceNorm p ι θ j a=1 ↔ a%9≠b.val := by
  have total := he.total_at_pair ι a
  dsimp only at total
  rw [period,uniform_mass_at_72 D board] at total
  rw [he.referenceNorm_eq_one]
  split_ifs at total
  · obtain ⟨v,hv⟩ := odd
    omega
  · omega

/-- The same selected field and level supports both smaller probes. Sample a and a+24
at the first; a alone gives the full column at the second. -/
theorem eventually_cross_period_norms :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧ Odd k ∧ #D.bPlaces=8*k ∧
      ∀ b : Fin 9, let E := D.translateOffset b.val
        (∀ c j,residueBoard E c j=if c=b then (k:ℤ) else 0) ∧
        (∀ (ι : PadicPlace (smallerPrime 1)) θ j a,
          (E.referenceNorm _ ι θ j a=1 ∧ E.referenceNorm _ ι θ j (a+24)=1) ↔ a%3≠b.val%3) ∧
        ∀ (ι : PadicPlace (smallerPrime 3)) θ j a,
          E.referenceNorm _ ι θ j a=1 ↔ a%9≠b.val := by
  filter_upwards [eventually_separate_the_nine_columns] with x hx
  obtain ⟨D,k,scale,hk,odd,size,cols⟩ := hx
  refine ⟨D,k,scale,hk,odd,size,?_⟩
  intro b E
  have board := (cols b).1
  exact ⟨board,
    fun ι θ j a ↦ two_norms_at_96 E odd board ι (small_probe_facts E 1).1 (small_probe_facts E 1).2.2 θ j a,
    fun ι θ j a ↦ norm_at_doubled_period E odd board ι (small_probe_facts E 3).1 (small_probe_facts E 3).2.2 θ j a⟩

end New.Data.CollisionPrimeExample
