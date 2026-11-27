module

public import New.UpperBound.Divisibility.SixPlaceCensus
import Mathlib.Tactic

/-!
# Which unsigned measurements recover the six counts?

At each probe the two prime ideals select the bins with negative and positive sign. The
middle pair always accounts for every high place. At fixed total and fixed signed readings,
the occupied totals at the first and third probes determine all six counts.
-/

@[expose] public section

open Finset Real Filter NumberField ThreePrimeEnvelope ColoredSparse
namespace New.Data.CollisionPrimeExample
open SixSignatures
local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 535919) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 665279) := ⟨by norm_num1⟩

/-- Counts above the prime of the negative unit and its conjugate, in that order. -/
noncomputable def pairCounts (D : Data params) (p : ℕ) [Fact p.Prime] (ι : PadicPlace p) : ℕ × ℕ :=
  let l := D.negativeUnitPrime p
  (D.highCount p l, D.highCount p (star l))

/-- Count the two sides together before taking their difference. -/
noncomputable def occupied (D : Data params) (p : ℕ) [Fact p.Prime] (ι : PadicPlace p) : ℕ :=
  (pairCounts D p ι).1 + (pairCounts D p ι).2

private def binCountAt (n : Fin 6 → ℕ) (i : Fin 3) (z : ℤ) : ℕ :=
  ∑ c, if signature c i = z then n c else 0

private theorem counts_at_signs (D : Data params) {p : ℕ} [Fact p.Prime] (ι : PadicPlace p)
    (he : D.IsExceptional p) {i : Fin 3} (period : D.returnPairCount p = probePeriod i) :
    pairCounts D p ι = (binCountAt (census D) i (-1), binCountAt (census D) i 1) := by
  classical
  let : PadicPlace p := ι
  let l := D.negativeUnitPrime p
  have side (u : FinPlace D.E) (z : ℤ)
      (test : ∀ σ ∈ D.bPlaces, inducedPlace σ = u ↔ signature (bin (D.negativeOffset σ)) i = z) :
      D.highCount p u = binCountAt (census D) i z := by
    rw [highCount, card_filter]
    calc (∑ σ ∈ D.bPlaces, if inducedPlace σ = u then 1 else 0) =
         ∑ σ ∈ D.bPlaces, if signature (bin (D.negativeOffset σ)) i = z then 1 else 0 :=
           sum_congr rfl fun σ hσ ↦ if_congr (test σ hσ) rfl rfl
      _ = _ := by
        rw [sum_census D (fun c ↦ if signature c i = z then (1:ℕ) else 0)]
        simp [binCountAt,mul_ite]
  have flags (σ : D.Φ) (hσ : σ ∈ D.bPlaces) := he.negative_unit_flags hσ
  have val (σ : D.Φ) : signAt (D.returnPairCount p) (D.negativeOffset σ) =
      signature (bin (D.negativeOffset σ)) i := by rw [period, sign_in_bin]
  exact Prod.ext (side l (-1) fun σ hσ ↦ by simpa only [← val] using (flags σ hσ).1)
    (side (star l) 1 fun σ hσ ↦ by simpa only [← val] using (flags σ hσ).2)

/-- All six unsigned numbers are counts at genuine finite primes. -/
theorem probe_pair_counts (D : Data params) (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919)
    (ι₂ : PadicPlace 665279) :
    let n := census D
    pairCounts D 479 ι₀ = (n 0+n 1+n 2,n 3) ∧
    pairCounts D 535919 ι₁ = (n 0+n 1+n 2+n 3+n 4,n 5) ∧
    pairCounts D 665279 ι₂ = (n 0,n 1) := by
  intro n
  have pair := singleton_and_thirty_six D ι₁ ι₂
  have mid : D.IsExceptional 535919 := by
    let : PadicPlace 535919 := ι₁
    exact pair.1.toIsMarked.isExceptional
  have last : D.IsExceptional 665279 := by
    let : PadicPlace 665279 := ι₂
    obtain ⟨_,v⟩ := pair.2.1
    exact v.toIsMarked.isExceptional
  rw [counts_at_signs D ι₀ (exceptional_479 D) (i := 0) (returnPairCount_479 D),
    counts_at_signs D ι₁ mid (i := 1) (first_return_counts D).2.2,
    counts_at_signs D ι₂ last (i := 2) (second_return_counts D).2.2]
  simp [binCountAt,signature,Fin.sum_univ_succ,n,add_assoc]

theorem occupied_eq_census (D : Data params) (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919)
    (ι₂ : PadicPlace 665279) :
    occupied D 479 ι₀ = firstOccupied (census D) ∧ occupied D 535919 ι₁ = #D.bPlaces ∧
      occupied D 665279 ι₂ = thirdOccupied (census D) := by
  obtain ⟨a,b,c⟩ := probe_pair_counts D ι₀ ι₁ ι₂
  simp [occupied,a,b,c,firstOccupied,thirdOccupied,← census_total,Fin.sum_univ_succ,add_assoc]

/-- The size, the three signed readings, and the occupied totals at 479 and 665279 determine
all six populations and are determined by them. The totals need no common field assumption. -/
theorem census_eq_iff_measurements_eq (D E : Data params) (ι₀ : PadicPlace 479)
    (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    census D = census E ↔ #D.bPlaces = #E.bPlaces ∧
      readings D ι₀ ι₁ ι₂ = readings E ι₀ ι₁ ι₂ ∧
      occupied D 479 ι₀ = occupied E 479 ι₀ ∧ occupied D 665279 ι₂ = occupied E 665279 ι₂ := by
  have d := occupied_eq_census D ι₀ ι₁ ι₂
  have e := occupied_eq_census E ι₀ ι₁ ι₂
  rw [d.1,e.1,d.2.2,e.2.2,readings_eq_census,readings_eq_census,← census_total,← census_total]
  constructor
  · rintro eq
    rw [eq]
    simp
  · rintro ⟨mass,value,first,third⟩
    have pos : 0 < ∑ i,census E i := (census_total E).symm ▸ card_pos.2 E.bPlaces_nonempty
    exact recover_from_occupancies ((observed_eq_iff_count_and_point pos).2 ⟨mass,value⟩) first third

end New.Data.CollisionPrimeExample
