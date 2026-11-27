module

public import New.UpperBound.Divisibility.RationalPrimeReadings
import Mathlib.Tactic

/-!
# The same unit norm with empty or balanced high-place fibers

At the third probe the signed exponent can vanish because both fibers are empty, or because
the same positive number of high places lies on each side. Both mechanisms can coexist with
the same three readings on equal-size assignments at the same field, ranks, and level.
-/

@[expose] public section

open NumberField Finset Real ThreePrimeEnvelope ColoredSparse Filter
namespace New.Data

variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- The sign test distinguishes membership on each side even when its aggregate vanishes. -/
theorem IsExceptional.negative_unit_flags (he : D.IsExceptional p) {σ : D.Φ} (hσ : σ ∈ D.bPlaces) :
    (inducedPlace σ = D.negativeUnitPrime p ↔ signAt (D.returnPairCount p) (D.negativeOffset σ) = -1) ∧
    (inducedPlace σ = star (D.negativeUnitPrime p) ↔ signAt (D.returnPairCount p) (D.negativeOffset σ) = 1) := by
  let a := D.placeOfInt (-1)
  let l := inducedPlace (p := p) a
  let t := D.negativeOffset σ
  have repr : σ = D.distinguishedLift t*a := D.negativePlace_eq_offset (D.placeClass_of_mem_bPlaces _ hσ)
  have tests := he.offset_return_tests t a
  rw [← repr] at tests
  have apart : star l ≠ l := he.star_ne (D.p_mem_inducedPlace a)
  change (inducedPlace σ = l ↔ signAt _ t = -1) ∧ (inducedPlace σ = star l ↔ signAt _ t = 1)
  by_cases same : 2*D.returnPairCount p ∣ t
  · have actual : inducedPlace σ = l := tests.1.2 same
    simp [signAt,same,actual,apart.symm]
  by_cases pair : D.returnPairCount p ∣ t
  · have other : inducedPlace σ = star l := (tests.2.2 pair).resolve_left (mt tests.1.1 same)
    simp [signAt,same,pair,other,apart]
  · have left : inducedPlace σ ≠ l := mt tests.1.1 same
    have right : inducedPlace σ ≠ star l := fun h ↦ pair (tests.2.1 (.inr h))
    simp [signAt,same,pair,left,right]

end New.Data

namespace New.Data.CollisionPrimeExample
local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 535919) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 665279) := ⟨by norm_num1⟩

/-- The two counts whose difference gives the 665279 reading. -/
noncomputable def thirdLedger (D : Data params) (ι : PadicPlace 665279) : ℕ × ℕ :=
  let l := D.negativeUnitPrime 665279
  (D.highCount 665279 l,D.highCount 665279 (star l))

private lemma exceptional_third (D : Data params) (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    D.IsExceptional 665279 := by
  let : PadicPlace 665279 := ι₂
  obtain ⟨_,full⟩ := (singleton_and_thirty_six D ι₁ ι₂).2.1
  exact full.toIsMarked.isExceptional

/-- The measured p-adic norm is one exactly when the two unsigned counts agree. -/
theorem third_norm_eq_one_iff (D : Data params) (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279)
    (ϑ : D.TameChar) (j : ℕ) :
    D.measuredNorm 665279 ι₂ ϑ j = 1 ↔ (thirdLedger D ι₂).1 = (thirdLedger D ι₂).2 := by
  let : PadicPlace 665279 := ι₂
  have above : (665279 : 𝓞 D.E) ∈ (D.negativeUnitPrime 665279).asIdeal :=
    D.p_mem_inducedPlace (D.placeOfInt (-1))
  exact norm_atUniformizer_eq_one_iff (exceptional_third D ι₁ ι₂).chiK_eq_neg_one above ϑ j

/-- Among the four corner types only the first two contribute high places at the third
measuring pair. Count them before the signed subtraction. -/
theorem thirdLedger_of_population (D : Data params) {w : Fin 4 → ℕ}
    (hp : HasCornerPopulation D.towerExp D.bPlaces w)
    (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    ∃ k > 0, #D.bPlaces = k*(∑ i,w i) ∧ thirdLedger D ι₂=(k*w 0,k*w 1) := by
  classical
  let : PadicPlace 665279 := ι₂
  obtain ⟨hd,k,hk,f,B,addr⟩ := hp
  have he := exceptional_third D ι₁ ι₂
  let l := D.negativeUnitPrime 665279
  have rules (c : Fin 4) : (corner c 2 = -1 ↔ c = 0) ∧ (corner c 2 = 1 ↔ c = 1) := by
    fin_cases c <;> norm_num [corner]
  have flags (a : Sample k w) :
      (inducedPlace (f a) = l ↔ a.2.1=0) ∧ (inducedPlace (f a) = star l ↔ a.2.1=1) := by
    have actual := he.negative_unit_flags (show f a ∈ D.bPlaces by rw [B]; exact mem_map.2 ⟨a,mem_univ _,rfl⟩)
    rw [(second_return_counts D).2.2] at actual
    have slot : (signAt 36 (D.negativeOffset (f a)) : ℝ) = corner a.2.1 2 :=
      congrFun (slot_row_eq_corner D f hd B addr a) 2
    have lower : (signAt 36 (D.negativeOffset (f a)) = -1) ↔ corner a.2.1 2 = -1 := by
      rw [← slot]; norm_cast
    have upper : (signAt 36 (D.negativeOffset (f a)) = 1) ↔ corner a.2.1 2 = 1 := by
      rw [← slot]; norm_cast
    exact ⟨actual.1.trans (lower.trans (rules _).1),actual.2.trans (upper.trans (rules _).2)⟩
  have count (u : FinPlace D.E) (c : Fin 4) (select : ∀ a : Sample k w, inducedPlace (f a)=u ↔ a.2.1=c) :
      D.highCount 665279 u=k*w c := by
    calc D.highCount 665279 u = ∑ σ ∈ D.bPlaces, if inducedPlace σ=u then 1 else 0 := by
           rw [← sum_filter]; simp [highCount]
      _ = ∑ a : Sample k w, if a.2.1=c then 1 else 0 := by
        rw [B,sum_map]
        exact sum_congr rfl fun a _ ↦ if_congr (select a) rfl rfl
      _ = _ := by simpa [nsmul_eq_mul] using sample_sum k w (fun i ↦ if i=c then (1:ℕ) else 0)
  refine ⟨k,hk,by rw [B,card_map,card_univ,sample_card],?_⟩
  exact Prod.ext (count l 0 fun a ↦ (flags a).1) (count (star l) 1 fun a ↦ (flags a).2)

/-- An all-first-corner population is concentrated at the true negative unit class. -/
lemma all_first_focused (D : Data params) (n : ℕ)
    (hp : HasCornerPopulation D.towerExp D.bPlaces ![n,0,0,0]) :
    params.NegOneFiber D.towerExp 72 D.bPlaces := by
  classical
  obtain ⟨hd,k,_,f,B,addr⟩ := hp
  refine ⟨hd,fun σ hσ ↦ ?_⟩
  rw [B] at hσ
  obtain ⟨a,_,rfl⟩ := mem_map.1 hσ
  have first : a.2.1 = 0 := by
    obtain ⟨_,i,v⟩ := a
    fin_cases i <;> first | rfl | exact Fin.elim0 v
  apply Units.ext
  simpa [first,cornerOffset] using addr a

theorem thirdLedger_empty_at_24 (D : Data params) (focus : params.NegOneFiber D.towerExp 72 D.bPlaces)
    (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    thirdLedger (D.translateOffset 24) ι₂ = (0,0) := by
  classical
  let : PadicPlace 665279 := ι₂
  let E := D.translateOffset 24
  have he := exceptional_third E ι₁ ι₂
  have none (σ : E.Φ) (hσ : σ ∈ E.bPlaces) :
      inducedPlace σ ≠ E.negativeUnitPrime 665279 ∧ inducedPlace σ ≠ star (E.negativeUnitPrime 665279) := by
    have flags := he.negative_unit_flags hσ
    have read : signAt (E.returnPairCount 665279) (E.negativeOffset σ) = 0 := by
      rw [(second_return_counts E).2.2]
      exact (signAt_congr (D.offset_after_translation focus 24 σ hσ) (by decide : 2*36 ∣ 72)).trans (by decide)
    rw [read] at flags
    exact ⟨fun u ↦ (by decide : (0:ℤ) ≠ -1) (flags.1.1 u),fun u ↦ (by decide : (0:ℤ) ≠ 1) (flags.2.1 u)⟩
  apply Prod.ext
  · exact card_eq_zero.2 (filter_eq_empty_iff.2 fun a h ↦ (none a h).1)
  · exact card_eq_zero.2 (filter_eq_empty_iff.2 fun a h ↦ (none a h).2)

/-- The same three local norm readings and the same scalar frame can conceal an empty
third pair or a positive, exactly balanced third pair. -/
theorem eventually_empty_or_balanced :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX=x ∧ ∃ c : HighPlaceChoice D,
      ∃ k > 0, #D.bPlaces = 2*k ∧
        ∀ (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279),
          readings (D.translateOffset 24) ι₀ ι₁ ι₂ = ![-1,-1,0] ∧
          readings c.toData ι₀ ι₁ ι₂ = ![-1,-1,0] ∧
          thirdLedger (D.translateOffset 24) ι₂ = (0,0) ∧ thirdLedger c.toData ι₂ = (k,k) ∧
          (∀ (ϑ : (D.translateOffset 24).TameChar) (j : ℕ),
            (D.translateOffset 24).measuredNorm 665279 ι₂ ϑ j = 1) ∧
          (∀ (ϑ : c.toData.TameChar) (j : ℕ), c.toData.measuredNorm 665279 ι₂ ϑ j = 1) := by
  classical
  let pure : Fin 4 → ℕ := ![2,0,0,0]
  let half : Fin 4 → ℕ := ![1,1,0,0]
  have pn : (∑ i,pure i)=2 := by simp [pure, Fin.sum_univ_succ]
  have hn : (∑ i,half i)=2 := by simp [half, Fin.sum_univ_succ]
  have positive : 0 < (∑ i,pure i) := by rw [pn]; decide
  filter_upwards [eventually_has_population_frame pure positive] with x hx
  obtain ⟨D,hx,source,menu⟩ := hx
  have focus := all_first_focused D 2 source
  obtain ⟨B,same,base,sparse,pop⟩ := menu half (hn.trans pn.symm)
  let c : HighPlaceChoice D := ⟨B,same,base,sparse⟩
  have cp : HasCornerPopulation c.toData.towerExp c.toData.bPlaces half := pop
  obtain ⟨hd,k,hk,embedding,hB,labels⟩ := cp
  have card : #D.bPlaces = 2*k := by
    rw [← c.same_card]
    change #c.toData.bPlaces = _
    rw [hB,card_map,card_univ,sample_card,hn,Nat.mul_comm]
  refine ⟨D,hx,c,k,hk,card,fun ι₀ ι₁ ι₂ ↦ ?_⟩
  have first := readings_translate_fiber D focus 24 ι₀ ι₁ ι₂
  have row24 : row 24 = ![-1,-1,0] := by funext i; fin_cases i <;> norm_num [row,signAt]
  have second := readings_of_population c.toData (show 0 < ∑ i,half i by rw [hn]; decide)
    (show HasCornerPopulation c.toData.towerExp c.toData.bPlaces half from ⟨hd,k,hk,embedding,hB,labels⟩) ι₀ ι₁ ι₂
  have center : populationPoint half = ![-1,-1,0] := by
    funext i; fin_cases i <;> norm_num [populationPoint,half,corner,Fin.sum_univ_succ]
  obtain ⟨k',_,card',highs⟩ := thirdLedger_of_population c.toData
    (show HasCornerPopulation c.toData.towerExp c.toData.bPlaces half from ⟨hd,k,hk,embedding,hB,labels⟩) ι₁ ι₂
  rw [hn, show #c.toData.bPlaces = #D.bPlaces from c.same_card, card] at card'
  have equal : k'=k := by omega
  rw [equal] at highs
  have empty := thirdLedger_empty_at_24 D focus ι₁ ι₂
  have balanced : thirdLedger c.toData ι₂ = (k,k) := by simpa [half] using highs
  refine ⟨first.trans row24,second.trans center,empty,balanced,?_,?_⟩
  · exact fun ϑ j ↦ (third_norm_eq_one_iff _ ι₁ ι₂ ϑ j).2 (by rw [empty])
  · exact fun ϑ j ↦ (third_norm_eq_one_iff _ ι₁ ι₂ ϑ j).2 (by rw [balanced])

end New.Data.CollisionPrimeExample
