module

public import New.UpperBound.Divisibility.EmptyAndBalancedFibers
public import New.UpperBound.Divisibility.SixSignatureCounts
import Mathlib.Tactic

/-!
# The six signed signatures on actual high places

Classifying each offset before summing gives six finite populations. Every complete word of
these six types can be installed on one field and level, with the same number of copies for
all words of a chosen length.
-/

@[expose] public section

open Finset Real Filter NumberField ThreePrimeEnvelope ColoredSparse
namespace New.SixSignatures

/-- Rows are in the order A, B, E, C, F, D. Columns measure 479, 535919 and 665279. -/
def signature (c : Fin 6) : Fin 3 → ℤ :=
  ![![-1,-1,-1], ![-1,-1,1], ![-1,-1,0], ![1,-1,0], ![0,-1,0], ![0,1,0]] c

def probePeriod : Fin 3 → ℕ := ![6,1,36]

/-- Bin of a residue in one full turn of length 72. -/
def binAt (r : ℕ) : Fin 6 :=
  if 72 ∣ r then 0 else if 36 ∣ r then 1 else if 12 ∣ r then 2
  else if 6 ∣ r then 3 else if 2 ∣ r then 4 else 5

def bin (t : ℕ) : Fin 6 := binAt (t%72)

lemma sign_in_bin (t : ℕ) (i : Fin 3) : signAt (probePeriod i) t = signature (bin t) i := by
  have period : ∀ i : Fin 3, 2*probePeriod i ∣ 72 := by decide
  have table : ∀ r : Fin 72, ∀ j : Fin 3, signAt (probePeriod j) r = signature (binAt r) j := by decide
  exact (signAt_congr (Nat.mod_modEq t 72) (period i)).symm.trans
    (table ⟨t%72, Nat.mod_lt _ (by decide)⟩ i)

lemma row_in_bin (t : ℕ) : row t = fun i ↦ (signature (bin t) i : ℝ) := by
  funext i
  have val := congrArg (fun z : ℤ ↦ (z:ℝ)) (sign_in_bin t i)
  fin_cases i <;> exact val

lemma observed_total (n : Fin 6 → ℕ) : observed n 0 = (∑ i,n i : ℕ) := by
  simp [observed, report, Fin.sum_univ_succ, add_assoc]

lemma observed_coordinate (n : Fin 6 → ℕ) (i : Fin 3) :
    observed n i.succ = ∑ c, (n c : ℤ)*signature c i := by
  fin_cases i <;> simp [observed,report,signature,Fin.sum_univ_succ] <;> ring

/-- A report as seen by the three normalized measurements. -/
noncomputable def point (n : Fin 6 → ℕ) : Point :=
  fun i ↦ (observed n i.succ : ℝ) / (observed n 0 : ℝ)

theorem observed_eq_iff_count_and_point {n m : Fin 6 → ℕ}
    (hm : 0 < ∑ i,m i) :
    observed n = observed m ↔ (∑ i,n i) = (∑ i,m i) ∧ point n = point m := by
  constructor
  · intro h
    have mass := congrFun h 0
    rw [observed_total,observed_total] at mass
    exact ⟨by exact_mod_cast mass, by unfold point; rw [h]⟩
  · rintro ⟨mass,eq⟩
    have z : observed n 0 = observed m 0 := by rw [observed_total,observed_total,mass]
    have pos : (observed m 0 : ℝ) ≠ 0 := by rw [observed_total]; exact_mod_cast hm.ne'
    funext i
    refine Fin.cases z (fun j ↦ ?_) i
    have each := congrFun eq j
    change (observed n j.succ : ℝ) / (observed n 0 : ℝ) = (observed m j.succ : ℝ) / (observed m 0 : ℝ) at each
    rw [z] at each
    have clear := congrArg (fun z : ℝ ↦ z * (observed m 0 : ℝ)) each
    simp only [div_mul_cancel₀ _ pos] at clear
    exact_mod_cast clear

end New.SixSignatures

namespace New.Data.CollisionPrimeExample
open SixSignatures
local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 535919) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 665279) := ⟨by norm_num1⟩

/-- The two interior types need no extra odd lane. -/
def sixAddress (c : Fin 6) : LaneAddress :=
  let offset : Fin 6 → ℕ := ![0,36,24,6,10,1]
  let lane : Fin 6 → Fin 4 := ![0,1,2,2,3,3]
  ⟨offset c, lane c, (by decide : ∀ i, oddLane (lane i) ≡ offset i [MOD 9]) c⟩

/-- Count the places themselves before taking any local signed reading. -/
noncomputable def census (D : Data params) (c : Fin 6) : ℕ :=
  #{σ ∈ D.bPlaces | bin (D.negativeOffset σ) = c}

lemma census_total (D : Data params) : ∑ c,census D c = #D.bPlaces :=
  (card_eq_sum_card_fiberwise (fun _ _ ↦ mem_univ _)).symm

lemma sum_census (D : Data params) {A : Type*} [AddCommMonoid A] (f : Fin 6 → A) :
    (∑ σ ∈ D.bPlaces, f (bin (D.negativeOffset σ))) = ∑ c, census D c • f c := by
  simpa only [sum_const, census] using
    (sum_fiberwise_of_maps_to' (g := fun σ ↦ bin (D.negativeOffset σ))
      (s := D.bPlaces) (t := univ) (fun _ _ ↦ mem_univ _) f).symm

/-- The four integers in the report come from the actual size and the three
measured character exponents, for any embeddings at the observing primes. -/
theorem readings_eq_census (D : Data params) (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919)
    (ι₂ : PadicPlace 665279) : readings D ι₀ ι₁ ι₂ = point (census D) := by
  classical
  rw [readings_eq_centerMass]
  funext i
  have r (σ : D.Φ) := congrFun (row_in_bin (D.negativeOffset σ)) i
  have sum : (∑ σ ∈ D.bPlaces, row (D.negativeOffset σ) i) =
      (observed (census D) i.succ : ℝ) := by
    rw [sum_congr rfl (fun σ _ ↦ r σ), sum_census D (fun c ↦ (signature c i : ℝ)), observed_coordinate, Int.cast_sum]
    simp [nsmul_eq_mul]
  simp only [centerMass, sum_const, nsmul_eq_mul, mul_one, one_smul, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, sum, point, observed_total, census_total, Int.cast_natCast]
  ring

/-- The census of a population witness has exactly k copies of its word, including its
two non-corner bins. This also recovers k from the number of places. -/
theorem census_of_population (D : Data params) {w : Fin 6 → ℕ}
    (hp : HasPopulation sixAddress D.towerExp D.bPlaces w) :
    ∃ k > 0, #D.bPlaces = k*(∑ i,w i) ∧ census D = fun i ↦ k*w i := by
  classical
  obtain ⟨hd,k,hk,f,B,addr⟩ := hp
  have ident : ∀ c : Fin 6, bin (sixAddress c).offset = c := by decide
  have cls (a : Sample k w) : bin (D.negativeOffset (f a)) = a.2.1 := by
    have h := slot_offset_modEq sixAddress D f hd B addr a
    exact (congrArg binAt h).trans (ident _)
  refine ⟨k,hk,by rw [B,card_map,card_univ,sample_card],?_⟩
  funext i
  change #{σ ∈ D.bPlaces | bin (D.negativeOffset σ) = i} = k*w i
  rw [card_filter, B, sum_map]
  simp only [cls]
  simpa [nsmul_eq_mul] using sample_sum k w (fun j ↦ if j=i then (1:ℕ) else 0)

/-- At any fixed denominator all six-bin words are available on the same fixed field and
level, with the same positive number k of copies. -/
theorem eventually_shared_census (d : ℕ) (hd : 0 < d) :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧ #D.bPlaces=k*d ∧
      ∀ w : Fin 6 → ℕ, (∑ i,w i)=d → ∃ c : HighPlaceChoice D, census c.toData = fun i ↦ k*w i := by
  let initial : Fin 6 → ℕ := ![d,0,0,0,0,0]
  have total : ∑ i,initial i=d := by simp [initial,Fin.sum_univ_succ]
  filter_upwards [eventually_population_frame_at sixAddress initial (total ▸ hd)] with x hx
  obtain ⟨D,scale,wit,menu⟩ := hx
  obtain ⟨k,hk,count,_⟩ := census_of_population D wit
  rw [total] at count
  refine ⟨D,k,scale,hk,count,?_⟩
  intro w hw
  obtain ⟨B,card,base,sparse,pop⟩ := menu w (hw.trans total.symm)
  let c : HighPlaceChoice D := ⟨B,card,base,sparse⟩
  obtain ⟨n,_,count',exactly⟩ := census_of_population c.toData pop
  change #B = n * (∑ i,w i) at count'
  rw [card,count,hw] at count'
  have nk : k=n := Nat.eq_of_mul_eq_mul_right hd count'
  exact ⟨c,nk ▸ exactly⟩

end New.Data.CollisionPrimeExample
