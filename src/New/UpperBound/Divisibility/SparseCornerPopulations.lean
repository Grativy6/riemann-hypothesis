module

public import New.UpperBound.Divisibility.ColoredTowerMap
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# One sparse population of labeled tower places

Each selected observation is an actual tower place. The same assignment passes the prime-two
and odd-prime tests. Complete copies of any prescribed finite population can then be selected
while retaining the sixth-power density.
-/

@[expose] public section

open Finset
namespace ColoredSparse

variable {ι : Type*}

abbrev Sample (k : ℕ) (pop : ι → ℕ) := Fin k × (Σ c : ι, Fin (pop c))

variable [Fintype ι]

lemma sample_card (k : ℕ) (pop : ι → ℕ) :
    Fintype.card (Sample k pop) = k * ∑ i, pop i := by
  simp [Sample,Fintype.card_sigma]

lemma sample_sum {A : Type*} [AddCommMonoid A] (k : ℕ) (pop : ι → ℕ) (F : ι → A) :
    (∑ i : Sample k pop, F i.2.1) = k • ∑ c, pop c • F c := by
  simp [Sample,Fintype.sum_prod_type,Fintype.sum_sigma]

/-- Select equally many copies of each full population word, losing a factor of at most two.
The cardinal bound after rounding retains the required sixth-power density. -/
theorem choose_population {S : Finset ℕ} (pop : ι → ℕ) (hd : 0 < ∑ i, pop i)
    (fits : (∑ i, pop i) ≤ #S) {T W : ℝ} (hW : 2 ≤ W) (dense : T ≤ #S*W^5) :
    ∃ k > 0, ∃ emb : Sample k pop ↪ ℕ, (∀ a, emb a ∈ S) ∧
       T ≤ (Fintype.card (Sample k pop) : ℝ)*W^6 ∧ k = #S/(∑ i,pop i) := by
  classical
  let d := ∑ i, pop i
  let k := #S/d
  have kpos : 0 < k := Nat.div_pos fits hd
  have leS : k*d ≤ #S := Nat.div_mul_le_self _ _
  have dsmall : d ≤ k*d := Nat.le_mul_of_pos_left _ kpos
  have double : #S ≤ 2*(k*d) := by
    have total := Nat.mod_add_div #S d
    have left : #S%d ≤ k*d := (Nat.mod_lt #S (show 0 < d from hd)).le.trans dsmall
    change #S%d + d*k = #S at total
    rw [Nat.mul_comm d k] at total
    calc #S = #S%d+k*d := total.symm
      _ ≤ k*d+k*d := Nat.add_le_add_right left _
      _ = _ := (two_mul _).symm
  have slots_fit : Fintype.card (Sample k pop) ≤ #S := (sample_card _ _).trans_le leS
  obtain ⟨emb, inside⟩ := Function.Embedding.exists_of_card_le_finset slots_fit
  refine ⟨k,kpos,emb,fun a ↦ inside (Set.mem_range_self _),dense.trans ?_,rfl⟩
  rw [sample_card]
  calc (#S:ℝ)*W^5 ≤ (2*(k*d:ℕ):ℕ)*W^5 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); exact_mod_cast double
    _ = ((k*d:ℕ):ℝ)*(2*W^5) := by push_cast; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc 2*W^5 ≤ W*W^5 := mul_le_mul_of_nonneg_right hW (by positivity)
        _ = W^6 := by ring

end ColoredSparse

namespace New.Data.CollisionPrimeExample
open Finset Real NumberField ThreePrimeEnvelope ColoredSparse

/-- Assign arbitrary compatible addresses to the macro exponents. The single resulting set of
tower places passes both the prime-two and odd-prime tests. -/
theorem sparse_address_family {s L q o : ℕ} (hs : 3 ≤ s) (hq : 8 ∣ q) (space : 14*l₀ s < q)
    (split : 2^s = q*o) (hL : 2*l₀ s*(L+1) < 2^s) (S : Finset ℕ)
    (lt : ∀ e ∈ S, e < o)
    (free : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ i j : ℕ, 0 < i → 0 < j → i+j ≤ 2*l₀ s →
       (i+j)*b ≡ i*a+j*c [MOD o] → a=b ∧ b=c) (tag : ℕ → LaneAddress) :
    let place := fun e ↦ lanePlace hs hq e (tag e)
    Set.InjOn place S ∧ params.IsSparse s L (S.image place) := by
  classical
  intro place
  let g := params.placeOfInt s (3*l₀ s*params.q₀+1 : ℕ)
  let start := params.placeOfInt s (-1)
  let digit := fun e ↦ ((tag e).lowDigit s).val
  let code := fun e ↦ q*e+digit e
  obtain ⟨v,hv,ho⟩ := params.exists_orderOf_placeClass_eq s
  let ψ := params.placeClass hv
  have ord : orderOf (ψ g) = q*o := ho.trans split
  have shape (e : ℕ) : ψ (place e) = ψ start * (ψ g)^(code e) := lanePlace_two hs hq hv e (tag e)
  have hl : 0 < l₀ s := by unfold l₀; positivity
  have qpos : 0 < q := by omega
  have smallDigit (e : ℕ) : digit e ≤ 7 := by have ht := ((tag e).lowDigit s).isLt; exact Nat.le_of_lt_succ ht
  have digitq (e : ℕ) : digit e < q := by have := smallDigit e; omega
  have bounded (e : ℕ) (he : e ∈ S) : code e < orderOf (ψ g) := by
    rw [ord]
    have hm := Nat.mul_le_mul_left q (Nat.succ_le_of_lt (lt e he))
    rw [Nat.mul_succ] at hm
    have hd := digitq e
    change q*e+digit e < q*o
    omega
  have recover (e : ℕ) : code e / q = e := by
    change (q*e+digit e)/q=e
    rw [Nat.add_comm,Nat.add_mul_div_left _ _ qpos,Nat.div_eq_of_lt (digitq e),zero_add]
  have inject : Set.InjOn place S := by
    intro x hx y hy eq
    have h := congrArg ψ eq
    rw [shape,shape] at h
    have c := pow_injOn_Iio_orderOf (x := ψ g) (bounded _ hx) (bounded _ hy) (mul_left_cancel h)
    simpa only [recover] using congrArg (· / q) c
  have base (σ) (hσ : σ ∈ S.image place) :
      params.placeClass (params.q₀.dvd_mul_right (towerDeg s)) σ = -1 := by
    obtain ⟨e,_,rfl⟩ := mem_image.1 hσ
    exact lanePlace_base hs hq e (tag e)
  refine ⟨inject, ?_⟩
  intro ℓ hℓ hb i j hi hij hj
  obtain rfl | odd := hℓ.eq_two_or_odd'
  · let color := fun σ ↦ if h : ∃ e ∈ S, place e = σ then (tag h.choose).lane else 0
    have lane (σ) (hσ : σ ∈ S.image place) : params.placeClass (oddTower_dvd s) σ =
        params.placeClass (oddTower_dvd s) (oddLanePlace s (oddLane (color σ))) := by
      have found : ∃ e ∈ S, place e = σ := mem_image.1 hσ
      have fixed : color σ = (tag found.choose).lane := dite_eq_left found
      rw [fixed]
      exact (congrArg (params.placeClass (oddTower_dvd s)) found.choose_spec.2.symm).trans
        (lanePlace_odd hs hq found.choose (tag found.choose))
    exact prime_two_clear (S.image place) color base (oddTower_dvd s) lane hi hij hj
  · apply params.sparse_odd_from_projection g start hv place code S (fun e _ ↦ shape e) _ hL hℓ odd hb hi hij hj
    intro x hx y hy z hz a b ha hb hab h
    rw [ord] at h
    have fits : (a+b)*7 < q := (Nat.mul_le_mul_right 7 hab).trans_lt (by simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using space)
    exact free x hx y hy z hz a b ha hb hab
      (remove_tags qpos (smallDigit x) (smallDigit y) (smallDigit z) fits h)

variable {ι : Type*} [Fintype ι]

/-- A population witness uses an actual injection of complete, indexed copies of a
prescribed population into the set of tower places. -/
def HasPopulation (address : ι → LaneAddress) (s : ℕ) (B : Finset (params.Φ s)) (w : ι → ℕ) : Prop :=
  ∃ hd : 72*params.q₀ ∣ params.q₁ s, ∃ k > 0, ∃ f : Sample k w ↪ params.Φ s,
    B = univ.map f ∧ ∀ a, (params.placeClass hd (f a) : ZMod (72*params.q₀)) =
        -((1+params.q₀*(address a.2.1).offset : ℕ) : ZMod (72*params.q₀))

/-- For this denominator every population can use another eligible high set of the
same cardinality at the same ranks and tower layer. -/
def HasPopulationMenu (address : ι → LaneAddress) (m r s : ℕ) (B : Finset (params.Φ s)) (d : ℕ) : Prop :=
  ∀ w : ι → ℕ, (∑ i,w i)=d → ∃ U : Finset (params.Φ s), #U = #B ∧
    (∀ σ ∈ U, params.placeClass (params.q₀.dvd_mul_right (towerDeg s)) σ = -1) ∧
    params.IsSparse s ((r+1-m)*(5*r)) U ∧ HasPopulation address s U w

abbrev HasCornerPopulation := HasPopulation cornerAddress
abbrev HasCornerMenu := HasPopulationMenu cornerAddress

/-- Spend the fifth-power density by rounding the number of complete population words. -/
theorem select_sparse_population [Nonempty ι] (address : ι → LaneAddress) {s L q o : ℕ} (hs : 3 ≤ s) (hq : 8 ∣ q) (space : 14*l₀ s < q)
    (split : 2^s=q*o) (hL : 2*l₀ s*(L+1) < 2^s) (S : Finset ℕ)
    (lt : ∀ e ∈ S, e < o)
    (free : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ i j : ℕ, 0 < i → 0 < j → i+j ≤ 2*l₀ s →
       (i+j)*b ≡ i*a+j*c [MOD o] → a=b ∧ b=c)
    (w : ι → ℕ) (pos : 0 < ∑ i, w i) (fits : (∑ i, w i) ≤ #S)
    {W : ℝ} (hw : 2 ≤ W) (dense : (towerDeg s : ℝ) ≤ #S*W^5) :
    ∃ B : Finset (params.Φ s), (∀ σ ∈ B, params.placeClass (params.q₀.dvd_mul_right (towerDeg s)) σ = -1) ∧
      (towerDeg s : ℝ) ≤ #B * W^6 ∧ params.IsSparse s L B ∧ HasPopulation address s B w ∧
        #B = (#S/(∑ i,w i))*(∑ i,w i) := by
  classical
  obtain ⟨k,hk,emb,mem,cost,number⟩ := choose_population w pos fits hw dense
  let tag := fun e ↦ if h : ∃ a, emb a=e then h.choose.2.1 else Classical.arbitrary ι
  have label (a : Sample k w) : tag (emb a) = a.2.1 := by
    have yes : ∃ i, emb i=emb a := ⟨a,rfl⟩
    exact (dite_eq_left yes).trans (congrArg (fun i : Sample k w ↦ i.2.1) (emb.injective yes.choose_spec))
  let place := fun e ↦ lanePlace hs hq e (address (tag e))
  obtain ⟨inj, sparse⟩ := sparse_address_family hs hq space split hL S lt free (fun e ↦ address (tag e))
  let f : Sample k w ↪ params.Φ s := ⟨fun a ↦ place (emb a), fun a b eq ↦ emb.injective (inj (mem a) (mem b) eq)⟩
  let B := univ.map f
  have sub : B ⊆ S.image place := by
    intro σ hσ
    obtain ⟨a,_,rfl⟩ := mem_map.1 hσ
    exact mem_image.2 ⟨emb a,mem a,rfl⟩
  refine ⟨B, ?_, ?_, sparse.mono sub, ⟨joint_dvd_tower hs,k,hk,f,rfl,?_⟩, ?_⟩
  · intro σ hσ
    obtain ⟨e,_,rfl⟩ := mem_image.1 (sub hσ)
    exact lanePlace_base hs hq e (address (tag e))
  · simpa [B] using cost
  · intro a
    change (params.placeClass (joint_dvd_tower hs) (lanePlace hs hq (emb a) (address (tag (emb a)))) : ZMod (72*params.q₀)) = _
    rw [label]
    exact lanePlace_joint hs hq _ _
  · simp [B, number]

end New.Data.CollisionPrimeExample
