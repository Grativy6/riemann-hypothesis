module

public import New.UpperBound.Divisibility.TranslatedSignatures
public import New.UpperBound.Divisibility.LargestPopulationFiber
import Mathlib.Tactic

/-!
# One field and level for all translated three-prime profiles

Each input occurrence has four labeled slots. All four lie in the same one of the six
original bins. Once spread across these slots, any two words with the same integer report
keep the same three signed readings at every common translation of the high places.
-/

@[expose] public section

open Finset Real Filter NumberField ThreePrimeEnvelope ColoredSparse

namespace New.SixSignatures

abbrev OrbitSlot := Fin 6 × Fin 4

def orbitWord (w : Fin 6 → ℕ) (v : OrbitSlot) : ℕ := w v.1

lemma orbitWord_sum (w : Fin 6 → ℕ) : ∑ v,orbitWord w v = 4 * ∑ c,w c := by
  simp [orbitWord,Fintype.sum_prod_type,mul_sum]

/-- Add the contribution of every slot before summing over the k complete copies. -/
lemma fold_orbit_slots {A : Type*} [AddCommMonoid A] (k : ℕ) (w : Fin 6 → ℕ) (f : OrbitSlot → A) :
    (∑ a : Sample k (orbitWord w), f a.2.1) = k • ∑ c, w c • ∑ j : Fin 4, f (c,j) := by
  rw [sample_sum,Fintype.sum_prod_type]
  simp only [orbitWord,Finset.smul_sum]

noncomputable def orbitPoint (w : Fin 6 → ℕ) (t : ℕ) : Point := fun i ↦
  (∑ c, (w c : ℤ)*translatedSum t c i : ℤ) / (((4*(∑ c,w c):ℕ):ℝ))

lemma orbitPoint_eq_of_report {w v : Fin 6 → ℕ} (eq : observed w = observed v) (t : ℕ) :
    orbitPoint w t = orbitPoint v t := by
  have same := congrFun eq 0
  rw [observed_total,observed_total] at same
  have size : (∑ c,w c)=(∑ c,v c) := by exact_mod_cast same
  funext i
  unfold orbitPoint
  rw [size,score_eq_all_shifts (a := fun c ↦ (w c:ℤ)) (b := fun c ↦ (v c:ℤ)) eq t i]

end New.SixSignatures

namespace New.Data.CollisionPrimeExample
open SixSignatures

local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 535919) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 665279) := ⟨by norm_num1⟩

/-- All twenty-four slots use the same three permissible odd lanes as the original construction. -/
def orbitAddress (v : OrbitSlot) : LaneAddress :=
  let lanes : Fin 6 → Fin 4 := ![0,1,2,2,3,3]
  ⟨microRow v.1 v.2,lanes v.1,(by decide : ∀ u : OrbitSlot, oddLane (lanes u.1) ≡ microRow u.1 u.2 [MOD 9]) v⟩

lemma bin_of_slot (v : OrbitSlot) : bin (orbitAddress v).offset = v.1 := (by decide : ∀ j, bin (orbitAddress j).offset=j.1) v

/-- Start every sum at the actual chosen tower places. Any finite additive statistic of
the residues can then be evaluated by grouping the four slots per type. -/
theorem orbit_sum_of_slots (D : Data params) {w : Fin 6 → ℕ} {k : ℕ}
    (f : Sample k (orbitWord w) ↪ D.Φ) (hd : 72*params.q₀ ∣ D.q₁) (B : D.bPlaces=univ.map f)
    (addr : ∀ a, (params.placeClass hd (f a) : ZMod (72*params.q₀)) =
        -((1+params.q₀*(orbitAddress a.2.1).offset : ℕ) : ZMod (72*params.q₀)))
    {A : Type*} [AddCommMonoid A] (F : ℕ → A)
    (modulo : ∀ a b, a ≡ b [MOD 72] → F a=F b) :
    (∑ z ∈ D.bPlaces, F (D.negativeOffset z)) = k • ∑ c,w c • ∑ j : Fin 4,F (microRow c j) := by
  rw [B,sum_map]
  calc (∑ a : Sample k (orbitWord w), F (D.negativeOffset (f a))) =
       ∑ a : Sample k (orbitWord w), F (microRow a.2.1.1 a.2.1.2) :=
      sum_congr rfl fun a _ ↦ modulo _ _ (slot_offset_modEq orbitAddress D f hd B addr a)
    _ = _ := fold_orbit_slots k w (fun v ↦ F (microRow v.1 v.2))

/-- Compute both the six-bin census and the whole orbit of the measured norms from one
population witness. The same number of copies gives all of these equalities. -/
theorem orbit_measurements (D : Data params) {w : Fin 6 → ℕ} (pos : 0 < ∑ c,w c)
    (wit : HasPopulation orbitAddress D.towerExp D.bPlaces (orbitWord w)) :
    ∃ k > 0, #D.bPlaces = (4*k)*(∑ c,w c) ∧ census D = (fun c ↦ (4*k)*w c) ∧
      ∀ t ι₀ ι₁ ι₂, readings (D.translateOffset t) ι₀ ι₁ ι₂ = orbitPoint w t := by
  classical
  obtain ⟨hd,k,hk,f,B,addr⟩ := wit
  have count : #D.bPlaces = k*(4*(∑ c,w c)) := by rw [B,card_map,card_univ,sample_card,orbitWord_sum]
  have total (t : ℕ) : #(D.translateOffset t).bPlaces = #D.bPlaces := D.card_translateHighPlaces _ _
  refine ⟨k,hk,by rw [count]; ring,?_,?_⟩
  · funext c
    let F := fun u : ℕ ↦ if bin u=c then 1 else 0
    have period (u v : ℕ) (h : u ≡ v [MOD 72]) : F u=F v := by
      unfold F bin; rw [show u%72=v%72 from h]
    have rule (a : Fin 6) (j : Fin 4) : F (microRow a j) = if a=c then 1 else 0 := by
      unfold F
      rw [show bin (microRow a j)=a from bin_of_slot (a,j)]
    change #{z ∈ D.bPlaces | bin (D.negativeOffset z)=c} = _
    rw [card_filter]
    change (∑ z ∈ D.bPlaces,F (D.negativeOffset z)) = _
    rw [orbit_sum_of_slots D f hd B addr F period]
    simp [rule,mul_ite]
    ring
  · intro t i₀ i₁ i₂
    funext i
    let g := D.distinguishedLift t
    let F := fun u : ℕ ↦ signAt (probePeriod i) (t+u+18480*t*u)
    have per : 2*probePeriod i ∣ 72 := (by decide : ∀ j,2*probePeriod j ∣ 72) i
    have congrF (u v : ℕ) (eq : u ≡ v [MOD 72]) : F u=F v :=
      signAt_congr ((eq.add_left t).add (eq.mul_left (18480*t))) per
    have summed := orbit_sum_of_slots D f hd B addr F congrF
    have actual : (∑ z ∈ (D.translateOffset t).bPlaces,
        signAt (probePeriod i) ((D.translateOffset t).negativeOffset z)) =
        (k:ℤ)*∑ c,(w c:ℤ)*translatedSum t c i := by
      change (∑ z ∈ D.bPlaces.image (fun a ↦ g*a), _) = _
      rw [sum_image (fun _ _ _ _ eq ↦ mul_left_cancel eq)]
      calc (∑ z ∈ D.bPlaces, signAt (probePeriod i) ((D.translateOffset t).negativeOffset (g*z))) =
          ∑ z ∈ D.bPlaces,F (D.negativeOffset z) :=
            sum_congr rfl fun z hz ↦ signAt_congr (D.shifted_offset_at_place hd t z hz) per
        _ = _ := by simpa only [nsmul_eq_mul,translatedSum,F] using summed
    have coordinate (u : ℕ) : row u i = (signAt (probePeriod i) u : ℝ) := by fin_cases i <;> rfl
    rw [readings_eq_centerMass]
    simp only [centerMass,sum_const,nsmul_eq_mul,mul_one,one_smul,Pi.smul_apply,Finset.sum_apply,
      smul_eq_mul,coordinate,← Int.cast_sum,actual,Int.cast_mul,Int.cast_natCast,total,count,orbitPoint,
      Nat.cast_mul,Nat.cast_ofNat]
    field_simp [(by exact_mod_cast hk.ne' : (k:ℝ)≠0),
      (by exact_mod_cast pos.ne' : ((∑ c,w c:ℕ):ℝ)≠0)]

/-- Every word of a fixed positive length has a separate assignment on the same field,
level and weight multiset. A single assignment per word gives its entire translated profile. -/
theorem eventually_orbit_menu (d : ℕ) (hd : 0<d) :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧ #D.bPlaces=(4*k)*d ∧
      ∀ w : Fin 6 → ℕ, (∑ c,w c)=d → ∃ choice : HighPlaceChoice D,
        HasPopulation orbitAddress choice.toData.towerExp choice.toData.bPlaces (orbitWord w) ∧
        census choice.toData=(fun i ↦ (4*k)*w i) ∧
          ∀ t ι₀ ι₁ ι₂, readings (choice.toData.translateOffset t) ι₀ ι₁ ι₂ = orbitPoint w t := by
  classical
  let start : Fin 6 → ℕ := ![d,0,0,0,0,0]
  have mass : ∑ i,start i = d := by simp [start,Fin.sum_univ_succ]
  have positive : 0 < ∑ i,orbitWord start i := by rw [orbitWord_sum,mass]; omega
  filter_upwards [eventually_population_frame_at orbitAddress (orbitWord start) positive] with x result
  obtain ⟨D,scale,hw,menu⟩ := result
  obtain ⟨k,hk,count,_,_⟩ := orbit_measurements D (mass ▸ hd) hw
  rw [mass] at count
  refine ⟨D,k,scale,hk,count,?_⟩
  intro w size
  obtain ⟨S,card,base,sparse,wp⟩ := menu (orbitWord w) (by rw [orbitWord_sum,orbitWord_sum,size,mass])
  let c : HighPlaceChoice D := ⟨S,card,base,sparse⟩
  obtain ⟨j,_,count',hist,sweep⟩ := orbit_measurements c.toData (size ▸ hd) wp
  change #S=(4*j)*(∑ i,w i) at count'
  rw [card,count,size] at count'
  have kj : k=j := by have y := Nat.eq_of_mul_eq_mul_right hd count'; omega
  exact ⟨c,wp,kj ▸ hist,sweep⟩

end New.Data.CollisionPrimeExample
