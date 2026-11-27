module

public import New.UpperBound.Divisibility.ActualScanKernel
public import New.UpperBound.Divisibility.NinePhaseResolver
import Mathlib.Tactic

/-!
# Distinct high-place populations with unit norm throughout every 72-compatible scan

One whole column places the same number of high places at all eight offsets above its
residue modulo nine. Translating the origin column gives all nine columns on one field
and level. Each has zero signed count at every compatible exceptional prime.
-/

@[expose] public section
open Finset Real Filter NumberField ThreePrimeEnvelope ColoredSparse
namespace New.Data.CollisionPrimeExample
open SixSignatures OrbitProbes

/-- Equality of the two actual local magnitudes at each finite place above p, for one
chosen pair of twists and lift indices. -/
def sameNormsAbove {D : Data params} (c e : HighPlaceChoice D) {p : ℕ} [Fact p.Prime]
    (ι : PadicPlace p) (θ : c.toData.TameChar) (η : e.toData.TameChar) (j j' : ℕ) : Prop :=
  ∀ l : FinPlace D.E, (p : 𝓞 D.E) ∈ l.asIdeal →
    ‖ιₚ ((c.toData.chainChar θ j).baseChange.atUniformizer l)‖ =
      ‖ιₚ ((e.toData.chainChar η j').baseChange.atUniformizer l)‖

/-- One lift and twist at each of the three dyadic stages already detects every
difference detectable by any compatible exceptional prime. -/
theorem three_norms_iff_flat {D : Data params} (c e : HighPlaceChoice D)
    (ι₉ : PadicPlace (rationalPrime 5)) (ι₁₈ : PadicPlace (rationalPrime 7))
    (ι₃₆ : PadicPlace (rationalPrime 8)) (θ : c.toData.TameChar) (η : e.toData.TameChar) (j j' : ℕ) :
    (sameNormsAbove c e ι₉ θ η j j' ∧ sameNormsAbove c e ι₁₈ θ η j j' ∧
      sameNormsAbove c e ι₃₆ θ η j j') ↔
    ∀ b k,residueBoard c.toData b k-residueBoard e.toData b k=
      residueBoard c.toData b 0-residueBoard e.toData b 0 := by
  constructor
  · rintro ⟨a,b,m⟩
    have read (i : Fin 9) (ι : PadicPlace (rationalPrime i)) (eq : sameNormsAbove c e ι θ η j j') :=
      boards_agree_at_probe c e i ι (fun x ↦
        (local_norm_eq_iff_signed_eq c e ι (period_and_exceptional D i).1
          (D.p_mem_inducedPlace (D.distinguishedLift x*D.placeOfInt (-1))) θ η j j').1
        (eq _ (D.p_mem_inducedPlace _)))
    exact flat_difference_of_three _ _ (read 8 ι₃₆ m) (read 7 ι₁₈ b) (read 5 ι₉ a)
  · intro flat
    have all := (allCompatibleProfiles_iff c e ι₉ ι₁₈ ι₃₆).2 flat
    have read (i : Fin 9) (ι : PadicPlace (rationalPrime i)) : sameNormsAbove c e ι θ η j j' := by
      intro l hl
      exact (all _ ι (period_and_exceptional D i).1
        (by rw [(period_and_exceptional D i).2.2.2]; exact Nat.mul_dvd_mul_left 2 (arithmetic i).2.1) l).2 hl θ η j j'
    exact ⟨read 5 ι₉,read 7 ι₁₈,read 8 ι₃₆⟩

/-- All eight addresses above zero modulo nine have the same admissible odd lane. -/
def originColumn (j : Fin 8) : LaneAddress :=
  ⟨9*j.val,0,by change 0 ≡ 9*j.val [MOD 9];simp [Nat.ModEq]⟩

lemma shifted_origin_address (b : Fin 9) (j : Fin 8) :
    b.val+9*j.val+18480*b.val*(9*j.val) ≡ address72 b j [MOD 72] := by
  rw [show b.val+9*j.val+18480*b.val*(9*j.val) = address72 b j+(2310*b.val*j.val)*72 by
    unfold address72;ring]
  simp [Nat.ModEq]

/-- Translating the uniform origin column through the first nine lifts gives all nine
columns on the same field and level, preserving every row multiplicity. -/
theorem board_after_column_translation (D : Data params)
    (wit : HasPopulation originColumn D.towerExp D.bPlaces (fun _ : Fin 8 ↦ 1)) :
    ∃ k > 0, #D.bPlaces=8*k ∧ ∀ (b v : Fin 9) (j : Fin 8),
      residueBoard (D.translateOffset b.val) v j = if v=b then (k:ℤ) else 0 := by
  classical
  let word : Fin 8 → ℕ := fun _ ↦ 1
  obtain ⟨hd,k,hk,f,B,addr⟩ := wit
  have mass : ∑ j,word j=8 := by decide
  refine ⟨k,hk,?_,?_⟩
  · rw [B,card_map,card_univ,sample_card]
    change k*(∑ j,word j)=8*k
    rw [mass,mul_comm]
  intro b v j
  let E := D.translateOffset b.val
  let g := D.distinguishedLift b.val
  have slot (a : Sample k word) : boardIndex (E.negativeOffset (g*f a)) = (b,a.2.1) := by
    have here : f a∈D.bPlaces := by rw [B];exact mem_map.2 ⟨a,mem_univ _,rfl⟩
    have old : D.negativeOffset (f a) ≡ 9*a.2.1.val [MOD 72] := slot_offset_modEq originColumn D f hd B addr a
    have moved := D.shifted_offset_at_place hd b.val (f a) here
    apply (boardIndex_congr (moved.trans (((old.add_left b.val).add
      (old.mul_left (18480*b.val))).trans (shifted_origin_address b a.2.1)))).trans
    exact boardIndex_address b _
  have nat : #{z ∈ E.bPlaces | boardIndex (E.negativeOffset z)=(v,j)} =
      if v=b then k else 0 := by
    rw [card_filter]
    change (∑ z ∈ D.bPlaces.image (fun a ↦ g*a), _) = _
    rw [sum_image (fun _ _ _ _ eq ↦ mul_left_cancel eq),B,sum_map]
    change (∑ a : Sample k word, if boardIndex (E.negativeOffset (g*f a))=(v,j) then 1 else 0) = _
    simp only [slot]
    rw [sample_sum k word (fun i ↦ if (b,i)=(v,j) then 1 else 0)]
    by_cases eq : v=b
    · subst v;simp [word]
    · simp [word,eq,Ne.symm eq]
  change ((#{z ∈ E.bPlaces | boardIndex (E.negativeOffset z)=(v,j)} : ℕ) : ℤ) = _
  rw [nat]
  split_ifs <;> simp

/-- A column-constant actual histogram gives zero signed count at every finite place,
and unit norm at every place above every compatible exceptional prime. -/
theorem unit_norms_of_flat_board (D : Data params) (flat : ∀ b j,residueBoard D b j=residueBoard D b 0)
    {p : ℕ} [Fact p.Prime] (ι : PadicPlace p) (he : D.IsExceptional p)
    (fits : 2*D.returnPairCount p ∣ 72) (l : FinPlace D.E) :
    D.signedCount p ι l=0 ∧ ((p : 𝓞 D.E) ∈ l.asIdeal → ∀ (θ : D.TameChar) (j : ℕ),
      ‖ιₚ ((D.chainChar θ j).baseChange.atUniformizer l)‖=1) := by
  have zero : D.signedCount p ι l=0 := by
    by_cases seen : ∃ a,D.anchorPrime p ι a=l
    · obtain ⟨a,rfl⟩ := seen
      exact (residueBoard_at_finite_prime D ι he fits a).trans ((all_scans_zero_iff _).2 flat _ fits a)
    · exact he.signedCount_off_orbit l (fun a eq ↦ seen ⟨a,eq⟩)
  refine ⟨zero,?_⟩
  intro above θ j
  have slope : D.highSlope p l=0 := by
    change D.signedCount p ι l*((D.natB:ℤ)-D.offWeight)=0
    rw [zero,zero_mul]
  rw [norm_atUniformizer_eq_highSlope he.chiK_eq_neg_one above θ j,slope,zpow_zero]

/-- Every pure residue class modulo nine is attainable on one frame. At all compatible
exceptional primes every finite place over p has local character norm one. The nine boards
are distinct, since the common per-slot count is positive. -/
theorem eventually_nine_invisible_columns :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧ #D.bPlaces=8*k ∧
      ∀ b : Fin 9, let E := D.translateOffset b.val
        (∀ v j,residueBoard E v j=if v=b then (k:ℤ) else 0) ∧
        ∀ p : ℕ, ∀ [_hp : Fact p.Prime], ∀ ι : PadicPlace p,
          D.IsExceptional p → 2*D.returnPairCount p ∣ 72 → ∀ l : FinPlace D.E,
          E.signedCount p ι l=0 ∧ ((p : 𝓞 D.E) ∈ l.asIdeal →
            ∀ (θ : E.TameChar) (j : ℕ), ‖ιₚ ((E.chainChar θ j).baseChange.atUniformizer l)‖=1) := by
  let word : Fin 8 → ℕ := fun _ ↦ 1
  have pos : 0 < ∑ j,word j := by decide
  filter_upwards [eventually_population_frame_at originColumn word pos] with x hx
  obtain ⟨D,scale,pop,_⟩ := hx
  obtain ⟨k,hk,card,board⟩ := board_after_column_translation D pop
  refine ⟨D,k,scale,hk,card,?_⟩
  intro b E
  exact ⟨board b,fun p _ ι he fits l ↦ unit_norms_of_flat_board E
    (fun v j ↦ (board b v j).trans (board b v 0).symm) ι he fits l⟩

end New.Data.CollisionPrimeExample
