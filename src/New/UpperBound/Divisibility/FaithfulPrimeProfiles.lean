module

public import New.UpperBound.Divisibility.AffineScans
public import New.UpperBound.Divisibility.SmallerPrimeFloor
import Mathlib.Tactic

/-!
# Full signed profiles distinguish more than support alone

The odd column on the original grid has a nonzero signed profile supported over one
residue modulo three at period 96 and modulo nine at period 144. All nonidentity
remaining shifts generate the conjugate half-turn. This identifies the absolute offset
modulo each measuring period, and hence modulo 288 when both are measured.
-/

@[expose] public section
open Finset Filter NumberField Real ThreePrimeEnvelope ColoredSparse
namespace New.Data.CollisionPrimeExample
open SixSignatures
variable {D : Data params} {p : ℕ} [Fact p.Prime]

/-- Comparison at every oriented reference at a single fixed prime. The twists and
lift indices may be chosen separately on the two shifted assignments. -/
def sameMovedNorms (D : Data params) (p : ℕ) [Fact p.Prime] (ι : PadicPlace p) (s t : ℕ)
    (θ : (D.translateOffset s).TameChar) (η : (D.translateOffset t).TameChar) (j j' : ℕ) : Prop :=
  ∀ a,(D.translateOffset s).referenceNorm p ι θ j a=(D.translateOffset t).referenceNorm p ι η j' a

lemma moved_norm_eq_iff_signed (D : Data params) (ι : PadicPlace p) (he : D.IsExceptional p)
    (s t a : ℕ) (θ : (D.translateOffset s).TameChar) (η : (D.translateOffset t).TameChar) (j j' : ℕ) :
    (D.translateOffset s).referenceNorm p ι θ j a=(D.translateOffset t).referenceNorm p ι η j' a ↔
      (D.translateOffset s).signedCount p ι ((D.translateOffset s).anchorPrime p ι a)=
      (D.translateOffset t).signedCount p ι ((D.translateOffset t).anchorPrime p ι a) := by
  rw [IsExceptional.referenceNorm_power (D := D.translateOffset s) ι he,
      IsExceptional.referenceNorm_power (D := D.translateOffset t) ι he]
  have gt : (1:ℝ)<p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  rw [(zpow_right_strictMono₀ gt).injective.eq_iff]
  let gap := (D.natB:ℤ)-D.offWeight
  have nz : gap≠0 := sub_ne_zero.2 (by exact_mod_cast (offWeight_lt_high D).ne')
  change _*gap=_*gap ↔ _
  exact ⟨fun h ↦ mul_right_cancel₀ nz h,fun h ↦ congrArg (·*gap) h⟩

lemma reference_zero_iff_unit (D : Data params) (ι : PadicPlace p) (he : D.IsExceptional p)
    (θ : D.TameChar) (j a : ℕ) :
    D.signedCount p ι (D.anchorPrime p ι a)=0 ↔ D.referenceNorm p ι θ j a=1 := by
  rw [he.referenceNorm_eq_one]
  unfold signedCount
  rw [sub_eq_zero]
  exact ⟨fun h ↦ by exact_mod_cast h.symm,fun h ↦ by exact_mod_cast h.symm⟩

theorem faithful_measurement (D : Data params) (ι : PadicPlace p) (he : D.IsExceptional p)
    {G d : ℕ} [NeZero (2*G)] [NeZero d] (period : D.returnPairCount p=G) (div : d∣2*G)
    (square : (18480:ZMod (2*G))^2=0)
    (hit : ∀ r : ZMod (2*G),r≠0 → r.val%d=0 → ∃ k,offsetPower r k=(G:ZMod (2*G)))
    (some_reading : ∃ a,D.signedCount p ι (D.anchorPrime p ι a)≠0)
    (support : ∀ a,D.signedCount p ι (D.anchorPrime p ι a)≠0 → a%d=0)
    (s t : ℕ) (θ : (D.translateOffset s).TameChar) (η : (D.translateOffset t).TameChar) (j j' : ℕ) :
    sameMovedNorms D p ι s t θ η j j' ↔ s ≡ t [MOD 2*G] := by
  have width : 2*D.returnPairCount p=2*G := by rw [period]
  constructor
  · intro same
    have sameRing (v : ZMod (2*G)) :
        residueProfile (D.translateOffset s) p ι v=residueProfile (D.translateOffset t) p ι v :=
      (moved_norm_eq_iff_signed D ι he s t v.val θ η j j').1 (same v.val)
    obtain ⟨a,ha⟩ := some_reading
    have nonzero : residueProfile D p ι (a:ZMod (2*G))≠0 := (residueProfile_nat D ι he width a).trans_ne ha
    have eq := faithful_signed_shift div square hit (residueProfile D p ι) ⟨_,nonzero⟩
      (fun v ↦ support v.val) (residueProfile_opposite D ι he period)
      (moved_profile_agreement D ι he width sameRing)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 eq
  · intro eq a
    have r : (s:ZMod (2*G))=t := (ZMod.natCast_eq_natCast_iff _ _ _).2 eq
    obtain ⟨v,hv⟩ := glide_surjective square (s:ZMod (2*G)) (a:ZMod (2*G))
    have hv' : glide (t:ZMod (2*G)) v=a := r ▸ hv
    have es := residueProfile_moved D ι he width s v
    have et := residueProfile_moved D ι he width t v
    rw [hv,residueProfile_nat (D.translateOffset s) ι he width] at es
    rw [hv',residueProfile_nat (D.translateOffset t) ι he width] at et
    exact (moved_norm_eq_iff_signed D ι he s t a θ η j j').2 (es.trans et.symm)

set_option maxRecDepth 8192 in
private lemma hit_96 (r : ZMod 96) (nz : r≠0) (col : r.val%3=0) :
    ∃ k,offsetPower r k=(48:ZMod 96) := by
  have cert : ∀ x : ZMod 96,x≠0 → x.val%3=0 → offsetPower x (48/(Nat.gcd x.val 48))=48 := by decide
  exact ⟨_,cert r nz col⟩

set_option maxRecDepth 8192 in
private lemma hit_144 (r : ZMod 144) (nz : r≠0) (col : r.val%9=0) :
    ∃ k,offsetPower r k=(72:ZMod 144) := by
  have cert : ∀ x : ZMod 144,x≠0 → x.val%9=0 → offsetPower x (72/(Nat.gcd x.val 72))=72 := by decide
  exact ⟨_,cert r nz col⟩

theorem recognize_96 (D : Data params) (ι : PadicPlace (smallerPrime 1)) {k : ℕ} (odd : Odd k)
    (board : ∀ b j,residueBoard D b j=if b=0 then (k:ℤ) else 0)
    (s t : ℕ) (θ : (D.translateOffset s).TameChar) (η : (D.translateOffset t).TameChar) (j j' : ℕ) :
    sameMovedNorms D _ ι s t θ η j j' ↔ s ≡ t [MOD 96] := by
  obtain ⟨he,_,period⟩ := small_probe_facts D 1
  have where_seen := two_norms_at_96 D odd board ι he period TameChar.one 0
  apply faithful_measurement D ι he (G := 48) (d := 3) period (by decide) (by decide) hit_96
  · by_contra! none
    have z := (where_seen 0).1 ⟨(reference_zero_iff_unit D ι he TameChar.one 0 0).1 (none _),
      (reference_zero_iff_unit D ι he TameChar.one 0 24).1 (none _)⟩
    exact z rfl
  · intro a nonzero
    by_contra off
    have unit := ((where_seen a).2 off).1
    exact nonzero ((reference_zero_iff_unit _ _ he TameChar.one 0 a).2 unit)

theorem recognize_144 (D : Data params) (ι : PadicPlace (smallerPrime 3)) {k : ℕ} (odd : Odd k)
    (board : ∀ b j,residueBoard D b j=if b=0 then (k:ℤ) else 0)
    (s t : ℕ) (θ : (D.translateOffset s).TameChar) (η : (D.translateOffset t).TameChar) (j j' : ℕ) :
    sameMovedNorms D _ ι s t θ η j j' ↔ s ≡ t [MOD 144] := by
  obtain ⟨he,_,period⟩ := small_probe_facts D 3
  have seen := norm_at_doubled_period D odd board ι he period TameChar.one 0
  apply faithful_measurement D ι he (G := 72) (d := 9) period (by decide) (by decide) hit_144
  · refine ⟨0,fun zero ↦ ?_⟩
    exact ((seen 0).1 ((reference_zero_iff_unit _ _ he TameChar.one 0 0).1 zero)) rfl
  · intro a nonzero
    by_contra off
    exact nonzero ((reference_zero_iff_unit _ _ he TameChar.one 0 a).2 ((seen a).2 off))

theorem recognize_both_iff_288 (D : Data params) (ι : PadicPlace (smallerPrime 1))
    (κ : PadicPlace (smallerPrime 3)) {k : ℕ} (odd : Odd k)
    (board : ∀ b j,residueBoard D b j=if b=0 then (k:ℤ) else 0)
    (s t : ℕ) (θ : (D.translateOffset s).TameChar) (η : (D.translateOffset t).TameChar) (j j' : ℕ) :
    (sameMovedNorms D _ ι s t θ η j j' ∧ sameMovedNorms D _ κ s t θ η j j') ↔
    s ≡ t [MOD 288] := by
  rw [recognize_96 D ι odd board,recognize_144 D κ odd board]
  exact ⟨fun h ↦ Nat.mod_lcm h.1 h.2,fun h ↦ ⟨h.of_dvd (by decide),h.of_dvd (by decide)⟩⟩

/-- At every large integer scale the same base assignment admits 96 distinct translated
norm profiles at 72959, 144 at 97919, and 288 when both local measurements are carried. -/
theorem eventually_recognize_all_shifts :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧ Odd k ∧ #D.bPlaces=8*k ∧
      (∀ b j,residueBoard D b j=if b=0 then (k:ℤ) else 0) ∧
      ∀ (ι : PadicPlace (smallerPrime 1)) (κ : PadicPlace (smallerPrime 3)) (s t : ℕ)
        (θ : (D.translateOffset s).TameChar) (η : (D.translateOffset t).TameChar) (j j' : ℕ),
        (sameMovedNorms D _ ι s t θ η j j' ↔ s ≡ t [MOD 96]) ∧
        (sameMovedNorms D _ κ s t θ η j j' ↔ s ≡ t [MOD 144]) ∧
        ((sameMovedNorms D _ ι s t θ η j j' ∧ sameMovedNorms D _ κ s t θ η j j') ↔ s ≡ t [MOD 288]) := by
  filter_upwards [eventually_separate_the_nine_columns] with x source
  obtain ⟨base,k,time,hk,odd,size,cols⟩ := source
  let D := base.translateOffset 0
  have board := (cols 0).1
  have frame := base.translateOffset_fields 0
  refine ⟨D,k,frame.1.trans time,hk,odd,?_,board,?_⟩
  · exact (base.card_translateHighPlaces _ _).trans size
  · intro ι κ s t θ η j j'
    exact ⟨recognize_96 D ι odd board _ _ _ _ _ _, recognize_144 D κ odd board _ _ _ _ _ _,
      recognize_both_iff_288 D ι κ odd board _ _ _ _ _ _⟩

end New.Data.CollisionPrimeExample
