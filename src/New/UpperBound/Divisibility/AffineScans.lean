module

public import New.UpperBound.Divisibility.CrossPeriodNorms
import Mathlib.Tactic

/-!
# Moving a signed profile and recognizing a full turn

On the finite offset ring the distinguished lifts act by t+x+Mtx. A conjugate half-turn
negates the signed profile. A nonzero profile supported above zero modulo the odd part
cannot be invariant under a nonidentity shift if every remaining shift generates the half-turn.
-/

@[expose] public section
open Finset NumberField ThreePrimeEnvelope
namespace New.SixSignatures

def affine (M t x : ℕ) : ℕ := t+x+M*t*x

lemma affine_same_iff {N M t : ℕ} (cop : N.Coprime (1+M*t)) (a b : ℕ) :
    affine M t a ≡ affine M t b [MOD N] ↔ a ≡ b [MOD N] := by
  have form (z : ℕ) : affine M t z=t+(1+M*t)*z := by unfold affine;ring
  rw [form,form]
  exact ⟨fun h ↦ Nat.ModEq.cancel_left_of_coprime cop (Nat.ModEq.add_left_cancel' t h),
    fun h ↦ (h.mul_left _).add_left _⟩

lemma affine_opposite (G M t a : ℕ) (even : 2∣M) :
    affine M t a+G ≡ affine M t (a+G) [MOD 2*G] := by
  obtain ⟨w,rfl⟩ := even
  apply Nat.modEq_of_dvd
  refine ⟨(w:ℤ)*t,?_⟩;unfold affine;push_cast;ring

/-- Offset multiplication modulo a measuring period, at the fixed base modulus 18480. -/
def glide {R : Type*} [CommRing R] (x y : R) : R := x+y+18480*x*y
lemma glide_comm {R : Type*} [CommRing R] (x y : R) : glide x y=glide y x := by unfold glide;ring
lemma glide_assoc {R : Type*} [CommRing R] (x y z : R) : glide (glide x y) z=glide x (glide y z) := by
  unfold glide;ring
@[simp] lemma glide_zero {R : Type*} [CommRing R] (x : R) : glide x 0=x := by simp [glide]
@[simp] lemma zero_glide {R : Type*} [CommRing R] (x : R) : glide 0 x=x := by simp [glide]

def offsetPower {R : Type*} [CommRing R] (x : R) : ℕ → R
  | 0 => 0
  | n+1 => glide x (offsetPower x n)

lemma reduction_val {n d : ℕ} [NeZero n] [NeZero d] (hd : d ∣ n) (x : ZMod n) :
    ZMod.castHom hd (ZMod d) x = (x.val : ZMod d) := by
  nth_rw 1 [← ZMod.natCast_zmod_val x]
  rw [map_natCast]

lemma glide_surjective {R : Type*} [CommRing R] (square : (18480:R)^2=0) (t : R) :
    Function.Surjective (glide t) := by
  let inv := -t+18480*t^2
  have undo : glide t inv=0 := by
    calc _ = (18480:R)^2*t^3 := by unfold glide inv;ring
      _ = 0 := by rw [square,zero_mul]
  exact fun y ↦ ⟨glide inv y,by rw [← glide_assoc,undo,zero_glide]⟩

/-- The observed support kills the odd component of a stabilizing shift. The controlled
power of any remaining nonzero shift then sends a nonzero value to its own negative. -/
theorem faithful_signed_shift {n d G : ℕ} [NeZero n] [NeZero d] (hd : d∣n)
    (square : (18480:ZMod n)^2=0)
    (hit : ∀ r : ZMod n,r≠0 → r.val%d=0 → ∃ k,offsetPower r k=(G:ZMod n))
    (S : ZMod n → ℤ) (nonzero : ∃ x,S x≠0) (supported : ∀ x,S x≠0 → x.val%d=0)
    (opposite : ∀ x,S (glide (G:ZMod n) x) = -S x)
    {s t : ZMod n} (same : ∀ x,S (glide s x)=S (glide t x)) : s=t := by
  let inv := -t+18480*t^2
  have undo : glide t inv=0 := by
    calc _ = (18480:ZMod n)^2*t^3 := by unfold glide inv;ring
      _ = 0 := by rw [square,zero_mul]
  let r := glide s inv
  have invariant (x : ZMod n) : S (glide r x)=S x := by
    calc _ = S (glide s (glide inv x)) := by rw [glide_assoc]
      _ = S (glide t (glide inv x)) := same _
      _ = _ := by rw [← glide_assoc,undo,zero_glide]
  let red := ZMod.castHom hd (ZMod d)
  have red_zero (x : ZMod n) : red x=0 ↔ x.val%d=0 := by
    rw [show red x=(x.val:ZMod d) from reduction_val hd x,ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]
  obtain ⟨x,hx⟩ := nonzero
  have h₀ := (red_zero x).2 (supported x hx)
  have h₁ := (red_zero (glide r x)).2 (supported _ ((invariant x).trans_ne hx))
  have hr : red r=0 := by simpa [glide,map_add,map_mul,h₀] using h₁
  have rz : r=0 := by
    by_contra bad
    obtain ⟨k,flip⟩ := hit r bad ((red_zero r).1 hr)
    have power (e : ℕ) : S (glide (offsetPower r e) x)=S x := by
      induction e with
      | zero => simp [offsetPower]
      | succ e ih => rw [offsetPower,glide_assoc,invariant,ih]
    have contrad := power k
    rw [flip,opposite] at contrad
    omega
  calc s = glide r t := by unfold r;rw [glide_assoc,glide_comm inv t,undo,glide_zero]
    _ = t := by rw [rz,zero_glide]

end New.SixSignatures

namespace New.Data
open SixSignatures
variable {P : Parameters} (D : Data P)

lemma offsetMass_congr {m a b : ℕ} (h : a ≡ b [MOD m]) : D.offsetMass m a=D.offsetMass m b := by
  classical
  unfold offsetMass
  congr 1
  apply filter_congr
  exact fun _ _ ↦ ⟨fun v ↦ v.trans h,fun v ↦ v.trans h.symm⟩

theorem mass_covariant {n : ℕ} (hn : n*P.q₀ ∣ D.q₁) (t a : ℕ) :
    (D.translateOffset t).offsetMass n (affine P.q₀ t a) = D.offsetMass n a := by
  classical
  let g := D.distinguishedLift t
  have d : n ∣ D.q₁ := (dvd_mul_right n _).trans hn
  have cop : n.Coprime (1+P.q₀*t) := by
    apply Nat.Coprime.symm
    apply (ZMod.isUnit_iff_coprime _ _).1
    rw [← D.distinguishedLift_val d t]
    exact Units.isUnit _
  simp only [offsetMass,card_filter]
  change (∑ z ∈ D.bPlaces.image (fun a ↦ g*a), _) = _
  rw [sum_image (fun _ _ _ _ eq ↦ mul_left_cancel eq)]
  apply sum_congr rfl;intro z hz
  have moved := D.shifted_offset_at_place hn t z hz
  have rel : ((D.translateOffset t).negativeOffset (g*z) ≡ affine P.q₀ t a [MOD n]) ↔
      affine P.q₀ t (D.negativeOffset z) ≡ affine P.q₀ t a [MOD n] :=
    ⟨fun v ↦ moved.symm.trans v,fun v ↦ moved.trans v⟩
  exact if_congr (rel.trans (affine_same_iff cop _ _)) rfl rfl

end New.Data

namespace New.Data.CollisionPrimeExample
open SixSignatures
variable {D : Data params} {p : ℕ} [Fact p.Prime]

/-- The signed reference function on its period ring. -/
noncomputable def residueProfile (D : Data params) (p : ℕ) [Fact p.Prime] (ι : PadicPlace p)
    {n : ℕ} (v : ZMod n) : ℤ := D.signedCount p ι (D.anchorPrime p ι v.val)

theorem residueProfile_nat (D : Data params) (ι : PadicPlace p) (he : D.IsExceptional p)
    {n : ℕ} [NeZero n] (per : 2*D.returnPairCount p=n) (a : ℕ) :
    residueProfile D p ι (a:ZMod n) = D.signedCount p ι (D.anchorPrime p ι a) := by
  unfold residueProfile
  apply congrArg (D.signedCount p ι)
  apply (he.anchorPrime_eq_iff _ _).2
  rw [per,ZMod.val_natCast];exact Nat.mod_modEq _ _

theorem residueProfile_moved (D : Data params) (ι : PadicPlace p) (he : D.IsExceptional p)
    {n : ℕ} [NeZero n] (per : 2*D.returnPairCount p=n) (t : ℕ) (v : ZMod n) :
    residueProfile (D.translateOffset t) p ι (glide (t:ZMod n) v) = residueProfile D p ι v := by
  let E := D.translateOffset t
  let G := D.returnPairCount p
  have econ : E.IsExceptional p := he
  have ep : E.returnPairCount p=G := rfl
  have hn : n*params.q₀ ∣ D.q₁ := by
    rw [← per];simpa [returnModulus,mul_left_comm,mul_assoc,mul_comm] using he.twice_returnModulus_dvd_tower
  have move_cast : ((affine params.q₀ t v.val : ℕ):ZMod n)=glide (t:ZMod n) v := by
    simp [affine,glide,show params.q₀=18480 from rfl]
  rw [← move_cast, residueProfile_nat E ι econ per]
  change E.highCount p (star (E.anchorPrime p ι _)) - (E.highCount p (E.anchorPrime p ι _) : ℤ) =
    D.highCount p (star (D.anchorPrime p ι v.val)) - (D.highCount p (D.anchorPrime p ι v.val) : ℤ)
  rw [← econ.anchorPrime_conjugate,← he.anchorPrime_conjugate,
    econ.highCount_at_anchor,econ.highCount_at_anchor,he.highCount_at_anchor,he.highCount_at_anchor,ep,per]
  have other := affine_opposite G params.q₀ t v.val (by decide)
  rw [show 2*G=n from per] at other
  rw [E.offsetMass_congr other,D.mass_covariant hn,D.mass_covariant hn]

theorem residueProfile_opposite (D : Data params) (ι : PadicPlace p) (he : D.IsExceptional p)
    {G : ℕ} [NeZero (2*G)] (per : D.returnPairCount p=G) (v : ZMod (2*G)) :
    residueProfile D p ι (glide (G:ZMod (2*G)) v) = -residueProfile D p ι v := by
  have shift : glide (G:ZMod (2*G)) v = ((v.val+G:ℕ):ZMod (2*G)) := by
    have annihilate : (18480:ZMod (2*G))*G=0 := by
      have h : ((2*G:ℕ):ZMod (2*G))=0 := ZMod.natCast_self _
      push_cast at h
      calc _ = 9240*(2*(G:ZMod (2*G))) := by ring
        _ = 0 := by rw [h,mul_zero]
    simp [glide,annihilate,add_comm]
  rw [shift,residueProfile_nat D ι he (by rw [per]) _]
  unfold residueProfile
  have conj : D.anchorPrime p ι (v.val+G) = star (D.anchorPrime p ι v.val) :=
    (congrArg (fun n ↦ D.anchorPrime p ι (v.val+n)) per.symm).trans (he.anchorPrime_conjugate v.val)
  rw [conj]
  simp [signedCount,star_star]

/-- Equality after two common moves transfers to an invariance of the original signed
profile; the moves commute as elements of the tower group. -/
theorem moved_profile_agreement (D : Data params) (ι : PadicPlace p) (he : D.IsExceptional p)
    {n : ℕ} [NeZero n] (per : 2*D.returnPairCount p=n) {s t : ℕ}
    (same : ∀ v : ZMod n, residueProfile (D.translateOffset s) p ι v =
          residueProfile (D.translateOffset t) p ι v) (v : ZMod n) :
    residueProfile D p ι (glide (s:ZMod n) v) = residueProfile D p ι (glide (t:ZMod n) v) := by
  rw [← residueProfile_moved D ι he per t,← residueProfile_moved D ι he per s (glide (t:ZMod n) v)]
  rw [← glide_assoc,glide_comm (t:ZMod n) s,glide_assoc,← same]

end New.Data.CollisionPrimeExample
