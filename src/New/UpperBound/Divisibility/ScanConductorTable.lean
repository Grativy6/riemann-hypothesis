module

public import New.UpperBound.Divisibility.FaithfulPrimeProfiles
import Mathlib.Tactic

/-!
# One full profile and two binary readings on a common frame

The original 72-slot histogram stays uniform on the column t mod 9 after *every*
translation t. Reference norms at the first doubled period therefore test membership
in one of nine columns. Once the smaller prime identifies the residue modulo 96,
two binary queries distinguish the three remaining possibilities modulo 288.
-/

@[expose] public section
open Finset Filter NumberField Real ThreePrimeEnvelope ColoredSparse
namespace New.Data.CollisionPrimeExample
open SixSignatures

theorem uniform_board_after_any_shift (D : Data params) {k : ℕ}
    (initial : ∀ b j,residueBoard D b j=if b=0 then (k:ℤ) else 0) (t : ℕ) :
    ∀ b j,residueBoard (D.translateOffset t) b j=if b.val=t%9 then (k:ℤ) else 0 := by
  intro b j
  let a := address72 b j
  obtain ⟨z,hz⟩ := glide_surjective (by decide : (18480:ZMod 72)^2=0) (t:ZMod 72) (a:ZMod 72)
  have moved : affine params.q₀ t z.val ≡ a [MOD 72] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).1
    simpa [affine,glide,show params.q₀=18480 from rfl] using hz
  have coord : affine params.q₀ t z.val ≡ b.val [MOD 9] :=
    (moved.of_dvd (by decide)).trans (by simp [a,address72,Nat.ModEq])
  have cp : Nat.Coprime 3 (1+params.q₀*t) := Nat.prime_three.coprime_iff_not_dvd.2 (by
    change ¬3 ∣ 1+18480*t;omega)
  have identify : z.val%9=0 ↔ b.val=t%9 := calc
    _ ↔ z.val ≡ 0 [MOD 9] := Iff.rfl
    _ ↔ affine params.q₀ t z.val ≡ affine params.q₀ t 0 [MOD 9] := (affine_same_iff (cp.pow_left 2) _ _).symm
    _ ↔ b.val ≡ t [MOD 9] := by
      rw [show affine params.q₀ t 0=t by simp [affine]]
      exact ⟨fun h ↦ coord.symm.trans h,fun h ↦ coord.trans h⟩
    _ ↔ _ := by simp [Nat.ModEq,Nat.mod_eq_of_lt b.isLt]
  obtain ⟨e,_,height⟩ := D.exists_m_eq_two_pow
  have hd := joint_dvd_tower (s := D.towerExp) (by omega)
  have mass := D.mass_covariant hd t z.val
  rw [(D.translateOffset t).offsetMass_congr moved,uniform_mass_at_72 D initial] at mass
  have actual := offsetMass_at_boardIndex (D.translateOffset t) (address72 b j)
  rw [boardIndex_address] at actual
  calc residueBoard (D.translateOffset t) b j = ((D.translateOffset t).offsetMass 72 a:ℤ) := actual.symm
    _ = _ := by rw [mass];by_cases h : b.val=t%9 <;> simp_all

/-- Unit status at the larger probe indicates only the old column, while remaining
independent of the sign at either finer lift. -/
theorem doubled_unit_support_after_shift (D : Data params) {k : ℕ} (hk : Odd k)
    (board : ∀ b j,residueBoard D b j=if b=0 then (k:ℤ) else 0) (t : ℕ)
    (ι : PadicPlace (smallerPrime 3)) (θ : (D.translateOffset t).TameChar) (j a : ℕ) :
    (D.translateOffset t).referenceNorm _ ι θ j a=1 ↔ a%9≠t%9 := by
  let c : Fin 9 := ⟨t%9,Nat.mod_lt _ (by decide)⟩
  have hist (b : Fin 9) (v : Fin 8) : residueBoard (D.translateOffset t) b v =
      if b=c then (k:ℤ) else 0 := by
    rw [uniform_board_after_any_shift D board]
    exact if_congr (by change b.val=c.val ↔ b=c;exact Fin.ext_iff.symm) rfl rfl
  exact norm_at_doubled_period (D.translateOffset t) hk hist ι (small_probe_facts _ 3).1
    (small_probe_facts _ 3).2.2 θ j a

/-- Given the calibrated 96-position profile only three columns are possible. Test the
first two at the doubled-period prime. This achieves the same resolution as the two full scans. -/
theorem recognize_288_with_two_bits (D : Data params) {k : ℕ} (odd : Odd k)
    (board : ∀ b j,residueBoard D b j=if b=0 then (k:ℤ) else 0)
    (ι : PadicPlace (smallerPrime 1)) (κ : PadicPlace (smallerPrime 3)) (s t : ℕ)
    (θ : (D.translateOffset s).TameChar) (η : (D.translateOffset t).TameChar) (j j' : ℕ) :
    (sameMovedNorms D _ ι s t θ η j j' ∧ ∀ i : Fin 2, let a := s%3+3*i.val
      ((D.translateOffset s).referenceNorm _ κ θ j a=1 ↔ (D.translateOffset t).referenceNorm _ κ η j' a=1)) ↔
    s ≡ t [MOD 288] := by
  rw [recognize_96 D ι odd board]
  simp only [doubled_unit_support_after_shift D odd board]
  constructor
  · rintro ⟨h,bits⟩
    have zero := bits 0
    have one := bits 1
    change s%96=t%96 at h
    change ((s%3+3*0)%9≠s%9 ↔ (s%3+3*0)%9≠t%9) at zero
    change ((s%3+3*1)%9≠s%9 ↔ (s%3+3*1)%9≠t%9) at one
    change s%288=t%288
    omega
  · intro h
    exact ⟨h.of_dvd (by decide),fun _ ↦ by rw [show s%9=t%9 from h.of_dvd (by decide)]⟩

/-- This frame stays silent everywhere below the least exceptional exit prime. At that
prime all 96 shifts have different full profiles. Together with two binary tests at the
least doubled-period prime it resolves 288. -/
theorem first_excursion_on_one_frame :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧ Odd k ∧ #D.bPlaces=8*k ∧
      (∀ t p : ℕ, ∀ [_hp : Fact p.Prime], ∀ _ι : PadicPlace p,
        D.IsExceptional p → p<72959 → ∀ l : FinPlace D.E, (p:𝓞 D.E)∈l.asIdeal →
        ∀ (θ : (D.translateOffset t).TameChar) (j : ℕ),
        ‖ιₚ (((D.translateOffset t).chainChar θ j).baseChange.atUniformizer l)‖=1) ∧
      ∀ (ι : PadicPlace (smallerPrime 1)) (κ : PadicPlace (smallerPrime 3)) (s t : ℕ)
        (θ : (D.translateOffset s).TameChar) (η : (D.translateOffset t).TameChar) (j j' : ℕ),
        (sameMovedNorms D _ ι s t θ η j j' ↔ s ≡ t [MOD 96]) ∧
        (sameMovedNorms D _ κ s t θ η j j' ↔ s ≡ t [MOD 144]) ∧
        ((sameMovedNorms D _ ι s t θ η j j' ∧ ∀ i : Fin 2, let a := s%3+3*i.val
          ((D.translateOffset s).referenceNorm _ κ θ j a=1 ↔ (D.translateOffset t).referenceNorm _ κ η j' a=1)) ↔
          s ≡ t [MOD 288]) := by
  filter_upwards [eventually_recognize_all_shifts] with x hx
  obtain ⟨D,k,time,hk,odd,card,board,measure⟩ := hx
  refine ⟨D,k,time,hk,odd,card,?_,?_⟩
  · intro t p hp ι he small l above θ j
    have flat := uniform_board_after_any_shift D board t
    exact (unit_norms_of_flat_board (D.translateOffset t) (fun b j ↦ (flat b j).trans (flat b 0).symm) ι he
      ((small_period_bounds D he (by omega)).2.1 small) l).2 above θ j
  · intro ι κ s t θ η j j'
    have pair := measure ι κ s t θ η j j'
    exact ⟨pair.1,pair.2.1,recognize_288_with_two_bits D odd board ι κ s t θ η j j'⟩

end New.Data.CollisionPrimeExample
