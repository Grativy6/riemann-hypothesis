module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Multiplicity
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

/-!
# A multiplicative return and an additive period

If M is divisible by 12 and T is supported on 2 and 3, the period of 1+M b modulo M T
is the additive order of b modulo T. The proof compares the two prime valuations of a
power difference after M is divided out. It applies to positive and negative integer carries.
-/

@[expose] public section

namespace ReturnQuotient

/-- Dividing out the base modulus leaves the 2- and 3-adic valuations of the carry times n. -/
theorem quotient_valuations {M b c : ℤ} (hM : M ≠ 0) (h12 : 12 ∣ M) (n : ℕ)
    (hc : (1 + M*b)^n - 1 = M*c) :
    emultiplicity (2 : ℤ) c = emultiplicity 2 (b*(n : ℤ)) ∧
    emultiplicity (3 : ℤ) c = emultiplicity 3 (b*(n : ℤ)) := by
  have h4 : 4 ∣ (1 + M*b) - 1 := by
    simpa using (show (4 : ℤ) ∣ M*b from ((by decide : (4 : ℤ) ∣ 12).trans h12).mul_right b)
  have h3 : 3 ∣ (1 + M*b) - 1 := by
    simpa using (show (3 : ℤ) ∣ M*b from ((by decide : (3 : ℤ) ∣ 12).trans h12).mul_right b)
  have h2x : ¬ 2 ∣ (1 + M*b) := by omega
  have h3x : ¬ 3 ∣ (1 + M*b) := by omega
  have cancel (l : ℤ) (hl : Prime l) (hf : FiniteMultiplicity l M)
      (v : emultiplicity l ((1+M*b)^n-1) = emultiplicity l (M*b) + emultiplicity l (n : ℤ)) :
      emultiplicity l c = emultiplicity l (b*(n : ℤ)) := by
    apply ENat.add_right_injective_of_ne_top (emultiplicity_lt_top.2 hf).ne
    rw [hc] at v
    simpa only [emultiplicity_mul hl, add_assoc] using v
  constructor
  · apply cancel 2 Int.prime_two (Int.finiteMultiplicity_iff.2 ⟨by decide, hM⟩)
    simpa using (Int.two_pow_sub_pow' (x := 1+M*b) (y := 1) n h4 h2x)
  · apply cancel 3 Int.prime_three (Int.finiteMultiplicity_iff.2 ⟨by decide, hM⟩)
    have hnat := Int.natCast_emultiplicity 3 n
    norm_num only [Nat.cast_ofNat] at hnat
    rw [hnat]
    simpa using (Int.emultiplicity_pow_sub_pow (p := 3) Nat.prime_three (by decide)
      (x := 1+M*b) (y := 1) h3 h3x n)

/-- For a tower factor supported on 2 and 3, the multiplicative return is an ordinary
divisibility test on the carry after the first return. -/
theorem return_iff {M b : ℤ} (hm : M ≠ 0) (h12 : (12 : ℤ) ∣ M) (s h n : ℕ) :
    M*((2 : ℤ)^s*3^h) ∣ (1+M*b)^n-1 ↔ (2 : ℤ)^s*3^h ∣ b*(n : ℤ) := by
  have hd : M ∣ (1+M*b)^n - 1 := by
    have hmul : M ∣ (1+M*b)-1 := by simp
    exact hmul.trans (by simpa using sub_dvd_pow_sub_pow (1+M*b) (1 : ℤ) n)
  obtain ⟨c, hc⟩ := hd
  obtain ⟨h2,h3⟩ := quotient_valuations hm h12 n hc
  have cop : IsCoprime ((2 : ℤ)^s) (3^h) := by
    exact_mod_cast (Nat.isCoprime_iff_coprime.2 (Nat.coprime_pow_primes s h Nat.prime_two Nat.prime_three (by decide)))
  have sep (z : ℤ) : (2 : ℤ)^s * 3^h ∣ z ↔ (2 : ℤ)^s ∣ z ∧ 3^h ∣ z :=
    ⟨fun hz ↦ ⟨(dvd_mul_right _ _).trans hz, (dvd_mul_left _ _).trans hz⟩,
      fun hz ↦ cop.mul_dvd hz.1 hz.2⟩
  rw [hc, Int.mul_dvd_mul_iff_left hm, sep, sep]
  simp only [pow_dvd_iff_le_emultiplicity, h2, h3]

end ReturnQuotient

namespace ReturnQuotient

/-- On a tower factor supported on 2 and 3, the order after one return is the additive
order of the signed carry modulo that factor. -/
theorem order_eq_addOrder (M : ℕ) (hM : M ≠ 0) (h12 : 12 ∣ M) (b : ℤ) (s h : ℕ) :
    orderOf (((1 + (M : ℤ)*b : ℤ) : ZMod (M*(2^s*3^h)))) =
      addOrderOf (b : ZMod (2^s*3^h)) := by
  let T := 2^s * 3^h
  let u : ℤ := 1 + M*b
  have equiv (n : ℕ) : ((u : ZMod (M*T))^n = 1) ↔ n • (b : ZMod T) = 0 := by
    calc ((u : ZMod (M*T))^n = 1)
        ↔ (((u^n-1 : ℤ) : ZMod (M*T))) = 0 := by push_cast; exact sub_eq_zero.symm
      _ ↔ ((M*T : ℕ) : ℤ) ∣ u^n-1 := ZMod.intCast_zmod_eq_zero_iff_dvd _ _
      _ ↔ (T : ℤ) ∣ b * n := by
        simpa only [T, u, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
          (return_iff (M := (M : ℤ)) (b := b) (Int.natCast_ne_zero.mpr hM)
            (by exact_mod_cast h12) s h n)
      _ ↔ ((b * n : ℤ) : ZMod T) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
      _ ↔ n • (b : ZMod T) = 0 := by push_cast; rw [nsmul_eq_mul, mul_comm]
  have periods (n : ℕ) : orderOf (u : ZMod (M*T)) ∣ n ↔ addOrderOf (b : ZMod T) ∣ n := by
    rw [orderOf_dvd_iff_pow_eq_one, addOrderOf_dvd_iff_nsmul_eq_zero]
    exact equiv n
  exact Nat.dvd_antisymm ((periods _).2 dvd_rfl) ((periods _).1 dvd_rfl)

end ReturnQuotient

namespace ReturnQuotient

open Finset

/-- The number of residue lifts of one class times the smaller modulus equals the larger modulus. -/
theorem card_cast_fiber_mul {n m : ℕ} [NeZero n] [NeZero m] (hm : m ∣ n) (y : ZMod m) :
    #{z : ZMod n | ZMod.castHom hm (ZMod m) z = y} * m = n := by
  classical
  let f := (ZMod.castHom hm (ZMod m)).toAddMonoidHom
  have surj : Function.Surjective f := ZMod.castHom_surjective hm
  have move := AddMonoidHom.card_fiber_eq_of_mem_range f (surj y) (surj 0)
  have ker : #{z : ZMod n | f z = 0} = Nat.card f.ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have count := AddSubgroup.card_ker_mul_card_of_surjective (f := f) surj
  change #{z : ZMod n | f z = y} * m = n
  rw [move, ker]
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using count

end ReturnQuotient


namespace ReturnOrientation

/-- A first return congruent to one modulo R squares to one modulo 2R when R is even. -/
theorem square_lifts {R z : ℤ} (hR : 2 ∣ R) (hz : R ∣ z-1) : 2*R ∣ z^2-1 := by
  obtain ⟨d, hd⟩ := hR
  obtain ⟨c, hc⟩ := hz
  have hu : (2 : ℤ) ∣ z+1 := ⟨1+d*c, by rw [hd] at hc; linarith⟩
  have h := mul_dvd_mul (show R ∣ z-1 from ⟨c,hc⟩) hu
  convert h using 1 <;> ring

/-- If the return does not already hold modulo 2R, the refined period is exactly two. -/
theorem square_period_two {R : ℕ} (hR : 2 ∣ R) (z : ℤ)
    (hz : (R : ℤ) ∣ z-1) (hn : ¬(2*(R : ℤ)) ∣ z-1) :
    orderOf (z : ZMod (2*R)) = 2 := by
  have hh := square_lifts (by exact_mod_cast hR) hz
  have eq2 : (z : ZMod (2*R)) ^ 2 = 1 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (z^2-1) (2*R)).2 (by exact_mod_cast hh)
    push_cast at h0
    exact sub_eq_zero.1 h0
  have ne1 : (z : ZMod (2*R)) ≠ 1 := by
    intro h
    apply hn
    have h0 : ((z-1 : ℤ) : ZMod (2*R)) = 0 := by push_cast; simpa using sub_eq_zero.2 h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (z-1) (2*R)).1 h0
    exact_mod_cast this
  exact ((Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_iff_pow_eq_one.2 eq2)).resolve_left
    (fun h ↦ ne1 (orderOf_eq_one_iff.1 h))

end ReturnOrientation
