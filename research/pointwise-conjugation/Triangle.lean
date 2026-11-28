import Mathlib.Algebra.Module.LinearMap.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Hearthline.ThreeMarks

/-- Over any commutative ring, when does the motion interchanging the marks (1,0) and
(0,m), multiplied by k, extend to a linear map of the whole coordinate plane? -/
theorem linear_swap_iff {R : Type*} [CommRing R] (m k : R) :
    (∃ T : R × R →ₗ[R] R × R, T (1,0) = (0,k*m) ∧ T (0,m) = (k,0)) ↔ m ∣ k := by
  constructor
  · rintro ⟨T, _, at_m⟩
    have scaled : m • T (0,1) = (k,0) := by simpa only [← map_smul, Prod.smul_mk, smul_zero, smul_eq_mul, mul_zero, mul_one] using at_m
    exact ⟨(T (0,1)).1, (congrArg Prod.fst scaled).symm⟩
  · rintro ⟨b, hb⟩
    let T : R × R →ₗ[R] R × R := (b • LinearMap.snd R R R).prod ((k*m) • LinearMap.fst R R R)
    exact ⟨T, by simp [T], by simp [T, hb, mul_comm]⟩

/-- With no scaling, an ambient extension that realizes the marked swap exists precisely
when m is a unit. The displayed extension then squares to the identity. -/
theorem involution_iff {R : Type*} [CommRing R] (m : R) :
    (∃ T : R × R →ₗ[R] R × R, T (1,0) = (0,m) ∧ T (0,m) = (1,0) ∧
      ∀ x, T (T x) = x) ↔ IsUnit m := by
  constructor
  · rintro ⟨T, h₁, h₂, _⟩
    exact isUnit_of_dvd_one ((linear_swap_iff m 1).1 ⟨T, by simpa using h₁, h₂⟩)
  · rintro ⟨u, rfl⟩
    let T : R × R →ₗ[R] R × R :=
      ((↑(u⁻¹) : R) • LinearMap.snd R R R).prod ((u : R) • LinearMap.fst R R R)
    exact ⟨T, by simp [T], by simp [T], fun x ↦ by ext <;> simp [T, ← mul_assoc]⟩

/-- The gcd is the exact amount of scaling required over a finite residue ring. -/
theorem dvd_mod_iff (m n k : ℕ) : (m : ZMod n) ∣ (k : ZMod n) ↔ m.gcd n ∣ k := by
  constructor
  · rintro ⟨b, hb⟩
    let f := ZMod.castHom (Nat.gcd_dvd_right m n) (ZMod (m.gcd n))
    have h := congrArg f hb
    rw [map_natCast, map_mul, map_natCast, (ZMod.natCast_eq_zero_iff _ _).2 (Nat.gcd_dvd_left m n),
      zero_mul] at h
    exact (ZMod.natCast_eq_zero_iff _ _).1 h
  · rintro ⟨t, rfl⟩
    have bez : (↑(m.gcd n) : ZMod n) = (m : ZMod n) * (m.gcdA n : ℤ) := by
      simpa using congrArg (fun z : ℤ ↦ (z : ZMod n)) (Nat.gcd_eq_gcd_ab m n)
    exact ⟨(m.gcdA n : ℤ) * (t : ZMod n), by rw [Nat.cast_mul, bez, mul_assoc]⟩

theorem scaled_residue_swap (m n k : ℕ) :
    (∃ T : ZMod n × ZMod n →ₗ[ZMod n] ZMod n × ZMod n,
      T (1,0) = (0,(k : ZMod n)*(m : ZMod n)) ∧ T (0,(m : ZMod n)) = ((k : ZMod n),0)) ↔
      m.gcd n ∣ k := (linear_swap_iff _ _).trans (dvd_mod_iff m n k)

def mark {R : Type*} [Ring R] (m : R) : Fin 3 → R × R := ![(0,0),(1,0),(0,m)]

/-- All three labels can still be distinguished modulo 289. -/
example : Function.Injective (mark (17 : ZMod 289)) := by decide +kernel
/-- They already collide modulo 17. -/
example : mark (17 : ZMod 17) 0 = mark 17 2 ∧ mark (17 : ZMod 17) 0 ≠ mark 17 1 := by decide +kernel
/-- The same swap fails at 289, succeeds at 19, and its scaled equations at 289
are soluble exactly when 17 divides the scale. -/
example : (¬IsUnit (17 : ZMod 289)) ∧ IsUnit (17 : ZMod 19) := by
  exact ⟨fun h ↦ (by decide : ¬Nat.Coprime 17 289) ((ZMod.isUnit_iff_coprime 17 289).1 h),
    (ZMod.isUnit_iff_coprime 17 19).2 (by decide)⟩

end Hearthline.ThreeMarks
