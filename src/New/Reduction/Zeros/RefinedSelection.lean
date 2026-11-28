module

public import Lib.Analytic.QuadraticTwist
import Lib.Analytic.EntireLFunction
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Ring

/-!
# Reading the class-seven zero-free selector in a smaller character level

Quadratic twisting commutes with change of level. Nonvanishing descends along this map.
A compatible pair of residue classes can therefore be sampled at a common multiple.
-/

@[expose] public section

open Nat Filter DirichletCharacter Complex ZMod

namespace New

/-- The Legendre twist and induction of the original character commute. -/
lemma quadTwist_changeLevel_eq {N L : ℕ} (χ : DirichletCharacter ℂ N) (h : N ∣ L)
    (d : ℕ) [Fact d.Prime] :
    quadTwist (χ.changeLevel h) d =
      (quadTwist χ d).changeLevel (Nat.mul_dvd_mul_right h d) := by
  simp [quadTwist, ← changeLevel_trans]

/-- Nonvanishing descends from any raised level to the character that was raised, at every
complex point. At one use regularity of the entire functions. Elsewhere use the Euler product. -/
lemma entireL_ne_zero_of_changeLevel {N L : ℕ} [NeZero N] [NeZero L]
    (χ : DirichletCharacter ℂ N) (h : N ∣ L) {s : ℂ}
    (good : entireL (χ.changeLevel h) s ≠ 0) : entireL χ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs
  · exact entireL_ne_zero χ (by norm_num)
  apply (entireL_ne_zero_iff χ hs).2
  have nonzero := (entireL_ne_zero_iff _ hs).1 good
  rw [LFunction_changeLevel h χ (.inr hs)] at nonzero
  exact left_ne_zero_of_mul nonzero

/-- A unit class lifts to a unit class at every multiple of its modulus. -/
lemma lift_unit_class {C L a : ℕ} [NeZero L] (h : C ∣ L) (ha : a.Coprime C) :
    ∃ c < L, c.Coprime L ∧ c ≡ a [MOD C] := by
  have unit : IsUnit (a : ZMod C) := (ZMod.isUnit_iff_coprime a C).2 ha
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective h unit.unit
  let c := (u : ZMod L).val
  have hc : (c : ZMod L) = (u : ZMod L) := ZMod.natCast_zmod_val _
  have cast : ((c : ℕ) : ZMod C) = a := calc
    _ = ZMod.castHom h (ZMod C) (c : ZMod L) := (map_natCast _ c).symm
    _ = (ZMod.unitsMap h u : (ZMod C)ˣ) := by rw [hc]; rfl
    _ = _ := by rw [hu, unit.unit_spec]
  exact ⟨c, (u : ZMod L).val_lt, (ZMod.isUnit_iff_coprime c L).1 (hc ▸ u.isUnit),
    (ZMod.natCast_eq_natCast_iff c a C).1 cast⟩

/-- Apply the published selector at L and read every resulting twist at the divisor N. -/
theorem exists_seven_at_cover {N L z : ℕ} [NeZero N] [NeZero L] (hNL : N ∣ L)
    (h8L : 8 ∣ L) (hunit : z.Coprime L) (h8 : z ≡ 7 [MOD 8]) {β : ℝ} (hβ : 1/2 < β) (H : ℝ) :
    ∃ d : Primes, (d : ℕ) ≡ z [MOD L] ∧ (d : ℕ) % 8 = 7 ∧ N.Coprime d ∧
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), β ≤ s.re → |s.im| ≤ H →
        entireL (quadTwist χ d) s ≠ 0 := by
  have readClass (d : Primes) (hd : ((d : ℕ) : ZMod L) = z) :
      (d : ℕ) % 8 = 7 ∧ L.Coprime d := by
    have eq := (ZMod.natCast_eq_natCast_iff d z L).1 hd
    exact ⟨(eq.of_dvd h8L).trans h8, Nat.Coprime.symm (eq.gcd_eq.trans hunit)⟩
  obtain ⟨d, hd, good⟩ := exists_entireL_quadTwist_ne_zero H hβ
    ((ZMod.isUnit_iff_coprime z L).2 hunit) readClass
  have dz := (ZMod.natCast_eq_natCast_iff d z L).1 hd
  obtain ⟨seven, cop⟩ := readClass d hd
  refine ⟨d, dz, seven, cop.of_dvd_left hNL, fun χ s hs hi ↦ ?_⟩
  apply entireL_ne_zero_of_changeLevel (quadTwist χ d) (Nat.mul_dvd_mul_right hNL (d : ℕ))
  rw [← quadTwist_changeLevel_eq]
  exact good (χ.changeLevel hNL) s hs hi


/-- For a reduced progression already in class seven, the common multiple of the two
moduli suffices. This is the interface consumed by the geometric proof. -/
theorem exists_seven_at_independent_level {N Q a : ℕ} [NeZero N] [NeZero Q] (eight : 8 ∣ Q)
    (seven : a ≡ 7 [MOD 8]) (unit : a.Coprime Q) {β : ℝ} (hβ : 1/2 < β) (H : ℝ) :
    ∃ d : Primes, (d : ℕ) ≡ a [MOD Q] ∧ (d : ℕ) % 8 = 7 ∧ N.Coprime d ∧
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), β ≤ s.re → |s.im| ≤ H →
        entireL (quadTwist χ d) s ≠ 0 := by
  let L := Nat.lcm N Q
  have : NeZero L := ⟨Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne Q)⟩
  have qL : Q ∣ L := Nat.dvd_lcm_right _ _
  obtain ⟨c, _, c_unit, eq⟩ := lift_unit_class qL unit
  obtain ⟨d, hit, h7, cop, good⟩ := exists_seven_at_cover (Nat.dvd_lcm_left N Q)
    (eight.trans qL) c_unit ((eq.of_dvd eight).trans seven) hβ H
  exact ⟨d, (hit.of_dvd qL).trans eq, h7, cop, good⟩

end New
