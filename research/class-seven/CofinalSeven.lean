import New.Reduction.Zeros.RefinedSelection
import Mathlib.Tactic

open Nat Filter DirichletCharacter Complex ZMod
namespace New

/-- Refine an odd unit class to one whose least nonnegative representative exceeds B.
Only a power of two is added to the modulus. -/
private lemma lift_above {L c : ℕ} [NeZero L] (even : 2 ∣ L) (hc : c.Coprime L) (lt : c < L)
    (B : ℕ) :
    ∃ k z : ℕ, B < z ∧ z < L * 2 ^ k ∧ z.Coprime (L * 2 ^ k) ∧ z ≡ c [MOD L] := by
  by_cases hb : B < c
  · exact ⟨0, c, hb, by simpa using lt, by simpa using hc, Nat.ModEq.refl _⟩
  let j := (B-c) / L + 1
  let k := Nat.log 2 j + 1
  let z := L * j + c
  have high : j < 2 ^ k := Nat.lt_pow_succ_log_self (by decide : 1 < 2) _
  have congr : z ≡ c [MOD L] := by simp [z]
  have unit : z.Coprime L := congr.gcd_eq.trans hc
  refine ⟨k, z, ?_, ?_, unit.mul_right ((unit.of_dvd_right even).pow_right k), congr⟩
  · have rem := Nat.mod_lt (B-c) (NeZero.pos L)
    have div := Nat.mod_add_div (B-c) L
    dsimp only [z, j]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · calc z < L * j + L := Nat.add_lt_add_left lt _
         _ = L * (j + 1) := (Nat.mul_succ L j).symm
         _ ≤ L * 2 ^ k := Nat.mul_le_mul_left _ high

/-- If a class modulo Q meets seven modulo eight, there is a common reduced class at a multiple
of the character level and both moduli. Its first representative can lie past any cutoff. -/
lemma exists_seven_refinement {N Q a : ℕ} [NeZero N] [NeZero Q] (ha : a.Coprime Q)
    (compat : a ≡ 7 [MOD Q.gcd 8]) (B : ℕ) :
    ∃ L z : ℕ, 0 < L ∧ N ∣ L ∧ Q ∣ L ∧ 8 ∣ L ∧ B < z ∧ z < L ∧
      z.Coprime L ∧ z ≡ a [MOD Q] ∧ z ≡ 7 [MOD 8] := by
  obtain ⟨b, bQ, b8⟩ := Nat.chineseRemainder' compat
  let C := Nat.lcm Q 8
  let M := Nat.lcm N C
  have hC : C ≠ 0 := Nat.lcm_ne_zero (NeZero.ne Q) (by decide)
  have : NeZero M := ⟨Nat.lcm_ne_zero (NeZero.ne N) hC⟩
  have qC : Q ∣ C := Nat.dvd_lcm_left _ _
  have eC : 8 ∣ C := Nat.dvd_lcm_right _ _
  have cm : C ∣ M := Nat.dvd_lcm_right _ _
  have nm : N ∣ M := Nat.dvd_lcm_left _ _
  have bcop : b.Coprime C := by
    have l : b.Coprime Q := bQ.gcd_eq.trans ha
    have r : b.Coprime 8 := b8.gcd_eq.trans (by decide : Nat.Coprime 7 8)
    exact (l.mul_right r).of_dvd_right (Nat.lcm_dvd (dvd_mul_right Q 8) (dvd_mul_left 8 Q))
  obtain ⟨c, c_lt, c_unit, cb⟩ := lift_unit_class cm bcop
  obtain ⟨k, z, z_gt, z_lt, z_unit, zc⟩ :=
    lift_above ((by decide : 2 ∣ 8).trans (eC.trans cm)) c_unit c_lt B
  have mult : M ∣ M * 2 ^ k := dvd_mul_right _ _
  exact ⟨_, z, Nat.mul_pos (NeZero.pos M) (pow_pos (by decide) _), nm.trans mult,
    qC.trans (cm.trans mult), eC.trans (cm.trans mult), z_gt, z_lt, z_unit,
    ((zc.of_dvd (qC.trans cm)).trans (cb.of_dvd qC)).trans bQ,
    ((zc.of_dvd (eC.trans cm)).trans (cb.of_dvd eC)).trans b8⟩

/-- The original selector supplies arbitrarily large zero-free class-seven twists at level N
in any compatible reduced progression modulo Q. -/
theorem exists_seven_twist_in_class {N Q : ℕ} [NeZero N] [NeZero Q] {a : ℕ}
    (ha : a.Coprime Q) (compat : a ≡ 7 [MOD Q.gcd 8]) {β : ℝ} (hβ : 1 / 2 < β)
    (H : ℝ) (B : ℕ) :
    ∃ d : Primes, B < (d : ℕ) ∧ (d : ℕ) ≡ a [MOD Q] ∧ (d : ℕ) % 8 = 7 ∧ N.Coprime d ∧
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), β ≤ s.re → |s.im| ≤ H →
        entireL (quadTwist χ d) s ≠ 0 := by
  obtain ⟨L, z, pos, hNL, hQL, h8L, hB, hlt, hunit, hQ, h8⟩ :=
    exists_seven_refinement (N := N) ha compat B
  have : NeZero L := ⟨pos.ne'⟩
  obtain ⟨d, dz, seven, cop, good⟩ := exists_seven_at_cover hNL h8L hunit h8 hβ H
  have first : (d : ℕ) % L = z := Eq.trans dz (Nat.mod_eq_of_lt hlt)
  exact ⟨d, hB.trans_le (first ▸ Nat.mod_le (d : ℕ) L), (dz.of_dvd hQL).trans hQ,
    seven, cop, good⟩

/-- A cofinal family of these actual primes exists precisely on the unit classes whose
intersection with seven modulo eight is inhabited. The cutoff above Q detects nonunits. -/
theorem cofinal_seven_iff {N Q : ℕ} [NeZero N] [NeZero Q] {a : ℕ} {β : ℝ} (hβ : 1 / 2 < β)
    (H : ℝ) :
    (∀ B : ℕ, ∃ d : Primes, B < (d : ℕ) ∧ (d : ℕ) ≡ a [MOD Q] ∧ (d : ℕ) % 8 = 7 ∧
      N.Coprime d ∧ ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), β ≤ s.re → |s.im| ≤ H →
        entireL (quadTwist χ d) s ≠ 0) ↔ a.Coprime Q ∧ a ≡ 7 [MOD Q.gcd 8] := by
  constructor
  · intro all
    obtain ⟨d, large, hd, seven, _, _⟩ := all Q
    have u := d.prop.coprime_iff_not_dvd.2 (fun h ↦ large.not_ge (Nat.le_of_dvd (NeZero.pos Q) h))
    exact ⟨hd.gcd_eq.symm.trans u, (hd.of_dvd (Nat.gcd_dvd_left _ _)).symm.trans
      ((show (d : ℕ) ≡ 7 [MOD 8] from seven).of_dvd (Nat.gcd_dvd_right _ _))⟩
  · rintro ⟨u, meet⟩ B
    exact exists_seven_twist_in_class u meet hβ H B


end New
