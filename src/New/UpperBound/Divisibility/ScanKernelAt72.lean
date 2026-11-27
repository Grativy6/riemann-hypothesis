module

public import New.UpperBound.Divisibility.OrbitProbeTable
import Mathlib.Tactic

/-!
# The part of a 72-slot histogram invisible to all complementary signed probes

Write a residue uniquely as b+9j with 0≤b<9 and 0≤j<8. The probes with half-periods
36, 18 and 9 force the difference in each such column to be constant. Conversely any
column-constant difference vanishes at all compatible even periods and all orientations.
-/

@[expose] public section
open Finset
namespace New.SixSignatures

abbrev Board72 := Fin 9 → Fin 8 → ℤ

def address72 (b : Fin 9) (j : Fin 8) : ℕ := b.val+9*j.val

def boardScan (z : Board72) (G a : ℕ) : ℤ :=
  ∑ b, ∑ j, z b j * referenceSign G a (address72 b j)

def columnScan (z : Fin 8 → ℤ) (G a : ℕ) : ℤ :=
  ∑ j, z j * referenceSign G a j.val

def step8 : Fin 3 → ℕ := ![4,2,1]

/-- For a period divisible by nine, each measuring location only sees its own column. -/
lemma column_coefficient (s : Fin 3) (chosen b : Fin 9) (a j : Fin 8) :
    referenceSign (9*step8 s) (address72 chosen a) (address72 b j) =
      if b=chosen then referenceSign (step8 s) a j else 0 := by
  have table : ∀ x : Fin 3, ∀ i k : Fin 9, ∀ u v : Fin 8,
      referenceSign (9*step8 x) (address72 i u) (address72 k v) =
        if k=i then referenceSign (step8 x) u v else 0 := by decide
  exact table s chosen b a j

lemma boardScan_column (z : Board72) (s : Fin 3) (b : Fin 9) (a : Fin 8) :
    boardScan z (9*step8 s) (address72 b a) = columnScan (z b) (step8 s) a.val := by
  unfold boardScan
  rw [sum_eq_single b]
  · unfold columnScan
    apply sum_congr rfl
    intro j _
    rw [column_coefficient,ite_eq_left rfl]
  · intro b' _ ne
    apply sum_eq_zero
    intro j _
    rw [column_coefficient,ite_eq_right ne,mul_zero]
  · simp

/-- On eight slots the four opposite-pair differences, the two sums of pairs,
and the one sum of four leave precisely a common additive constant. -/
lemma flat_column_of_three_scans (z : Fin 8 → ℤ) (h4 : ∀ a : Fin 8,columnScan z 4 a=0)
    (h2 : ∀ a : Fin 8,columnScan z 2 a=0) (h1 : columnScan z 1 0=0) :
    ∀ i,z i=z 0 := by
  have a := h4 0
  have b := h4 1
  have c := h4 2
  have d := h4 3
  have e := h2 0
  have f := h2 1
  norm_num [columnScan,referenceSign,Nat.ModEq,Fin.sum_univ_succ] at a b c d e f h1
  intro i
  fin_cases i
  · rfl
  · change z 1=z 0;omega
  · change z 2=z 0;omega
  · change z 3=z 0;omega
  · change z 4=z 0;omega
  · change z 5=z 0;omega
  · change z 6=z 0;omega
  · change z 7=z 0;omega

theorem flat_of_three (z : Board72) (h36 : ∀ a,boardScan z 36 a=0)
    (h18 : ∀ a,boardScan z 18 a=0) (h9 : ∀ a,boardScan z 9 a=0) :
    ∀ b j,z b j=z b 0 := by
  intro b
  apply flat_column_of_three_scans
  · intro a; exact (boardScan_column z 0 b a).symm.trans (h36 _)
  · intro a; exact (boardScan_column z 1 b a).symm.trans (h18 _)
  · exact (boardScan_column z 2 b 0).symm.trans (h9 _)

set_option maxRecDepth 8192 in
/-- For every compatible period, each entire column contains equally many positive and
negative contributions. Its total charge is zero. -/
lemma whole_column_neutral {G : ℕ} (div : 2*G ∣ 72) (a : ℕ) (b : Fin 9) :
    (∑ j : Fin 8, referenceSign G a (address72 b j)) = 0 := by
  have gBound := Nat.le_of_dvd (by decide : 0<72) div
  have table : ∀ g : Fin 37, 2*g.val ∣ 72 → ∀ u : Fin 72, ∀ c : Fin 9,
      (∑ j : Fin 8, referenceSign g u (address72 c j))=0 := by decide
  have eq := table ⟨G,by omega⟩ div ⟨a%72,Nat.mod_lt _ (by decide)⟩ b
  have per := (Nat.mod_modEq a 72).of_dvd div
  simpa only [referenceSign_anchor per] using eq

/-- The common kernel of every signed probe on the board is the space of histograms
constant on each residue modulo nine. Three of the actual primes already force this. -/
theorem all_scans_zero_iff (z : Board72) :
    (∀ G,2*G ∣ 72 → ∀ a,boardScan z G a=0) ↔ ∀ b j,z b j=z b 0 := by
  constructor
  · intro h
    exact flat_of_three z (h 36 (by decide)) (h 18 (by decide)) (h 9 (by decide))
  · intro flat G div a
    unfold boardScan
    apply sum_eq_zero
    intro b _
    calc (∑ j,z b j*referenceSign G a (address72 b j)) =
         ∑ j,z b 0*referenceSign G a (address72 b j) :=
           sum_congr rfl fun j _ ↦ congrArg (· * referenceSign G a (address72 b j)) (flat b j)
      _ = 0 := by rw [← mul_sum,whole_column_neutral div,mul_zero]

/-- Equality at just the three largest dyadic stages already forces all nine column
offsets in the difference. -/
theorem flat_difference_of_three (u v : Board72)
    (h36 : ∀ a,boardScan u 36 a=boardScan v 36 a)
    (h18 : ∀ a,boardScan u 18 a=boardScan v 18 a)
    (h9 : ∀ a,boardScan u 9 a=boardScan v 9 a) :
    ∀ b j,u b j-v b j=u b 0-v b 0 := by
  let z : Board72 := fun b j ↦ u b j-v b j
  have sub (G a : ℕ) : boardScan z G a = boardScan u G a-boardScan v G a := by
    simp [boardScan,z,sub_mul,sum_sub_distrib]
  exact flat_of_three z (fun a ↦ (sub _ _).trans (sub_eq_zero.2 (h36 a)))
    (fun a ↦ (sub _ _).trans (sub_eq_zero.2 (h18 a)))
    (fun a ↦ (sub _ _).trans (sub_eq_zero.2 (h9 a)))

/-- Equal scans at all reference primes mean precisely equal shapes up to the nine
constant column offsets. This is a difference of integer histograms. -/
theorem equal_scans_iff (h h' : Board72) :
    (∀ G,2*G ∣ 72 → ∀ a,boardScan h G a=boardScan h' G a) ↔
    ∀ b j,h b j-h' b j = h b 0-h' b 0 := by
  let z : Board72 := fun b j ↦ h b j-h' b j
  have sub (G a : ℕ) : boardScan z G a = boardScan h G a-boardScan h' G a := by
    simp [boardScan,z,sub_mul,sum_sub_distrib]
  change _ ↔ ∀ b j,z b j=z b 0
  rw [← all_scans_zero_iff]
  simp only [sub,sub_eq_zero]

/-- Keeping the total puts one relation on the nine additive column offsets. -/
theorem fixed_mass_kernel (u v : Board72) :
    ((∑ b,∑ j,u b j)=(∑ b,∑ j,v b j) ∧ ∀ G,2*G ∣ 72 → ∀ a,boardScan u G a=boardScan v G a) ↔
    ∃ g : Fin 9 → ℤ, (∑ b,g b)=0 ∧ ∀ b j,u b j-v b j=g b := by
  have mass_of (g : Fin 9 → ℤ) (flat : ∀ b j,u b j-v b j=g b) :
      (∑ b,∑ j,u b j)-(∑ b,∑ j,v b j) = 8*∑ b,g b := by
    calc _ = ∑ b,∑ j,(u b j-v b j) := by simp [sum_sub_distrib]
      _ = ∑ b,∑ _j : Fin 8,g b := by simp only [flat]
      _ = _ := by simp [mul_sum]
  constructor
  · rintro ⟨mass,scans⟩
    let g := fun b ↦ u b 0-v b 0
    have flat := (equal_scans_iff _ _).1 scans
    refine ⟨g,?_,flat⟩
    have eq := mass_of g flat
    rw [mass,sub_self] at eq
    omega
  · rintro ⟨g,zero,flat⟩
    have eq := mass_of g flat
    rw [zero,mul_zero] at eq
    exact ⟨sub_eq_zero.1 eq,(equal_scans_iff _ _).2 fun b j ↦ (flat b j).trans (flat b 0).symm⟩

end New.SixSignatures
