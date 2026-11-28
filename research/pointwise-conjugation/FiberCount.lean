import Triangle
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement

open Matrix

namespace Hearthline.ThreeMarks

variable {R : Type*} [CommRing R]

/-- The columns of a matrix realizing the scaled swap. The first column is specified
by the mark (1,0); multiplying the second column by m gives the requested image of (0,m). -/
def Completion (m k : R) := {T : Matrix (Fin 2) (Fin 2) R //
  T 0 0 = 0 ∧ T 1 0 = k*m ∧ m*T 0 1 = k ∧ m*T 1 1 = 0}

/-- The four entry conditions are equivalent to applying the actual matrix to the two
marked column vectors. -/
theorem acts_on_marks_iff (m k : R) (T : Matrix (Fin 2) (Fin 2) R) :
    (T *ᵥ ![1,0] = ![0,k*m] ∧ T *ᵥ ![0,m] = ![k,0]) ↔
      T 0 0 = 0 ∧ T 1 0 = k*m ∧ m*T 0 1 = k ∧ m*T 1 1 = 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, funext_iff, Fin.forall_fin_two, mul_comm,
    and_assoc]

def matrixEquiv (m k : R) :
    {T : Matrix (Fin 2) (Fin 2) R // T *ᵥ ![1,0] = ![0,k*m] ∧ T *ᵥ ![0,m] = ![k,0]} ≃
      Completion m k where
  toFun T := ⟨T.val, (acts_on_marks_iff m k T.val).1 T.property⟩
  invFun T := ⟨T.val, (acts_on_marks_iff m k T.val).2 T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Both free entries of the second column can be counted independently. -/
def columns (m k : R) : Completion m k ≃ ({b : R // m*b=k} × {d : R // m*d=0}) where
  toFun T := (⟨T.val 0 1, T.property.2.2.1⟩, ⟨T.val 1 1, T.property.2.2.2⟩)
  invFun v := ⟨!![0,v.1.val;k*m,v.2.val],rfl,rfl,v.1.property,v.2.property⟩
  left_inv T := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact T.property.1.symm
    · rfl
    · exact T.property.2.1.symm
    · rfl
  right_inv _ := rfl

private def fiberEquiv (m k b : R) (hb : m*b=k) :
    {x : R // m*x=k} ≃ {x : R // m*x=0} where
  toFun x := ⟨x.val-b, by rw [mul_sub, x.property, hb, sub_self]⟩
  invFun x := ⟨x.val+b, by rw [mul_add, x.property, hb, zero_add]⟩
  left_inv x := Subtype.ext <| sub_add_cancel _ _
  right_inv x := Subtype.ext <| add_sub_cancel_right _ _

private theorem kernel_card (m n : ℕ) [NeZero n] :
    Nat.card {b : ZMod n // (m : ZMod n)*b = 0} = m.gcd n := by
  let f := AddMonoidHom.mulLeft (m : ZMod n)
  have ran : f.range = AddSubgroup.zmultiples (m : ZMod n) := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      obtain ⟨t,rfl⟩ := ZMod.intCast_surjective b
      exact ⟨t, by simp [f, zsmul_eq_mul, mul_comm]⟩
    · rintro ⟨t,rfl⟩
      exact ⟨(t : ZMod n), by simp [f, zsmul_eq_mul, mul_comm]⟩
  have h := AddSubgroup.card_ker_mul_card_range f
  rw [ran, Nat.card_zmultiples, ZMod.addOrderOf_coe m (NeZero.ne n), show Nat.card (ZMod n) = n from (Nat.card_eq_fintype_card.trans (ZMod.card n))] at h
  change Nat.card f.ker = m.gcd n
  rw [Nat.gcd_comm]
  have pos : 0 < n / n.gcd m := Nat.div_pos (Nat.gcd_le_left m (NeZero.pos n))
    (Nat.gcd_pos_of_pos_left m (NeZero.pos n))
  exact Nat.eq_of_mul_eq_mul_right pos (h.trans (Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)).symm)

/-- Exact cardinality of all ambient matrices realizing the scaled swap modulo n. -/
theorem completion_count (m n k : ℕ) [NeZero n] :
    Nat.card (Completion (m : ZMod n) (k : ZMod n)) =
      if m.gcd n ∣ k then (m.gcd n)^2 else 0 := by
  classical
  rw [Nat.card_congr (columns _ _), Nat.card_prod, kernel_card]
  split_ifs with h
  · obtain ⟨b, hb⟩ := (dvd_mod_iff m n k).2 h
    rw [Nat.card_congr (fiberEquiv (m : ZMod n) (k : ZMod n) b hb.symm), kernel_card, sq]
  · have : IsEmpty {b : ZMod n // (m : ZMod n)*b = (k : ZMod n)} :=
      ⟨fun t ↦ h ((dvd_mod_iff m n k).1 ⟨t.val,t.property.symm⟩)⟩
    simp

/-- Count matrices by the two prescribed images under matrix-vector multiplication. -/
theorem count_by_images (m n k : ℕ) [NeZero n] :
    Nat.card {T : Matrix (Fin 2) (Fin 2) (ZMod n) //
      T *ᵥ ![1,0] = ![0,(k:ZMod n)*m] ∧ T *ᵥ ![0,(m:ZMod n)] = ![(k:ZMod n),0]} =
      if m.gcd n ∣ k then (m.gcd n)^2 else 0 :=
  (Nat.card_congr (matrixEquiv _ _)).trans (completion_count m n k)

example : Nat.card (Completion (17 : ZMod 289) 17) = 289 := by
  exact (completion_count 17 289 17).trans (by decide +kernel)

end Hearthline.ThreeMarks
