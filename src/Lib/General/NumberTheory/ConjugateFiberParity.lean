module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Conjugate observations in an odd finite sample

Count each fiber modulo two. The conjugation pairs every observed value with its conjugate.
An odd total forces some pair to have different parities.
-/

@[expose] public section

open Finset

namespace Finset

open scoped Classical in
/-- An odd collection of observations detects an odd difference between some two conjugate
fibers whenever none of the observed values is fixed by conjugation. -/
theorem exists_unmatched_mod_two {α β : Type*} [InvolutiveStar β] (S : Finset α) (f : α → β)
    (ho : Odd #S) (no_fixed : ∀ a ∈ S, star (f a) ≠ f a) :
    ∃ l ∈ S.image f ∪ (S.image f).image star,
      (#{a ∈ S | f a = l} : ZMod 2) ≠ (#{a ∈ S | f a = star l} : ZMod 2) := by
  classical
  let I := S.image f
  let J := I ∪ I.image star
  let n := fun l : β ↦ #{a ∈ S | f a = l}
  have closed (l : β) (hl : l ∈ J) : star l ∈ J := by
    rcases mem_union.1 hl with h | h
    · exact mem_union_right _ (mem_image_of_mem _ h)
    · obtain ⟨r,hr,rfl⟩ := mem_image.1 h
      simpa only [star_star] using mem_union_left (I.image star) hr
  have free (l : β) (hl : l ∈ J) : star l ≠ l := by
    rcases mem_union.1 hl with h | h
    · obtain ⟨a,ha,rfl⟩ := mem_image.1 h
      exact no_fixed a ha
    · obtain ⟨r,hr,rfl⟩ := mem_image.1 h
      obtain ⟨a,ha,rfl⟩ := mem_image.1 hr
      simpa only [star_star, ne_comm] using no_fixed a ha
  have total : #S = ∑ l ∈ J, n l := card_eq_sum_card_fiberwise (f := f)
    (fun a ha ↦ mem_union_left _ (mem_image_of_mem _ ha))
  by_contra! hall
  have paired : ∑ l ∈ J, (n l : ZMod 2) = 0 := by
    refine sum_involution (fun l _ ↦ star l) (fun l hl ↦ ?_)
      (fun l hl _ ↦ free l hl) closed (fun l _ ↦ star_star l)
    have h : (n l : ZMod 2) = n (star l) := hall l hl
    rw [← h, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  have hzero : (#S : ZMod 2) = 0 := by
    rw [total, Nat.cast_sum]
    exact paired
  obtain ⟨k, hk⟩ := ho
  rw [hk] at hzero
  push_cast at hzero
  simp [show (2 : ZMod 2) = 0 by decide] at hzero

end Finset
