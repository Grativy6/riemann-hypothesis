import Lib.ClassField.Places.DecompositionCompletion

namespace Hearthline

/-- Compare two decompositions of one reading. The position type only has multiplication.
The update maps can be arbitrary functions. -/
theorem balance_iff {P V : Type*} [Mul P] [AddCancelCommMonoid V]
    {A : P → V → V} {x : P → V} (law : ∀ g h, x (g*h) = x g + A g (x h))
    {u v w : P} (same : x (u*v) = x (v*w)) :
    x u = A v (x w) ↔ A u (x v) = x v := by
  have eq : x u + A u (x v) = A v (x w) + x v :=
    (law u v).symm.trans (same.trans ((law v w).trans (add_comm _ _)))
  constructor
  · intro h
    rw [h] at eq
    exact add_left_cancel eq
  · intro h
    rw [h] at eq
    exact add_right_cancel eq

variable {G A V : Type*} [Group G] [AddCancelCommMonoid V] [DistribSMul A V]
  {a : G → A} {x : G → V} (law : ∀ g h, x (g*h) = x g + a g • x h)

include law

/-- In the new frame cancellation at the common product alone makes this test exact. -/
theorem fixed_after_iff (s g : G) :
    x (s*g*s⁻¹) = a s • x g ↔ a (s*g*s⁻¹) • x s = x s :=
  balance_iff law (by simp [mul_assoc])

/-- For additive updates the one fixed reading from before the change of frame is also
necessary. Its converse follows by turning the same calculation around at the inverse. -/
theorem pointwise_iff (s g : G) :
    x (s*g*s⁻¹) = a s • x g ↔ a g • x s⁻¹ = x s⁻¹ := by
  refine ⟨fun transported ↦ ?_, fun fixed ↦ New.cocycle_conj_eq_smul law fixed⟩
  have fixed := (fixed_after_iff law s g).1 transported
  have back := New.cocycle_conj_eq_smul law (g := s*g*s⁻¹) (γ := s⁻¹) (by simpa only [inv_inv] using fixed)
  simpa only [inv_mul_cancel_left, inv_inv, mul_assoc, inv_mul_cancel, mul_one, one_mul]
    using (fixed_after_iff law s⁻¹ (s*g*s⁻¹)).1 back

/-- The value at the identity is forced to vanish if any update fixes any reading. -/
theorem origin_zero_of_fixed {g h : G} (fixed : a g • x h = x h) : x 1 = 0 := by
  have sum : x (g*h) = x g + x h := by rw [law, fixed]
  have at_one (k : G) : x 1 + a 1 • x k = x k := by simpa only [one_mul] using (law 1 k).symm
  have pair := at_one (g*h)
  rw [sum, smul_add, ← add_assoc, at_one g] at pair
  simpa only [add_left_cancel pair, add_eq_right] using at_one h

/-- Thus even one correctly transported value forces normalization, without a prior
assumption that the updates form a representation on V. -/
theorem origin_zero_of_transport {s g : G} (h : x (s*g*s⁻¹) = a s • x g) : x 1 = 0 :=
  origin_zero_of_fixed law ((pointwise_iff law s g).1 h)

end Hearthline
