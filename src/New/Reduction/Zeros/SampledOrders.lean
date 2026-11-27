module

public import New.Reduction.Zeros.MatchedStrip
public import New.Reduction.Zeros.WeightedCountRectangle
public import New.Reduction.Zeros.SampleMesh
public import New.Reduction.Zeros.Criterion
import Mathlib.Tactic

/-!
# At a fixed prime each power of spacing gives a further strip

Start at Re > 1, where both products are nonzero. A match of their orders
above θ controls the sharp count. The nearby upper readings improve the real
remainder exponent; the one-prime Landau comparison then improves the region
in which the orders match. No prime is selected during the induction.
-/

@[expose] public section

open Nat Real Complex Filter Finset
namespace New.PrimeCutoff

/-- A match of orders controls the sharp weighted count at every power strictly
inside the matched half-plane. -/
theorem count_of_matched {d q : ℕ} [Fact d.Prime] [NeZero q] {θ b : ℝ}
    (d₂ : d ≠ 2) (cop : q.Coprime d) (hθ : 1 / 2 ≤ θ) (h : θ < b) (hb : b ≤ 1)
    (ord : matchedOrders d q θ) :
    ∃ B : ℝ, ∀ᶠ x : ℝ in atTop, |countError d q x| ≤ B * x ^ b := by
  let σ := (θ + b) / 2
  have ts : θ < σ := by dsimp [σ]; linarith
  have sb : σ < b := by dsimp [σ]; linarith
  obtain ⟨D, D₀, rect⟩ := rectangle_of_matched hθ ts (sb.trans_le hb) ord
  exact weighted_count_of_rectangle (hθ.trans ts.le) (sb.trans_le hb) sb D₀
    (fun s hs ↦ (regularMean_analytic ord (ts.trans_le hs)).differentiableAt)
    (fun _ hs ↦ regularMean_series d₂ cop hs) rect

/-- At one fixed prime, sufficiently frequent upper readings imply equality of
all zero orders right of β. A separate real-axis dominance hypothesis supplies
the sign of the residues in the one-sided Landau theorem. -/
theorem matched_of_nearby {d q : ℕ} [Fact d.Prime] [NeZero q] {β δ : ℝ}
    (h8 : d % 8 = 7) (cop : q.Coprime d) (β₀ : 1 / 2 < β) (β₁ : β < 1) (δp : 0 < δ)
    (samples : nearbyUpper d q β δ)
    (axis : ∀ t : ℝ, β < t → t < 1 →
      (∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL (quadTwist χ d)) t) ≤
      ∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL χ) t) :
    matchedOrders d q β := by
  let α := δ / 2
  have αp : 0 < α := by dsimp [α]; positivity
  let edge := fun n : ℕ ↦ max β (1 - (n : ℝ) * α)
  have lower (n : ℕ) : β ≤ edge n := le_max_left _ _
  have finer (n : ℕ) : edge n - α ≤ edge (n + 1) := by
    change max β (1 - (n : ℝ) * α) - α ≤ max β (1 - ((n + 1 : ℕ) : ℝ) * α)
    rw [sub_le_iff_le_add]
    apply max_le
    · linarith only [le_max_left β (1 - ((n + 1 : ℕ) : ℝ) * α), αp]
    · have h := le_max_right β (1 - ((n + 1 : ℕ) : ℝ) * α)
      push_cast at h ⊢
      linarith only [h]
  have step (n : ℕ) (prev : matchedOrders d q (edge n)) : matchedOrders d q (edge (n + 1)) := by
    let b := min 1 (edge n + α)
    have b₀ : 0 ≤ b := le_min zero_le_one (by linarith only [lower n, β₀, αp])
    have b₁ : b ≤ 1 := min_le_left _ _
    have counts : ∃ B : ℝ, ∀ᶠ x : ℝ in atTop, |countError d q x| ≤ B * x ^ b := by
      rcases le_or_gt 1 (edge n + α) with easy | interior
      · refine ⟨13,?_⟩
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
        simpa only [b, min_eq_left easy, Real.rpow_one] using abs_countError_le (d := d) (q := q) hx
      · have exp : edge n < b := by dsimp [b]; rw [min_eq_right interior.le]; linarith
        exact count_of_matched (by omega : d ≠ 2) cop (β₀.le.trans (lower n)) exp b₁ prev
    obtain ⟨B, hB⟩ := counts
    have gain : b - δ ≤ edge (n + 1) := by
      have cap : b ≤ edge n + α := min_le_right _ _
      have h := finer n
      dsimp [α] at cap h
      linarith only [cap, h]
    obtain ⟨C, hC⟩ := real_of_nearby_count δp b₀ b₁ (by linarith) β₁.le (lower _) gain samples hB
    intro z hz
    exact sum_entireL_orders_eq_twisted_of_primeRemainder_le h8 cop
      (by linarith only [β₀, lower (n + 1)] : 0 < edge (n + 1)) hC
      (fun t h₁ h₂ ↦ axis t ((lower _).trans_lt h₁) h₂) hz
  have stages (n : ℕ) : matchedOrders d q (edge n) := by
    induction n with
    | zero =>
      intro z hz
      have h : 1 < z.re := by simpa [edge, max_eq_right β₁.le] using hz
      have zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
          analyticOrderNatAt (entireL χ) z = 0 :=
        (analyticOrderNatAt_entireL_eq_zero_iff _ _).2 (entireL_ne_zero _ h.le)
      simp [zero]
    | succ n ih => exact step n ih
  -- This many passes always reach β; the ceiling is taken only after d and δ are fixed.
  let n := ⌈(1 - β) / α⌉₊
  have hn : (1 - β) / α ≤ (n : ℝ) := Nat.le_ceil _
  have last : edge n = β := max_eq_left (by linarith only [(div_le_iff₀ αp).1 hn])
  simpa only [last] using stages n

end New.PrimeCutoff
