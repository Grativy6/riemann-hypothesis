module

public import New.UpperBound.Size.ShortColumns
import Lib.CM.FormalGroup.PrimeNotation
import Mathlib.Tactic

/-!
# The finite long-row cost of a collision

The partner weight is at least a/x₁. Thus a collision of long rows can cost at most
(a/pᵉ − a/x₁)₊ at exponent e. A prime power reaching x₁ contributes zero, and the
whole charge can be evaluated as a finite sum.
-/

@[expose] public section

open Finset Real
namespace New.Data

variable {P : Parameters} (D : Data P) (p : ℕ)

open scoped Classical in
/-- The positive part lost at a colliding long row of weight a against the least partner weight. -/
noncomputable def collisionDeficitAt (S : Finset D.Φ) (τ : D.Φ) (e : ℕ) : ℝ :=
  if D.IsCollision p S τ e then ((D.a : ℝ) / p^e - D.a/D.x₁)⁺ else 0

/-- Only exponents below the first power reaching x₁ can contribute a long-row deficit. -/
noncomputable def collisionDeficit (S : Finset D.Φ) : ℝ :=
  ∑ τ : D.Φ, ∑ e ∈ range (p.clog ⌈D.x₁⌉₊), D.collisionDeficitAt p S τ e

/-- Each colliding long row contributes a nonnegative deficit. -/
lemma collisionDeficitAt_nonneg (S : Finset D.Φ) (τ : D.Φ) (e : ℕ) :
    0 ≤ D.collisionDeficitAt p S τ e := by
  unfold collisionDeficitAt
  split_ifs <;> positivity

/-- The total finite deficit is nonnegative. -/
lemma collisionDeficit_nonneg (S : Finset D.Φ) : 0 ≤ D.collisionDeficit p S :=
  sum_nonneg fun τ _ ↦ sum_nonneg fun e _ ↦ D.collisionDeficitAt_nonneg p S τ e

variable {p} [hp : Fact p.Prime]

omit hp in
/-- A prime power reaching the cutoff gives no long-row deficit. -/
lemma collisionDeficitAt_eq_zero_of_le_pow (S : Finset D.Φ) (τ : D.Φ) {e : ℕ}
    (hx : D.x₁ ≤ (p : ℝ)^e) : D.collisionDeficitAt p S τ e = 0 := by
  unfold collisionDeficitAt
  split_ifs with hc
  · exact posPart_eq_zero.2 (sub_nonpos.2
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (HasLogBound.pos D) hx))
  · rfl

/-- The series for a place is exactly its sum below the cutoff. -/
lemma hasSum_collisionDeficitAt (S : Finset D.Φ) (τ : D.Φ) :
    HasSum (D.collisionDeficitAt p S τ)
      (∑ e ∈ range (p.clog ⌈D.x₁⌉₊), D.collisionDeficitAt p S τ e) := by
  apply hasSum_sum_of_ne_finset_zero
  intro e he
  apply D.collisionDeficitAt_eq_zero_of_le_pow
  exact (Nat.le_ceil D.x₁).trans <| mod_cast (Nat.le_pow_clog hp.out.one_lt _).trans
    (Nat.pow_le_pow_right hp.out.pos (by simpa using he))

open scoped Classical in
omit hp in
/-- The positive part at a collision is bounded by the full reciprocal weight. -/
lemma collisionDeficitAt_le (S : Finset D.Φ) (τ : D.Φ) (e : ℕ) :
    D.collisionDeficitAt p S τ e ≤ if D.IsCollision p S τ e then (D.a / p^e : ℝ) else 0 := by
  unfold collisionDeficitAt
  split_ifs
  · rw [posPart_def]
    exact max_le (sub_le_self _ (by positivity)) (by positivity)
  · rfl

open scoped Classical in
/-- Charging the full reciprocal at every collision bounds the finite deficit. -/
lemma collisionDeficit_le_collisionSum (S : Finset D.Φ) :
    D.collisionDeficit p S ≤ D.collisionSum p S := by
  classical
  apply sum_le_sum
  intro τ _
  have hraw : Summable fun e : ℕ ↦ if D.IsCollision p S τ e then (D.a / p^e : ℝ) else 0 := by
    refine (hasSum_div_pow_positivePartnerExponents P.d p D.a).summable.of_nonneg_of_le
      (fun e ↦ by positivity) fun e ↦ ?_
    by_cases hc : D.IsCollision p S τ e
    · rw [ite_eq_left hc, ite_eq_left hc.1]
    · rw [ite_eq_right hc]
      positivity
  exact hasSum_le (D.collisionDeficitAt_le S τ) (D.hasSum_collisionDeficitAt S τ) hraw.hasSum

end New.Data
