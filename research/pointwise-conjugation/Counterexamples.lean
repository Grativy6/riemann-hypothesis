import ReadingTransport
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Hearthline.Controls

abbrev Labels := Fin 3
abbrev Perm := Equiv.Perm Labels
abbrev Row := Labels → ℤ

def permute (g : Perm) (v : Row) : Row := fun i ↦ v (g.symm i)
def markedRow : Row := ![2,1,0]
def displacement (g : Perm) : Row := markedRow - permute g markedRow

theorem cocycle (g h : Perm) :
    displacement (g*h) = displacement g + permute g (displacement h) := by
  funext i
  change markedRow i - markedRow (h.symm (g.symm i)) =
    (markedRow i - markedRow (g.symm i)) +
    (markedRow (g.symm i) - markedRow (h.symm (g.symm i)))
  abel

def swap01 : Perm := Equiv.swap 0 1
def turn : Perm := Equiv.swap 0 1 * Equiv.swap 1 2

/-- The inverse reading, the forward reading and the transported value can each be
calculated by permuting three coordinates. -/
theorem strict_pointwise_example :
    displacement turn⁻¹ = ![1,1,-2] ∧
    permute swap01 (displacement turn⁻¹) = displacement turn⁻¹ ∧
    permute swap01 (displacement turn) ≠ displacement turn ∧
    displacement swap01 = ![1,-1,0] ∧
    displacement (turn*swap01*turn⁻¹) = ![0,1,-1] ∧
    displacement (turn*swap01*turn⁻¹) = permute turn (displacement swap01) := by
  decide +kernel

/-- A nonzero constant offset with zero additive operators obeys the raw equation. -/
example (G : Type*) [Group G] :
    (∀ g h : G, (fun _ : G ↦ (17:ℤ)) (g*h) =
      (fun _ : G ↦ (17:ℤ)) g + (0 : ℤ →+ ℤ) ((fun _ : G ↦ (17:ℤ)) h)) ∧
      (fun _ : G ↦ (17:ℤ)) 1 ≠ 0 := by simp

/-- A three-coordinate instrument with a permanent 17, one moving coordinate and one
coordinate never reported. The operators are additive on the whole ambient group. -/
def offsetReading (i : ZMod 2) : Fin 3 → ℤ := ![if i=0 then 0 else 2, 17, 0]
def ambientUpdate (i : ZMod 2) (z : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![if i=0 then z 0 else -z 0, 0, if i=0 then 0 else 2*z 2]

theorem ambient_additive (i : ZMod 2) (u v : Fin 3 → ℤ) :
    ambientUpdate i (u+v) = ambientUpdate i u + ambientUpdate i v := by
  ext j
  fin_cases j <;> by_cases h : i=0 <;> simp [ambientUpdate, h, mul_add, add_comm]

theorem ambient_need_not_compose :
    (∀ i j : ZMod 2, offsetReading (i+j) = offsetReading i + ambientUpdate i (offsetReading j)) ∧
    offsetReading 0 = ![0,17,0] ∧
    ambientUpdate 1 (ambientUpdate 1 ![0,0,1]) ≠ ambientUpdate (1+1) ![0,0,1] := by
  decide +kernel

/-- Three signed readings of the cyclic positions 0, 1, 2. -/
def signed (i : ZMod 3) : ℤ := if i = 0 then 0 else if i = 1 then 1 else -1
def update (g : ZMod 3) (v : ℤ) : ℤ := signed (g + (v : ZMod 3)) - signed g

theorem signed_round_trip (i : ZMod 3) : ((signed i : ℤ) : ZMod 3) = i := by
  exact (by decide +kernel : ∀ j : ZMod 3, ((signed j : ℤ) : ZMod 3) = j) i

/-- The raw transition equation and zero preservation both hold. The transition is not
additive, and fixing the inverse reading fails to imply transport in the forward direction. -/
theorem nonadditive_boundary :
    (∀ g h : ZMod 3, signed (g+h) = signed g + update g (signed h)) ∧
    (∀ g : ZMod 3, update g 0 = 0) ∧
    update 1 (signed (-1)) = signed (-1) ∧
    signed (1+1-1) ≠ update 1 (signed 1) ∧
    update 1 ((1:ℤ)+(-1)) ≠ update 1 1 + update 1 (-1) := by
  refine ⟨fun g h ↦ ?_, fun g ↦ ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · rw [update, signed_round_trip]
    abel
  · simp [update]

def boolUpdate (g : ZMod 2) (v : Bool) : Bool := if g = 0 then v else false

/-- With Boolean join instead of cancellative addition, both updates distribute.
The constant true reading obeys the rule. Transport nevertheless fails. -/
theorem noncancellative_boundary :
    (∀ (g : ZMod 2) (v w : Bool), boolUpdate g (v || w) =
      (boolUpdate g v || boolUpdate g w)) ∧
    (∀ g h : ZMod 2, (fun _ : ZMod 2 ↦ true) (g+h) = (true || boolUpdate g true)) ∧
    boolUpdate 0 true = true ∧ true ≠ boolUpdate 1 true ∧
    (true || false) = (true || true) ∧ false ≠ true := by decide +kernel

end Hearthline.Controls
