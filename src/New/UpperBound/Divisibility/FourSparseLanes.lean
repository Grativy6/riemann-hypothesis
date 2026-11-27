module

public import New.UpperBound.Divisibility.CollisionPrimeFloor
public import New.UpperBound.Divisibility.OrientedPrime
public import New.UpperBound.Divisibility.TaggedSparseArithmetic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic

/-!
# The odd components of four chosen residues

At the prime two, the residues modulo seven and nine restrict each short orbit to two
of the three allowed odd components. Three distinct returns would need three.
-/

@[expose] public section

namespace ColoredSparse

/-- The four target offsets modulo nine have only three odd-component choices.
Both offsets 0 and 36 use the first choice. -/
def oddLane : Fin 4 → ℕ := ![0,0,6,1]

def squaredAtNine (i : Fin 4) : ZMod 9 := (1 + 18480 * oddLane i : ℕ)^2

lemma same_nine_has_repeat (x y z : Fin 4)
    (hy : squaredAtNine y = squaredAtNine x) (hz : squaredAtNine z = squaredAtNine x) :
    oddLane x = oddLane y ∨ oddLane x = oddLane z ∨ oddLane y = oddLane z := by
  have check : ∀ i j k : Fin 4, squaredAtNine j = squaredAtNine i → squaredAtNine k = squaredAtNine i →
      oddLane i = oddLane j ∨ oddLane i = oddLane k ∨ oddLane j = oddLane k := by decide
  exact check x y z hy hz

lemma four_at_nine_of_seven {i : ℕ} (h : (4 : ZMod 7)^i = 1) : (4 : ZMod 9)^i = 1 := by
  have order : orderOf (4 : ZMod 7) = 3 := by
    apply (orderOf_eq_iff (by decide : 0 < 3)).2
    refine ⟨by decide, ?_⟩
    intro j hj hj'
    interval_cases j <;> decide
  have hdiv := orderOf_dvd_iff_pow_eq_one.2 h
  rw [order] at hdiv
  obtain ⟨n,rfl⟩ := hdiv
  rw [pow_mul, show (4:ZMod 9)^3 = 1 by decide, one_pow]

/-- Three visits at 0 < i < j below the order of the generator need three different
labels when the ratio of a label to itself reads one. -/
theorem short_walk_needs_three {G A : Type*} [Monoid G] (g : G) (compare : A → A → G)
    (self : ∀ a, compare a a = 1) {x y z : A} {i j : ℕ}
    (hi : 0 < i) (hij : i < j) (hj : j < orderOf g)
    (yi : compare x y = g^i) (zj : compare x z = g^j) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  refine ⟨?_,?_,?_⟩
  · rintro rfl
    exact (not_le_of_gt (hij.trans hj)) (orderOf_le_of_pow_eq_one hi (yi.symm.trans (self _)))
  · rintro rfl
    exact (not_le_of_gt hj) (orderOf_le_of_pow_eq_one (hi.trans hij) (zj.symm.trans (self _)))
  · rintro rfl
    exact hij.ne (pow_injOn_Iio_orderOf (x := g) (hij.trans hj) hj (yi.symm.trans zj))

/-- The odd-coordinate part of the prime-two check needs only the three displayed lanes.
Modulo seven the squared ratios are one; reducing them modulo nine forces a repeated
lane, which is incompatible with the two nonzero short returns. -/
theorem impossible_prime_two_lanes {G : Type*} [Monoid G] (g : G) (compare : ℕ → ℕ → G)
    (self : ∀ a, compare a a = 1) (x y z : Fin 4) {i j : ℕ}
    (hi : 0 < i) (hij : i < j) (hj : j < orderOf g)
    (y7 : (4 : ZMod 7)^i = 1) (z7 : (4 : ZMod 7)^j = 1)
    (y9 : squaredAtNine y = squaredAtNine x * (4 : ZMod 9)^i)
    (z9 : squaredAtNine z = squaredAtNine x * (4 : ZMod 9)^j)
    (yG : compare (oddLane x) (oddLane y) = g^i)
    (zG : compare (oddLane x) (oddLane z) = g^j) : False := by
  rw [four_at_nine_of_seven y7,mul_one] at y9
  rw [four_at_nine_of_seven z7,mul_one] at z9
  have distinct := short_walk_needs_three g compare self hi hij hj yG zG
  rcases same_nine_has_repeat x y z y9 z9 with h | h | h
  · exact distinct.1 h
  · exact distinct.2.1 h
  · exact distinct.2.2 h

end ColoredSparse

namespace New.Data.CollisionPrimeExample
open NumberField Finset ColoredSparse

noncomputable def oddLanePlace (s label : ℕ) : params.Φ s :=
  params.placeOfInt s (-((1+params.q₀*label : ℕ) : ℤ))

lemma oddLanePlace_val {s q : ℕ} (d : q ∣ params.q₁ s) (label : ℕ) :
    (params.placeClass d (oddLanePlace s label) : ZMod q) = -((1+18480*label : ℕ) : ZMod q) := by
  have cop : IsCoprime (-((1+params.q₀*label : ℕ) : ℤ)) (params.q₀ : ℤ) :=
    ⟨-1, -(label:ℤ), by push_cast; ring⟩
  simpa [oddLanePlace, show params.q₀ = 18480 from rfl] using (params.placeClass_placeOfInt (s := s) (h_dvd := d) cop)

private lemma two_square_step {s q i : ℕ} (hq : q ∣ params.q₁ s) (hc : Nat.Coprime 2 q)
    {x y : params.Φ s} {e : ℤˣ}
    (h : (params.placeClass (Nat.ordCompl_dvd (params.q₁ s) 2) (y/x)).val = (e : ℤ) * 2^i) :
    (params.placeClass hq y : ZMod q)^2 =
      (params.placeClass hq x : ZMod q)^2 * (4:ZMod q)^i := by
  let φ := params.placeClass hq
  have sq := params.placeClass_sq_eq Nat.prime_two h hq hc
  simp only [Nat.cast_ofNat] at sq
  calc (φ y : ZMod q)^2 = (φ (y/x) : ZMod q)^2*(φ x : ZMod q)^2 := by
          rw [← mul_pow, ← Units.val_mul, ← map_mul, div_mul_cancel]
    _ = _ := by
      change (params.placeClass hq (y/x) : ZMod q)^2 * _ = _
      rw [sq, pow_mul, show (2:ZMod q)^2 = 4 by ring, mul_comm]

/-- A sufficient condition on actual tower places for the complete ell=2 part of IsSparse.
The four labels can be assigned in any proportions, provided their odd components agree
with the specified three lanes. -/
theorem prime_two_clear {s : ℕ} (S : Finset (params.Φ s)) (tag : params.Φ s → Fin 4)
    (hbase : ∀ σ ∈ S, params.placeClass (params.q₀.dvd_mul_right (towerDeg s)) σ = -1)
    (hd : 3^(Nat.log 3 s+5) ∣ params.q₁ s)
    (lanes : ∀ σ ∈ S, params.placeClass hd σ = params.placeClass hd (oddLanePlace s (oddLane (tag σ))))
    {i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j < l₀ s) :
    let φ := params.placeClass (Nat.ordCompl_dvd (params.q₁ s) 2)
    ¬∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, ∃ e e' : ℤˣ,
        (φ (y/x)).val = (e : ℤ)*2^i ∧ (φ (z/x)).val = (e' : ℤ)*2^j := by
  classical
  intro φ
  rintro ⟨x,hx,y,hy,z,hz,e,e',yi,zj⟩
  let c := Nat.log 3 s+5
  have hseven : 7 ∣ params.q₀ := by decide
  have h7 := hseven.trans (params.q₀.dvd_mul_right (towerDeg s))
  have h9small : 9 ∣ 3^c := pow_dvd_pow 3 (show 2 ≤ c by dsimp [c]; omega)
  have h9 := h9small.trans hd
  have seven (a : params.Φ s) (ha : a ∈ S) : (params.placeClass h7 a : ZMod 7) = -1 := by
    have red := Parameters.reduce_placeClass hseven (params.q₀.dvd_mul_right (towerDeg s)) a
    rw [hbase a ha] at red
    exact (congrArg (fun v : (ZMod 7)ˣ ↦ (v : ZMod 7)) red.symm).trans (by
      change ZMod.castHom hseven (ZMod 7) (-1) = -1
      rw [map_neg, map_one])
  have nine (a : params.Φ s) (ha : a ∈ S) : (params.placeClass h9 a : ZMod 9)^2 = squaredAtNine (tag a) := by
    have red := congrArg (ZMod.unitsMap h9small) (lanes a ha)
    simp only [Parameters.reduce_placeClass] at red
    rw [red, oddLanePlace_val]
    simp [squaredAtNine]
    ring
  have y7 := two_square_step h7 (by decide) yi
  have z7 := two_square_step h7 (by decide) zj
  rw [seven x hx, seven y hy] at y7
  rw [seven x hx, seven z hz] at z7
  have a7 : (4:ZMod 7)^i = 1 := by simpa using y7.symm
  have b7 : (4:ZMod 7)^j = 1 := by simpa using z7.symm
  have a9 := two_square_step h9 (by decide) yi
  have b9 := two_square_step h9 (by decide) zj
  rw [nine x hx,nine y hy] at a9
  rw [nine x hx,nine z hz] at b9
  let lane := fun n ↦ params.placeClass hd (oddLanePlace s n)
  let compare := fun a b : ℕ ↦ (((lane b)/(lane a) : (ZMod (3^c))ˣ) : ZMod (3^c))^2
  have self (k : ℕ) : compare k k = 1 := by simp [compare]
  have long (a b : params.Φ s) (ha : a ∈ S) (hb : b ∈ S) {k : ℕ} {ε : ℤˣ}
      (h : (φ (b/a)).val = (ε : ℤ)*2^k) : compare (oddLane (tag a)) (oddLane (tag b)) = (4:ZMod (3^c))^k := by
    have raw := params.placeClass_sq_eq Nat.prime_two h hd ((by decide : Nat.Coprime 2 3).pow_right _)
    simp only [Nat.cast_ofNat] at raw
    rw [map_div,lanes a ha, lanes b hb, pow_mul, show (2:ZMod (3^c))^2=4 by ring] at raw
    exact raw
  have order' : orderOf (1 + 3 : ZMod (3^c)) = l₀ s :=
    ZMod.orderOf_one_add_prime Nat.prime_three (by norm_num) _
  have order : orderOf (4 : ZMod (3^c)) = l₀ s := by
    simpa only [show (1+3 : ZMod (3^c)) = 4 by ring] using order'
  exact impossible_prime_two_lanes (4:ZMod (3^c)) compare self _ _ _ hi hij (order ▸ hj) a7 b7 a9 b9
    (long x y hx hy yi) (long x z hx hz zj)

end New.Data.CollisionPrimeExample
