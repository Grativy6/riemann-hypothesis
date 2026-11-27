module

public import New.UpperBound.Divisibility.FourSparseLanes
public import New.UpperBound.Divisibility.ThreePrimeGeometry
import Mathlib.Tactic

/-!
# One tower place with both prescribed projections

The offset is chosen by the Chinese remainder theorem before it is turned into a tower
place. Its 2-primary projection is a tagged power, its odd projection is one of three lanes,
and its residue modulo 72 times the base selects the desired offset.
-/

@[expose] public section

open Finset NumberField ThreePrimeEnvelope ColoredSparse
namespace New.Data.CollisionPrimeExample

/-- The odd part of the tower factor, before multiplication by the fixed base modulus. -/
def oddTower (s : ℕ) := 3^(Nat.log 3 s+5)

lemma oddTower_eq (s : ℕ) : oddTower s = 3*l₀ s := by
  unfold oddTower l₀
  rw [show Nat.log 3 s + 5 = (Nat.log 3 s+4)+1 by omega,pow_succ']

lemma oddTower_dvd (s : ℕ) : oddTower s ∣ params.q₁ s :=
  ⟨params.q₀*2^s,by change params.q₀*(oddTower s*2^s)=oddTower s*(params.q₀*2^s); ring⟩

lemma nine_dvd_oddTower (s : ℕ) : 9 ∣ oddTower s :=
  pow_dvd_pow 3 (show 2 ≤ Nat.log 3 s+5 by omega)

lemma joint_dvd_tower {s : ℕ} (hs : 3 ≤ s) : 72*params.q₀ ∣ params.q₁ s := by
  have d : 72 ∣ towerDeg s :=
    Nat.mul_dvd_mul (nine_dvd_oddTower s) (pow_dvd_pow 2 hs)
  simpa only [Nat.mul_comm 72 params.q₀] using Nat.mul_dvd_mul_left params.q₀ d

/-- The class read modulo 72 and the odd lane used for sparseness must agree modulo nine. -/
structure LaneAddress where
  offset : ℕ
  lane : Fin 4
  compatible : oddLane lane ≡ offset [MOD 9]

/-- The four extreme signatures as admissible addresses. -/
def cornerAddress (c : Fin 4) : LaneAddress :=
  ⟨cornerOffset c, c, (by decide : ∀ i : Fin 4, oddLane i ≡ cornerOffset i [MOD 9]) c⟩

@[simp] lemma cornerAddress_offset (c : Fin 4) : (cornerAddress c).offset = cornerOffset c := rfl

def LaneAddress.lowDigit (c : LaneAddress) (s : ℕ) : Fin 8 :=
  ⟨(oddTower s*c.offset)%8, Nat.mod_lt _ (by decide)⟩

lemma exists_lane_offset {s q : ℕ} (hs : 3 ≤ s) (hq : 8 ∣ q) (e : ℕ) (c : LaneAddress) :
    ∃ r : ℕ, 1+params.q₀*r ≡ (1+params.q₀*oddTower s)^(q*e+(c.lowDigit s).val) [MOD params.q₀*2^s] ∧
      1+params.q₀*r ≡ 1+params.q₀*oddLane c.lane [MOD params.q₀*oddTower s] ∧ r ≡ c.offset [MOD 72] := by
  have odd : Odd (oddTower s) := (by decide : Odd (3:ℕ)).pow
  have cop : (2^s).Coprime (oddTower s) :=
    ((by decide : Nat.Coprime 2 3).pow_left s).pow_right _
  exact exists_colored_offset (show 8 ∣ params.q₀ by decide) odd (nine_dvd_oddTower s)
    (pow_dvd_pow 2 hs) hq cop e _ _ c.compatible

noncomputable def lanePlace {s q : ℕ} (hs : 3 ≤ s) (hq : 8 ∣ q) (e : ℕ) (c : LaneAddress) :
    params.Φ s := oddLanePlace s (exists_lane_offset hs hq e c).choose

lemma lanePlace_base {s q : ℕ} (hs : 3 ≤ s) (hq : 8 ∣ q) (e : ℕ) (c : LaneAddress) :
    params.placeClass (params.q₀.dvd_mul_right (towerDeg s)) (lanePlace hs hq e c) = -1 := by
  apply Units.ext
  rw [lanePlace,oddLanePlace_val]
  change -((1 + params.q₀*(exists_lane_offset hs hq e c).choose : ℕ) : ZMod params.q₀) = -1
  simp [ZMod.natCast_self]

lemma lanePlace_odd {s q : ℕ} (hs : 3 ≤ s) (hq : 8 ∣ q) (e : ℕ) (c : LaneAddress) :
    params.placeClass (oddTower_dvd s) (lanePlace hs hq e c) =
      params.placeClass (oddTower_dvd s) (oddLanePlace s (oddLane c.lane)) := by
  apply Units.ext
  rw [lanePlace,oddLanePlace_val,oddLanePlace_val]
  exact congrArg Neg.neg ((ZMod.natCast_eq_natCast_iff _ _ _).2
    ((exists_lane_offset hs hq e c).choose_spec.2.1.of_dvd (dvd_mul_left _ _)))

lemma lanePlace_joint {s q : ℕ} (hs : 3 ≤ s) (hq : 8 ∣ q) (e : ℕ) (c : LaneAddress) :
    (params.placeClass (joint_dvd_tower hs) (lanePlace hs hq e c) : ZMod (72*params.q₀)) =
      -((1+params.q₀*c.offset : ℕ) : ZMod (72*params.q₀)) := by
  rw [lanePlace,oddLanePlace_val]
  apply congrArg Neg.neg
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  rw [mul_comm 72]
  exact (((exists_lane_offset hs hq e c).choose_spec.2.2.mul_left' params.q₀).add_left 1)

lemma lanePlace_two {s q v : ℕ} (hs : 3 ≤ s) (hq : 8 ∣ q) (hv : 2^(s+v) ∣ params.q₁ s)
    (e : ℕ) (c : LaneAddress) :
    params.placeClass hv (lanePlace hs hq e c) = params.placeClass hv (params.placeOfInt s (-1)) *
      (params.placeClass hv (params.placeOfInt s (3*l₀ s*params.q₀+1 : ℕ)))^(q*e+(c.lowDigit s).val) := by
  have cop : (2^(s+v)).Coprime (oddTower s) :=
    ((by decide : Nat.Coprime 2 3).pow_left _).pow_right _
  have dvd : 2^(s+v) ∣ params.q₀*2^s := cop.dvd_of_dvd_mul_right (by
    convert hv using 1
    change params.q₀*2^s*oddTower s = params.q₀*(oddTower s*2^s)
    ring)
  have num := ((exists_lane_offset hs hq e c).choose_spec.1).of_dvd dvd
  have eq := (ZMod.natCast_eq_natCast_iff _ _ _).2 num
  apply Units.ext
  rw [lanePlace,oddLanePlace_val,Units.val_mul,Units.val_pow_eq_pow_val,
    params.placeClass_placeOfInt (ν := -1) (show IsCoprime (-1 : ℤ) params.q₀ from ⟨-1,0,by ring⟩),
    params.placeClass_placeOfInt (by simp [isCoprime_one_left])]
  rw [show (18480:ℕ) = params.q₀ from rfl, eq]
  push_cast
  rw [oddTower_eq]
  push_cast
  ring

end New.Data.CollisionPrimeExample
