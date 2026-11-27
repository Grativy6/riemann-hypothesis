module

public import New.Reduction.Data.Existence
public import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic

/-!
# Digit tags and sparse exponents

A low digit chosen independently for each large exponent can retain a prescribed residue
without admitting a weighted three-term relation. The two-three tower has room for the
digit block at a cost of one additional power of W.
-/

@[expose] public section

namespace ColoredSparse

/-- Bounded tags cannot create a weighted three-term congruence between widely spaced
digit blocks. The lower digits first agree as integers; then the macro exponents agree
modulo the original cyclic order. -/
theorem remove_tags {q o a b x y z u v w C : ℕ} (hq : 0 < q)
    (hu : u ≤ C) (hv : v ≤ C) (hw : w ≤ C) (small : (a+b)*C < q)
    (h : (a+b)*(q*y+v) ≡ a*(q*x+u)+b*(q*z+w) [MOD q*o]) :
    (a+b)*y ≡ a*x+b*z [MOD o] := by
  have expanded : q*((a+b)*y)+(a+b)*v ≡ q*(a*x+b*z)+(a*u+b*w) [MOD q*o] := by
    convert h using 1 <;> ring
  have eqtags : (a+b)*v = a*u+b*w := by
    have red := expanded.of_dvd (dvd_mul_right q o)
    have onlytags : (a+b)*v ≡ a*u+b*w [MOD q] := by
      simpa [Nat.ModEq, Nat.add_mod] using red
    apply onlytags.eq_of_lt_of_lt ((Nat.mul_le_mul_left _ hv).trans_lt small)
    calc a*u+b*w ≤ a*C+b*C := Nat.add_le_add (Nat.mul_le_mul_left _ hu) (Nat.mul_le_mul_left _ hw)
      _ = (a+b)*C := (Nat.add_mul _ _ _).symm
      _ < _ := small
  rw [eqtags] at expanded
  exact Nat.ModEq.mul_left_cancel' hq.ne' (Nat.ModEq.add_right_cancel' _ expanded)

end ColoredSparse

namespace ColoredSparse
open Finset

/-- Select the ordinary Behrend exponents once. Each exponent can subsequently receive any
tag from 0 through 7, independently, preserving the cardinality and the weighted three-term
condition at the expanded modulus. -/
theorem arbitrary_eight_tags {n H L o q : ℕ} (hL : 0 < L) (hfit : (L*H)^n ≤ o)
    (space : L*7 < q) :
    ∃ S : Finset ℕ, (H^n / (n*H^2) : ℝ) ≤ #S ∧
      ∀ tag : ℕ → Fin 8, let U := S.image (fun e ↦ q*e + (tag e).val)
        #U = #S ∧ (∀ e ∈ U, e < q*o) ∧
          ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, ∀ a b : ℕ, 0 < a → 0 < b → a+b ≤ L →
            (a+b)*y ≡ a*x+b*z [MOD q*o] → x=y ∧ y=z := by
  obtain ⟨S, lt, count, free⟩ := New.exists_three_term_free hL hfit
  refine ⟨S, count, fun tag ↦ ?_⟩
  intro U
  have hq : 0 < q := by omega
  have taglt (i : ℕ) : (tag i).val < q := by have := (tag i).isLt; omega
  have recover (i : ℕ) : (q*i+(tag i).val)/q=i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt (taglt i), zero_add]
  constructor
  · exact card_image_of_injective _ (fun i j eq ↦ by
      simpa only [recover] using congrArg (· / q) eq)
  constructor
  · intro e he
    obtain ⟨i,hi,rfl⟩ := mem_image.1 he
    have h := Nat.mul_le_mul_left q (Nat.succ_le_of_lt (lt i hi))
    rw [Nat.mul_succ] at h
    have := taglt i
    omega
  · rintro _ hx _ hy _ hz a b ha hb hab eq
    obtain ⟨x,hxS,rfl⟩ := mem_image.1 hx
    obtain ⟨y,hyS,rfl⟩ := mem_image.1 hy
    obtain ⟨z,hzS,rfl⟩ := mem_image.1 hz
    have digit (i : ℕ) : (tag i).val ≤ 7 := by have := (tag i).isLt; omega
    have small : (a+b)*7 < q := (Nat.mul_le_mul_right _ hab).trans_lt space
    have := remove_tags hq (digit x) (digit y) (digit z) small eq
    obtain ⟨rfl,rfl⟩ := free x hxS y hyS z hzS a b ha hb hab this
    exact ⟨rfl,rfl⟩

end ColoredSparse

namespace ColoredSparse

/-- The integer left after removing the base modulus from a power of 1+M*A. -/
def powerOffset (M A : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => A+(1+M*A)*powerOffset M A n

theorem powerOffset_identity (M A e : ℕ) : 1+M*powerOffset M A e=(1+M*A)^e := by
  induction e with
  | zero => simp [powerOffset]
  | succ e ih =>
    rw [pow_succ, ← ih, powerOffset]
    ring

lemma powerOffset_mod_eight {M : ℕ} (hm : 8 ∣ M) (A e : ℕ) :
    powerOffset M A e ≡ A*e [MOD 8] := by
  have hM : M ≡ 0 [MOD 8] := Nat.modEq_zero_iff_dvd.2 hm
  have base : 1+M*A ≡ 1 [MOD 8] := by simpa using (hM.mul_right A).add_left 1
  induction e with
  | zero => simp [powerOffset, Nat.ModEq]
  | succ e ih =>
    simpa [powerOffset,Nat.mul_succ,Nat.add_comm] using (base.mul ih).add_left A

/-- Any odd coefficient is its own inverse modulo eight. -/
lemma odd_square_mod_eight {A : ℕ} (h : Odd A) : A*A ≡ 1 [MOD 8] := by
  have all : ∀ r : Fin 8, Odd r.val → r.val*r.val ≡ 1 [MOD 8] := by decide
  let r : Fin 8 := ⟨A%8,Nat.mod_lt _ (by decide)⟩
  have par : Odd r.val := by rw [Nat.odd_iff] at h ⊢; dsimp [r]; omega
  exact ((Nat.mod_modEq A 8).symm.mul (Nat.mod_modEq A 8).symm).trans (all r par)

/-- A single CRT offset carries a chosen 2-primary exponent and the prescribed odd lane.
If the lane and target agree modulo nine, their full low address agrees modulo 72. -/
theorem exists_colored_offset {M A two q : ℕ} (hm : 8 ∣ M) (hA : Odd A) (h9 : 9 ∣ A)
    (h2 : 8 ∣ two) (hq : 8 ∣ q) (cop : two.Coprime A) (e target lane : ℕ)
    (lane_matches : lane ≡ target [MOD 9]) :
    let delta := (A*target)%8
    ∃ r : ℕ, 1+M*r ≡ (1+M*A)^(q*e+delta) [MOD M*two] ∧
      1+M*r ≡ 1+M*lane [MOD M*A] ∧ r ≡ target [MOD 72] := by
  intro delta
  let r := Nat.chineseRemainder cop (powerOffset M A (q*e+delta)) lane
  have r2 := r.property.1
  have r3 := r.property.2
  refine ⟨r.val, ?_, (r3.mul_left' M).add_left 1, ?_⟩
  · simpa only [powerOffset_identity] using (r2.mul_left' M).add_left 1
  · apply (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 8 9)).1
    refine ⟨?_,(r3.of_dvd h9).trans lane_matches⟩
    have zero : q ≡ 0 [MOD 8] := Nat.modEq_zero_iff_dvd.2 hq
    have exp : q*e+delta ≡ delta [MOD 8] := by simpa using (zero.mul_right e).add_right delta
    have low : delta ≡ A*target [MOD 8] := Nat.mod_modEq _ _
    calc r.val ≡ powerOffset M A (q*e+delta) [MOD 8] := r2.of_dvd h2
      _ ≡ A*(q*e+delta) [MOD 8] := powerOffset_mod_eight hm _ _
      _ ≡ A*(A*target) [MOD 8] := (exp.trans low).mul_left A
      _ ≡ target [MOD 8] := by simpa [← Nat.mul_assoc] using (odd_square_mod_eight hA).mul_right target

end ColoredSparse

open Finset Real
namespace New

/-- Reserving a block of more than seven times the weight bound for low tags costs
at most one power of W at the chosen scale. -/
theorem exists_tagged_macro_budget {s n : ℕ} {W : ℝ} (hn : 0 < n) (hw : 1 ≤ W)
    (hwidth : (28 : ℝ)*l₀ s ≤ W) (hfloor : W^2 ≤ (2:ℝ)^s)
    (hupper : (2:ℝ)^s ≤ W^n) (hroom : (2*l₀ s : ℝ)^n ≤ W)
    (hcount : (3:ℝ)*l₀ s*n*2^n ≤ W) :
    ∃ q o : ℕ, 2^s = q*o ∧ 8 ∣ q ∧ 14*l₀ s < q ∧
      ∃ S : Finset ℕ, (∀ a ∈ S, a < o) ∧ (towerDeg s : ℝ) ≤ #S*W^5 ∧
        ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ i j : ℕ, 0 < i → 0 < j → i+j ≤ 2*l₀ s →
          (i+j)*b ≡ i*a+j*c [MOD o] → a=b ∧ b=c := by
  have hlpos : 0 < l₀ s := by unfold l₀; positivity
  let b := Nat.log 2 (14*l₀ s) + 1
  let q := 2^b
  have low : 14*l₀ s < q := Nat.lt_pow_succ_log_self (by decide : 1 < 2) _
  have up : q ≤ 28*l₀ s := by
    have near := Nat.pow_log_le_self 2 (show 14*l₀ s ≠ 0 by positivity)
    dsimp [q,b]
    rw [pow_succ]
    omega
  have qmax : (q:ℝ) ≤ W := (by exact_mod_cast up : (q:ℝ) ≤ 28*l₀ s).trans hwidth
  have qpos : 0 < q := by omega
  have fits : (q:ℝ)*W ≤ (2:ℝ)^s := by
    refine le_trans (mul_le_mul_of_nonneg_right qmax (by linarith)) ?_
    simpa only [sq] using hfloor
  have qb : q ≤ 2^s := by
    exact_mod_cast (calc (q:ℝ) ≤ q*W := le_mul_of_one_le_right (Nat.cast_nonneg _) hw
      _ ≤ (2:ℝ)^s := fits)
  have bs : b ≤ s := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 qb
  let o := 2^(s-b)
  have split : 2^s = q*o := by dsimp [q,o]; rw [←pow_add]; congr 1; omega
  have big : 8 ≤ q := by omega
  have three : 3 ≤ b := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (show 2^3 ≤ 2^b from big)
  have dq : 8 ∣ q := pow_dvd_pow 2 three
  have qWpos : 0 < (q:ℝ)*W := mul_pos (by exact_mod_cast qpos) (by linarith)
  obtain ⟨k, kmin, kmax⟩ :
      ∃ k : ℕ, ((2:ℝ)^n)^k ≤ 2^s/(q*W) ∧ 2^s/(q*W) < (2^n)^(k+1) :=
    exists_nat_pow_near ((one_le_div qWpos).2 fits) (one_lt_pow₀ one_lt_two hn.ne')
  rw [pow_right_comm, le_div_iff₀ qWpos] at kmin
  rw [pow_right_comm, div_lt_iff₀ qWpos, pow_succ', mul_pow] at kmax
  have cap : (2:ℝ)^k ≤ W := by
    apply le_of_pow_le_pow_left₀ hn.ne' (by linarith)
    calc ((2:ℝ)^k)^n ≤ ((2:ℝ)^k)^n*(q*W) := by
          apply le_mul_of_one_le_right (by positivity)
          exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast (show 1 ≤ q by omega)) hw
      _ ≤ 2^s := kmin
      _ ≤ W^n := hupper
  have packed : (2*l₀ s*2^k)^n ≤ o := by
    have eq : (2:ℝ)^s = q*o := by exact_mod_cast split
    have budget : (((2*l₀ s : ℝ)*2^k)^n)*(q:ℝ) ≤ o*q := calc
      _ = (2*l₀ s : ℝ)^n*((2:ℝ)^k)^n*q := by ring
      _ ≤ W*((2:ℝ)^k)^n*q := by gcongr
      _ = ((2:ℝ)^k)^n*(q*W) := by ring
      _ ≤ 2^s := kmin
      _ = _ := by rw [eq]; ring
    exact_mod_cast (le_of_mul_le_mul_right budget (by exact_mod_cast qpos : 0 < (q:ℝ)))
  obtain ⟨S, lt, count, free⟩ := exists_three_term_free (L := 2*l₀ s) (by positivity) packed
  refine ⟨q,o,split,dq,low,S,lt,?_,free⟩
  push_cast at count
  calc (towerDeg s : ℝ) = 3*l₀ s*2^s := by simp [towerDeg_eq]
    _ ≤ 3*l₀ s*((2:ℝ)^n*((2:ℝ)^k)^n*(q*W)) := by gcongr
    _ = ((2:ℝ)^k)^n / (n*((2:ℝ)^k)^2) * (3*l₀ s*n*2^n*q*W*((2:ℝ)^k)^2) := by field_simp
    _ ≤ #S * (W*W*W*W^2) := by gcongr
    _ = _ := by ring

end New
