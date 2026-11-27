module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The four faces determined by three residue tests

The periods 12, 2 and 72 give six integer sign triples. Their convex hull is a tetrahedron.
The barycentric coordinates express all four supporting inequalities explicitly.
-/

@[expose] public section

open Finset Set
namespace ThreePrimeEnvelope

/-- One offset, measured in a system with G unordered pairs. -/
def signAt (G t : ℕ) : ℤ := if 2*G ∣ t then -1 else if G ∣ t then 1 else 0

lemma signAt_congr {G x y n : ℕ} (h : x ≡ y [MOD n]) (hd : 2*G ∣ n) :
    signAt G x = signAt G y := by
  simp only [signAt, h.dvd_iff hd, h.dvd_iff ((dvd_mul_left G 2).trans hd)]

abbrev Point := Fin 3 → ℝ

/-- Coordinates are ordered by the rational primes 479, 535919, and 665279. -/
def row (t : ℕ) : Point := ![signAt 6 t, signAt 1 t, signAt 36 t]

def tag (t : ℕ) : ℤ × ℤ × ℤ := (signAt 6 t, signAt 1 t, signAt 36 t)

lemma row_congr {a b : ℕ} (h : a ≡ b [MOD 72]) : row a = row b := by
  simp only [row, signAt_congr h (by decide : 2*6 ∣ 72),
    signAt_congr h (by decide : 2*1 ∣ 72), signAt_congr h (by decide : 2*36 ∣ 72)]

/-- Multiplicities of the six different readings over one complete turn of 72 offsets. -/
theorem table_cardinalities :
    [(-1,-1,-1), (-1,-1,1), (-1,-1,0), (1,-1,0), (0,-1,0), (0,1,0)].map
      (fun q : ℤ × ℤ × ℤ ↦ #((range 72).filter (fun t ↦ tag t = q))) = [1,1,4,6,24,36] := by decide

set_option maxRecDepth 4096 in
theorem distinct_readings_one_turn :
    (range 72).image tag = {(-1,-1,-1), (-1,-1,1), (-1,-1,0), (1,-1,0), (0,-1,0), (0,1,0)} := by
  decide

/-- The four extreme offset signatures. -/
def corner : Fin 4 → Point := ![![-1,-1,-1], ![-1,-1,1], ![1,-1,0], ![0,1,0]]

def tetrahedron : Set Point := convexHull ℝ (Set.range corner)

/-- The four faces of the tetrahedron as linear inequalities. -/
def inside (u : Point) : Prop :=
  -1 ≤ u 1 ∧ u 1 - 2*u 0 ≤ 1 ∧ u 1 + 2*u 0 + 4*u 2 ≤ 1 ∧ u 1 + 2*u 0 - 4*u 2 ≤ 1

lemma inside_row (t : ℕ) : inside (row t) := by
  have table : ∀ r : Fin 72, -1 ≤ signAt 1 r ∧ signAt 1 r - 2*signAt 6 r ≤ 1 ∧
      signAt 1 r+2*signAt 6 r+4*signAt 36 r ≤ 1 ∧ signAt 1 r+2*signAt 6 r-4*signAt 36 r ≤ 1 := by decide
  let r : Fin 72 := ⟨t%72, Nat.mod_lt _ (by decide)⟩
  rw [← row_congr (Nat.mod_modEq t 72)]
  obtain ⟨h₁,h₂,h₃,h₄⟩ := table r
  change -1 ≤ (signAt 1 r : ℝ) ∧ (signAt 1 r : ℝ) - 2*signAt 6 r ≤ 1 ∧
    (signAt 1 r : ℝ)+2*signAt 6 r+4*signAt 36 r ≤ 1 ∧ (signAt 1 r : ℝ)+2*signAt 6 r-4*signAt 36 r ≤ 1
  exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂, by exact_mod_cast h₃, by exact_mod_cast h₄⟩

lemma convex_inside : Convex ℝ {u : Point | inside u} := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x₁,x₂,x₃,x₄⟩ := hx
  obtain ⟨y₁,y₂,y₃,y₄⟩ := hy
  change inside (a • x + b • y)
  simp only [inside, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact ⟨by linarith only [add_le_add (mul_le_mul_of_nonneg_left x₁ ha) (mul_le_mul_of_nonneg_left y₁ hb), hab],
    by nlinarith only [add_le_add (mul_le_mul_of_nonneg_left x₂ ha) (mul_le_mul_of_nonneg_left y₂ hb), hab],
    by nlinarith only [add_le_add (mul_le_mul_of_nonneg_left x₃ ha) (mul_le_mul_of_nonneg_left y₃ hb), hab],
    by nlinarith only [add_le_add (mul_le_mul_of_nonneg_left x₄ ha) (mul_le_mul_of_nonneg_left y₄ hb), hab]⟩

/-- The face inequalities are sufficient: their four slacks, scaled by 1/8, 1/8, 1/4,
and 1/2, are explicit barycentric coordinates. -/
theorem inside_iff_mem (v : Point) : inside v ↔ v ∈ tetrahedron := by
  constructor
  · intro hv
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hv
    let w : Fin 4 → ℝ := ![(1-v 1-2*v 0-4*v 2)/8, (1-v 1-2*v 0+4*v 2)/8,
      (1-v 1+2*v 0)/4, (1+v 1)/2]
    apply mem_convexHull_of_exists_fintype w corner
    · intro i; fin_cases i <;> simp [w] <;> linarith
    · simp [w, Fin.sum_univ_succ]; ring
    · exact fun i ↦ Set.mem_range_self i
    · funext i
      fin_cases i <;> simp [w,corner,Fin.sum_univ_succ] <;> ring
  · apply convexHull_min _ convex_inside
    rintro _ ⟨i,rfl⟩
    fin_cases i <;> norm_num [inside,corner]

lemma row_mem (t : ℕ) : row t ∈ tetrahedron := (inside_iff_mem _).1 (inside_row t)

/-- When the second reading attains its positive extreme, both other readings vanish. -/
theorem top_is_singleton {v : Point} (hv : v ∈ tetrahedron) (ht : v 1 = 1) :
    v 0 = 0 ∧ v 2 = 0 := by
  obtain ⟨_,h₂,h₃,h₄⟩ := (inside_iff_mem v).2 hv
  constructor <;> linarith

/-- The offsets giving the four corners, in the displayed order. -/
def cornerOffset : Fin 4 → ℕ := ![0,36,6,1]

lemma row_cornerOffset (i : Fin 4) : row (cornerOffset i) = corner i := by
  funext j
  fin_cases i <;> fin_cases j <;> norm_num [row,cornerOffset,corner,signAt]

/-- The three edge vectors from the first corner, in rows. -/
noncomputable def edgeMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j ↦ corner i.succ j - corner 0 j

/-- The determinant is eight, so the geometric volume in normalized coordinates is 8/6. -/
theorem det_edges : Matrix.det edgeMatrix = 8 := by
  rw [Matrix.det_fin_three edgeMatrix]
  norm_num [edgeMatrix, Matrix.of_apply, corner, Fin.succ]

end ThreePrimeEnvelope
