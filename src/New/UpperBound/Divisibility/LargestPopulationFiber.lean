module

public import New.UpperBound.Divisibility.PopulationFibers
import Mathlib.Tactic

/-!
# The largest population fiber at fixed denominator

The two allowed exchanges give a clipped integer wedge. Its largest size,
1 + floor(n(n+6)/12), is the classical number of partitions into at most three parts.
Here the extremal cut and the realization of all its six-bin words on one fixed field and
level are established directly. The classical partition formula also appears in G. H. Hardy
and S. Ramanujan, *Asymptotic Formulae in Combinatory Analysis* (1918), p. 76, footnote.
-/

@[expose] public section

open Finset
namespace New.SixSignatures

/-- Number of x ≥ 0 with 2x + y ≤ m. -/
def column (m y : ℕ) : ℕ := if y ≤ m then (m-y)/2+1 else 0

/-- Points in the integer wedge 2x+y≤m cut off at y≤k. -/
def columns (m k : ℕ) : ℕ := ∑ j ∈ range (k+1), column m j

@[simp] lemma column_shift (m j : ℕ) : column (m+1) (j+1) = column m j := by
  simp [column]

lemma columns_right (m k : ℕ) : columns m (k+1) = columns m k + column m (k+1) := by
  exact sum_range_succ _ _

lemma columns_shift (m k : ℕ) : columns (m+1) (k+1) = columns m k + column (m+1) 0 := by
  unfold columns
  rw [sum_range_succ']
  simp

lemma balance (m k : ℕ) :
    columns (m+1) k + column m k + column m (k+1) = columns m (k+1) + column (m+1) 0 := by
  cases k with
  | zero => simp [columns,column,Finset.sum_range_succ]; omega
  | succ k => rw [columns_shift, columns_right m (k+1), columns_right m k]; omega

def peakCut (n : ℕ) := (2*n+1)/3

lemma peakCut_le (n : ℕ) : peakCut n ≤ n := by unfold peakCut; omega
lemma remainder_le_peakCut (n : ℕ) : n-peakCut n ≤ peakCut n := by unfold peakCut; omega

lemma rising_step (m k : ℕ) (h : m < peakCut (m+k+1)) : columns m (k+1) ≤ columns (m+1) k := by
  have step := balance m k
  unfold peakCut at h
  simp only [column, Nat.zero_le, ite_true,Nat.sub_zero] at step
  split_ifs at step <;> omega

lemma falling_step (m k : ℕ) (h : peakCut (m+k+1) ≤ m) : columns (m+1) k ≤ columns m (k+1) := by
  have step := balance m k
  unfold peakCut at h
  simp only [column, Nat.zero_le, ite_true,Nat.sub_zero] at step
  split_ifs at step <;> omega

lemma peak (n m : ℕ) (mn : m ≤ n) :
    columns m (n-m) ≤ columns (peakCut n) (n-peakCut n) := by
  have bound := peakCut_le n
  by_cases left : m ≤ peakCut n
  · have incr (a : ℕ) (ma : m≤a) : a≤peakCut n → columns m (n-m) ≤ columns a (n-a) := by
      induction a,ma using Nat.le_induction with
      | base => exact fun _ ↦ le_rfl
      | succ j hj ih =>
        intro ltd
        have denom : n-j = (n-(j+1))+1 := by omega
        have id : j+(n-(j+1))+1=n := by omega
        apply (ih (by omega)).trans
        rw [denom]
        exact rising_step _ _ (by rw [id]; omega)
    exact incr _ left le_rfl
  · have decr (a : ℕ) (pa : peakCut n ≤ a) : a≤n →
        columns a (n-a) ≤ columns (peakCut n) (n-peakCut n) := by
      induction a,pa using Nat.le_induction with
      | base => exact fun _ ↦ le_rfl
      | succ j hj ih =>
        intro ltd
        have denom : n-j = (n-(j+1))+1 := by omega
        have id : j+(n-(j+1))+1=n := by omega
        apply le_trans _ (ih (by omega))
        rw [denom]
        exact falling_step _ _ (by rw [id]; omega)
    exact decr _ (by omega) mn

lemma grow_four_two {m k : ℕ} (le : k≤m) :
    columns (m+4) (k+2) = columns m k + (m+k+6) := by
  have each (j : ℕ) (hj : j ∈ range (k+1)) : column (m+4) j = column m j + 2 := by
    have := mem_range.1 hj
    simp [column,show j≤m+4 by omega,show j≤m by omega]; omega
  have body : columns (m+4) k = columns m k + 2*(k+1) := by
    unfold columns
    rw [sum_congr rfl each, sum_add_distrib]
    simp [mul_comm]
  rw [columns_right,columns_right,body]
  simp [column,show k+1 ≤ m+4 by omega, show k+1+1 ≤ m+4 by omega]
  omega

lemma peak_six (n : ℕ) :
    columns (peakCut (n+6)) (n+6-peakCut (n+6)) =
      columns (peakCut n) (n-peakCut n) + n+6 := by
  have a : peakCut (n+6) = peakCut n+4 := by unfold peakCut; omega
  have le := peakCut_le n
  rw [a,show n+6-(peakCut n+4) = (n-peakCut n)+2 by omega, grow_four_two (remainder_le_peakCut n)]
  omega

/-- Closed form for the largest number of six-bin histograms at total n. -/
def largest (n : ℕ) : ℕ := (n*n+6*n+12)/12

lemma largest_six (n : ℕ) : largest (n+6)=largest n+n+6 := by
  unfold largest
  rw [show (n+6)*(n+6)+6*(n+6)+12=(n*n+6*n+12)+(n+6)*12 by ring,
    Nat.add_mul_div_right _ _ (by decide : 0<12)]
  omega

theorem peak_value (n : ℕ) : columns (peakCut n) (n-peakCut n) = largest n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases small : n<6
    · interval_cases n <;> decide
    · obtain ⟨m,rfl⟩ : ∃ m, n=m+6 := ⟨n-6,by omega⟩
      rw [peak_six,largest_six,ih m (by omega)]


/-- Column y of the wedge contains exactly the permitted x values. -/
abbrev ColumnChoices (m k : ℕ) := Σ y : Fin (k+1), Fin (column m y.val)

/-- A position in a row of variable length is determined by its two natural indices. -/
lemma finSlot_ext {n : ℕ} {f : Fin n → ℕ} {a b : Σ i : Fin n, Fin (f i)}
    (h : a.1.val = b.1.val) (h' : a.2.val = b.2.val) : a=b := by
  obtain ⟨i,j⟩ := a
  obtain ⟨k,l⟩ := b
  have ik : i=k := Fin.ext h
  subst k
  have jl : j=l := Fin.ext h'
  subst l
  rfl

lemma column_mem {x y m : ℕ} : x < column m y ↔ 2*x+y≤m := by
  unfold column
  split_ifs <;> omega

/-- Write x = min(A,B)-i and y = j. The two compression bounds become
y≤C and 2x+y≤2 min(A,B)+E. -/
def movesByColumn (h : Fin 6 → ℕ) (he : h 2<2) :
    Moves h ≃ ColumnChoices (2*min (h 0) (h 1)+h 2) (h 3) := by
  let I := min (h 0) (h 1)
  let m := 2*I + h 2
  let forward (z : Moves h) : ColumnChoices m (h 3) :=
    ⟨⟨z.2.val, by have := z.2.isLt; omega⟩, ⟨I-z.1.val, by
      apply column_mem.2
      have i : z.1.val<I+1 := z.1.isLt
      have j := z.2.isLt
      change 2*(I-z.1.val)+z.2.val≤2*I+h 2
      omega⟩⟩
  let back (z : ColumnChoices m (h 3)) : Moves h :=
    ⟨⟨I-z.2.val,by change I-z.2.val < I+1; omega⟩, ⟨z.1.val,by
      have bound : 2*z.2.val+z.1.val≤m := column_mem.1 z.2.isLt
      have yc := z.1.isLt
      change z.1.val < min (h 3) (h 2+2*(I-z.2.val))+1
      dsimp [m] at bound
      omega⟩⟩
  refine ⟨forward,back,?_,?_⟩
  · rintro ⟨i,j⟩
    apply finSlot_ext
    · change I-(I-i.val)=i.val
      have hi : i.val<I+1 := i.isLt
      omega
    · rfl
  · rintro ⟨y,x⟩
    apply finSlot_ext
    · rfl
    · change I-(I-x.val)=x.val
      have bound : 2*x.val+y.val≤m := column_mem.1 x.isLt
      dsimp [m] at bound
      omega

lemma columnChoices_card (m k : ℕ) : Fintype.card (ColumnChoices m k) = columns m k := by
  simp [ColumnChoices,columns,Fintype.card_sigma,Fin.sum_univ_eq_sum_range]

lemma count_by_columns (h : Fin 6 → ℕ) (he : h 2<2) (hf : h 4<2) :
    Nat.card {n : Fin 6 → ℕ // observed h=observed n} =
      columns (2*min (h 0) (h 1)+h 2) (h 3) := by
  rw [← Nat.card_congr (representatives h he hf),Nat.card_congr (movesByColumn h he),
    Nat.card_eq_fintype_card,columnChoices_card]

lemma columns_mono (m : ℕ) {a b : ℕ} (le : a≤b) : columns m a ≤ columns m b := by
  apply sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.add_le_add_right le 1))
  exact fun _ _ _ ↦ Nat.zero_le _

/-- No integer report has more histories than the closed formula at its total. -/
theorem count_le_largest (w : Fin 6 → ℕ) :
    Nat.card {n : Fin 6 → ℕ // observed w=observed n} ≤ largest (∑ i,w i) := by
  let h := normalForm w
  have same : observed w = observed h := observed_normalForm w
  have total : (∑ i,h i) = ∑ i,w i := by
    have v := congrFun same 0
    rw [observed_total,observed_total] at v
    exact_mod_cast v.symm
  have he : h 2 < 2 := by change (w 2+w 4/2)%2<2; omega
  have hf : h 4 < 2 := by change w 4%2<2; omega
  rw [same,count_by_columns h he hf,← total]
  let m := 2*min (h 0) (h 1)+h 2
  have room : m+h 3≤ ∑ i,h i := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Nat.add_zero]; dsimp [m]; omega
  calc columns m (h 3) ≤ columns m ((∑ i,h i)-m) := columns_mono _ (by omega)
    _ ≤ _ := (peak _ _ (by omega)).trans_eq (peak_value _)

/-- Put as many pairs into A and B as m allows, its remainder into E and the rest into C. -/
def cutWord (n m : ℕ) : Fin 6 → ℕ := ![m/2,m/2,m%2,n-m,0,0]

lemma cutWord_total {n m : ℕ} (hm : m≤n) : (∑ i,cutWord n m i)=n := by
  simp [cutWord,Fin.sum_univ_succ]
  omega

lemma count_cutWord (n m : ℕ) :
    Nat.card {w : Fin 6 → ℕ // observed (cutWord n m)=observed w} = columns m (n-m) := by
  have he : cutWord n m 2<2 := by change m%2<2; omega
  have hf : cutWord n m 4<2 := by change 0<2; decide
  rw [count_by_columns _ he hf]
  change columns (2*min (m/2) (m/2)+m%2) (n-m)=columns m (n-m)
  rw [min_self,show 2*(m/2)+m%2=m by omega]

/-- A report of maximal size at the indicated total. -/
def peakWord (n : ℕ) : Fin 6 → ℕ := cutWord n (peakCut n)

lemma peakWord_total (n : ℕ) : (∑ i,peakWord n i)=n := cutWord_total (peakCut_le n)

theorem count_peakWord (n : ℕ) :
    Nat.card {w : Fin 6 → ℕ // observed (peakWord n) = observed w} = largest n :=
  (count_cutWord n (peakCut n)).trans (peak_value n)

/-- Three unordered, nonnegative piles, represented uniquely in increasing order. -/
@[ext] structure ThreePiles (n : ℕ) where
  low : ℕ
  middle : ℕ
  high : ℕ
  low_le : low ≤ middle
  middle_le : middle ≤ high
  total : low+middle+high=n

abbrev PileChoices (n : ℕ) := Σ s : Fin (n/3+1), Fin ((n-3*s.val)/2+1)

/-- Choose the smallest pile s and the excess q of the middle pile over s. The
remaining pile is n-2s-q, and ordering it last requires exactly 2q+3s≤n. -/
def threePilesByMinimum (n : ℕ) : PileChoices n ≃ ThreePiles n where
  toFun z :=
    { low := z.1.val
      middle := z.1.val+z.2.val
      high := n-2*z.1.val-z.2.val
      low_le := by omega
      middle_le := by have := z.1.isLt; have := z.2.isLt; omega
      total := by have := z.1.isLt; have := z.2.isLt; omega }
  invFun t := by
    obtain ⟨s,m,h,sm,mh,total⟩ := t
    refine ⟨⟨s,by omega⟩,m-s,?_⟩
    change m-s < (n-3*s)/2+1
    omega
  left_inv := by
    rintro ⟨s,q⟩
    apply finSlot_ext
    · rfl
    · change s.val+q.val-s.val=q.val
      omega
  right_inv := by
    rintro ⟨s,m,h,sm,mh,total⟩
    apply ThreePiles.ext
    · rfl
    · change s+(m-s)=m; omega
    · change n-2*s-(m-s)=h; omega

def pileSum (n : ℕ) : ℕ := ∑ s ∈ range (n/3+1), ((n-3*s)/2+1)

lemma card_threePiles (n : ℕ) : Nat.card (ThreePiles n) = pileSum n := by
  rw [← Nat.card_congr (threePilesByMinimum n),Nat.card_eq_fintype_card]
  simp only [PileChoices,pileSum,Fintype.card_sigma,Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun s : ℕ ↦ (n-3*s)/2+1) _

lemma piles_six (n : ℕ) : pileSum (n+6) = pileSum n+n+6 := by
  let f := fun s : ℕ ↦ (n+6-3*s)/2+1
  have count : (n+6)/3+1=(n/3+1)+1+1 := by omega
  change (∑ s ∈ range ((n+6)/3+1), f s) = _
  rw [count,sum_range_succ' f,sum_range_succ' (fun j ↦ f (j+1))]
  have rest : (∑ s ∈ range (n/3+1), f (s+1+1)) = pileSum n := by
    apply sum_congr rfl
    intro s _
    dsimp [f]
    omega
  rw [rest]
  dsimp [f]
  omega

/-- The classical three-pile count and the extremal size have the same six-step
recurrence and agree at the first six indices. -/
theorem largest_eq_threePiles (n : ℕ) : largest n = Nat.card (ThreePiles n) := by
  rw [card_threePiles]
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases small : n<6
    · interval_cases n <;> decide
    · obtain ⟨m,rfl⟩ : ∃ m, n=m+6 := ⟨n-6,by omega⟩
      rw [largest_six,piles_six,ih m (by omega)]

end New.SixSignatures

namespace New.Data.CollisionPrimeExample
open New.SixSignatures Filter NumberField
local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 535919) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 665279) := ⟨by norm_num1⟩

/-- At positive denominator n the most ambiguous report has as many different
six-bin words as unordered triples of nonnegative piles totaling n. Each of its
words has an actual high-place assignment on one field and level, up to the same
positive factor k. -/
theorem largest_report_on_one_frame (n : ℕ) (hn : 0<n) :
    (∀ w : Fin 6 → ℕ, (∑ i,w i)=n →
      Nat.card {u : Fin 6 → ℕ // observed w=observed u} ≤ Nat.card (ThreePiles n)) ∧
    Nat.card {w : Fin 6 → ℕ // observed (peakWord n)=observed w} = Nat.card (ThreePiles n) ∧
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧ #D.bPlaces=k*n ∧
      ∀ w : Fin 6 → ℕ, observed (peakWord n)=observed w → ∃ c : HighPlaceChoice D,
        census c.toData=(fun i ↦ k*w i) ∧ ∀ ι₀ ι₁ ι₂,
          readings c.toData ι₀ ι₁ ι₂=point (peakWord n) := by
  refine ⟨fun w hw ↦ (count_le_largest w).trans_eq (hw ▸ largest_eq_threePiles n),
    (count_peakWord n).trans (largest_eq_threePiles n),?_⟩
  simpa only [peakWord_total] using
    eventually_whole_report_fiber (peakWord n) (by simpa only [peakWord_total] using hn)

end New.Data.CollisionPrimeExample
