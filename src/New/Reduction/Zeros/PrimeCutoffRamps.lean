module

public import New.Reduction.Zeros.PrimeError
import Mathlib.Tactic

/-!
# Exact prime weights from the smoothed remainder

The compensated remainder is a sum of nonnegative ramps. The chord defect records
exactly the interior weights with a tent kernel. Three neighboring integer readings
recover the middle weight even if the additive normalizing constant is unknown.
-/

@[expose] public section

open Finset Nat Set Real
open scoped Topology
namespace New.PrimeCutoff

/-- After adding back the smooth terms, multiplying by the cutoff turns the
smoothed prime sum into a sum of ramps with knots at the actual prime powers. -/
noncomputable def integrated (d q : ℕ) [Fact d.Prime] [NeZero q] (x : ℝ) : ℝ :=
  x * (primeRemainder d q x + Real.log x / q.totient + (logDerivMean d q 1).re)

theorem integrated_eq_ramps {d q : ℕ} [Fact d.Prime] [NeZero q] {x : ℝ} {N : ℕ}
    (hx : 0 < x) (cutoff : ⌊x⌋₊ ≤ N) :
    integrated d q x = ∑ n ∈ Finset.Icc 1 N, (lambdaKResidueClass d q n / n) * (x-n)⁺ := by
  have cancel (u v c : ℝ) : u-v-c+v+c=u := by ring
  rw [integrated, primeRemainder_eq_sum_posPart hx cutoff, cancel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hn).1
  have scale : 1/(n:ℝ)-1/x = (x-n)/(n*x) := by field
  rw [scale]
  obtain under | above := le_total (n:ℝ) x
  · rw [posPart_of_nonneg (div_nonneg (sub_nonneg.2 under) (mul_pos hn₀ hx).le),
      posPart_of_nonneg (sub_nonneg.2 under)]
    field
  · rw [posPart_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 above) (mul_pos hn₀ hx).le),
      posPart_of_nonpos (sub_nonpos.2 above)]
    ring

/-- The exact gap between a ramp and its chord is a tent supported between the endpoints. -/
theorem ramp_chord {a b y x z : ℝ} (ha : 0≤a) (hb : 0≤b) (weights : a+b=1)
    (mix : a*y+b*z=x) (left : y≤x) (right : x≤z) (n : ℝ) :
    a*(y-n)⁺ + b*(z-n)⁺ - (x-n)⁺ = min (a*(n-y)⁺) (b*(z-n)⁺) := by
  have line : x-n = a*(y-n)+b*(z-n) := by linear_combination n*weights - mix
  obtain before | afterLeft := le_or_gt n y
  · rw [posPart_of_nonneg (sub_nonneg.2 before), posPart_of_nonneg (sub_nonneg.2 (before.trans (left.trans right))),
      posPart_of_nonneg (sub_nonneg.2 (before.trans left)), posPart_of_nonpos (sub_nonpos.2 before)]
    rw [mul_zero,min_eq_left (mul_nonneg hb (sub_nonneg.2 (before.trans (left.trans right))))]
    linarith only [line]
  obtain afterRight | beforeRight := le_or_gt z n
  · rw [posPart_of_nonpos (sub_nonpos.2 afterLeft.le), posPart_of_nonpos (sub_nonpos.2 afterRight),
      posPart_of_nonpos (sub_nonpos.2 (right.trans afterRight)), posPart_of_nonneg (sub_nonneg.2 afterLeft.le)]
    simp [mul_nonneg ha (sub_nonneg.2 afterLeft.le)]
  rw [posPart_of_nonpos (sub_nonpos.2 afterLeft.le), posPart_of_nonneg (sub_nonneg.2 beforeRight.le),
    posPart_of_nonneg (sub_nonneg.2 afterLeft.le),mul_zero,zero_add]
  have value : x-n = b*(z-n) - a*(n-y) := by linarith only [line]
  rw [value]
  obtain h | h := le_total (a*(n-y)) (b*(z-n))
  · rw [posPart_of_nonneg (sub_nonneg.2 h),min_eq_left h]
    ring
  · rw [posPart_of_nonpos (sub_nonpos.2 h),min_eq_right h,sub_zero]

theorem integrated_chord_defect {d q : ℕ} [Fact d.Prime] [NeZero q] {a b y x z : ℝ} (hy : 0<y)
    (ha : 0≤a) (hb : 0≤b) (weights : a+b=1) (mix : a*y+b*z=x) (left : y≤x) (right : x≤z) :
    a*integrated d q y + b*integrated d q z - integrated d q x =
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (lambdaKResidueClass d q n / n) *
        min (a*((n:ℝ)-y)⁺) (b*(z-n)⁺) := by
  rw [integrated_eq_ramps hy (Nat.floor_mono (left.trans right)),
    integrated_eq_ramps (hy.trans_le (left.trans right)) (le_refl ⌊z⌋₊),
    integrated_eq_ramps (hy.trans_le left) (Nat.floor_mono right),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  linear_combination (lambdaKResidueClass d q n / n) * ramp_chord ha hb weights mix left right n

theorem integrated_le_chord {d q : ℕ} [Fact d.Prime] [NeZero q] {a b y x z : ℝ} (hy : 0<y)
    (ha : 0≤a) (hb : 0≤b) (weights : a+b=1) (mix : a*y+b*z=x) (left : y≤x) (right : x≤z) :
    integrated d q x ≤ a*integrated d q y + b*integrated d q z := by
  rw [← sub_nonneg, integrated_chord_defect hy ha hb weights mix left right]
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (div_nonneg (lambdaKResidueClass_nonneg d q n) (Nat.cast_nonneg n))
    (le_min (mul_nonneg ha (posPart_nonneg _)) (mul_nonneg hb (posPart_nonneg _)))

/-- On three consecutive integer cutoffs the tent keeps just the middle mark. -/
theorem second_difference {d q : ℕ} [Fact d.Prime] [NeZero q] (m : ℕ) (hm : 2 ≤ m) :
    (m:ℝ) * (integrated d q (m-1) + integrated d q (m+1) - 2*integrated d q m) =
      lambdaKResidueClass d q m := by
  have hm₁ : (1:ℝ)<m := by exact_mod_cast hm
  have eq := integrated_chord_defect (d:=d) (q:=q) (y:=(m:ℝ)-1) (x:=(m:ℝ)) (z:=(m:ℝ)+1)
    (a:=(1/2:ℝ)) (b:=(1/2:ℝ)) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by ring) (by linarith) (by linarith)
  have point (n : ℕ) : min ((1/2:ℝ)*((n:ℝ)-(m-1))⁺) ((1/2:ℝ)*((m:ℝ)+1-n)⁺) =
      if n=m then 1/2 else 0 := by
    obtain small | equal | big := lt_trichotomy n m
    · have side : (n:ℝ)≤m-1 := by
        have e : (n:ℝ)+1≤m := by exact_mod_cast (by omega : n+1≤m)
        linarith
      rw [ite_eq_right small.ne,posPart_of_nonpos (sub_nonpos.2 side),mul_zero,min_eq_left (by positivity)]
    · subst n
      norm_num [show ((m:ℝ)-(m-1))=1 by ring,show ((m:ℝ)+1-m)=1 by ring,posPart_def]
    · have side : (m:ℝ)+1≤n := by exact_mod_cast (by omega : m+1≤n)
      rw [ite_eq_right big.ne',posPart_of_nonpos (sub_nonpos.2 side),mul_zero,min_eq_right (by positivity)]
  have floor : ⌊(m:ℝ)+1⌋₊=m+1 := by rw [← Nat.cast_add_one,Nat.floor_natCast]
  simp only [floor,point,mul_ite,mul_zero] at eq
  have member : m∈Finset.Icc 1 (m+1) := Finset.mem_Icc.2 ⟨by omega,by omega⟩
  rw [Finset.sum_ite_eq',ite_eq_left member] at eq
  have nz : (m:ℝ) ≠ 0 := by linarith
  field_simp [nz] at eq
  linarith only [eq]


/-- In the interior, the corrected chord is exact precisely when every strictly
interior integer has zero arithmetic weight. -/
theorem chord_exact_iff {d q : ℕ} [Fact d.Prime] [NeZero q] {a b y x z : ℝ} (hy : 0<y)
    (ha : 0<a) (hb : 0<b) (weights : a+b=1) (mix : a*y+b*z=x) (left : y≤x) (right : x≤z) :
    integrated d q x = a*integrated d q y + b*integrated d q z ↔
      ∀ n ∈ Finset.Icc 1 ⌊z⌋₊, y < (n:ℝ) → (n:ℝ) < z → lambdaKResidueClass d q n = 0 := by
  let t (n : ℕ) := min (a*((n:ℝ)-y)⁺) (b*(z-n)⁺)
  have nn (n : ℕ) : 0 ≤ t n :=
    le_min (mul_nonneg ha.le (posPart_nonneg _)) (mul_nonneg hb.le (posPart_nonneg _))
  have pos (n : ℕ) (yn : y<n) (nz : (n:ℝ)<z) : 0 < t n := by
    exact lt_min (mul_pos ha (lt_of_lt_of_le (sub_pos.2 yn) (le_posPart _)))
      (mul_pos hb (lt_of_lt_of_le (sub_pos.2 nz) (le_posPart _)))
  have eq := integrated_chord_defect (d:=d) (q:=q) hy ha.le hb.le weights mix left right
  change _ = ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (lambdaKResidueClass d q n / n) * t n at eq
  constructor
  · intro straight n hn yn nz
    rw [straight,sub_self] at eq
    have none := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦
      mul_nonneg (div_nonneg (lambdaKResidueClass_nonneg d q i) (Nat.cast_nonneg i)) (nn i))).1 eq.symm n hn
    have div_zero := (mul_eq_zero.1 none).resolve_right (pos n yn nz).ne'
    exact (div_eq_zero_iff.1 div_zero).resolve_right (hy.trans yn).ne'
  · intro empty
    have none : ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (lambdaKResidueClass d q n / n) * t n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      by_cases yn : y < (n:ℝ)
      · by_cases nz : (n:ℝ)<z
        · simp [empty n hn yn nz]
        · have zero : t n = 0 := by simp [t,posPart_of_nonpos (sub_nonpos.2 (le_of_not_gt nz)),mul_nonneg ha.le (posPart_nonneg _)]
          rw [zero,mul_zero]
      · have zero : t n = 0 := by simp [t,posPart_of_nonpos (sub_nonpos.2 (le_of_not_gt yn)),mul_nonneg hb.le (posPart_nonneg _)]
        rw [zero,mul_zero]
    linarith only [eq,none]

/-- The three-point recovery works without knowing the normalizing constant in R. -/
theorem recover_without_constant {d q : ℕ} [Fact d.Prime] [NeZero q] (m : ℕ) (hm : 2≤m) :
    let F (x : ℝ) := x*(primeRemainder d q x + Real.log x/q.totient)
    (m:ℝ)*(F (m-1)+F (m+1)-2*F m) = lambdaKResidueClass d q m := by
  dsimp only
  rw [← second_difference (d:=d) (q:=q) m hm]
  unfold integrated
  ring

end New.PrimeCutoff
