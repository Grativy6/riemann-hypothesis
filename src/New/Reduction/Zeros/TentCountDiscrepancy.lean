module

public import New.Reduction.Zeros.CutoffEntropyBounds
public import New.Reduction.Zeros.PrimeNumberTheorem
import Mathlib.Tactic

/-!
# The tent against continuous mass and actual prime counts

The entropy contribution is exactly the integral of the tent against dt/t.
The excess above the reciprocal chord is also the weighted difference between
the left and right counting errors. A common bias cancels from this measurement.
-/

@[expose] public section

open MeasureTheory Set Finset Filter Real InformationTheory
open scoped Topology
namespace New.PrimeCutoff

noncomputable def tent (a b y z t : ℝ) := min (a*(t-y)⁺) (b*(z-t)⁺)

lemma tent_left {a b y x z t : ℝ} (weights : a+b=1) (mix : a*y+b*z=x)
    (lo : y≤t) (left : t≤x) (xz : x≤z) : tent a b y z t = a*(t-y) := by
  rw [tent,posPart_of_nonneg (sub_nonneg.2 lo),posPart_of_nonneg (sub_nonneg.2 (left.trans xz)),min_eq_left]
  calc a*(t-y) = b*(z-t)+(t-x) := by linear_combination t*weights-mix
    _ ≤ _ := by linarith

lemma tent_right {a b y x z t : ℝ} (weights : a+b=1) (mix : a*y+b*z=x)
    (yx : y≤x) (right : x≤t) (hi : t≤z) : tent a b y z t = b*(z-t) := by
  rw [tent,posPart_of_nonneg (sub_nonneg.2 (yx.trans right)),posPart_of_nonneg (sub_nonneg.2 hi),min_eq_right]
  calc b*(z-t) = a*(t-y)+(x-t) := by linear_combination mix-t*weights
    _ ≤ _ := by linarith

/-- Integrating the tent against dt/t produces exactly the KL normalization numerator. -/
theorem tent_integral {a b y x z : ℝ} (hy : 0<y) (weights : a+b=1)
    (mix : a*y+b*z=x) (yx : y≤x) (xz : x≤z) :
    (∫ t in y..z, tent a b y z t/t) = a*y*Real.log (y/x)+b*z*Real.log (z/x) := by
  have hx := hy.trans_le yx
  have hz := hx.trans_le xz
  have continuous (l r : ℝ) (hl : 0<l) (lr : l≤r) :
      IntervalIntegrable (fun t : ℝ ↦ tent a b y z t/t) volume l r := by
    apply ContinuousOn.intervalIntegrable_of_Icc lr
    have notzero (t : ℝ) (mem : t∈Set.Icc l r) : t ≠ 0 := (hl.trans_le mem.1).ne'
    fun_prop (disch := assumption) [tent,posPart_def]
  have invint (l r : ℝ) (hl : 0<l) (lr : l≤r) :
      IntervalIntegrable (fun t : ℝ ↦ 1/t) volume l r := by
    apply ContinuousOn.intervalIntegrable_of_Icc lr
    exact continuousOn_const.div continuousOn_id (fun _ ht ↦ (hl.trans_le ht.1).ne')
  rw [← intervalIntegral.integral_add_adjacent_intervals (continuous y x hy yx) (continuous x z hx xz)]
  have first : (∫ t in y..x, tent a b y z t/t) = a*(x-y)-a*y*Real.log (x/y) := by
    calc _ = ∫ t in y..x, a - (a*y)*(1/t) := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [Set.uIcc_of_le yx] at ht
            dsimp only
            rw [tent_left weights mix ht.1 ht.2 xz]
            field [(hy.trans_le ht.1).ne']
      _ = _ := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const ((invint y x hy yx).const_mul _),
          intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_one_div_of_pos hy hx]
        simp [smul_eq_mul,mul_comm]
  have last : (∫ t in x..z, tent a b y z t/t) = b*z*Real.log (z/x) - b*(z-x) := by
    calc _ = ∫ t in x..z, (b*z)*(1/t) - b := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [Set.uIcc_of_le xz] at ht
            dsimp only
            rw [tent_right weights mix yx ht.1 ht.2]
            field [(hx.trans_le ht.1).ne']
      _ = _ := by
        rw [intervalIntegral.integral_sub ((invint x z hx xz).const_mul _) intervalIntegrable_const,
          intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_one_div_of_pos hx hz]
        simp [smul_eq_mul,mul_comm]
  rw [first,last,Real.log_div hx.ne' hy.ne',Real.log_div hy.ne' hx.ne']
  linear_combination x*weights - mix

/-- The same tent tests the constant continuous density and the arithmetic prime atoms. -/
theorem remainder_eq_tent_discrepancy {d q : ℕ} [Fact d.Prime] [NeZero q] {a b y x z : ℝ}
    (hy : 0<y) (ha : 0≤a) (hb : 0≤b) (weights : a+b=1) (mix : a*y+b*z=x)
    (yx : y≤x) (xz : x≤z) :
    primeRemainder d q x - (a*(y/x)*primeRemainder d q y + b*(z/x)*primeRemainder d q z) =
      ((∫ t in y..z, tent a b y z t/t)/q.totient -
       ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, lambdaKResidueClass d q n/n*tent a b y z n)/x := by
  rw [exact_chord_with_entropy hy ha hb weights mix yx xz,
    (entropy_of_chord hy (hy.trans_le (yx.trans xz)) (hy.trans_le yx) ha hb weights mix).2.2,
    tent_integral hy weights mix yx xz]
  unfold tent
  ring

lemma remainder_change {d q : ℕ} [Fact d.Prime] [NeZero q] {u v : ℝ} (hu : 1≤u) (uv : u≤v) :
    primeRemainder d q v-primeRemainder d q u = ∫ t in u..v, countError d q t/t^2 := by
  rw [primeRemainder_eq_integral_countError_sub (hu.trans uv), primeRemainder_eq_integral_countError_sub hu,
    sub_sub_sub_cancel_right,intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_countError_div_sq le_rfl (hu.trans uv))
      (intervalIntegrable_countError_div_sq le_rfl hu)]

lemma integral_inv_sq {u v : ℝ} (hu : 0<u) (uv : u≤v) :
    (∫ t in u..v, 1/t^2) = 1/u-1/v := by
  have smooth : IntervalIntegrable (fun t : ℝ ↦ 1/t^2) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc uv (continuousOn_const.div (continuousOn_id.pow 2)
      (fun _ h ↦ (pow_pos (hu.trans_le h.1) 2).ne'))
  have deriv (t : ℝ) (ht : t∈Set.uIcc u v) : HasDerivAt (fun s : ℝ ↦ -s⁻¹) (1/t^2) t := by
    rw [Set.uIcc_of_le uv] at ht
    simpa [one_div,inv_pow,Pi.neg_def] using (hasDerivAt_inv (hu.trans_le ht.1).ne').neg
  simpa [one_div,sub_eq_add_neg,add_comm] using intervalIntegral.integral_eq_sub_of_hasDerivAt deriv smooth


/-- A reciprocal-square weighted mean of the arithmetic counting error. -/
noncomputable def meanError (d q : ℕ) [Fact d.Prime] (u v : ℝ) :=
  (∫ t in u..v, countError d q t/t^2)/(1/u-1/v)

noncomputable def leftShare (y x z : ℝ) := (z-x)/(z-y)*(y/x)
noncomputable def rightShare (y x z : ℝ) := (x-y)/(z-y)*(z/x)
noncomputable def gapFactor (y x z : ℝ) := (x-y)*(z-x)/((z-y)*x^2)

lemma shares_total {y x z : ℝ} (hy : 0<y) (left : y<x) (right : x<z) :
    leftShare y x z + rightShare y x z = 1 := by
  have hx := hy.trans left
  have gap := sub_pos.2 (left.trans right)
  dsimp [leftShare,rightShare]
  field

lemma mean_denominator {u v : ℝ} (hu : 0<u) (uv : u<v) : 0<1/u-1/v :=
  sub_pos.2 (one_div_lt_one_div_of_lt hu uv)

theorem chord_eq_local_mean_drop {d q : ℕ} [Fact d.Prime] [NeZero q] {y x z : ℝ}
    (hy : 1≤y) (left : y<x) (right : x<z) :
    primeRemainder d q x - (leftShare y x z * primeRemainder d q y + rightShare y x z * primeRemainder d q z) =
      gapFactor y x z * (meanError d q y x - meanError d q x z) := by
  have h₀ := zero_lt_one.trans_le hy
  have hx := h₀.trans left
  have hz := hx.trans right
  have gap := sub_pos.2 (left.trans right)
  have L := mean_denominator h₀ left
  have R := mean_denominator hx right
  have balanceL : gapFactor y x z /(1/y-1/x)=leftShare y x z := by
    unfold gapFactor leftShare
    field_simp [L.ne',hx.ne',h₀.ne',gap.ne', (sub_pos.2 left).ne']

  have balanceR : gapFactor y x z /(1/x-1/z)=rightShare y x z := by
    unfold gapFactor rightShare
    field_simp [R.ne',hx.ne',hz.ne',gap.ne', (sub_pos.2 right).ne']

  rw [meanError,meanError,←remainder_change hy left.le,←remainder_change (hy.trans left.le) right.le]
  have regroup (g u v : ℝ) : g*(u/v)=(g/v)*u := by ring
  rw [mul_sub,regroup (gapFactor y x z) _ (1/y-1/x),regroup (gapFactor y x z) _ (1/x-1/z),balanceL,balanceR]
  linear_combination -(primeRemainder d q x) * shares_total h₀ left right

lemma mean_le {d q : ℕ} [Fact d.Prime] [NeZero q] {u v M : ℝ} (hu : 1≤u) (uv : u<v)
    (upper : ∀ t∈Set.Icc u v, countError d q t≤M) : meanError d q u v ≤ M := by
  have hp := zero_lt_one.trans_le hu
  have ai : IntervalIntegrable (fun t : ℝ ↦ 1/t^2) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc uv.le (continuousOn_const.div (continuousOn_id.pow 2)
      (fun _ h ↦ (pow_pos (hp.trans_le h.1) 2).ne'))
  apply (div_le_iff₀ (mean_denominator hp uv)).2
  calc (∫ t in u..v, countError d q t/t^2) ≤ ∫ t in u..v, M*(1/t^2) := by
        apply intervalIntegral.integral_mono_on uv.le (intervalIntegrable_countError_div_sq hu uv.le) (ai.const_mul M)
        intro t ht
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (upper t ht) (sq_nonneg t)
    _ = _ := by rw [intervalIntegral.integral_const_mul,integral_inv_sq hp uv.le]

lemma le_mean {d q : ℕ} [Fact d.Prime] [NeZero q] {u v M : ℝ} (hu : 1≤u) (uv : u<v)
    (lower : ∀ t∈Set.Icc u v, M≤countError d q t) : M ≤ meanError d q u v := by
  have hp := zero_lt_one.trans_le hu
  have ai : IntervalIntegrable (fun t : ℝ ↦ 1/t^2) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc uv.le (continuousOn_const.div (continuousOn_id.pow 2)
      (fun _ h ↦ (pow_pos (hp.trans_le h.1) 2).ne'))
  apply (le_div_iff₀ (mean_denominator hp uv)).2
  calc M*(1/u-1/v) = ∫ t in u..v, M*(1/t^2) := by rw [intervalIntegral.integral_const_mul,integral_inv_sq hp uv.le]
    _ ≤ ∫ t in u..v, countError d q t/t^2 := by
        apply intervalIntegral.integral_mono_on uv.le (ai.const_mul M) (intervalIntegrable_countError_div_sq hu uv.le)
        intro t ht
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (lower t ht) (sq_nonneg t)

/-- Only a drop in the counting error from left to right costs an upper estimate.
A constant error shared by both sides cancels exactly. -/
theorem chord_le_of_count_drawdown {d q : ℕ} [Fact d.Prime] [NeZero q] {y x z D : ℝ}
    (hy : 1≤y) (left : y<x) (right : x<z)
    (drop : ∀ u∈Set.Icc y x, ∀ v∈Set.Icc x z, countError d q u-countError d q v ≤ D) :
    primeRemainder d q x - (leftShare y x z * primeRemainder d q y + rightShare y x z * primeRemainder d q z)
      ≤ gapFactor y x z*D := by
  rw [chord_eq_local_mean_drop hy left right]
  have compare (v : ℝ) (hv : v∈Set.Icc x z) :
      meanError d q y x ≤ countError d q v+D :=
    mean_le hy left fun u hu ↦ by linarith only [drop u hu v hv]
  have lower : meanError d q y x-D ≤ meanError d q x z :=
    le_mean (hy.trans left.le) right fun v hv ↦ by linarith only [compare v hv]
  have nonneg : 0≤gapFactor y x z := div_nonneg
    (mul_nonneg (sub_nonneg.2 left.le) (sub_nonneg.2 right.le))
    (mul_nonneg (sub_nonneg.2 (left.trans right).le) (sq_nonneg _))
  exact mul_le_mul_of_nonneg_left (by linarith only [lower]) nonneg

lemma countError_drop_eq {d q : ℕ} [Fact d.Prime] {u v : ℝ} (uv : u≤v) :
    countError d q u-countError d q v =
      (v-u)/q.totient - ∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, lambdaKResidueClass d q n := by
  let L := Finset.Icc 0 ⌊u⌋₊
  let R := Finset.Ioc ⌊u⌋₊ ⌊v⌋₊
  have h := Nat.floor_mono uv
  have cover : L ∪ R = Finset.Icc 0 ⌊v⌋₊ := by
    ext n;simp only [L,R,Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc];omega
  have dis : Disjoint L R := Finset.disjoint_left.2 fun n l r ↦
    (Finset.mem_Ioc.1 r).1.not_ge (Finset.mem_Icc.1 l).2
  unfold countError
  rw [←cover,Finset.sum_union dis]
  dsimp [L,R]
  ring

end New.PrimeCutoff
