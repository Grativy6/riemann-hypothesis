module

public import New.Reduction.Zeros.TentCountDiscrepancy
public import New.Reduction.Zeros.PowerGridCriterion
import Mathlib.Tactic

/-!
# A local arithmetic census for fifth-power sampling

The mean-error identity transfers from fifth powers under a separate shortfall
bound of order y^(7/10+ε) on the actual weights in each cell.
-/

@[expose] public section

open Nat Real Finset Set Filter
open scoped Topology
namespace New.PrimeCutoff

/-- The largest one-sided interpolation factor in a fifth-power cell is of order
x^(-6/5). This is the scale against which a local count shortfall is measured. -/
lemma fifth_gap_factor {n : ℕ} (hn : 1≤n) {x : ℝ}
    (left : (n:ℝ)^5<x) (right : x<((n:ℝ)+1)^5) :
    gapFactor ((n:ℝ)^5) x (((n:ℝ)+1)^5) ≤ 8*x^(-(6/5):ℝ) := by
  let u : ℝ := n
  have hu : 1≤u := by change 1≤(n:ℝ);exact_mod_cast hn
  have up := zero_lt_one.trans_le hu
  let y := u^5
  let z := (u+1)^5
  have hx : 0<x := (pow_pos up 5).trans left
  have gz : 0<z-y := sub_pos.2 (left.trans right)
  have a : u≤u^4 := le_self_pow₀ hu (by decide)
  have b : u^2≤u^4 := pow_le_pow_right₀ hu (by decide)
  have c : u^3≤u^4 := pow_le_pow_right₀ hu (by decide)
  have d : 1≤u^4 := one_le_pow₀ hu
  have gap : z-y ≤ 31*u^4 := by dsimp [z,y];nlinarith only [a,b,c,d]
  have inv : u^4 ≤ x^(4/5:ℝ) := by
    calc u^4 = (u^5)^(4/5:ℝ) := by
          rw [←Real.rpow_natCast_mul up.le];norm_num
      _ ≤ _ := Real.rpow_le_rpow (pow_nonneg up.le _) left.le (by norm_num)
  have product : (x-y)*(z-x) ≤ (z-y)^2 /4 := by
    nlinarith only [sq_nonneg ((x-y)-(z-x))]
  change (x-y)*(z-x)/((z-y)*x^2) ≤ _
  calc _ ≤ ((z-y)^2/4)/((z-y)*x^2) := div_le_div_of_nonneg_right product (by positivity)
    _ = (z-y)/x^2/4 := by field
    _ ≤ (31*x^(4/5:ℝ))/x^2/4 :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (gap.trans (by linarith only [inv])) (sq_nonneg x)) (by norm_num)
    _ = (31/4:ℝ)*x^(-(6/5):ℝ) := by
      rw [show -(6/5:ℝ)=4/5-2 by ring,Real.rpow_sub hx,Real.rpow_two]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hx.le _)

/-- The extra arithmetic input controls shortfalls on subintervals inside each
fifth-power cell. It uses the original prime weights and no remainder values. -/
def fifthCellCountBound (d q : ℕ) [Fact d.Prime] : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ B : ℝ, ∀ᶠ n : ℕ in atTop, ∀ u v : ℝ,
    (n:ℝ)^5≤u → u≤v → v≤((n:ℝ)+1)^5 →
    (v-u)/q.totient - ∑ j ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, lambdaKResidueClass d q j ≤ B*((n:ℝ)^5)^(7/10+ε)

theorem real_of_fifths_and_counts {d q : ℕ} [Fact d.Prime] [NeZero q]
    (counts : fifthCellCountBound d q) (samples : ∀ ε : ℝ, 0<ε → ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      primeRemainder d q ((n:ℝ)^5) ≤ A*((n:ℝ)^5)^(-1/2+ε)) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ C*x^(-1/2+ε) := by
  let δ := min ε (1/4:ℝ)
  let t := -(1:ℝ)/2+δ
  have δp : 0<δ := lt_min hε (by norm_num)
  have t₀ : t≤0 := by dsimp [t];linarith [show δ≤1/4 from min_le_right _ _]
  have t₁ : -1≤t := by dsimp [t];linarith
  have tε : t≤-1/2+ε := by dsimp [t];linarith [show δ≤ε from min_le_left _ _]
  obtain ⟨A,bound⟩ := samples δ δp
  obtain ⟨B,localBound⟩ := counts δ δp
  have tends : Tendsto (fun x : ℝ ↦ ⌊x^(1/(5:ℝ))⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num))
  refine ⟨32*|A|+8*|B|,?_⟩
  filter_upwards [tends.eventually bound,tends.eventually ((tendsto_add_atTop_nat 1).eventually bound),
    tends.eventually localBound,eventually_ge_atTop (1:ℝ)] with x l r inside hx
  let n := ⌊x^(1/(5:ℝ))⌋₊
  let y := (n:ℝ)^5
  let z := ((n:ℝ)+1)^5
  obtain ⟨hn,lo,hi⟩ := enclose_by_powers (k:=5) (by decide) hx
  change 1≤n at hn
  change y≤x at lo
  change x≤z at hi
  have np : (1:ℝ)≤n := by exact_mod_cast hn
  have yp : 1≤y := one_le_pow₀ np
  have xp := zero_lt_one.trans_le hx
  have zp : 0<z := xp.trans_le hi
  have size : x≤32*y := by
    calc x ≤ ((n:ℝ)+1)^5 := hi
      _ ≤ (2*(n:ℝ))^5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
      _ = _ := by dsimp [y];ring
  have pyr : y^t ≤ 32*x^(-1/2+ε) := by
    calc y^t ≤ (x/32)^t := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [size]) t₀
      _ = x^t/(32:ℝ)^t := Real.div_rpow xp.le (by norm_num) _
      _ ≤ x^t/((32:ℝ)^(-1:ℝ)) := div_le_div_of_nonneg_left (Real.rpow_nonneg xp.le _)
        (by positivity) (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤32) t₁)
      _ = 32*x^t := by rw [Real.rpow_neg_one];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx tε) (by norm_num)
  let Q := 32*|A| * x^(-1/2+ε)
  have boundY : primeRemainder d q y ≤ Q := by
    calc _ ≤ |A| * (32*x^(-1/2+ε)) := l.trans (mul_le_mul (le_abs_self A) pyr (by positivity) (abs_nonneg _))
      _ = _ := by dsimp [Q];ring
  have rb : primeRemainder d q z ≤ A*z^t := by simpa only [Nat.cast_add_one] using r
  have boundZ : primeRemainder d q z ≤ Q := by
    calc _ ≤ |A| * (32*x^(-1/2+ε)) := rb.trans (mul_le_mul (le_abs_self _)
          ((Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le yp) (lo.trans hi) t₀).trans pyr)
          (Real.rpow_nonneg zp.le _) (abs_nonneg _))
      _ = _ := by dsimp [Q];ring
  have room : Q≤(32*|A|+8*|B|)*x^(-1/2+ε) := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg B]) (Real.rpow_nonneg xp.le _)
  obtain eq | left := lo.eq_or_lt
  · exact (eq ▸ boundY).trans room
  obtain eq | right := hi.eq_or_lt
  · exact (eq.symm ▸ boundZ).trans room
  let D := |B| * x^(7/10+δ)
  have drop (u : ℝ) (hu : u∈Set.Icc y x) (v : ℝ) (hv : v∈Set.Icc x z) :
      countError d q u-countError d q v≤D := by
    have uv := hu.2.trans hv.1
    rw [countError_drop_eq uv]
    exact (inside u v hu.1 uv hv.2).trans (mul_le_mul (le_abs_self _)
      (Real.rpow_le_rpow (zero_le_one.trans yp) lo (by linarith : (0:ℝ)≤7/10+δ))
      (by positivity) (abs_nonneg _))
  have deficit := chord_le_of_count_drawdown yp left right drop
  have fact := fifth_gap_factor hn left right
  have err : gapFactor y x z*D ≤ 8*|B| * x^(-1/2+ε) := calc
    _ ≤ (8*x^(-(6/5):ℝ))*D := mul_le_mul_of_nonneg_right fact (by dsimp [D];positivity)
    _ = 8*|B| * x^t := by
      rw [show t=-(6/5:ℝ)+(7/10+δ) by dsimp [t];ring,Real.rpow_add xp]
      dsimp [D];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx tε) (by positivity)
  have g := sub_pos.2 (left.trans right)
  have lpos : 0≤leftShare y x z := by unfold leftShare;positivity [sub_nonneg.2 right.le,sub_nonneg.2 (left.trans right).le]
  have rpos : 0≤rightShare y x z := by unfold rightShare;positivity [sub_nonneg.2 left.le,sub_nonneg.2 (left.trans right).le]
  have chord : leftShare y x z*primeRemainder d q y+rightShare y x z*primeRemainder d q z ≤ Q := calc
    _ ≤ leftShare y x z*Q+rightShare y x z*Q := add_le_add
      (mul_le_mul_of_nonneg_left boundY lpos) (mul_le_mul_of_nonneg_left boundZ rpos)
    _ = Q := by rw [←add_mul,shares_total (zero_lt_one.trans_le yp) left right,one_mul]
  rw [add_mul]
  dsimp only [Q] at chord
  linarith only [deficit,err,chord]

end New.PrimeCutoff


namespace New.TwistSelection

/-- Fifth-power samples need a separate short-interval arithmetic input. The bound
controls only shortfalls of mass in subintervals of the selected fifth-power cells. -/
theorem light_fifths_with_counts {η : ℝ} (hη : 0<η) :
    ∃ K : ℕ, Summable (weight ∘ (Subtype.val : after seventeenPool K → ℕ)) ∧
      0 < (∑' d : after seventeenPool K, weight d) ∧
      (∑' d : after seventeenPool K, weight d) < η ∧
      (powerBoundsOn (fun _ ↦ 5) (after seventeenPool K) →
        (∀ d : Nat.Primes, (d:ℕ) ∈ after seventeenPool K → PrimeCutoff.fifthCellCountBound d 18480) →
        RiemannHypothesis) := by
  obtain ⟨K,sums,pos,light,criterion⟩ := arbitrarily_light_RH_criterion hη
  exact ⟨K,sums,pos,light,fun samples counts ↦ criterion (fun d hd ↦
    PrimeCutoff.real_of_fifths_and_counts (counts d hd) (samples d hd))⟩

end New.TwistSelection
