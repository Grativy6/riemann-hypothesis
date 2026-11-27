module

public import New.Reduction.Zeros.PrimeCutoffChord
public import New.Reduction.Zeros.SmallPrimeBudget
import Mathlib.Tactic

/-!
# Power grids for the actual prime remainder

The logarithmic chord penalty is quadratic in the relative gap. For degrees one
through four, the resulting interpolation error fits the half-exponent bound.
The power may depend on the auxiliary prime while the same light tail works.
-/

@[expose] public section

open Nat Real Filter
namespace New.PrimeCutoff

/-- For the first four power grids, consecutive endpoints are within a factor
sixteen and the quadratic interpolation error is at most 225/sqrt(x). -/
lemma small_power_mesh {k n : ℕ} (hk : 1≤k) (hk₄ : k≤4) (hn : 1≤n) {x : ℝ}
    (lo : (n:ℝ)^k≤x) (hi : x≤((n:ℝ)+1)^k) :
    x≤16*(n:ℝ)^k ∧
    (x-(n:ℝ)^k)*(((n:ℝ)+1)^k-x)/x^2 ≤ 225*x^(-(1/2):ℝ) := by
  let u := (n:ℝ)
  have hu : 1≤u := by change 1≤(n:ℝ); exact_mod_cast hn
  have hu₀ : 0<u := one_pos.trans_le hu
  have hx : 0<x := (pow_pos hu₀ k).trans_le lo
  have htwo : u+1≤2*u := by linarith
  have h16 : (2:ℝ)^k≤16 := (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hk₄).trans_eq (by norm_num)
  have scale : x≤16*u^k := calc
    x ≤ (u+1)^k := hi
    _ ≤ (2*u)^k := pow_le_pow_left₀ (by linarith) htwo k
    _ = (2:ℝ)^k*u^k := mul_pow _ _ _
    _ ≤ 16*u^k := mul_le_mul_of_nonneg_right h16 (pow_nonneg hu₀.le _)
  have h₂ : u≤u^2 := le_self_pow₀ hu (by decide)
  have h₃ : u^2≤u^3 := pow_le_pow_right₀ hu (by decide)
  have h₄ : u^3≤u^4 := pow_le_pow_right₀ hu (by decide)
  have jump : ((u+1)^k-u^k)*u ≤ 15*u^k := by
    interval_cases k <;> nlinarith only [hu,h₂,h₃,h₄]
  have relative : ((u+1)^k-u^k)/x ≤ 15/u :=
    (div_le_div_iff₀ hx hu₀).2 (jump.trans (by linarith only [lo]))
  have fourth : x ≤ ((2*u)^2)^2 := by
    calc x ≤ (u+1)^k := hi
      _ ≤ (u+1)^4 := pow_le_pow_right₀ (by linarith) hk₄
      _ ≤ (2*u)^4 := pow_le_pow_left₀ (by linarith) htwo 4
      _ = _ := by ring
  have root : √x ≤ 4*u^2 := by
    have h := Real.sqrt_le_sqrt fourth
    rwa [Real.sqrt_sq (sq_nonneg _),mul_pow,show (2:ℝ)^2=4 by norm_num] at h
  have positive : 0≤((u+1)^k-u^k)/x := div_nonneg (sub_nonneg.2 (lo.trans hi)) hx.le
  refine ⟨scale,?_⟩
  change (x-u^k)*((u+1)^k-x)/x^2 ≤ _
  calc _ ≤ (((u+1)^k-u^k)/x)^2/4 := by
        rw [div_pow, div_div]
        apply (div_le_div_iff₀ (sq_pos_of_pos hx) (by positivity)).2
        nlinarith only [mul_nonneg (sq_nonneg ((x-u^k)-((u+1)^k-x))) (sq_nonneg x)]
    _ ≤ (15/u)^2/4 := by gcongr
    _ = 225/(4*u^2) := by field
    _ ≤ 225/√x := div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hx) root
    _ = _ := by rw [Real.rpow_neg hx.le,← Real.sqrt_eq_rpow,div_eq_mul_inv]

/-- Enclose a positive real cutoff between natural k-th powers. -/
lemma enclose_by_powers {k : ℕ} (hk : 0<k) {x : ℝ} (hx : 1≤x) :
    let n := ⌊x^(1/(k:ℝ))⌋₊
    1≤n ∧ (n:ℝ)^k≤x ∧ x≤((n:ℝ)+1)^k := by
  let r := x^(1/(k:ℝ))
  have hx₀ := zero_lt_one.trans_le hx
  have hk₀ : (0:ℝ)<k := Nat.cast_pos.2 hk
  have hr : 1≤r := Real.one_le_rpow hx (by positivity)
  have root : r^k=x := by
    rw [show r=x^(1/(k:ℝ)) from rfl,← Real.rpow_mul_natCast hx₀.le,div_mul_cancel₀ _ hk₀.ne',Real.rpow_one]
  exact ⟨Nat.le_floor (by simpa only [Nat.cast_one] using hr),
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (zero_le_one.trans hr)) k).trans_eq root,
    root.symm.trans_le (pow_le_pow_left₀ (zero_le_one.trans hr) (Nat.lt_floor_add_one r).le k)⟩


/-- Bounds on a power grid extend to all real cutoffs, using the actual positive
prime-power measure. The argument covers the first four integer powers. -/
theorem real_of_power_grid {d q k : ℕ} [Fact d.Prime] [NeZero q] (hk : 1≤k) (hk₄ : k≤4)
    (samples : ∀ ε : ℝ, 0<ε → ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      primeRemainder d q ((n:ℝ)^k) ≤ A*((n:ℝ)^k)^(-1/2+ε)) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ C*x^(-1/2+ε) := by
  let δ := min ε (1/4:ℝ)
  let t := -(1:ℝ)/2+δ
  have hδ : 0<δ := lt_min hε (by norm_num)
  have ht : t≤0 := by dsimp [t]; linarith [show δ≤1/4 from min_le_right _ _]
  have ht₁ : -(1/2:ℝ)≤t := by dsimp [t]; linarith
  have htε : t ≤ -1/2+ε := by dsimp [t]; linarith [show δ≤ε from min_le_left _ _]
  obtain ⟨A,bound⟩ := samples δ hδ
  have hk₀ : (0:ℝ)<k := by exact_mod_cast hk
  have root_tends : Tendsto (fun x : ℝ ↦ ⌊x^(1/(k:ℝ))⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by positivity))
  refine ⟨4*|A| + 225,?_⟩
  filter_upwards [root_tends.eventually bound,
    root_tends.eventually ((tendsto_add_atTop_nat 1).eventually bound),eventually_ge_atTop (1:ℝ)]
    with x at_left at_right hx
  let n := ⌊x^(1/(k:ℝ))⌋₊
  obtain ⟨hn,lo,hi⟩ := enclose_by_powers hk hx
  change (n:ℝ)^k≤x at lo
  change x≤((n:ℝ)+1)^k at hi
  change 1≤n at hn
  have npos : (0:ℝ)<n := by exact_mod_cast hn
  have xpos := zero_lt_one.trans_le hx
  let y := (n:ℝ)^k
  let z := ((n:ℝ)+1)^k
  have yz : y < z := pow_lt_pow_left₀ (lt_add_one (n:ℝ)) (Nat.cast_nonneg n) (by omega)
  have ypositive : 0<y := pow_pos npos _
  obtain ⟨span,mesh⟩ := small_power_mesh hk hk₄ hn lo hi
  have qpos : (1:ℝ)≤q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have compare : y^t ≤ 4*x^(-1/2+ε) := by
    have lower : x/16 ≤ y := by dsimp [y]; linarith only [span]
    have h16 : (16:ℝ)^(-(1/2):ℝ) = 1/4 := by
      rw [Real.rpow_neg (by norm_num),← Real.sqrt_eq_rpow];norm_num
    calc y^t ≤ (x/16)^t := Real.rpow_le_rpow_of_nonpos (by positivity) lower ht
      _ = x^t / (16:ℝ)^t := Real.div_rpow xpos.le (by norm_num) _
      _ ≤ x^t/((16:ℝ)^(-(1/2):ℝ)) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg xpos.le t)
          (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<16) _)
          (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤16) ht₁)
      _ = 4*x^t := by rw [h16]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx htε) (by norm_num)
  have later := (Real.rpow_le_rpow_of_nonpos ypositive yz.le ht).trans compare
  let M := |A| * (4*x^(-1/2+ε))
  have lbound : primeRemainder d q y ≤ M :=
    at_left.trans (mul_le_mul (le_abs_self A) compare (Real.rpow_nonneg ypositive.le _) (abs_nonneg _))
  have rb : primeRemainder d q z ≤ A*z^t := by
    simpa only [Nat.cast_add_one] using at_right
  have rbound : primeRemainder d q z ≤ M :=
    rb.trans (mul_le_mul (le_abs_self A) later (Real.rpow_nonneg (by positivity) _) (abs_nonneg _))
  have err : (x-y)*(z-x)/(x^2*q.totient) ≤ 225*x^(-1/2+ε) := by
    rw [← div_div]
    calc _ ≤ (x-y)*(z-x)/x^2 :=
          div_le_self (div_nonneg (mul_nonneg (sub_nonneg.2 lo) (sub_nonneg.2 hi)) (sq_nonneg _)) qpos
      _ ≤ 225*x^(-(1/2):ℝ) := mesh
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by norm_num)
  calc primeRemainder d q x ≤ M + (x-y)*(z-x)/(x^2*q.totient) :=
        remainder_le_of_endpoint_bounds ypositive lo hi yz lbound rbound
    _ ≤ M + 225*x^(-1/2+ε) := add_le_add (le_refl M) err
    _ = _ := by dsimp [M];ring

end New.PrimeCutoff


namespace New.TwistSelection

/-- The grid degree can be chosen separately for every retained auxiliary prime. -/
def powerBoundsOn (degree : ℕ → ℕ) (pool : Set ℕ) : Prop :=
  ∀ d : Nat.Primes, (d:ℕ) ∈ pool → ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      primeRemainder d 18480 ((n:ℝ)^(degree d)) ≤ A*((n:ℝ)^(degree d))^(-1/2+ε)

theorem remainderBoundsOn_iff_powerBoundsOn {degree : ℕ → ℕ} {pool : Set ℕ}
    (range : ∀ d : Nat.Primes, (d:ℕ)∈pool → 1 ≤ degree d ∧ degree d ≤ 4) :
    remainderBoundsOn pool ↔ powerBoundsOn degree pool := by
  refine ⟨fun h d hd ε hε ↦ ?_, fun h d hd ↦ ?_⟩
  · obtain ⟨C,bound⟩ := h d hd ε hε
    have pos := (range d hd).1
    have step : Tendsto (fun n : ℕ ↦ (n:ℝ)^(degree d)) atTop atTop :=
      (tendsto_pow_atTop (by omega : degree d ≠ 0)).comp tendsto_natCast_atTop_atTop
    exact ⟨C,step.eventually bound⟩
  · exact PrimeCutoff.real_of_power_grid (range d hd).1 (range d hd).2 (h d hd)

/-- One positive-weight tail, under any specified budget, works for all allowed
assignments of integer, square, cube or fourth-power cutoffs. -/
theorem light_prime_power_grids_imply_RH {η : ℝ} (hη : 0<η) :
    ∃ K : ℕ, Summable (weight ∘ (Subtype.val : after seventeenPool K → ℕ)) ∧
      0 < (∑' d : after seventeenPool K, weight d) ∧
      (∑' d : after seventeenPool K, weight d) < η ∧
      ∀ degree : ℕ → ℕ, (∀ d : Nat.Primes, (d:ℕ)∈after seventeenPool K →
        1 ≤ degree d ∧ degree d ≤ 4) → powerBoundsOn degree (after seventeenPool K) → RiemannHypothesis := by
  obtain ⟨K,sums,pos,small,criterion⟩ := arbitrarily_light_RH_criterion hη
  exact ⟨K,sums,pos,small,fun _ range bound ↦
    criterion ((remainderBoundsOn_iff_powerBoundsOn range).2 bound)⟩

/-- In particular, retaining fourth-power observations suffices on that fixed tail. -/
theorem arbitrarily_light_fourth_power_RH {η : ℝ} (hη : 0<η) :
    ∃ K : ℕ, Summable (weight ∘ (Subtype.val : after seventeenPool K → ℕ)) ∧
      0 < (∑' d : after seventeenPool K, weight d) ∧
      (∑' d : after seventeenPool K, weight d) < η ∧
      (powerBoundsOn (fun _ ↦ 4) (after seventeenPool K) → RiemannHypothesis) := by
  obtain ⟨K,sums,pos,small,all⟩ := light_prime_power_grids_imply_RH hη
  exact ⟨K,sums,pos,small,all (fun _ ↦ 4) (by intro d hd; decide)⟩

end New.TwistSelection
