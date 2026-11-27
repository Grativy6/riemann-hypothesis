module

public import New.Reduction.Zeros.SmallPrimeBudget
import New.Reduction.Zeros.PrimeNumberTheorem
import Mathlib.Tactic

/-!
# Square sampling in the cutoff variable

The next square above x is within three square roots of x. The actual variation
bound for the smoothed remainder makes this grid sufficient at the half exponent.
The auxiliary prime may independently be drawn from a fixed tail of finite weight.
-/

@[expose] public section

open Real Set Filter Nat
open scoped Topology
namespace New.TwistSelection

/-- A real point and the next perfect square are at most three square roots apart. -/
lemma next_square_mesh {x : ℝ} (hx : 1 ≤ x) :
    x ≤ (⌈√x⌉₊:ℝ)^2 ∧ ((⌈√x⌉₊:ℝ)^2-x)/x ≤ 3*x^(-(1/2):ℝ) := by
  have hx₀ : 0 < x := one_pos.trans_le hx
  have root₁ : 1 ≤ √x := by simpa using Real.sqrt_le_sqrt hx
  have lower := Nat.le_ceil (√x)
  have upper := (Nat.ceil_lt_add_one (Real.sqrt_nonneg x)).le
  have lo : x ≤ (⌈√x⌉₊:ℝ)^2 := by
    simpa [Real.sq_sqrt hx₀.le] using pow_le_pow_left₀ (Real.sqrt_nonneg x) lower 2
  have hi : (⌈√x⌉₊:ℝ)^2 ≤ (√x+1)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) upper 2
  have gap : (⌈√x⌉₊:ℝ)^2-x ≤ 3*√x := by nlinarith [Real.sq_sqrt hx₀.le]
  refine ⟨lo,(div_le_div_of_nonneg_right gap hx₀.le).trans_eq ?_⟩
  rw [Real.rpow_neg hx₀.le,← Real.sqrt_eq_rpow]
  field_simp
  nlinarith [Real.sq_sqrt hx₀.le]

/-- A Lipschitz estimate in relative distance transfers a bound on all sufficiently
large perfect squares to all sufficiently large positive reals at the half exponent. -/
theorem real_bounds_of_square_bounds {R : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (variation : ∀ ⦃y z : ℝ⦄, 1 ≤ y → y ≤ z → |R z - R y| ≤ C*((z-y)/y))
    (on_squares : ∀ ε : ℝ, 0 < ε →
      ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, R ((n:ℝ)^2) ≤ A*((n:ℝ)^2)^(-1/2+ε))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ᶠ x : ℝ in atTop, R x ≤ A*x^(-1/2+ε) := by
  let δ := min ε (1/4:ℝ)
  have hδ := lt_min hε (by norm_num : (0:ℝ)<1/4)
  have hδ₁ : δ ≤ ε := min_le_left _ _
  have hδ₂ : δ ≤ 1/4 := min_le_right _ _
  obtain ⟨A,est⟩ := on_squares δ hδ
  refine ⟨|A|+3*C,?_⟩
  have at_squares : Tendsto (fun x : ℝ ↦ ⌈√x⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp Real.tendsto_sqrt_atTop
  filter_upwards [at_squares.eventually est,eventually_ge_atTop (1:ℝ)] with x at_n hx
  obtain ⟨lo,mesh⟩ := next_square_mesh hx
  have x_pos := one_pos.trans_le hx
  have var := variation hx lo
  have err : R x - R ((⌈√x⌉₊:ℝ)^2) ≤ 3*C*x^(-1/2+ε) := by
    calc
      _ ≤ |R ((⌈√x⌉₊:ℝ)^2)-R x| := by rw [abs_sub_comm]; exact le_abs_self _
      _ ≤ C*(((⌈√x⌉₊:ℝ)^2-x)/x) := var
      _ ≤ C*(3*x^(-(1/2):ℝ)) := mul_le_mul_of_nonneg_left mesh hC
      _ ≤ 3*C*x^(-1/2+ε) := by
        rw [mul_left_comm, mul_assoc]
        gcongr
        linarith
  have power : ((⌈√x⌉₊:ℝ)^2)^(-1/2+δ) ≤ x^(-1/2+ε) :=
    (Real.rpow_le_rpow_of_nonpos x_pos lo (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
  have sample : R ((⌈√x⌉₊:ℝ)^2) ≤ |A| * x^(-1/2+ε) :=
    at_n.trans (mul_le_mul (le_abs_self A) power (by positivity) (abs_nonneg _))
  rw [add_mul]
  linarith

/-- The two sampling choices act on different coordinates: keep a numerical tail of
the fixed prime set, and inspect the entire remainder only at perfect-square cutoffs. -/
def squareBoundsOn (pool : Set ℕ) : Prop :=
  ∀ d : Primes, (d:ℕ) ∈ pool → ∀ ε : ℝ, 0<ε →
    ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      primeRemainder d 18480 ((n:ℝ)^2) ≤ A*((n:ℝ)^2)^(-1/2+ε)

theorem remainderBoundsOn_iff_squareBoundsOn (pool : Set ℕ) :
    remainderBoundsOn pool ↔ squareBoundsOn pool := by
  refine ⟨fun h d hd ε hε ↦ ?_,fun h d hd ↦ ?_⟩
  · obtain ⟨A,est⟩ := h d hd ε hε
    exact ⟨A,(tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop |>.eventually est⟩
  · exact real_bounds_of_square_bounds (C := 13) (by norm_num)
      (by intro y z hy hz; exact abs_primeRemainder_sub_le (d := d) (q := 18480) hy hz) (h d hd)

/-- In particular an arbitrarily light set of prime tests on perfect squares suffices
for the usual Riemann hypothesis, with genuine convergence and positive weight. -/
theorem arbitrarily_light_square_RH_criterion {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, Summable (weight ∘ (Subtype.val : after seventeenPool K → ℕ)) ∧
      0 < (∑' p : after seventeenPool K, weight p) ∧
      (∑' p : after seventeenPool K, weight p) < η ∧
      (squareBoundsOn (after seventeenPool K) → RiemannHypothesis) := by
  obtain ⟨K,sums,pos,budget,criterion⟩ := arbitrarily_light_RH_criterion hη
  exact ⟨K,sums,pos,budget,fun h ↦ criterion ((remainderBoundsOn_iff_squareBoundsOn _).2 h)⟩

end New.TwistSelection
