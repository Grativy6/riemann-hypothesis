module

public import New.Reduction.Zeros.SelectedTwistPrimes
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
Retain at most 2^k/(k+1)^3 marks in the kth block, in increasing order. Their log-weight sums to a finite number. If the candidate set had divergent weight, a power saving on the retained count would eventually leave every block below quota and retain every large candidate.
-/

@[expose] public section

open Nat Set Finset Filter Asymptotics Real
open scoped Classical Nat Topology
namespace New.TwistSelection

/-- Keep at most this many primes in the k-th dyadic interval. -/
def quota (k : ℕ) := 2^k/(k+1)^3

noncomputable def block (S : Set ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.Ico (2^k) (2^(k+1))).filter (· ∈ S)

/-- Inspect a finite block in increasing order. -/
noncomputable def kept (S : Set ℕ) (k : ℕ) : Finset ℕ :=
  (((block S k).sort).take (quota k)).toFinset

/-- Membership uses only the given candidate set and the dyadic index of n. -/
def thin (S : Set ℕ) : Set ℕ := {n | n ∈ kept S (Nat.log 2 n)}

lemma kept_subset (S : Set ℕ) (k : ℕ) : kept S k ⊆ block S k := by
  intro n hn
  exact (Finset.mem_sort (· ≤ ·)).1 (List.mem_of_mem_take (List.mem_toFinset.1 hn))

lemma card_kept (S : Set ℕ) (k : ℕ) :
    (kept S k).card = min (quota k) (block S k).card := by
  unfold kept
  rw [List.toFinset_card_of_nodup ((List.take_sublist _ _).nodup ((block S k).sort_nodup _)),
    List.length_take,Finset.length_sort]

lemma thin_subset (S : Set ℕ) : thin S ⊆ S :=
  fun n hn ↦ (Finset.mem_filter.1 (kept_subset S (Nat.log 2 n) hn)).2

lemma kept_mem (S : Set ℕ) {n k : ℕ} (hn : n ∈ kept S k) : n ∈ thin S := by
  obtain ⟨le,lt⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 (kept_subset S k hn)).1
  change n ∈ kept S (Nat.log 2 n)
  rwa [Nat.log_eq_of_pow_le_of_lt_pow le lt]

lemma quota_le (k : ℕ) : (quota k:ℝ) ≤ (2:ℝ)^k/((k:ℝ)+1)^3 := by
  rw [le_div_iff₀ (by positivity)]
  have bound : quota k * (k+1)^3 ≤ 2^k := Nat.div_mul_le_self _ _
  exact_mod_cast bound

lemma lt_quota_succ (k : ℕ) : (2:ℝ)^k/((k:ℝ)+1)^3 < (quota k:ℝ)+1 := by
  rw [div_lt_iff₀ (by positivity)]
  have a := Nat.mod_lt (2^k) (by positivity : 0<(k+1)^3)
  have e := Nat.div_add_mod (2^k) ((k+1)^3)
  have bound : 2^k < (quota k+1)*(k+1)^3 := by
    rw [add_mul,one_mul,Nat.mul_comm (quota k)]
    unfold quota
    omega
  exact_mod_cast bound

lemma weight_nonneg (n : ℕ) : 0 ≤ weight n :=
  div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)

lemma block_weight_le (S : Set ℕ) (k : ℕ) :
    (∑ n : kept S k, weight n) ≤ Real.log 2 / ((k:ℝ)+1)^2 := by
  have single (n : kept S k) :
      weight n ≤ (((k:ℝ)+1)*Real.log 2)/(2:ℝ)^k := by
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 (kept_subset S k n.property)).1
    have lower : (2:ℝ)^k ≤ (n.val:ℝ) := by exact_mod_cast lo
    have upper : (n.val:ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast hi.le
    have hlog : Real.log (n:ℝ) ≤ ((k:ℝ)+1)*Real.log 2 := by
      simpa using Real.log_le_log (lt_of_lt_of_le (by positivity) lower) upper
    exact div_le_div₀ (by positivity) hlog (by positivity) lower
  calc
    _ ≤ ∑ _n : kept S k, (((k:ℝ)+1)*Real.log 2)/(2:ℝ)^k := Finset.sum_le_sum fun n _ ↦ single n
    _ = (kept S k).card * ((((k:ℝ)+1)*Real.log 2)/(2:ℝ)^k) := by simp
    _ ≤ ((2:ℝ)^k/((k:ℝ)+1)^3) * ((((k:ℝ)+1)*Real.log 2)/(2:ℝ)^k) := by
      gcongr
      exact (Nat.cast_le.2 ((card_kept S k).le.trans (min_le_left _ _))).trans (quota_le k)
    _ = _ := by field_simp

theorem summable_thin (S : Set ℕ) : Summable (weight ∘ (Subtype.val : thin S → ℕ)) := by
  have series : Summable (fun k : ℕ ↦ Real.log 2 / ((k:ℝ)+1)^2) := by
    have base := (summable_nat_add_iff (f := fun n : ℕ ↦ 1/(n:ℝ)^2) 1).2
      (Real.summable_one_div_nat_pow.2 (by decide : 1 < 2))
    simpa [div_eq_mul_inv] using base.mul_left (Real.log 2)
  have sums : Summable (fun k : ℕ ↦ ∑ n : kept S k, weight n) :=
    series.of_nonneg_of_le (fun k ↦ Finset.sum_nonneg fun n _ ↦ weight_nonneg _) (block_weight_le S)
  let f (v : (k : ℕ) × kept S k) := weight v.2.val
  have total : Summable f := by
    refine (summable_sigma_of_nonneg (f := f) (fun v ↦ weight_nonneg v.2.val)).2
      ⟨fun k ↦ (hasSum_fintype _).summable, ?_⟩
    simpa only [tsum_fintype, f] using sums
  let index (n : thin S) : (k : ℕ) × kept S k := ⟨Nat.log 2 n, ⟨n,n.property⟩⟩
  have inj : Function.Injective index := fun u v eq ↦
    Subtype.ext (congrArg (fun t : (k : ℕ) × kept S k ↦ t.2.val) eq)
  exact (total.comp_injective inj : Summable (f ∘ index))


/-- The dyadic quota eventually exceeds C times the α-th power of the block endpoint,
for every fixed α < 1. The cubic divisor costs only a polynomial in the block index. -/
lemma eventually_power_lt_quota {α : ℝ} (hα : α < 1) (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, C*((2:ℝ)^(k+1))^α < quota k := by
  let r := (2:ℝ)^α/2
  have hr₀ : 0 ≤ r := by dsimp [r]; positivity
  have hr : r < 1 := by
    change (2:ℝ)^α/2 < 1
    rw [div_lt_one (by norm_num)]
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hα
  have decay (b : ℝ) (hb : |b|<1) :
      Tendsto (fun k : ℕ ↦ ((k:ℝ)+1)^3 * b^(k+1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_pow_const_mul_const_pow_of_abs_lt_one 3 hb).comp (tendsto_add_atTop_nat 1)
  have rhs : Tendsto (fun k : ℕ ↦ (2*C)*(((k:ℝ)+1)^3*r^(k+1)) +
      2*(((k:ℝ)+1)^3*(1/2:ℝ)^(k+1))) atTop (𝓝 0) := by
    simpa using ((decay r (by rwa [abs_of_nonneg hr₀])).const_mul (2*C)).add
      ((decay (1/2:ℝ) (by norm_num)).const_mul 2)
  filter_upwards [rhs.eventually_lt_const zero_lt_one] with k hk
  have powers : ((2:ℝ)^(k+1))^α = ((2:ℝ)^α)^(k+1) := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul (by norm_num),Real.rpow_natCast]
  have key : (C*((2:ℝ)^(k+1))^α+1) * ((k:ℝ)+1)^3 / (2:ℝ)^k < 1 := by
    convert hk using 1
    rw [powers]
    dsimp only [r]
    rw [div_pow, div_pow, pow_succ (2:ℝ) k, one_pow]
    field_simp
  have stronger : C*((2:ℝ)^(k+1))^α+1 < (2:ℝ)^k / ((k:ℝ)+1)^3 := by
    rw [lt_div_iff₀ (by positivity)]
    simpa using (div_lt_iff₀ (by positivity : 0 < (2:ℝ)^k)).1 key
  linarith [lt_quota_succ k]

lemma block_card_le_count (S : Set ℕ) (k : ℕ) :
    ((kept S k).card : ℝ) ≤ count (thin S) (2^(k+1)) := by
  apply Nat.cast_le.2
  apply Finset.card_le_card
  intro d hd
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 (kept_subset S k hd)).1
  exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨(by positivity : 0 < 2^k).trans_le lo,hi.le⟩,
    kept_mem S hd⟩

/-- If the thinned count had a power saving, then eventually the dyadic quota would
never fill. Every sufficiently large original mark would have survived. -/
lemma eventually_mem_thin_iff_of_power_bound (S : Set ℕ) {α : ℝ} (hα : α < 1)
    (bound : count (thin S) =O[atTop] fun x : ℕ ↦ (x:ℝ)^α) :
    ∀ᶠ n : ℕ in atTop, n ∈ thin S ↔ n ∈ S := by
  obtain ⟨C,_,hC⟩ := bound.exists_nonneg
  have tpow : Tendsto (fun k : ℕ ↦ 2^(k+1) : ℕ → ℕ) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ))).comp (tendsto_add_atTop_nat 1)
  have small : ∀ᶠ k : ℕ in atTop, (kept S k).card < quota k := by
    filter_upwards [tpow.eventually hC.bound,eventually_power_lt_quota hα C] with k hk hq
    have npos (x : ℕ) : 0 ≤ count (thin S) x := Nat.cast_nonneg _
    rw [Real.norm_eq_abs,abs_of_nonneg (npos _),Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),Nat.cast_pow,Nat.cast_ofNat] at hk
    exact_mod_cast (block_card_le_count S k).trans_lt (hk.trans_lt hq)
  obtain ⟨K,hK⟩ := small.exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop (2^K)] with n hn
  refine ⟨fun hn ↦ thin_subset S hn,fun hS ↦ ?_⟩
  let k := Nat.log 2 n
  have hkn : K ≤ k := Nat.le_log_of_pow_le (by decide) hn
  have strict := hK k hkn
  rw [card_kept] at strict
  have fits : (block S k).card ≤ quota k := by omega
  have eq : kept S k = block S k := Finset.eq_of_subset_of_card_le (kept_subset S k)
    (by rw [card_kept,min_eq_right fits])
  change n ∈ kept S k
  rw [eq]
  exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨Nat.pow_log_le_self 2
    ((by positivity : 0 < 2^K).trans_le hn).ne',Nat.lt_pow_succ_log_self (by decide) n⟩,hS⟩

/-- One deterministic set has finite log-weight and still exceeds every power x^α
with α < 1 along some cutoffs. -/
theorem thin_no_power_saving {S : Set ℕ}
    (diverges : ¬ Summable (weight ∘ (Subtype.val : S → ℕ))) {α : ℝ} (hα : α < 1) :
    ¬ (count (thin S) =O[atTop] fun x : ℕ ↦ (x:ℝ)^α) := by
  intro bound
  have same : (thin S).indicator weight =ᶠ[cofinite] S.indicator weight := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_mem_thin_iff_of_power_bound S hα bound] with n hn
    simp only [Set.indicator,hn]
  exact diverges (summable_subtype_iff_indicator.2
    ((summable_congr_cofinite same).1 (summable_subtype_iff_indicator.1 (summable_thin S))))

end New.TwistSelection
