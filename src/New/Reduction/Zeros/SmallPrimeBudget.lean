module

public import New.Reduction.Zeros.ThinPrimeCriterion
import Mathlib.Tactic

/-!
# Arbitrarily small positive auxiliary-prime budgets

Removing a finite prefix leaves every required counting comparison available.
Any positive logarithmic budget therefore admits a strictly lighter sufficient
list of primes. Positivity and summability are included with the exact RH implication.
-/

@[expose] public section

open Complex DirichletCharacter Filter Nat Set Finset Asymptotics
open scoped Classical Topology
namespace New.TwistSelection

def after (S : Set ℕ) (K : ℕ) : Set ℕ := {n | n ∈ S ∧ K ≤ n}

lemma count_le_after_add (S : Set ℕ) (K X : ℕ) : count S X ≤ count (after S K) X + K := by
  let before := (Finset.Ioc 0 X).filter (· ∈ S)
  let later := (Finset.Ioc 0 X).filter (· ∈ after S K)
  have cover : before ⊆ later ∪ Finset.range K := by
    intro n hn
    obtain ⟨hx,hs⟩ := Finset.mem_filter.1 hn
    obtain left | right := lt_or_ge n K
    · exact Finset.mem_union_right _ (Finset.mem_range.2 left)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx,hs,right⟩)
  have bound : before.card ≤ later.card+K := by
    simpa only [Finset.card_range] using (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  change (before.card : ℝ) ≤ (later.card : ℝ) + K
  exact_mod_cast bound

lemma no_power_saving_after {S : Set ℕ}
    (hS : ∀ b : ℝ, b < 1 → ¬ (count S =O[atTop] fun x : ℕ ↦ (x:ℝ)^b))
    (K : ℕ) {α : ℝ} (hα : α < 1) :
    ¬ (count (after S K) =O[atTop] fun x : ℕ ↦ (x:ℝ)^α) := by
  intro h
  let B := max α 0
  have hb : B < 1 := max_lt hα zero_lt_one
  obtain ⟨C,hC,hbound⟩ := h.exists_nonneg
  apply hS B hb
  refine .of_bound (C+K) ?_
  filter_upwards [hbound.bound,eventually_ge_atTop (1:ℕ)] with n hn hn₁
  have pos : (1:ℝ) ≤ n := by exact_mod_cast hn₁
  have zero (T : Set ℕ) : 0 ≤ count T n := Nat.cast_nonneg _
  rw [Real.norm_eq_abs,abs_of_nonneg (zero _),Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hn ⊢
  calc
    _ ≤ count (after S K) n + K := count_le_after_add S K n
    _ ≤ C*(n:ℝ)^B + K*(n:ℝ)^B := add_le_add
        (hn.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le pos (le_max_left _ _)) hC))
        (le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow pos (le_max_right _ _)))
    _ = _ := by ring

lemma tail_mass_eq (S : Set ℕ) (K : ℕ) :
    (∑' p : after S K, weight p) =
      ∑' n : {v : ℕ // v ∉ Finset.range K}, S.indicator weight n := by
  let outside : Set ℕ := {n | n ∉ Finset.range K}
  change (∑' n : after S K, weight n.val) = ∑' n : outside, S.indicator weight n.val
  rw [_root_.tsum_subtype (after S K) weight, _root_.tsum_subtype outside (S.indicator weight)]
  apply tsum_congr
  intro n
  by_cases hS : n∈S <;> by_cases hK : K≤n <;> simp [after,outside,Set.indicator,hS,hK]

theorem after_summable {S : Set ℕ} (hs : Summable (weight ∘ (Subtype.val : S→ℕ))) (K : ℕ) :
    Summable (weight ∘ (Subtype.val : after S K → ℕ)) := by
  let sub : after S K ⊆ S := fun _ h ↦ h.1
  have result := hs.comp_injective (i := Set.inclusion sub) (Set.inclusion_injective sub)
  exact result

lemma tendsto_tail_mass (S : Set ℕ) :
    Tendsto (fun K : ℕ ↦ ∑' n : after S K, weight n) atTop (𝓝 0) := by
  simp only [tail_mass_eq]
  exact (tendsto_tsum_compl_atTop_zero (S.indicator weight)).comp tendsto_finset_range

/-- The same fixed selection can be started past any numerical cutoff, with
genuine summability and arbitrarily small remaining logarithmic weight. -/
theorem arbitrarily_small_budget {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, Summable (weight ∘ (Subtype.val : after seventeenPool K → ℕ)) ∧
      (∑' n : after seventeenPool K, weight n) < η ∧
      ∀ b : ℝ, b < 1 → ¬ (count (after seventeenPool K) =O[atTop] fun n : ℕ ↦ (n:ℝ)^b) := by
  obtain ⟨K,cap⟩ := ((tendsto_tail_mass seventeenPool).eventually_lt_const hη).exists
  exact ⟨K,after_summable summable_seventeenPool K,cap,
    fun b hb ↦ no_power_saving_after (fun _ h ↦ seventeenPool_no_power_saving h) K hb⟩


/-- A nonempty summable family of primes has strictly positive log-weight. -/
lemma log_weight_pos {S : Set ℕ} (nonempty : S.Nonempty) (prime : ∀ n ∈ S, n.Prime)
    (sums : Summable (weight ∘ (Subtype.val : S → ℕ))) : 0 < ∑' n : S, weight n := by
  obtain ⟨p,hp⟩ := nonempty
  have pos : 0 < weight p := div_pos (Real.log_pos (by exact_mod_cast (prime p hp).one_lt))
    (Nat.cast_pos.2 (prime p hp).pos)
  exact pos.trans_le (sums.le_tsum (⟨p,hp⟩ : S) (fun n _ ↦ weight_nonneg _))

theorem tail_nonempty (K : ℕ) : (after seventeenPool K).Nonempty := by
  by_contra h
  have empty := Set.not_nonempty_iff_eq_empty.1 h
  have cannot := no_power_saving_after (S := seventeenPool) (fun _ h ↦ seventeenPool_no_power_saving h)
    K (α := 0) (by norm_num)
  apply cannot
  rw [empty]
  exact .of_bound 0 (Filter.Eventually.of_forall fun n ↦ by simp [count])

/-- For every positive budget there is one fixed numerical cutoff whose retained
prime set has strictly positive, genuinely convergent weight below that budget.
The remainder bounds on that tail alone imply Mathlib's Riemann hypothesis. -/
theorem arbitrarily_light_RH_criterion {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, Summable (weight ∘ (Subtype.val : after seventeenPool K → ℕ)) ∧
      0 < (∑' p : after seventeenPool K, weight p) ∧
      (∑' p : after seventeenPool K, weight p) < η ∧
      (remainderBoundsOn (after seventeenPool K) → RiemannHypothesis) := by
  obtain ⟨K,sums,cap,large⟩ := arbitrarily_small_budget hη
  exact ⟨K,sums,log_weight_pos (tail_nonempty K) (fun _ h ↦ (arithmetic_of_seventeenPool h.1).1) sums,
    cap,riemannHypothesis_of_pool (fun _ h ↦ h.1) large⟩

end New.TwistSelection
