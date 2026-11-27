module

public import New.UpperBound.Divisibility.SparseCornerPopulations
import Lib.Analytic.Primes
import Mathlib.Tactic

/-!
# Admissible data for prescribed corner counts

Macro exponents have fifth-power density. At the actual ranks their number is at least m,
so any fixed population fits at every sufficiently large scale. Passing that exact set
through the level construction realizes the counts in the returned data.
-/

@[expose] public section

open NumberField Finset Real Filter
namespace New.Data.CollisionPrimeExample

/-- At the project's ranks, a common tagged exponent pool can accommodate any prescribed
population whose total is at most the lift rank. -/
theorem population_from_ranks (w : Fin 4 → ℕ) (positive : 0 < ∑ i, w i)
    {m r s n : ℕ} {y W : ℝ} (hy : 2 ≤ y) (hn : 0 < n)
    (hm : exp (y/2) ≤ m) (hr : r ≤ 3*exp (5*y)) (hPow : 2^s = m^22)
    (hs : s ≤ 32*y) (hW : W ≤ exp (y/2)) (hUpper : (2:ℝ)^s ≤ W^n)
    (large : 1e6*y ≤ W) (room : (5184*y)^n ≤ W) (count : 7776*y*n*2^n ≤ W)
    (den : (∑ i, w i) ≤ m) :
    ∃ B : Finset (params.Φ s), (∀ σ ∈ B, params.placeClass (params.q₀.dvd_mul_right (towerDeg s)) σ = -1) ∧
      (towerDeg s : ℝ) ≤ #B * W^6 ∧ params.IsSparse s ((r+1-m)*(5*r)) B ∧ HasCornerPopulation s B w ∧
        HasCornerMenu m r s B (∑ i,w i) := by
  have hw : 12 ≤ W := by linarith
  have hwm : W ≤ m := hW.trans hm
  have hm1 : 1 ≤ (m:ℝ) := by linarith
  have hcast : (2:ℝ)^s = (m:ℝ)^22 := by exact_mod_cast hPow
  have floor : W^2 ≤ (2:ℝ)^s := calc
    W^2 ≤ (m:ℝ)^2 := pow_le_pow_left₀ (by linarith) hwm 2
    _ ≤ (m:ℝ)^22 := pow_le_pow_right₀ hm1 (by decide)
    _ = _ := hcast.symm
  have s3 : 3 ≤ s := by
    have lower : W ≤ (2:ℝ)^s := (show W ≤ W^2 by nlinarith [sq_nonneg (W-1)]).trans floor
    by_contra! h
    interval_cases s <;> norm_num at lower <;> linarith
  have hl : (l₀ s:ℝ) ≤ 2592*y := by
    have h := l₀_le_mul (show s ≠ 0 by omega)
    have h' : (l₀ s : ℝ) ≤ 81*s := by exact_mod_cast h
    linarith
  have fit : (2*l₀ s : ℝ)^n ≤ W := by grw [← room,hl,← mul_assoc,show (2*2592:ℝ)=5184 by norm_num]
  have cost : (3:ℝ)*l₀ s*n*2^n ≤ W := by grw [hl]; linarith
  have width : (28:ℝ)*l₀ s ≤ W := by linarith
  obtain ⟨q,o,split,h8,hspace,S,hlt,dense,free⟩ := exists_tagged_macro_budget hn
    (show 1 ≤ W by linarith) width floor hUpper fit cost
  have tpos : 0 < 3*l₀ s := by unfold l₀; positivity
  have degree : (2:ℝ)^s ≤ towerDeg s := by
    exact_mod_cast (show 2^s ≤ towerDeg s by rw [towerDeg_eq]; exact Nat.le_mul_of_pos_left _ tpos)
  have mf : (m:ℝ)*m^5 ≤ #S*(m:ℝ)^5 := calc
    (m:ℝ)*(m:ℝ)^5 = (m:ℝ)^6 := by ring
    _ ≤ (m:ℝ)^22 := pow_le_pow_right₀ hm1 (by decide : 6 ≤ 22)
    _ = (2:ℝ)^s := hcast.symm
    _ ≤ towerDeg s := degree
    _ ≤ #S*W^5 := dense
    _ ≤ _ := by gcongr
  have enough : m ≤ #S := by
    exact_mod_cast le_of_mul_le_mul_right mf (pow_pos (by linarith : 0 < (m:ℝ)) 5)
  have hexp : 1e6*y ≤ exp y := (large.trans hW).trans (exp_le_exp.2 (by linarith))
  have bounds := mul_rank_lt_two_pow (by linarith) hexp hm hr hPow hl
  have choose (v : Fin 4 → ℕ) (same : (∑ i,v i) = ∑ i,w i) :=
    select_sparse_population s3 h8 hspace split bounds S hlt free v (same ▸ positive)
      (same ▸ den.trans enough) (show 2 ≤ W by linarith) dense
  obtain ⟨B,base,card,sparse,source,mass⟩ := choose w rfl
  refine ⟨B,base,card,sparse,source,?_⟩
  intro v same
  obtain ⟨U,ubase,_,usparse,reading,umass⟩ := choose v same
  exact ⟨U,by rw [umass,mass,same],ubase,usparse,reading⟩

/-- The data select the specified rational population at all sufficiently large integer scales. -/
theorem eventually_has_population_frame (w : Fin 4 → ℕ) (positive : 0 < ∑ i, w i) :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX = x ∧ HasCornerPopulation D.towerExp D.bPlaces w ∧
      HasCornerMenu D.m D.r D.towerExp D.bPlaces (∑ i,w i) := by
  let ε : ℝ := 1/200
  obtain ⟨n,scale⟩ := params.exists_eventually_isLargeScale (ε := ε) (by norm_num [ε]) (by norm_num [ε])
  have four : 4 ∣ params.q₀*params.d := by decide
  have hW : Tendsto (fun x : ℕ ↦ (x:ℝ)^(ε/6)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [ε])).comp tendsto_natCast_atTop_atTop
  let d := ∑ i, w i
  filter_upwards [scale,hW.eventually (exists_prime_modEq_one_log_mem _ (n+7) four),
      eventually_ge_atTop ((d+1)^2)] with x hx window big
  have x_pos : 0 < (x:ℝ) := by exact_mod_cast (show 0 < x from (pow_pos (Nat.succ_pos d) 2).trans_le big)
  have rank_large {m : ℕ} (hm : exp (log x/2) ≤ m) : d ≤ m := by
    rw [exp_half, exp_log x_pos] at hm
    have sq : (d:ℝ)^2 ≤ x := by exact_mod_cast (show d^2 ≤ x from (Nat.pow_le_pow_left (Nat.le_succ d) 2).trans big)
    exact_mod_cast (calc (d:ℝ) = √((d:ℝ)^2) := (sqrt_sq (Nat.cast_nonneg _)).symm
      _ ≤ √(x:ℝ) := sqrt_le_sqrt sq
      _ ≤ m := hm)
  obtain ⟨m,r,s,b,B,g,α,N,β,adm,pop⟩ := hx.exists_isAdmissibleData_selecting
    (fun m r s T ↦ HasCornerPopulation s T w ∧ HasCornerMenu m r s T (∑ i,w i)) window
    (fun m r s hm hr hPow hs hw upper ↦ population_from_ranks w positive
      (by linarith [hx.hundred_le]) hx.n_pos hm hr hPow hs hw upper
      (by linarith [hx.mul_y_le_W]) hx.pow_le hx.mul_two_pow_le (rank_large hm))
  obtain ⟨D,fields,_,_,_,preserve⟩ := adm.exists_hasFields_preserving
    (fun s T ↦ HasCornerPopulation s T w ∧ HasCornerMenu m r s T (∑ i,w i)) hx
  refine ⟨D,fields.natX_eq,?_⟩
  rw [fields.m_eq,fields.r_eq]
  exact preserve.2 pop

/-- In particular the specified population itself is realized in the constructed data. -/
theorem eventually_has_corner_population (w : Fin 4 → ℕ) (positive : 0 < ∑ i,w i) :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX = x ∧ HasCornerPopulation D.towerExp D.bPlaces w := by
  filter_upwards [eventually_has_population_frame w positive] with x hx
  obtain ⟨D,hx,pop,_⟩ := hx
  exact ⟨D,hx,pop⟩

end New.Data.CollisionPrimeExample
