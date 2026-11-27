module

public import New.Reduction.Zeros.CutoffEntropyBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic

/-!
# A nonnegative-ramp boundary for fifth-power sampling

Piecewise-linear interpolation of t log t on consecutive fifth powers has positive
slope jumps at integer knots. After undoing the smooth normalization the readings
vanish at every fifth power, but fail every eventual decay exponent above 2/5.
-/

@[expose] public section

open Filter Finset Real Set
open scoped Topology
namespace New.PrimeCutoff.FifthModel

/-- The n-th knot and its value on the convex function t log t. -/
def node (n : ℕ) : ℝ := (n:ℝ)^5
noncomputable def height (n : ℕ) : ℝ := node n * Real.log (node n)
noncomputable def slope (j : ℕ) : ℝ := (height (j+1)-height j)/(node (j+1)-node j)
noncomputable def jump (j : ℕ) : ℝ := slope (j+1)-slope j

lemma node_inc : StrictMono node := by
  intro a b h
  unfold node
  exact pow_lt_pow_left₀ (by exact_mod_cast h) (Nat.cast_nonneg a) (by decide)

lemma node_nonneg (n : ℕ) : 0≤node n := by simp [node]

lemma jump_nonnegative (j : ℕ) : 0≤jump j := by
  have cvx := Real.strictConvexOn_mul_log.convexOn
  exact sub_nonneg.2 (cvx.slope_mono_adjacent (node_nonneg j) (node_nonneg (j+2))
    (node_inc (Nat.lt_succ_self j)) (node_inc (Nat.lt_succ_self (j+1))))

/-- A positive ramp at each positive fifth power. The integer cutoff suffices
because (j+1)^5 ≥ j+1. -/
noncomputable def curve (x : ℝ) :=
  ∑ j ∈ Finset.range ⌊x⌋₊, jump j * (x-node (j+1))⁺

noncomputable def remainder (x : ℝ) : ℝ := curve x/x - Real.log x

lemma height_step (n : ℕ) : height (n+1)=height n+slope n*(node (n+1)-node n) := by
  have h := sub_ne_zero.2 (node_inc (Nat.lt_succ_self n)).ne'
  simp [slope,h]

lemma telescope (n : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range n, jump j*(x-node (j+1)) = height n+slope n*(x-node n) := by
  induction n with
  | zero => norm_num [height,slope,node]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,jump,height_step n]
    ring

lemma node_above_index (n : ℕ) : (n:ℝ)≤node n := by
  obtain rfl | h := Nat.eq_zero_or_pos n
  · norm_num [node]
  · exact le_self_pow₀ (by exact_mod_cast h : (1:ℝ)≤n) (by decide : 5≠0)

/-- Between fifth powers the sum is the straight chord joining two heights. -/
theorem curve_on_block {n : ℕ} {x : ℝ} (lo : node n ≤ x) (hi : x ≤ node (n+1)) :
    curve x = height n+slope n*(x-node n) := by
  have nc : n≤⌊x⌋₊ := Nat.le_floor ((node_above_index n).trans lo)
  have cover := Finset.range_mono nc
  calc curve x = ∑ j ∈ Finset.range n, jump j*(x-node (j+1))⁺ := by
        symm
        apply Finset.sum_subset cover
        intro j _ hj
        have gn : n≤j := Nat.le_of_not_gt (fun h ↦ hj (Finset.mem_range.2 h))
        have no : x≤node (j+1) := hi.trans (node_inc.monotone (by omega))
        rw [posPart_of_nonpos (sub_nonpos.2 no),mul_zero]
    _ = ∑ j ∈ Finset.range n, jump j*(x-node (j+1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [posPart_of_nonneg (sub_nonneg.2 ((node_inc.monotone (Finset.mem_range.1 hj)).trans lo))]
    _ = _ := telescope n x

theorem all_fifths_zero (n : ℕ) : remainder (node n) = 0 := by
  unfold remainder
  rw [curve_on_block (n:=n) le_rfl (node_inc (Nat.lt_succ_self n)).le,sub_self,mul_zero,add_zero]
  obtain rfl | pos := Nat.eq_zero_or_pos n
  · norm_num [height,node]
  · have h : 0<node n := pow_pos (Nat.cast_pos.2 pos) _
    simp [height,h.ne']

noncomputable def midpoint (n : ℕ) : ℝ := (node n + node (n+1))/2

lemma midpoint_value {n : ℕ} (hn : 1≤n) :
    remainder (midpoint n) =
      (height n/2+height (n+1)/2-midpoint n*Real.log (midpoint n))/midpoint n := by
  have hy : 0<node n := pow_pos (Nat.cast_pos.2 hn) _
  have span := node_inc (Nat.lt_succ_self n)
  have lo : node n≤midpoint n := by dsimp [midpoint];linarith
  have hi : midpoint n≤node (n+1) := by dsimp [midpoint];linarith
  have gap := sub_ne_zero.2 span.ne'
  have half : midpoint n-node n = (node (n+1)-node n)/2 := by dsimp [midpoint];ring
  rw [remainder,curve_on_block lo hi,half]
  unfold slope
  field_simp [gap,(hy.trans_le lo).ne']
  ring


/-- The positive crest between consecutive fifth powers is at least a fixed
multiple of 1/n². This is too large for a half-exponent estimate in x≈n⁵. -/
theorem midpoint_lower (n : ℕ) (hn : 1≤n) :
    1/(8192*(n:ℝ)^2) ≤ remainder (midpoint n) := by
  let y := node n
  let z := node (n+1)
  let x := midpoint n
  have u : (1:ℝ)≤n := by exact_mod_cast hn
  have hy : 0<y := pow_pos (Nat.cast_pos.2 hn) _
  have yz : y<z := node_inc (Nat.lt_succ_self n)
  have hx : 0<x := by change 0<(y+z)/2; linarith
  have hz := hy.trans yz
  have mix : (1/2:ℝ)*y+1/2*z=x := by dsimp [x,midpoint,y,z];ring
  have low := log_chord_quadratic (σ:=1) hy hz (a:=1/2) (b:=1/2)
    (by norm_num) (by norm_num) (by norm_num) mix yz.le (fun t ht ↦ by
      rw [one_mul]; exact sub_nonneg.2 (inv_anti₀ (hy.trans_le ht.1) ht.2))
  have crest : (z-y)^2/(8*z*x) ≤ remainder x := by
    rw [show x=midpoint n from rfl,midpoint_value hn]
    change (z-y)^2/(8*z*x) ≤ (y*Real.log y/2+z*Real.log z/2-x*Real.log x)/x
    rw [div_le_div_iff₀ (by positivity) hx]
    have d : (x-y)*(z-x)=(z-y)^2/4 := by change ((y+z)/2-y)*(z-(y+z)/2)=_;ring
    rw [one_mul,sub_nonneg,d] at low
    have no := (div_le_iff₀ (show 0 < 2*z by positivity)).1 low
    nlinarith only [mul_le_mul_of_nonneg_right no hx.le]
  have upper : z ≤ 32*(n:ℝ)^5 := by
    change ((n+1:ℕ):ℝ)^5 ≤ _
    push_cast
    calc ((n:ℝ)+1)^5 ≤ (2*(n:ℝ))^5 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by ring
  have mid_upper : x ≤ 32*(n:ℝ)^5 :=
    (show x ≤ z by change (y+z)/2≤z;linarith).trans upper
  have gap : (n:ℝ)^4 ≤ z-y := calc
    _ ≤ (n:ℝ)^4 + (4*(n:ℝ)^4+10*(n:ℝ)^3+10*(n:ℝ)^2+5*n+1) := le_add_of_nonneg_right (by positivity)
    _ = z-y := by dsimp [z,y,node]; push_cast; ring
  have g2 := pow_le_pow_left₀ (by positivity : 0≤(n:ℝ)^4) gap 2
  refine LE.le.trans ?_ crest
  rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul]
  calc 8*z*x ≤ 8*(32*(n:ℝ)^5)*(32*(n:ℝ)^5) := by gcongr
    _ = ((n:ℝ)^4)^2 * (8192*(n:ℝ)^2) := by ring
    _ ≤ (z-y)^2 * (8192*(n:ℝ)^2) := mul_le_mul_of_nonneg_right g2 (by positivity)

/-- The fifth-grid samples vanish, while every exponent strictly larger than
2/5 fails as an eventual power-saving rate for this one positive-ramp model. -/
theorem no_better_than_two_fifths {γ : ℝ} (hγ : 2/5<γ) (C : ℝ) :
    ¬ (∀ᶠ x : ℝ in atTop, remainder x ≤ C*x^(-γ)) := by
  intro bounded
  have γpos : 0<γ := by linarith
  have tend : Tendsto (fun n : ℕ ↦ midpoint n) atTop atTop := by
    have grows : Tendsto (fun n : ℕ ↦ (n:ℝ)^5) atTop atTop :=
      (tendsto_pow_atTop (by decide : 5≠0)).comp tendsto_natCast_atTop_atTop
    apply tendsto_atTop_mono _ grows
    intro n
    change node n≤(node n+node (n+1))/2
    linarith [node_inc (Nat.lt_succ_self n)]
  have ratio : Tendsto (fun n : ℕ ↦ (n:ℝ)^(5*γ-2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0<5*γ-2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n,large,step,hn⟩ := ((ratio.eventually (eventually_gt_atTop (8192*C))).and
    ((tend.eventually bounded).and (eventually_ge_atTop 1))).exists
  have np : (0:ℝ)<n := Nat.cast_pos.2 hn
  have xy : node n ≤ midpoint n := by
    dsimp [midpoint];linarith [node_inc (Nat.lt_succ_self n)]
  have xp : 0<midpoint n := (pow_pos (show (0:ℝ)<n from np) 5).trans_le xy
  have nonneg := (show 0<1/(8192*(n:ℝ)^2) by positivity).le.trans (midpoint_lower n hn)
  have prod := mul_le_mul (midpoint_lower n hn) (Real.rpow_le_rpow (node_nonneg n) xy γpos.le)
    (Real.rpow_nonneg (node_nonneg n) γ) nonneg
  have right : remainder (midpoint n)*(midpoint n)^γ ≤ C := by
    rw [Real.rpow_neg xp.le] at step
    calc _ ≤ (C*((midpoint n)^γ)⁻¹)*(midpoint n)^γ :=
            mul_le_mul_of_nonneg_right step (Real.rpow_nonneg xp.le γ)
      _ = C := by field
  have left : (1/(8192*(n:ℝ)^2))*(node n)^γ=(n:ℝ)^(5*γ-2)/8192 := by
    rw [node,← Real.rpow_natCast_mul (show (0:ℝ)≤n from np.le), Real.rpow_sub np,Real.rpow_two]
    push_cast
    ring
  rw [left] at prod
  linarith only [prod.trans right,large]


/-- All cutoff-dependent sums are restrictions of one positive discrete measure. -/
lemma common_truncation (x : ℝ) {N : ℕ} (enough : ⌊x⌋₊ ≤ N) :
    curve x = ∑ j ∈ Finset.range N, jump j * (x-node (j+1))⁺ := by
  apply Finset.sum_subset (Finset.range_mono enough)
  intro j _ outside
  have le : ⌊x⌋₊ ≤ j := by simpa using outside
  have cast : (⌊x⌋₊:ℝ)+1 ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ le
  have cutoff := (Nat.lt_floor_add_one x).le.trans (cast.trans (node_above_index (j+1)))
  rw [posPart_of_nonpos (sub_nonpos.2 cutoff),mul_zero]

theorem curve_convex : ConvexOn ℝ Set.univ curve := by
  refine ⟨convex_univ,?_⟩
  intro u _ v _ a b ha hb total
  change curve (a*u+b*v) ≤ a*curve u+b*curve v
  let N := max ⌊a*u+b*v⌋₊ (max ⌊u⌋₊ ⌊v⌋₊)
  have hm : ⌊a*u+b*v⌋₊≤N := le_max_left _ _
  have hu : ⌊u⌋₊≤N := (le_max_left _ _).trans (le_max_right _ _)
  have hv : ⌊v⌋₊≤N := (le_max_right _ _).trans (le_max_right _ _)
  rw [common_truncation _ hm,common_truncation _ hu,common_truncation _ hv,
    Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  let w := node (j+1)
  have bend : (a*u+b*v-w)⁺ ≤ a*(u-w)⁺+b*(v-w)⁺ := by
    rw [posPart_def]
    apply max_le
    · rw [show a*u+b*v-w=a*(u-w)+b*(v-w) by linear_combination w*total]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_posPart _) ha)
        (mul_le_mul_of_nonneg_left (le_posPart _) hb)
    · exact add_nonneg (mul_nonneg ha (posPart_nonneg _)) (mul_nonneg hb (posPart_nonneg _))
  calc jump j*(a*u+b*v-w)⁺ ≤ jump j*(a*(u-w)⁺+b*(v-w)⁺) :=
        mul_le_mul_of_nonneg_left bend (jump_nonnegative _)
    _ = _ := by dsimp [w];ring

theorem fifth_grid_counterexample :
    ConvexOn ℝ Set.univ curve ∧ (∀ j : ℕ, 0 ≤ jump j) ∧ (∀ n : ℕ, remainder (node n) = 0) ∧
    ¬ ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, remainder x ≤ C*x^(-(1:ℝ)/2+1/20) := by
  refine ⟨curve_convex,jump_nonnegative,all_fifths_zero,?_⟩
  rintro ⟨C,bound⟩
  exact no_better_than_two_fifths (γ:=9/20) (by norm_num) C
    (by simpa only [show -(1:ℝ)/2+1/20 = -(9/20) by norm_num] using bound)

end New.PrimeCutoff.FifthModel
