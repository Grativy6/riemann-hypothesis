module

public import New.Reduction.Zeros.TentCountDiscrepancy
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# A bounded positive-atom control for endpoint-only fifths

Individual weights stay between one half and five quarters. Each disjoint triple
preserves both endpoint moments, while their interior signals add on every fifth-power block.
-/

@[expose] public section

open Real Nat Finset Filter
open scoped Topology
namespace New.PrimeCutoff.Packets

/-- Move positive mass among s, s+h and s+2h. Both the mass and the mass
divided by the site sum to their previous values. -/
lemma two_moments {s h c : ℝ} (hs : 0<s) (hh : 0≤h) :
    (c*s - 2*c*(s+h) + c*(s+2*h) = 0) ∧
    (c*s/s - 2*c*(s+h)/(s+h) + c*(s+2*h)/(s+2*h)=0) := by
  constructor
  · ring
  · field [hs.ne',(by linarith : 0<s+h).ne',(by linarith : 0<s+2*h).ne']

lemma modified_weights {s h z : ℝ} (hs : 0≤s) (hh : 0≤h) (hz : 0<z) (last : s+2*h≤z) :
    (1/2:ℝ)≤1+s/(4*z) ∧ 1+s/(4*z)≤5/4 ∧
    (1/2:ℝ)≤1-(s+h)/(2*z) ∧ 1-(s+h)/(2*z)≤5/4 ∧
    (1/2:ℝ)≤1+(s+2*h)/(4*z) ∧ 1+(s+2*h)/(4*z)≤5/4 := by
  have hp : 0<4*z := by positivity
  have hq : 0<2*z := by positivity
  constructor
  · linarith [div_nonneg hs hp.le]
  constructor
  · have bound := (div_le_iff₀ hp).2 (show s≤(1/4)*(4*z) by linarith)
    linarith
  constructor
  · have bound := (div_le_iff₀ hq).2 (show s+h≤(1/2)*(2*z) by linarith)
    linarith
  constructor
  · linarith [div_nonneg (add_nonneg hs hh) hq.le]
  constructor
  · linarith [div_nonneg (show 0≤s+2*h by linarith) hp.le]
  · have bound := (div_le_iff₀ hp).2 (show s+2*h≤(1/4)*(4*z) by linarith)
    linarith

/-- The change to x times the compensated remainder, before multiplication by c. -/
def one (s h x : ℝ) := (x-s)⁺-2*(x-(s+h))⁺+(x-(s+2*h))⁺

/-- The tent is exactly the smoothed readout change of the three modified atom weights. -/
lemma one_eq_weight_change {s h x : ℝ} (hs : 0<s) (hh : 0≤h) (hx : 0<x) (c : ℝ) :
    c*s*(1/s-1/x)⁺ - 2*c*(s+h)*(1/(s+h)-1/x)⁺ + c*(s+2*h)*(1/(s+2*h)-1/x)⁺ =
      c*one s h x/x := by
  have ramp (v : ℝ) (hv : 0<v) : v*(1/v-1/x)⁺=(x-v)⁺/x := by
    obtain le | le := le_total v x
    · rw [posPart_of_nonneg (sub_nonneg.2 (one_div_le_one_div_of_le hv le)),posPart_of_nonneg (sub_nonneg.2 le)]
      field
    · rw [posPart_of_nonpos (sub_nonpos.2 (one_div_le_one_div_of_le hx le)),posPart_of_nonpos (sub_nonpos.2 le)]
      ring
  rw [mul_assoc c s,mul_assoc (2*c) (s+h),mul_assoc c (s+2*h),ramp s hs,
    ramp (s+h) (by linarith),ramp (s+2*h) (by linarith)]
  unfold one
  ring

lemma one_nonneg {s h x : ℝ} (hh : 0≤h) : 0≤one s h x := by
  by_cases lo : x≤s
  · simp [one,posPart_of_nonpos (sub_nonpos.2 lo),
      posPart_of_nonpos (show x-(s+h)≤0 by linarith),posPart_of_nonpos (show x-(s+2*h)≤0 by linarith)]
  by_cases mid : x≤s+h
  · simp [one,posPart_of_nonpos (sub_nonpos.2 mid),
      posPart_of_nonpos (show x-(s+2*h)≤0 by linarith),show s≤x by linarith]
  by_cases endp : x≤s+2*h
  · rw [one,posPart_of_nonneg (by linarith),posPart_of_nonneg (by linarith),posPart_of_nonpos (sub_nonpos.2 endp)]
    linarith
  · rw [one,posPart_of_nonneg (by linarith),posPart_of_nonneg (by linarith),posPart_of_nonneg (by linarith)]
    linarith

lemma one_before {s h x : ℝ} (hh : 0≤h) (hx : x≤s) : one s h x=0 := by
  simp [one,posPart_of_nonpos (sub_nonpos.2 hx),posPart_of_nonpos (show x-(s+h)≤0 by linarith),
    posPart_of_nonpos (show x-(s+2*h)≤0 by linarith)]

lemma one_after {s h x : ℝ} (hh : 0≤h) (hx : s+2*h≤x) : one s h x=0 := by
  rw [one,posPart_of_nonneg (by linarith),posPart_of_nonneg (by linarith),posPart_of_nonneg (by linarith)]
  ring

def width (k : ℕ) := k^4
def bottom (k : ℕ) := k^5
def top (k : ℕ) := (k+1)^5

noncomputable def block (k : ℕ) (x : ℝ) :=
  (∑ r ∈ Finset.range (width k), one (bottom k+r+1) (width k) x)/(4*(top k)*x)

lemma after_three (k : ℕ) : bottom k+3*width k≤top k := by
  simp only [bottom,width,top]
  nlinarith [Nat.zero_le (k^2),Nat.zero_le (k^3),Nat.zero_le (k^4)]

lemma block_off_grid {k : ℕ} {x : ℝ} (outside : x≤bottom k ∨ (top k:ℝ)≤x) : block k x=0 := by
  unfold block
  rw [Finset.sum_eq_zero,zero_div]
  intro r hr
  obtain before | afterC := outside
  · exact one_before (Nat.cast_nonneg _) (by linarith [Nat.cast_nonneg (α:=ℝ) r])
  · apply one_after (Nat.cast_nonneg _)
    have below : r+1≤width k := Finset.mem_range.1 hr
    have total := after_three k
    have b : bottom k+r+1+2*width k ≤ top k := by omega
    exact (show (bottom k:ℝ)+r+1+2*(width k:ℝ) ≤ top k by exact_mod_cast b).trans afterC

lemma block_nonneg (k : ℕ) {x : ℝ} (xp : 0≤x) : 0≤block k x :=
  div_nonneg (Finset.sum_nonneg (fun r hr ↦ one_nonneg (Nat.cast_nonneg _))) (by positivity)

lemma packet_midpoint (k : ℕ) :
    let h : ℝ := width k
    let x : ℝ := bottom k + 2*h
    block k x = h*(h+1)/(8*(top k)*x) := by
  let n := width k
  let x : ℝ := (bottom k:ℝ)+2*n
  have at_r (r : ℕ) (hr : r<n) :
      one ((bottom k:ℝ)+r+1) n x = (r:ℝ)+1 := by
    have right : (r:ℝ)+1≤n := by exact_mod_cast (show r+1≤n from hr)
    unfold one
    dsimp [x]
    rw [posPart_of_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n]),
      posPart_of_nonneg (by linarith),posPart_of_nonpos (by linarith [Nat.cast_nonneg (α:=ℝ) r])]
    ring
  have total : ∑ r ∈ Finset.range n, ((r:ℝ)+1) = (n:ℝ)*((n:ℝ)+1)/2 := by
    have all : ∀ j : ℕ, ∑ r ∈ Finset.range j, ((r:ℝ)+1) = (j:ℝ)*((j:ℝ)+1)/2 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [Finset.sum_range_succ,ih];push_cast;ring
    exact all n
  change (∑ r ∈ Finset.range n, one ((bottom k:ℝ)+r+1) n x)/(4*(top k)*x)=_
  rw [Finset.sum_congr rfl (fun r hr ↦ at_r r (Finset.mem_range.1 hr)),total]
  rw [div_div]
  congr 1
  dsimp [x,n];ring

/-- One fixed collection of disjoint blocks. At every cutoff only finitely many
transfers can contribute; at fifth powers they vanish exactly. -/
noncomputable def allBlocks (x : ℝ) := ∑ k ∈ Finset.range ⌊x⌋₊, block k x

lemma all_fifths_cancel (n : ℕ) : allBlocks ((n:ℝ)^5)=0 := by
  apply Finset.sum_eq_zero
  intro k _
  apply block_off_grid
  obtain h | h := le_or_gt n k
  · left; exact_mod_cast (Nat.pow_le_pow_left h 5)
  · right; exact_mod_cast (Nat.pow_le_pow_left (show k+1≤n from h) 5)


/-- The three bands occupy disjoint integer sites even after the blocks are
joined. The coefficient adjustment at one site is therefore made just once. -/
def site (k band r : ℕ) := bottom k+1+band*width k+r

lemma site_in_block {k band r : ℕ} (bb : band<3) (rr : r<width k) :
    bottom k < site k band r ∧ site k band r ≤ top k := by
  have cap := after_three k
  unfold site
  interval_cases band <;> omega

lemma distinct_sites {k l i j r s : ℕ} (bi : i<3) (bj : j<3) (ri : r<width k) (sj : s<width l)
    (eq : site k i r=site l j s) : k=l ∧ i=j ∧ r=s := by
  obtain ⟨l₁,l₂⟩ := site_in_block bi ri
  obtain ⟨r₁,r₂⟩ := site_in_block bj sj
  have same : k=l := by
    rcases lt_trichotomy k l with lt | same | gt
    · have no : top k≤bottom l := Nat.pow_le_pow_left (show k+1≤l from lt) 5
      omega
    · exact same
    · have no : top l≤bottom k := Nat.pow_le_pow_left (show l+1≤k from gt) 5
      omega
  subst l
  unfold site at eq
  interval_cases i <;> interval_cases j <;> omega

/-- The unit-weight Riesz remainder. Its centring gives O(1/N) at the integers. -/
noncomputable def unitR (x : ℝ) :=
  (harmonic ⌊x⌋₊ : ℝ) - (⌊x⌋₊:ℝ)/x - Real.log x - (Real.eulerMascheroniConstant-1)

lemma unit_integer (m : ℕ) (hm : 1≤m) : 0≤unitR m ∧ unitR m≤1/(m:ℝ) := by
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have above := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' m
  have below := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant m
  simp only [Real.eulerMascheroniSeq',ite_eq_right (show m≠0 by omega)] at above
  unfold Real.eulerMascheroniSeq at below
  have logstep : Real.log ((m:ℝ)+1) - Real.log m ≤ 1/(m:ℝ) := by
    rw [←Real.log_div (by positivity : (m:ℝ)+1≠0) mp.ne']
    apply (Real.log_le_sub_one_of_pos (div_pos (by positivity) mp)).trans_eq
    field
  rw [unitR,Nat.floor_natCast,div_self mp.ne']
  constructor <;> linarith

noncomputable def model (x : ℝ) := unitR x + allBlocks x

theorem fifth_samples (n : ℕ) (hn : 1≤n) :
    0≤model ((n:ℝ)^5) ∧ model ((n:ℝ)^5)≤1/((n:ℝ)^5) := by
  rw [model,all_fifths_cancel,add_zero]
  exact_mod_cast unit_integer (n^5) (Nat.one_le_pow _ n hn)

def middleNat (k : ℕ) := bottom k+2*width k

lemma middle_lower (k : ℕ) (hk : 1≤k) :
    1/(768*(k:ℝ)^2) ≤ model (middleNat k) := by
  let h := width k
  let x := middleNat k
  let z := top k
  have u : (1:ℝ)≤k := by exact_mod_cast hk
  have kn : k≤bottom k := Nat.le_self_pow (by decide : 5≠0) _
  have hw : 0<h := Nat.pow_pos hk
  have nless : k<x := by dsimp [x,middleNat];change 0<width k at hw;omega
  have xpos : (0:ℝ)<x := by exact_mod_cast (by omega : 0<x)
  have zpos : (0:ℝ)<z := by dsimp [z,top];positivity
  have zcap : (z:ℝ)≤32*(k:ℝ)^5 := by
    dsimp [z,top];push_cast
    calc ((k:ℝ)+1)^5 ≤ (2*(k:ℝ))^5 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by ring
  have xcap : (x:ℝ)≤3*(k:ℝ)^5 := by
    have hi := pow_le_pow_right₀ u (by decide : 4≤5)
    dsimp [x,middleNat,bottom,width];push_cast;linarith only [hi]
  have blockValue : block k x = (h:ℝ)*(h+1)/(8*(z:ℝ)*x) := by
    simpa only [x,middleNat,h,z,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using packet_midpoint k
  have oneBlock : block k x ≤ allBlocks x := Finset.single_le_sum
    (fun j _ ↦ block_nonneg j xpos.le) (Finset.mem_range.2 (by simpa only [Nat.floor_natCast] using nless))
  have base := (unit_integer x (show 1≤x by omega)).1
  change _ ≤ unitR x+allBlocks x
  refine LE.le.trans ?_ (oneBlock.trans (by linarith only [base]))
  rw [blockValue,div_le_div_iff₀ (by positivity) (by positivity),one_mul]
  calc 8*(z:ℝ)*x ≤ 8*(32*(k:ℝ)^5)*(3*(k:ℝ)^5) := by gcongr
    _ = (h:ℝ)*h*(768*(k:ℝ)^2) := by dsimp [h,width];push_cast;ring
    _ ≤ _ := by gcongr;linarith

theorem no_faster_decay {γ : ℝ} (hg : 2/5<γ) (C : ℝ) :
    ¬ (∀ᶠ x : ℝ in atTop, model x ≤ C*x^(-γ)) := by
  intro bounded
  have grows : Tendsto (fun k : ℕ ↦ (k:ℝ)^5) atTop atTop :=
    (tendsto_pow_atTop (by decide : 5≠0)).comp tendsto_natCast_atTop_atTop
  have after : Tendsto (fun k : ℕ ↦ (middleNat k:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono _ grows
    intro k;dsimp [middleNat,bottom,width];push_cast;exact le_add_of_nonneg_right (by positivity)
  have ratio : Tendsto (fun n : ℕ ↦ (n:ℝ)^(5*γ-2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0<5*γ-2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n,large,measure,hn⟩ := ((ratio.eventually (eventually_gt_atTop (768*C))).and
    ((after.eventually bounded).and (eventually_ge_atTop 1))).exists
  have np : (0:ℝ)<n := by exact_mod_cast hn
  have earlier : (n:ℝ)^5 ≤ middleNat n := by dsimp [middleNat,bottom,width];push_cast;exact le_add_of_nonneg_right (by positivity)
  have xp := (pow_pos np 5).trans_le earlier
  have low := middle_lower n hn
  have num := mul_le_mul low (Real.rpow_le_rpow (pow_nonneg np.le _) earlier (by linarith : 0≤γ))
    (Real.rpow_nonneg (pow_nonneg np.le _) γ) ((by positivity : 0≤1/(768*(n:ℝ)^2)).trans low)
  rw [Real.rpow_neg xp.le] at measure
  have high : model (middleNat n)*(middleNat n:ℝ)^γ≤C := by
    calc _ ≤ (C*((middleNat n:ℝ)^γ)⁻¹)*(middleNat n:ℝ)^γ :=
              mul_le_mul_of_nonneg_right measure (Real.rpow_nonneg xp.le γ)
      _ = _ := by field
  have same : 1/(768*(n:ℝ)^2)*((n:ℝ)^5)^γ = (n:ℝ)^(5*γ-2)/768 := by
    rw [←Real.rpow_natCast_mul np.le,Real.rpow_sub np,Real.rpow_two];push_cast;ring
  rw [same] at num
  linarith only [num.trans high,large]

end New.PrimeCutoff.Packets
