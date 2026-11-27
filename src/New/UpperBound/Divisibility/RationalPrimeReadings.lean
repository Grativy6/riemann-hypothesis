module

public import New.Reduction.Data.SparseFiber
public import New.UpperBound.Divisibility.AdmissibleCornerPopulations
public import New.UpperBound.Divisibility.ThreePrimeReadings
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# The rational points of the three-prime tetrahedron

Any rational point inside the four faces prescribes integer populations of the four corner
types. One admissible high set realizes those populations at every sufficiently large
integer scale. Irrational coordinates cannot be read from a single configuration.
-/

@[expose] public section

open Finset
namespace ColoredSparse

/-- Clear the denominators at once. The sum-one condition makes the common
denominator exactly the total number of counted observations. -/
theorem integer_population_of_rational_weights {ι : Type*} [Fintype ι] (a : ι → ℚ) (pos : ∀ i, 0 ≤ a i)
    (sum_one : ∑ i, a i = 1) :
    ∃ w : ι → ℕ, 0 < ∑ i, w i ∧ ∀ i, (w i : ℚ) = ((∑ j, w j : ℕ) : ℚ) * a i := by
  classical
  let d := ∏ i, (a i).den
  have dp : 0 < d := Finset.prod_pos (fun i _ ↦ (a i).den_pos)
  have divs (i : ι) : (a i).den ∣ d := dvd_prod_of_mem (fun i ↦ (a i).den) (mem_univ i)
  let w := fun i ↦ (a i).num.natAbs * (d/(a i).den)
  have wi (i : ι) : (w i : ℚ) = (d : ℚ)*a i := by
    let z := a i
    have natnum : ((z.num.natAbs : ℕ) : ℚ) = (z.num : ℚ) := by
      rw [← Int.cast_natCast]
      exact congrArg (fun m : ℤ ↦ (m:ℚ)) (Int.natAbs_of_nonneg (Rat.num_nonneg.2 (pos i)))
    have dpos : (z.den : ℚ) ≠ 0 := by exact_mod_cast z.den_ne_zero
    have num : (z.num : ℚ) = z*z.den := (div_eq_iff dpos).1 z.num_div_den
    have f : ((d/z.den : ℕ) : ℚ)*z.den = d := by exact_mod_cast Nat.div_mul_cancel (divs i)
    change ((z.num.natAbs*(d/z.den) : ℕ) : ℚ) = (d : ℚ)*z
    rw [Nat.cast_mul,natnum,num,← f]
    ring
  have sum : (∑ i, w i) = d := by
    apply Nat.cast_injective (R := ℚ)
    rw [Nat.cast_sum,Finset.sum_congr rfl (fun i _ ↦ wi i),← Finset.mul_sum,sum_one,mul_one]
  exact ⟨w,sum ▸ dp,fun i ↦ sum ▸ wi i⟩

end ColoredSparse

namespace New.Data.CollisionPrimeExample
open NumberField Finset Real Filter ThreePrimeEnvelope ColoredSparse
local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 535919) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 665279) := ⟨by norm_num1⟩

/-- The normalized point specified by a finite population of the four corners. -/
noncomputable def populationPoint (w : Fin 4 → ℕ) : Point :=
  (((∑ i,w i : ℕ):ℝ)⁻¹) • ∑ c, (w c : ℝ) • corner c

/-- Read the actual offset of every assigned high place before taking any signed sum. -/
theorem slot_offset_modEq {ι : Type*} [Fintype ι] (address : ι → LaneAddress) (D : Data params) {w : ι → ℕ} {k : ℕ}
    (f : Sample k w ↪ D.Φ) (hd : 72*params.q₀ ∣ D.q₁) (B : D.bPlaces = univ.map f)
    (addr : ∀ a, (params.placeClass hd (f a) : ZMod (72*params.q₀)) =
      -((1+params.q₀*(address a.2.1).offset : ℕ) : ZMod (72*params.q₀)))
    (a : Sample k w) : D.negativeOffset (f a) ≡ (address a.2.1).offset [MOD 72] := by
  classical
  have at_anchor : params.placeClass hd (D.placeOfInt (-1)) = -1 := by
    apply Units.ext
    simpa using (params.placeClass_placeOfInt (s := D.towerExp) (ν := -1) (h_dvd := hd)
      (show IsCoprime (-1:ℤ) params.q₀ from ⟨-1,0,by ring⟩))
  have here : f a ∈ D.bPlaces := by rw [B]; exact mem_map.2 ⟨a,mem_univ _,rfl⟩
  have repr := D.negativePlace_eq_offset (D.placeClass_of_mem_bPlaces _ here)
  have read : (params.placeClass hd (f a) : ZMod (72*params.q₀)) =
      -((1+params.q₀*D.negativeOffset (f a) : ℕ) : ZMod (72*params.q₀)) := by
    conv_lhs => rw [repr,map_mul,Units.val_mul,D.distinguishedLift_val,at_anchor]
    simp
  have eq := neg_injective (read.symm.trans (addr a))
  rw [ZMod.natCast_eq_natCast_iff, mul_comm 72] at eq
  exact (lifted_offsets_modEq (P := params) 72 _ _).1 eq

/-- A population witness identifies the normalized row of every individual high place.
The slot index retains both its copy number and its assigned corner. -/
theorem slot_row_eq_corner (D : Data params) {w : Fin 4 → ℕ} {k : ℕ}
    (f : Sample k w ↪ D.Φ) (hd : 72*params.q₀ ∣ D.q₁) (B : D.bPlaces = univ.map f)
    (addr : ∀ a, (params.placeClass hd (f a) : ZMod (72*params.q₀)) =
      -((1+params.q₀*cornerOffset a.2.1 : ℕ) : ZMod (72*params.q₀)))
    (a : Sample k w) : row (D.negativeOffset (f a)) = corner a.2.1 := by
  exact (row_congr (slot_offset_modEq cornerAddress D f hd B addr a)).trans (row_cornerOffset _)

/-- The character readings average the actual labeled places. Each full population word
has the same average, so the number of copies cancels in the normalized result. -/
theorem readings_of_population (D : Data params) {w : Fin 4 → ℕ} (positive : 0 < ∑ i,w i)
    (hp : HasCornerPopulation D.towerExp D.bPlaces w)
    (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    readings D ι₀ ι₁ ι₂ = populationPoint w := by
  classical
  obtain ⟨hd,k,hk,f,B,addr⟩ := hp
  have card : #D.bPlaces = k * ∑ i,w i := by rw [B,card_map,card_univ,sample_card]
  have term := slot_row_eq_corner D f hd B addr
  have total : (∑ σ ∈ D.bPlaces, row (D.negativeOffset σ)) = (k:ℝ) • ∑ c, (w c:ℝ) • corner c := by
    calc (∑ σ ∈ D.bPlaces, row (D.negativeOffset σ)) = ∑ a : Sample k w, corner a.2.1 := by
           rw [B,sum_map]
           exact sum_congr rfl fun a _ ↦ term a
      _ = _ := by
        simpa only [Nat.cast_smul_eq_nsmul] using sample_sum k w corner
  rw [readings_eq_centerMass,centerMass,populationPoint]
  simp only [sum_const, nsmul_eq_mul, mul_one, one_smul, total, card, Nat.cast_mul, smul_smul]
  congr 1
  field_simp [(by exact_mod_cast hk.ne' : (k:ℝ) ≠ 0),
    (by exact_mod_cast positive.ne' : ((∑ i,w i : ℕ):ℝ) ≠ 0)]

/-- Any finite population of the four corners occurs in one actual configuration,
simultaneously for all choices of p-adic embeddings. -/
theorem eventually_populationPoint (w : Fin 4 → ℕ) (positive : 0 < ∑ i,w i) :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX = x ∧
      ∀ ι₀ ι₁ ι₂, readings D ι₀ ι₁ ι₂ = populationPoint w := by
  filter_upwards [eventually_has_corner_population w positive] with x hx
  obtain ⟨D,hx,hp⟩ := hx
  exact ⟨D,hx,readings_of_population D positive hp⟩

/-- Rational coordinates inside the four faces give a finite nonnegative integer
population of the four vertices, by clearing their barycentric denominators. -/
theorem populationPoint_of_rational {v : Point} (hv : v ∈ tetrahedron)
    (rational : ∀ i, ∃ q : ℚ, (q:ℝ) = v i) :
    ∃ w : Fin 4 → ℕ, 0 < ∑ i,w i ∧ populationPoint w = v := by
  choose z hz using rational
  let a : Fin 4 → ℚ := ![(1-z 1-2*z 0-4*z 2)/8,(1-z 1-2*z 0+4*z 2)/8,
    (1-z 1+2*z 0)/4,(1+z 1)/2]
  obtain ⟨h₁,h₂,h₃,h₄⟩ := (inside_iff_mem v).2 hv
  have nonnegative (i : Fin 4) : 0 ≤ a i := by
    have h : (0:ℝ) ≤ (a i:ℝ) := by fin_cases i <;> simp [a,hz] <;> linarith
    exact_mod_cast h
  have one : ∑ i,a i=1 := by simp [a,Fin.sum_univ_succ]; ring
  obtain ⟨w,pos,hw⟩ := integer_population_of_rational_weights a nonnegative one
  have numer (i) : (w i:ℝ) = ((∑ j,w j : ℕ):ℝ)*(a i:ℝ) := by
    simpa using congrArg (fun q : ℚ ↦ (q:ℝ)) (hw i)
  have data : ∑ i, (w i:ℝ) • corner i = ((∑ i,w i : ℕ):ℝ) • ∑ i, (a i:ℝ) • corner i := by
    rw [Finset.smul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [numer,smul_smul]
  refine ⟨w,pos,?_⟩
  rw [populationPoint,data,smul_smul,inv_mul_cancel₀ (by exact_mod_cast pos.ne'),one_smul]
  funext i
  fin_cases i <;> simp [a,corner,Fin.sum_univ_succ,hz] <;> ring

/-- Exact pointwise classification. For fixed rational-prime embeddings, a point occurs
at every sufficiently large integer scale precisely when its coordinates are rational and
it lies in the tetrahedron. The scale threshold may depend on the point. -/
theorem eventual_reading_iff_rational (v : Point) (ι₀ : PadicPlace 479)
    (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    (∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX=x ∧ readings D ι₀ ι₁ ι₂=v) ↔
      v ∈ tetrahedron ∧ ∀ i, ∃ q : ℚ, (q:ℝ)=v i := by
  constructor
  · intro frequent
    obtain ⟨_,D,_,rfl⟩ := frequent.exists
    refine ⟨inside_for_every_data D ι₀ ι₁ ι₂, ?_⟩
    intro i
    fin_cases i
    · exact D.normalizedProbe_is_rat 479 ι₀
    · exact D.normalizedProbe_is_rat 535919 ι₁
    · exact D.normalizedProbe_is_rat 665279 ι₂
  · rintro ⟨inside,rational⟩
    obtain ⟨w,pos,rfl⟩ := populationPoint_of_rational inside rational
    filter_upwards [eventually_populationPoint w pos] with x hx
    obtain ⟨D,hx,value⟩ := hx
    exact ⟨D,hx,value ι₀ ι₁ ι₂⟩

/-- At a fixed denominator there is one field and one set of scalar and level data
on which every population word of that size can be realized by an equal-size replacement. -/
theorem eventually_shared_denominator (d : ℕ) (hd : 0 < d) :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX=x ∧
      ∀ w : Fin 4 → ℕ, (∑ i,w i)=d → ∃ c : HighPlaceChoice D,
        ∀ ι₀ ι₁ ι₂, readings c.toData ι₀ ι₁ ι₂ = populationPoint w := by
  let initial : Fin 4 → ℕ := ![d,0,0,0]
  have total : ∑ i,initial i=d := by simp [initial,Fin.sum_univ_succ]
  filter_upwards [eventually_has_population_frame initial (total ▸ hd)] with x hx
  obtain ⟨D,hx,_,menu⟩ := hx
  refine ⟨D,hx,?_⟩
  intro w hw
  obtain ⟨B,card,base,sparse,pop⟩ := menu w (hw.trans total.symm)
  let c : HighPlaceChoice D := ⟨B,card,base,sparse⟩
  exact ⟨c, readings_of_population c.toData (hw ▸ hd) pop⟩

lemma populationPoint_repeat (w : Fin 4 → ℕ) (hw : 0 < ∑ i,w i) (n : ℕ) (hn : 0 < n) :
    populationPoint (fun i ↦ n*w i) = populationPoint w := by
  have vec : (∑ i, ((n*w i : ℕ):ℝ) • corner i) = (n:ℝ) • ∑ i,(w i:ℝ) • corner i := by
    rw [Finset.smul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [Nat.cast_mul,smul_smul]
  unfold populationPoint
  rw [← Finset.mul_sum,vec,smul_smul,Nat.cast_mul]
  congr 1
  field_simp [(by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0),
    (by exact_mod_cast hw.ne' : ((∑ i,w i : ℕ):ℝ) ≠ 0)]

/-- A finite list of rational points in the tetrahedron shares one field, one level and
one weight multiset at every sufficiently large scale. Each point chooses its own eligible
assignment of that multiset. -/
theorem eventually_one_frame_for_finite_points {n : ℕ} (v : Fin n → Point)
    (inside : ∀ i, v i ∈ tetrahedron) (rat : ∀ i j, ∃ a : ℚ, (a:ℝ)=v i j) :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX=x ∧
      ∀ i, ∃ c : HighPlaceChoice D, ∀ ι₀ ι₁ ι₂, readings c.toData ι₀ ι₁ ι₂ = v i := by
  classical
  choose w pos val using fun i ↦ populationPoint_of_rational (inside i) (rat i)
  let d := fun i ↦ ∑ j,w i j
  let common := ∏ i,d i
  have common_pos : 0 < common := Finset.prod_pos fun i _ ↦ pos i
  have divs (i : Fin n) : d i ∣ common := dvd_prod_of_mem d (mem_univ i)
  filter_upwards [eventually_shared_denominator common common_pos] with x hx
  obtain ⟨D,hx,choose_reading⟩ := hx
  refine ⟨D,hx,fun i ↦ ?_⟩
  let m := common/d i
  have mpos : 0 < m := Nat.div_pos (Nat.le_of_dvd common_pos (divs i)) (pos i)
  have scale : (∑ j,m*w i j)=common := by
    rw [← Finset.mul_sum]
    exact Nat.div_mul_cancel (divs i)
  obtain ⟨c,hc⟩ := choose_reading _ scale
  exact ⟨c,fun ι₀ ι₁ ι₂ ↦ (hc ι₀ ι₁ ι₂).trans ((populationPoint_repeat (w i) (pos i) m mpos).trans (val i))⟩

/-- The concrete 3,6,8,13 word is an actual interior reading at all sufficiently large scales. -/
theorem eventually_three_six_eight_thirteen :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX = x ∧
      ∀ ι₀ ι₁ ι₂, readings D ι₀ ι₁ ι₂ = ![-1/30, -2/15, 1/10] := by
  let w : Fin 4 → ℕ := ![3,6,8,13]
  have positive : 0 < ∑ i,w i := by norm_num [w,Fin.sum_univ_succ]
  have actual : populationPoint w = ![-1/30,-2/15,1/10] := by
    funext i
    fin_cases i <;> norm_num [w,populationPoint,corner,Fin.sum_univ_succ]
  simpa only [actual] using eventually_populationPoint w positive

end New.Data.CollisionPrimeExample
