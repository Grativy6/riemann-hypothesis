module

public import New.UpperBound.Divisibility.UnsignedProbeReadings
import Mathlib.Tactic

/-!
# All the hidden populations at a fixed reading

Every finite integer report has a complete menu on one field and one level. At the reading
(-1,-1,0), every allowable equal two-sided count occurs. For arbitrary rational readings
the two unmeasured proportions obey explicit linear inequalities.
-/

@[expose] public section

open Finset Real Filter NumberField ThreePrimeEnvelope ColoredSparse
namespace New.SixSignatures

lemma observed_repeat (k : ℕ) (w : Fin 6 → ℕ) (j : Fin 4) :
    observed (fun c ↦ k*w c) j = (k:ℤ)*observed w j := by
  fin_cases j <;> simp [observed,report] <;> ring

lemma point_repeat (k : ℕ) (hk : 0 < k) (w : Fin 6 → ℕ) : point (fun c ↦ k*w c) = point w := by
  funext j
  simp only [point,observed_repeat,Int.cast_mul,Int.cast_natCast]
  exact mul_div_mul_left _ _ (by exact_mod_cast hk.ne' : (k:ℝ) ≠ 0)

/-- One hidden population per unit of edge weight, including the empty ends. -/
def edgeWord (d i : ℕ) : Fin 6 → ℕ := ![i,i,d-2*i,0,0,0]

lemma edgeWord_total (d i : ℕ) (hi : 2*i ≤ d) : ∑ c,edgeWord d i c = d := by
  simp [edgeWord,Fin.sum_univ_succ]
  omega

lemma edgeWord_point (d i : ℕ) (hd : 0<d) (hi : 2*i ≤ d) :
    point (edgeWord d i) = ![-1,-1,0] := by
  have z : observed (edgeWord d i) 0 = (d:ℤ) := by rw [observed_total,edgeWord_total d i hi]
  have a : observed (edgeWord d i) 1 = -(d:ℤ) := by simp [observed, report, edgeWord]; omega
  have b : observed (edgeWord d i) 2 = -(d:ℤ) := by simp [observed, report, edgeWord]; omega
  have c : observed (edgeWord d i) 3 = 0 := by simp [observed,report,edgeWord]
  have h : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  funext j
  fin_cases j
  · change (observed (edgeWord d i) 1:ℝ)/(observed (edgeWord d i) 0:ℝ) = -1
    simp [a,z,h]
  · change (observed (edgeWord d i) 2:ℝ)/(observed (edgeWord d i) 0:ℝ) = -1
    simp [b,z,h]
  · change (observed (edgeWord d i) 3:ℝ)/(observed (edgeWord d i) 0:ℝ) = 0
    simp [c]

/-- Signed rational averages when the six entries are proportions of total mass one. -/
def rationalPoint (p : Fin 6 → ℚ) : Fin 3 → ℚ :=
  ![-p 0-p 1-p 2+p 3, -p 0-p 1-p 2-p 3-p 4+p 5, -p 0+p 1]

def proportions (w : Fin 6 → ℕ) (c : Fin 6) : ℚ := (w c:ℚ)/(∑ i,w i : ℕ)

lemma rationalPoint_proportions (w : Fin 6 → ℕ) :
    (fun j ↦ (rationalPoint (proportions w) j : ℝ)) = point w := by
  funext j
  fin_cases j <;> simp [rationalPoint,proportions,point,observed,report,Fin.sum_univ_succ] <;> ring

/-- Barycentric coefficients in the vertex order A,B,C,D. -/
def barycentric (v : Fin 3 → ℚ) : Fin 4 → ℚ :=
  ![(1-v 1-2*v 0-4*v 2)/8, (1-v 1-2*v 0+4*v 2)/8,
    (1-v 1+2*v 0)/4, (1+v 1)/2]

/-- Every proportion is specified once the edge-bin and face-bin proportions are given. -/
def weightsAt (v : Fin 3 → ℚ) (e f : ℚ) : Fin 6 → ℚ :=
  let b := barycentric v
  ![b 0-e/2-f/4, b 1-e/2-f/4, e, b 2-f/2, f, b 3]

lemma weightsAt_sum (v : Fin 3 → ℚ) (e f : ℚ) : ∑ i,weightsAt v e f i = 1 := by
  simp [weightsAt,barycentric,Fin.sum_univ_succ]; ring

lemma weightsAt_point (v : Fin 3 → ℚ) (e f : ℚ) : rationalPoint (weightsAt v e f) = v := by
  funext j
  fin_cases j <;> simp [weightsAt,barycentric,rationalPoint] <;> ring

lemma weightsAt_unique (p : Fin 6 → ℚ) (h : ∑ i,p i=1) :
    weightsAt (rationalPoint p) (p 2) (p 4) = p := by
  simp [Fin.sum_univ_succ] at h
  funext j
  fin_cases j <;> simp [weightsAt,barycentric,rationalPoint] <;> linarith

/-- Nonnegativity written in the two coordinates that were lost. -/
def allows (v : Fin 3 → ℚ) (e f : ℚ) : Prop :=
  0≤e ∧ 0≤f ∧ e/2+f/4 ≤ min (barycentric v 0) (barycentric v 1) ∧
    f/2 ≤ barycentric v 2 ∧ 0≤barycentric v 3

lemma allows_iff (v : Fin 3 → ℚ) (e f : ℚ) :
    allows v e f ↔ ∀ i, 0 ≤ weightsAt v e f i := by
  constructor
  · rintro ⟨he,hf,hab,hc,hd⟩ i
    obtain ⟨ha,hb⟩ := le_min_iff.1 hab
    fin_cases i
    · change 0 ≤ barycentric v 0-e/2-f/4; linarith
    · change 0 ≤ barycentric v 1-e/2-f/4; linarith
    · exact he
    · change 0 ≤ barycentric v 2-f/2; linarith
    · exact hf
    · exact hd
  · intro h
    have a := h 0
    have b := h 1
    have c := h 3
    change 0 ≤ barycentric v 0-e/2-f/4 at a
    change 0 ≤ barycentric v 1-e/2-f/4 at b
    change 0 ≤ barycentric v 2-f/2 at c
    exact ⟨h 2,h 4,le_min (by linarith) (by linarith),by linarith,h 5⟩

end New.SixSignatures

namespace New.Data.CollisionPrimeExample
open SixSignatures
local instance : Fact (Nat.Prime 479) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 535919) := ⟨by norm_num1⟩
local instance : Fact (Nat.Prime 665279) := ⟨by norm_num1⟩

/-- Every histogram with the indicated integer report can be installed on one fixed level
and field after multiplication by the same k. -/
theorem eventually_whole_report_fiber (h : Fin 6 → ℕ) (hd : 0<∑ i,h i) :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧
      #D.bPlaces=k*(∑ i,h i) ∧ ∀ w, observed h=observed w → ∃ c : HighPlaceChoice D,
      census c.toData = (fun i ↦ k*w i) ∧
      ∀ ι₀ ι₁ ι₂, readings c.toData ι₀ ι₁ ι₂ = point h := by
  filter_upwards [eventually_shared_census _ hd] with x result
  obtain ⟨D,k,scale,hk,mass,menu⟩ := result
  refine ⟨D,k,scale,hk,mass,?_⟩
  intro w eq
  obtain ⟨same,points⟩ := (observed_eq_iff_count_and_point hd).1 eq.symm
  obtain ⟨c,hc⟩ := menu w same
  exact ⟨c,hc,fun i j l ↦ by rw [readings_eq_census,hc,point_repeat k hk,points]⟩

/-- Every intermediate balanced count occurs, with one common scale and one level prime.
At d=30 there are sixteen choices of i. -/
theorem eventually_every_balanced_count (d : ℕ) (hd : 0<d) :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧ #D.bPlaces=k*d ∧
      ∀ i, 2*i ≤ d → ∃ c : HighPlaceChoice D,
        ∀ (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279),
          readings c.toData ι₀ ι₁ ι₂ = ![-1,-1,0] ∧ thirdLedger c.toData ι₂ = (k*i,k*i) ∧
          ∀ ϑ j, c.toData.measuredNorm 665279 ι₂ ϑ j = 1 := by
  filter_upwards [eventually_shared_census d hd] with x result
  obtain ⟨D,k,scale,hk,mass,menu⟩ := result
  refine ⟨D,k,scale,hk,mass,?_⟩
  intro i hi
  obtain ⟨c,hc⟩ := menu _ (edgeWord_total d i hi)
  refine ⟨c,fun a b m ↦ ?_⟩
  have both : thirdLedger c.toData m = (k*i,k*i) := by
    change pairCounts c.toData 665279 m = _
    rw [(probe_pair_counts c.toData a b m).2.2,hc]
    rfl
  exact ⟨by rw [readings_eq_census,hc,point_repeat k hk,edgeWord_point d i hd hi],both,
    fun ϑ j ↦ (third_norm_eq_one_iff _ b m ϑ j).2 (by rw [both])⟩

lemma census_proportions_sum (D : Data params) : ∑ i,proportions (census D) i = 1 := by
  unfold proportions
  rw [← Finset.sum_div,← Nat.cast_sum,div_self]
  exact_mod_cast (census_total D).symm ▸ (card_pos.2 D.bPlaces_nonempty).ne'

theorem eventually_given_proportions (p : Fin 6 → ℚ) (pos : ∀ i,0≤p i) (one : ∑ i,p i=1) :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX=x ∧ proportions (census D) = p := by
  obtain ⟨w,hw,proportional⟩ := integer_population_of_rational_weights p pos one
  filter_upwards [eventually_shared_census _ hw] with x result
  obtain ⟨D,k,scale,hk,card,menu⟩ := result
  obtain ⟨c,hc⟩ := menu w rfl
  refine ⟨c.toData,c.fields.1.trans scale,?_⟩
  funext i
  rw [proportions,census_total,c.fields.2.2.2.2.2.2.2.2.2.2,card,hc,Nat.cast_mul,Nat.cast_mul,
    proportional]
  field_simp [(by exact_mod_cast hk.ne' : (k:ℚ) ≠ 0),
    (by exact_mod_cast hw.ne' : ((∑ i,w i : ℕ):ℚ) ≠ 0)]

/-- Exact rational fiber of the three measured exponents. The inequalities are both
necessary on any data and sufficient at every sufficiently large integer scale. -/
theorem eventual_hidden_proportions_iff (v : Fin 3 → ℚ) (e f : ℚ) (ι₀ : PadicPlace 479)
    (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) :
    (∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX=x ∧
      readings D ι₀ ι₁ ι₂ = (fun i ↦ (v i : ℝ)) ∧
      proportions (census D) 2=e ∧ proportions (census D) 4=f) ↔ allows v e f := by
  constructor
  · intro often
    obtain ⟨_,D,_,reading,edge,face⟩ := often.exists
    rw [readings_eq_census,← rationalPoint_proportions] at reading
    have eq : rationalPoint (proportions (census D)) = v := by
      funext i; exact_mod_cast congrFun reading i
    apply (allows_iff v e f).2
    have fill := weightsAt_unique _ (census_proportions_sum D)
    rw [eq,edge,face] at fill
    rw [fill]
    intro i; unfold proportions; positivity
  · intro allowed
    filter_upwards [eventually_given_proportions (weightsAt v e f) ((allows_iff v e f).1 allowed)
      (weightsAt_sum v e f)] with x hx
    obtain ⟨D,scale,frac⟩ := hx
    refine ⟨D,scale,?_,?_,?_⟩
    · rw [readings_eq_census,← rationalPoint_proportions,frac,weightsAt_point]
    · rw [frac]; rfl
    · rw [frac]; rfl

/-- The first exchange keeps the 479 occupancy fixed, and the second keeps the 665279
occupancy fixed. In either case the signed readings coincide. All four assignments share
one frame, showing why each of the two additional tallies is needed. -/
theorem eventually_neither_occupied_total_alone :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧ #D.bPlaces=2*k ∧
      ∃ choices : Fin 4 → HighPlaceChoice D,
      ∀ (ι₀ : PadicPlace 479) (ι₁ : PadicPlace 535919) (ι₂ : PadicPlace 665279) (j : Fin 4),
        readings (choices j).toData ι₀ ι₁ ι₂ = (![![-1,-1,0],![-1,-1,0],![0,-1,0],![0,-1,0]] : Fin 4 → Point) j ∧
        occupied (choices j).toData 479 ι₀ = ![2*k,2*k,2*k,0] j ∧
        occupied (choices j).toData 665279 ι₂ = ![2*k,0,0,0] j := by
  classical
  let word : Fin 4 → Fin 6 → ℕ := ![![1,1,0,0,0,0],![0,0,2,0,0,0],
    ![0,0,1,1,0,0],![0,0,0,0,2,0]]
  have size (j) : ∑ i,word j i=2 := by fin_cases j <;> decide
  filter_upwards [eventually_shared_census 2 (by decide)] with x hx
  obtain ⟨D,k,scale,hk,mass,menu⟩ := hx
  have get (j : Fin 4) := menu (word j) (size j)
  choose choices hvals using get
  refine ⟨D,k,scale,hk,by simpa [mul_comm] using mass,choices,?_⟩
  intro a b c j
  obtain ⟨first,_,third⟩ := occupied_eq_census (choices j).toData a b c
  rw [readings_eq_census,first,third,hvals,point_repeat k hk]
  constructor
  · funext v
    fin_cases j <;> fin_cases v <;> norm_num [word,point,observed,report]
  · fin_cases j <;> simp [word,firstOccupied,thirdOccupied,two_mul,mul_two]

end New.Data.CollisionPrimeExample
