module

public import New.UpperBound.Divisibility.OddColumnFrame
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-!
# A genuine period-144 prime separates the nine invisible columns

For p=38,586,239 the two sides of one measuring pair exhaust a single residue modulo 72.
Odd multiplicity in that residue forces a nonunit characteristic norm, regardless of
how the copies are distributed between its two lifts. Empty residues give norm one.
-/

@[expose] public section
open Finset Filter NumberField Real ThreePrimeEnvelope ColoredSparse
namespace New.Data.CollisionPrimeExample
open SixSignatures OrbitProbes
local instance : Fact (Nat.Prime 38586239) := ⟨by norm_num1⟩

lemma period_144_facts (D : Data params) :
    D.IsExceptional 38586239 ∧ D.o₀ 38586239=1 ∧ D.returnQuotient 38586239=2088 ∧
      D.returnPairCount 38586239=72 := by
  have : Fact (Nat.Prime 9239) := ⟨by norm_num1⟩
  have hi : chiK params.d (38586239:ℕ) = -1 := by
    change chiK 9239 (38586239:ℕ) = -1
    rw [chiK_eq_legendreSym,jacobiSym.legendreSym.to_jacobiSym];norm_num
  have ho := (order_one_iff_base_dvd_succ (D := D) hi).2 (by decide)
  have ret : D.returnQuotient 38586239=2088 := by rw [returnQuotient,ho];decide
  have mlarge : 38586239+1<D.m := by
    have lb : (7000:ℝ) ≤ D.logX/4 := by
      linarith [D.mul_log_logB_le_logX,D.constantBound_le,(le_constantBound (P := params)).1]
    have base : (7000:ℝ) ≤ exp (D.logX/4) := by linarith [Real.add_one_le_exp (D.logX/4)]
    have bound : (38586240:ℝ)<exp (D.logX/2) := calc
      _ < (7000:ℝ)^2 := by norm_num
      _ ≤ (exp (D.logX/4))^2 := pow_le_pow_left₀ (by norm_num) base 2
      _ = exp (D.logX/4+D.logX/4) := by rw [Real.exp_add,pow_two]
      _ = _ := congrArg exp (by ring)
    exact_mod_cast bound.trans_le D.m_mem.1
  obtain ⟨n,_,hn⟩ := D.exists_m_eq_two_pow
  have t : 72 ∣ towerDeg D.towerExp := Nat.mul_dvd_mul
    (pow_dvd_pow 3 (show 2 ≤ Nat.log 3 D.towerExp+5 by omega))
    (pow_dvd_pow 2 (show 3 ≤ D.towerExp by omega))
  have cop : (towerDeg D.towerExp).Coprime 29 :=
    ((by decide : Nat.Coprime 3 29).pow_left _).mul_left ((by decide : Nat.Coprime 2 29).pow_left _)
  exact ⟨exceptional_of_local_order_one hi ho mlarge,ho,ret,by
    rw [returnPairCount,ret,show 2088=72*29 by decide,gcd_with_coprime_cofactor t cop]⟩

lemma index_eq_iff_mod72 (u v : ℕ) : boardIndex u=boardIndex v ↔ u ≡ v [MOD 72] := by
  constructor
  · intro same
    have h := address_boardIndex u
    rw [same] at h
    exact h.symm.trans (address_boardIndex v)
  · exact boardIndex_congr

set_option maxRecDepth 4096 in
/-- The two counts at period 144 sum to the actual number of high places in one 72-slot
residue, independently of the additional digit. -/
theorem paired_mass_at_144 (D : Data params) (ι : PadicPlace 38586239) (a : ℕ) :
    let l := D.anchorPrime 38586239 ι a
    ((D.highCount 38586239 l + D.highCount 38586239 (star l) : ℕ) : ℤ) =
      residueBoard D (boardIndex a).1 (boardIndex a).2 := by
  classical
  intro l
  obtain ⟨he,_,_,per⟩ := period_144_facts D
  have split (u : ℕ) :
      (if u ≡ a [MOD 144] then (1:ℕ) else 0)+(if u ≡ a+72 [MOD 144] then 1 else 0) =
      if boardIndex u = boardIndex a then 1 else 0 := by
    let r : Fin 144 := ⟨u%144,Nat.mod_lt _ (by decide)⟩
    let b : Fin 144 := ⟨a%144,Nat.mod_lt _ (by decide)⟩
    have rx : r.val ≡ u [MOD 144] := Nat.mod_modEq _ _
    have byy : b.val ≡ a [MOD 144] := Nat.mod_modEq _ _
    have transfer {k x y x' y' : ℕ} (hx : x' ≡ x [MOD k]) (hy : y' ≡ y [MOD k]) :
        (x ≡ y [MOD k]) ↔ x' ≡ y' [MOD k] :=
      ⟨fun h ↦ hx.trans (h.trans hy.symm),fun h ↦ hx.symm.trans (h.trans hy)⟩
    have two : 72 ∣ 144 := by decide
    have middle := (index_eq_iff_mod72 u a).trans (transfer (rx.of_dvd two) (byy.of_dvd two))
    have left := transfer rx byy
    have right := transfer rx (byy.add_right 72)
    have table : ∀ x y : Fin 144,
        (if x.val ≡ y.val [MOD 144] then (1:ℕ) else 0)+(if x.val ≡ y.val+72 [MOD 144] then 1 else 0) =
        if x.val ≡ y.val [MOD 72] then 1 else 0 := by decide
    exact (congrArg₂ (fun x y : ℕ ↦ x+y) (if_congr left rfl rfl) (if_congr right rfl rfl)).trans
      ((table r b).trans (if_congr middle.symm rfl rfl))
  have nat : D.highCount 38586239 l + D.highCount 38586239 (star l) =
      #{z ∈ D.bPlaces | boardIndex (D.negativeOffset z)=boardIndex a} := by
    rw [highCount,highCount,card_filter,card_filter,card_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro z hz
    have orig : D.inducedPlace (p := 38586239) z=D.anchorPrime 38586239 ι (D.negativeOffset z) :=
      congrArg (D.inducedPlace (p := 38586239)) (D.negativePlace_eq_offset (D.placeClass_of_mem_bPlaces _ hz))
    have left : D.inducedPlace (p := 38586239) z=l ↔ D.negativeOffset z ≡ a [MOD 144] := by
      change _=D.anchorPrime 38586239 ι a ↔ _
      rw [orig,he.anchorPrime_eq_iff,per]
    have right : D.inducedPlace (p := 38586239) z=star l ↔ D.negativeOffset z ≡ a+72 [MOD 144] := by
      change _=star (D.anchorPrime 38586239 ι a) ↔ _
      rw [orig,← he.anchorPrime_conjugate,he.anchorPrime_eq_iff,per]
    simpa only [left,right] using split (D.negativeOffset z)
  change ((_+_ : ℕ):ℤ) = ((#{z ∈ D.bPlaces | boardIndex (D.negativeOffset z)=boardIndex a} : ℕ):ℤ)
  exact congrArg (fun n : ℕ ↦ (n:ℤ)) nat

/-- All nine columns are invisible on the 72-slot board. On the very same data,
p=38,586,239 detects a nonunit precisely in the occupied residue class modulo nine.
All choices of embeddings, twists and lift indices satisfy the comparison. -/
theorem eventually_separate_the_nine_columns :
    ∀ᶠ x : ℕ in atTop, ∃ (D : Data params) (k : ℕ), D.natX=x ∧ 0<k ∧ Odd k ∧ #D.bPlaces=8*k ∧
      ∀ b : Fin 9, let E := D.translateOffset b.val
        (∀ v j,residueBoard E v j=if v=b then (k:ℤ) else 0) ∧
        (∀ p : ℕ, ∀ [_hp : Fact p.Prime], ∀ _ι : PadicPlace p,
          D.IsExceptional p → 2*D.returnPairCount p ∣ 72 → ∀ l : FinPlace D.E,
          (p : 𝓞 D.E) ∈ l.asIdeal → ∀ (θ : E.TameChar) (j : ℕ),
            ‖ιₚ ((E.chainChar θ j).baseChange.atUniformizer l)‖=1) ∧
        ∀ (ι : PadicPlace 38586239) (a : ℕ) (θ : E.TameChar) (j : ℕ),
          (‖ιₚ ((E.chainChar θ j).baseChange.atUniformizer (E.anchorPrime 38586239 ι a))‖=1 ↔
             a%9≠b.val) := by
  filter_upwards [eventually_odd_column] with x hx
  obtain ⟨D,scale,pop,odd⟩ := hx
  obtain ⟨k,hk,card,hist⟩ := board_after_column_translation D pop
  rw [card,Nat.mul_div_cancel_left _ (by decide : 0<8)] at odd
  refine ⟨D,k,scale,hk,odd,card,?_⟩
  intro b E
  refine ⟨hist b,fun p _ ι he fits l hl θ j ↦
    (unit_norms_of_flat_board E (fun v z ↦ (hist b v z).trans (hist b v 0).symm) ι he fits l).2 hl θ j,?_⟩
  intro ι a θ j
  let l := E.anchorPrime 38586239 ι a
  have both := paired_mass_at_144 E ι a
  change ((E.highCount 38586239 l+E.highCount 38586239 (star l) : ℕ) : ℤ)=_ at both
  rw [hist] at both
  change (‖ιₚ ((E.chainChar θ j).baseChange.atUniformizer l)‖=1) ↔ _
  have above : (38586239 : 𝓞 E.E) ∈ l.asIdeal := E.p_mem_inducedPlace (E.distinguishedLift a*E.placeOfInt (-1))
  rw [norm_atUniformizer_eq_one_iff (D := E) (l := l) (period_144_facts E).1.chiK_eq_neg_one above θ j]
  change (E.highCount 38586239 l=E.highCount 38586239 (star l)) ↔ _
  by_cases same : (boardIndex a).1=b
  · have residue : a%9=b.val := congrArg Fin.val same
    rw [ite_eq_left same] at both
    obtain ⟨u,hu⟩ := odd
    omega
  · have diff : a%9≠b.val := fun eq ↦ same (Fin.ext eq)
    rw [ite_eq_right same] at both
    omega

end New.Data.CollisionPrimeExample
