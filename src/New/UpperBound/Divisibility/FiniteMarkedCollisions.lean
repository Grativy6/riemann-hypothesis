module

public import New.UpperBound.Divisibility.MarkedCollisionFormula
public import New.UpperBound.Divisibility.CollisionDeficit
import Mathlib.Tactic

/-!
# The finite charge of a marked collision

At a colliding long row the partner has weight a/x₁. Reindex the positive terms by odd
multiples of the local order and sum the resulting finite geometric progression. Each active
term removes one integral off weight from the raw allowance. The final estimates relate
this change to the scalar exponent and to the determinant cost of the marked product.
-/

@[expose] public section

open Finset
namespace New.CollisionArithmetic

/-- Reindex the positive odd multiples of o lying strictly below the cutoff in norm. -/
theorem sum_odd_multiples_below {p o : ℕ} (hp : 1 < p) (ho : Odd o) (N : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (∑ e ∈ range (p.clog N), if Odd e ∧ o ∣ e then (a / (p : ℝ)^e - a/N)⁺ else 0) =
      ∑ j ∈ range ((p^o).clog N / 2), (a / ((p : ℝ)^o)^(2*j+1) - a/N) := by
  let next (j : ℕ) := o * (2*j+1)
  have hq := Nat.one_lt_pow ho.pos.ne' hp
  have small (j : ℕ) : next j < p.clog N ↔ j < (p^o).clog N / 2 := by
    have equiv : next j < p.clog N ↔ 2*j+1 < (p^o).clog N := by
      rw [Nat.lt_clog_iff_pow_lt hp, Nat.lt_clog_iff_pow_lt hq]
      simp only [next, pow_mul]
    rw [equiv]
    omega
  rw [← sum_filter]
  symm
  apply sum_bij (fun j _ ↦ next j)
  · intro j hj
    exact mem_filter.2 ⟨mem_range.2 ((small j).2 (mem_range.1 hj)),
      Nat.odd_mul.2 ⟨ho, ⟨j, rfl⟩⟩, dvd_mul_right ..⟩
  · intro j hj k hk heq
    have := Nat.eq_of_mul_eq_mul_left ho.pos heq
    omega
  · intro e he
    obtain ⟨hcut, heodd, d, rfl⟩ := mem_filter.1 he
    obtain ⟨j, rfl⟩ := (Nat.odd_mul.1 heodd).2
    exact ⟨j, mem_range.2 ((small j).1 (mem_range.1 hcut)), rfl⟩
  · intro j hj
    have pn : p^(next j) < N := (Nat.lt_clog_iff_pow_lt hp).1 ((small j).2 (mem_range.1 hj))
    have pos : 0 < (p : ℝ)^(next j) := pow_pos (by exact_mod_cast Nat.zero_lt_of_lt hp) _
    have hsub : 0 ≤ a/(p : ℝ)^(next j) - a/N :=
      sub_nonneg.2 (div_le_div_of_nonneg_left ha pos (by exact_mod_cast pn.le))
    rw [posPart_of_nonneg hsub]
    simp [next, pow_mul]

/-- A finite geometric sum minus the same partner weight at each active exponent. -/
theorem finite_odd_geometric {q : ℝ} (hq : 1 < q) (a w : ℝ) (K : ℕ) :
    (∑ j ∈ range K, (a/q^(2*j+1) - w)) =
      (a*q/(q^2-1)) * (1-((q^2)⁻¹)^K) - K*w := by
  have hq0 : q ≠ 0 := by linarith
  have h2 : 1 < q^2 := one_lt_pow₀ hq (by decide)
  have hr : (q^2)⁻¹ ≠ 1 := (inv_lt_one_of_one_lt₀ h2).ne
  have term (j : ℕ) : a/q^(2*j+1) = (a/q)*((q^2)⁻¹)^j := by
    simp only [pow_succ, pow_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [term]
  rw [sum_sub_distrib, ← mul_sum, geom_sum_eq hr, sum_const, card_range, nsmul_eq_mul]
  congr 1
  have hd : q^2 - 1 ≠ 0 := by linarith
  have hdr : (q^2)⁻¹ - 1 = -(q^2-1)/q^2 := by field_simp; ring
  generalize ((q^2)⁻¹)^K = z
  rw [hdr]
  field_simp [hd, hq0]
  ring

end New.CollisionArithmetic


namespace New.Data

open Finset Real

variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]
  {Λ : Finset (FinPlace D.E)}

variable (D) in
/-- At an odd local order, the number of odd multiples whose prime powers lie strictly below x₁. -/
noncomputable def collisionTermCount (p : ℕ) : ℕ := (p ^ D.o₀ p).clog D.natX₁ / 2

omit hp [PadicPlace p] in
/-- A colliding partner is a distinguished place and therefore has precisely the off weight. -/
lemma IsCollision.partner_weight {S : Finset D.Φ} {τ : D.Φ} {e : ℕ} (hc : D.IsCollision p S τ e) :
    (D.weight (D.placeOfInt (-p ^ e) * τ) : ℝ) = D.a / D.x₁ := by
  let σ := D.placeOfInt (-p ^ e) * τ
  have ha : σ ∈ D.aPlaces := (mem_sdiff.1 hc.2.2).1
  have hn : σ ∉ D.bPlaces := by
    intro hb
    have hone : P.placeClass (P.q₀.dvd_mul_right _) σ = 1 := by simpa [aPlaces] using ha
    have heq := hone.symm.trans (D.placeClass_of_mem_bPlaces σ hb)
    exact P.d_pow_ne_neg_one 0 (by simpa using congrArg (fun z : (ZMod P.q₀)ˣ ↦ (z : ZMod P.q₀)) heq)
  rw [D.cast_weight, ite_eq_right hn]

open scoped Classical in
omit [PadicPlace p] in
/-- At a collision, the surviving long-row positive part equals the charge in the finite sum. -/
lemma IsCollision.longRow_deficit {S : Finset D.Φ} {τ : D.Φ} {e : ℕ} (hc : D.IsCollision p S τ e)
    (j : ℕ) :
    (D.a / p^e - D.weight (D.placeOfInt (-p ^ e) * τ) : ℝ)⁺ -
      (longRow S τ / p^e - longRow S (D.placeOfInt (-p ^ e) * τ) -
        D.lowColumns j (D.placeOfInt (-p ^ e) * τ))⁺ = D.collisionDeficitAt p S τ e := by
  have hpow : 1 ≤ (p : ℝ)^e := one_le_pow₀ (by exact_mod_cast hp.out.one_le)
  have hle : (D.a : ℝ) / p^e ≤ D.a := div_le_self (Nat.cast_nonneg _) hpow
  rw [hc.partner_weight, collisionDeficitAt, ite_eq_left hc]
  simp only [longRow, ite_eq_left hc.2.1, ite_eq_left hc.2.2]
  have hz : ((D.a : ℝ)/(p : ℝ)^e - D.a - D.lowColumns j (D.placeOfInt (-p^e)*τ))⁺ = 0 :=
    posPart_eq_zero.2 (by linarith [Nat.cast_nonneg (D.lowColumns j (D.placeOfInt (-p^e)*τ)) (α := ℝ)])
  rw [hz, sub_zero]

open scoped Classical in
/-- The finite loss equals the raw collision sum with its geometric tail removed, less the
integer off weight at every active place and exponent. -/
theorem IsMarked.collisionDeficit_formula (h : D.IsMarked Λ) :
    D.collisionDeficit p (placesInducing Λ) = D.collisionSum p (placesInducing Λ) *
        (1 - ((((p : ℝ)^D.o₀ p)^2)⁻¹)^(D.collisionTermCount p)) -
      (#{τ ∈ D.aPlaces | inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ} : ℝ) *
        D.collisionTermCount p * D.offWeight := by
  classical
  let U := D.aPlaces.filter fun τ ↦ inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ
  let R := p.clog ⌈D.x₁⌉₊
  let K := D.collisionTermCount p
  let q := (p : ℝ)^D.o₀ p
  let T := ∑ e ∈ range R, if Odd e ∧ D.o₀ p ∣ e then (D.a / (p : ℝ)^e - D.a/D.x₁)⁺ else 0
  have hx : D.x₁ = D.natX₁ := D.exp_logX₁
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hq : 1 < q := one_lt_pow₀ hp1 h.isExceptional.odd_o₀.pos.ne'
  have term (τ : D.Φ) :
      (∑ e ∈ range R, D.collisionDeficitAt p (placesInducing Λ) τ e) =
        if τ ∈ U then T else 0 := by
    by_cases hτ : τ ∈ U
    · have hu := mem_filter.1 hτ
      simp [collisionDeficitAt, h.collision_iff_uncovered, hu, hτ, T]
    · have hu : ¬(τ ∈ D.aPlaces ∧ inducedPlace τ ∉ Λ ∧ star (inducedPlace τ) ∉ Λ) :=
        fun z ↦ hτ (mem_filter.2 z)
      simp [collisionDeficitAt, h.collision_iff_uncovered, hu, hτ]
  have factor : D.collisionDeficit p (placesInducing Λ) = (#U : ℝ)*T := by
    unfold collisionDeficit
    change (∑ τ : D.Φ, ∑ e ∈ range R, D.collisionDeficitAt p (placesInducing Λ) τ e) = _
    simp_rw [term]
    rw [← sum_filter]
    simp [nsmul_eq_mul]
  have eval : T = (D.a*q/(q^2-1)) * (1-((q^2)⁻¹)^K) - K*(D.offWeight : ℝ) := by
    dsimp only [T, R, K, collisionTermCount, q]
    rw [D.cast_offWeight, hx, Nat.ceil_natCast, CollisionArithmetic.sum_odd_multiples_below
      hp.out.one_lt h.isExceptional.odd_o₀ D.natX₁ (Nat.cast_nonneg _)]
    exact CollisionArithmetic.finite_odd_geometric hq _ _ _
  rw [factor, eval, h.collisionSum_eq_uncovered]
  change (#U : ℝ) * ((D.a*q / (q^2-1)) * (1-((q^2)⁻¹)^K) - K*(D.offWeight : ℝ)) = _
  dsimp only [U, q, K]
  ring

end New.Data


namespace New.Data

open Finset Real

variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]
  {Λ : Finset (FinPlace D.E)}

/-- At an exceptional small prime every distinguished place contributes in the unmarked case. -/
lemma IsExceptional.collisionDeficit_empty (he : D.IsExceptional p) (hs : D.IsSmallNonsplit p) :
    D.collisionDeficit p ∅ = D.collisionSum p ∅ *
      (1 - ((((p : ℝ)^D.o₀ p)^2)⁻¹)^(D.collisionTermCount p)) -
      (#D.aPlaces : ℝ) * D.collisionTermCount p * D.offWeight := by
  classical
  have h : D.IsMarked (p := p) (∅ : Finset (FinPlace D.E)) := ⟨by simp, he, by simp, hs⟩
  simpa [placesInducing] using h.collisionDeficit_formula

omit [PadicPlace p] in
/-- A single eligible exponent below the cutoff supplies this much finite deficit on the entire
unmarked distinguished set. -/
lemma first_active_term_le_deficit (hi : chiK P.d p = -1) {e : ℕ} (he : Odd e)
    (ho : D.o₀ p ∣ e) (hx : (p : ℝ)^e < D.x₁) :
    (#D.aPlaces : ℝ) * ((D.a : ℝ)/(p : ℝ)^e - D.a/D.x₁) ≤ D.collisionDeficit p ∅ := by
  classical
  let T := (D.a : ℝ)/(p : ℝ)^e - D.a/D.x₁
  let R := p.clog ⌈D.x₁⌉₊
  have hm : e ∈ range R := mem_range.2 <| (Nat.lt_clog_iff_pow_lt hp.out.one_lt).2 <| by
    exact_mod_cast (hx.trans_le (Nat.le_ceil D.x₁))
  have le_all (τ : D.Φ) : (if τ ∈ D.aPlaces then T else 0) ≤
      ∑ n ∈ range R, D.collisionDeficitAt p ∅ τ n := by
    by_cases ha : τ ∈ D.aPlaces
    · rw [ite_eq_left ha]
      have hc := (D.collision_empty_iff τ e).2 ⟨ha, hi, he, ho⟩
      refine le_trans ?_ (single_le_sum (fun n _ ↦ D.collisionDeficitAt_nonneg p ∅ τ n) hm)
      rw [collisionDeficitAt, ite_eq_left hc]
      exact le_posPart _
    · rw [ite_eq_right ha]
      exact sum_nonneg fun n _ ↦ D.collisionDeficitAt_nonneg p ∅ τ n
  calc (#D.aPlaces : ℝ) * T = ∑ τ : D.Φ, if τ ∈ D.aPlaces then T else 0 := by
        rw [← sum_filter]; simp [nsmul_eq_mul]
    _ ≤ _ := sum_le_sum fun τ _ ↦ le_all τ

/-- Once the finite excess is nonnegative, each active term removes one integral off weight
per place and lift from the raw scalar-exponent budget. -/
lemma IsExceptional.clearance_saving (he : D.IsExceptional p) (hs : D.IsSmallNonsplit p)
    (hpaid : 0 ≤ D.m * D.collisionDeficit p ∅ - D.loss p) :
    D.collisionClearance p + D.m * #D.aPlaces * D.collisionTermCount p * D.offWeight ≤
      ⌈D.m * D.collisionSum p ∅ - D.loss p⌉₊ := by
  have hraw : 0 ≤ D.collisionSum p ∅ := (D.collisionDeficit_nonneg p ∅).trans
    (D.collisionDeficit_le_collisionSum ∅)
  let r := ((((p : ℝ)^D.o₀ p)^2)⁻¹)^(D.collisionTermCount p)
  have ht : 0 ≤ D.m * D.collisionSum p ∅ * r := by dsimp [r]; positivity
  rw [collisionClearance, ← Nat.ceil_add_natCast hpaid]
  apply Nat.ceil_mono
  push_cast
  rw [he.collisionDeficit_empty hs]
  dsimp only [r] at ht
  linarith

end New.Data

namespace New.Data

open Finset Real

variable {P : Parameters} (D : Data P) (p : ℕ) [Fact p.Prime] [PadicPlace p]
  (Λ : Finset (FinPlace D.E))

/-- Varying the scalar exponent changes the local additive index allowance by a fixed slope. -/
theorem markedProductIndexCost_sub (J j : ℕ) :
    D.markedProductIndexCost p Λ J - D.markedProductIndexCost p Λ j =
      (#Λ : ℝ) * ((J : ℝ) - j) / ((D.m : ℝ) * D.f) := by
  have hm : (D.m : ℝ) ≠ 0 := (HasLogBound.pos D).ne'
  have hf : (D.f : ℝ) ≠ 0 := (HasLogBound.pos D).ne'
  unfold markedProductIndexCost
  rw [← mul_sub, ← sum_sub_distrib]
  have term (l : FinPlace D.E) :
      (12 * D.heckeScalingExponent l / (D.m * p) + 1 / (D.m^2 * D.f) * J : ℝ) -
        (12 * D.heckeScalingExponent l / (D.m * p) + 1 / (D.m^2 * D.f) * j) =
        ((J : ℝ)-j) / (D.m^2 * D.f) := by ring
  simp_rw [term]
  rw [sum_const, nsmul_eq_mul]
  field_simp

end New.Data
