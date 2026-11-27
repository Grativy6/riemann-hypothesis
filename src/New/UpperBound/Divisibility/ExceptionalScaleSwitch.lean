module

public import New.UpperBound.Divisibility.FiniteMarkedCollisions
public import New.UpperBound.Divisibility.CollisionPrimeFloor
import New.Reduction.Data.Existence
import New.Reduction.PrimeSums
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-!
# One exceptional prime in the two clearance branches

For arbitrarily large primes in one progression, the local order is three. Choosing the
scale near p⁴ or at p¹⁰⁰ keeps the prime small and exceptional in both cases. The first
scale gives zero clearance. At the second the first collision term forces positive clearance.
-/

@[expose] public section

open Finset Real Filter
namespace New.Data.CollisionPrimeExample

private lemma residue_inert_34319 : chiK params.d (34319 : ℕ) = -1 := by
  have : Fact (Nat.Prime 9239) := ⟨by norm_num1⟩
  change chiK 9239 (34319 : ℕ) = -1
  rw [chiK_eq_legendreSym, jacobiSym.legendreSym.to_jacobiSym]
  norm_num

private lemma local_order_three {p : ℕ} [Fact p.Prime]
    (hmod : p ≡ 34319 [MOD (18480*9239)]) (D : Data params) :
    chiK params.d p = -1 ∧ D.o₀ p = 3 := by
  have hd : (p : ZMod params.d) = ((34319 : ℕ) : ZMod params.d) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (hmod.of_dvd (dvd_mul_left 9239 18480))
  have hi : chiK params.d p = -1 := by rw [hd]; exact residue_inert_34319
  have hbase : (p : ZMod params.q₀) = ((34319 : ℕ) : ZMod params.q₀) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (hmod.of_dvd (dvd_mul_right 18480 9239))
  refine ⟨hi, ?_⟩
  unfold o₀
  rw [← orderOf_units, placeClass_neg_prime_val (D := D) (p := p) hi dvd_rfl, hbase]
  change orderOf (-((34319 : ℕ) : ZMod 18480)) = 3
  apply (orderOf_eq_iff (by decide : 0 < 3)).2
  refine ⟨by decide, ?_⟩
  intro i h1 h2
  interval_cases i <;> decide

private lemma exceptional_of_cube {p : ℕ} [hp : Fact p.Prime] (D : Data params)
    (hi : chiK params.d p = -1) (ho : D.o₀ p = 3) (hm : p^2 < D.m) : D.IsExceptional p := by
  have h2 := hp.out.two_le
  have hlarge : p + 1 < D.m := lt_of_le_of_lt (by nlinarith) hm
  refine ⟨hi, ?_, by rw [ho]; decide, ?_⟩
  · rintro (hd | hd)
    · have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.out.one_lt) hd
      omega
    · exact (not_le_of_gt hlarge) (Nat.le_of_dvd (Nat.succ_pos _) hd)
  · rw [ho, ceilLogLifts]
    exact (Nat.lt_clog_iff_pow_lt hp.out.one_lt).2 hm

private lemma m_at_square (D : Data params) {n : ℕ} (hx : D.natX = n^2) :
    n ≤ D.m ∧ D.m ≤ 2*n := by
  have hs : exp (D.logX/2) = (n : ℝ) := by
    rw [exp_half, D.exp_logX, hx, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]
  have hm := D.m_mem
  rw [hs] at hm
  exact ⟨by exact_mod_cast hm.1, by exact_mod_cast hm.2⟩

private lemma x_le_secondary (D : Data params) : (D.natX : ℝ) ≤ D.x₁ := by
  rw [← D.exp_logX]
  have hpos : 0 < D.logX := by linarith [D.mul_log_logB_le_logX, D.constantBound_le, (le_constantBound (P := params)).1]
  exact exp_le_exp.2 (by linarith [D.logX_le_logX₁])

/-- Near the bottom of the order-three exceptional window even the full reciprocal sum
already fits the loss allowance. -/
theorem clearance_zero_at_square_window {p : ℕ} [hp : Fact p.Prime] (D : Data params)
    (ho : D.o₀ p = 3) (hx : D.natX = (p^2+1)^2) : D.collisionClearance p = 0 := by
  have hm : D.m ≤ 3*p^2 := by
    have hh := (m_at_square D hx).2
    have hh2 := hp.out.two_le
    nlinarith
  have hsum : D.collisionSum p ∅ ≤ 2*D.f*D.a/(p:ℝ)^3 := collisionSum_le fun hc ↦ by
    obtain ⟨_, he, hd⟩ := hc.ne_and_odd_and_dvd
    rw [ho] at hd
    exact Nat.le_of_dvd he.pos hd
  have hB : (6:ℝ) ≤ D.logB^2 := by
    have h : 3 ≤ D.logB := by
      have := Real.log_le_sub_one_of_pos (HasLogBound.pos D : 0 < D.logB)
      linarith [D.constantBound_le, (le_constantBound (P := params)).1]
    nlinarith [sq_nonneg (D.logB-3)]
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.out.pos
  have hpaid : D.m * D.collisionDeficit p ∅ ≤ D.loss p := calc
    D.m * D.collisionDeficit p ∅ ≤ D.m * (2*D.f*D.a/(p:ℝ)^3) := by
      gcongr
      exact (D.collisionDeficit_le_collisionSum ∅).trans hsum
    _ ≤ (3*(p:ℝ)^2) * (2*D.f*D.a/(p:ℝ)^3) := by gcongr; exact_mod_cast hm
    _ = 6*D.f*D.a/p := by field_simp; ring
    _ ≤ D.f*D.logB^2*(D.a/p) := by
      calc 6*D.f*D.a/(p:ℝ) = D.f*6*(D.a/p) := by ring
        _ ≤ _ := by gcongr
    _ ≤ D.loss p := D.le_loss p
  exact Nat.eq_zero_of_le_zero ((collisionClearance_le_iff 0).2 (by simpa using hpaid))

private lemma logB_le_prime_at_late_scale {p : ℕ} (D : Data params) (hx : D.natX = p^100) :
    D.logB ≤ (p : ℝ) := by
  have hB : 0 < D.logB := HasLogBound.pos D
  have hpow : D.logB^100 ≤ (p : ℝ)^100 := calc
    D.logB^100 = exp (100 * log D.logB) := by
      rw [show (100 : ℝ) = (100 : ℕ) by norm_num, exp_natCast_mul, exp_log hB]
    _ ≤ exp D.logX := exp_le_exp.2 D.mul_log_logB_le_logX
    _ = _ := by rw [D.exp_logX, hx, Nat.cast_pow]
  exact (pow_le_pow_iff_left₀ hB.le (Nat.cast_nonneg p) (by decide : 100 ≠ 0)).1 hpow

/-- At a second scale for the same prime, the first eligible term of the finite deficit
already exceeds the loss allowance. -/
theorem clearance_positive_at_late_scale {p : ℕ} [fact : Fact p.Prime] (D : Data params)
    (hlarge : 34319 < p) (hi : chiK params.d p = -1) (ho : D.o₀ p = 3)
    (hx : D.natX = p^100) : 0 < D.collisionClearance p := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast fact.out.pos
  have htwo : (2 : ℝ) ≤ p := by exact_mod_cast fact.out.two_le
  have hsq : D.natX = (p^50)^2 := by rw [hx]; ring
  have hm50 := (m_at_square D hsq).1
  have hm2 : p^2 < D.m := (Nat.pow_lt_pow_of_lt fact.out.one_lt (by decide : 2 < 50)).trans_le hm50
  have he := exceptional_of_cube D hi ho hm2
  have hB := logB_le_prime_at_late_scale D hx
  have hB0 : 0 < D.logB := HasLogBound.pos D
  have hφ : (params.q₀.totient : ℝ) ≤ 18480 := by exact_mod_cast Nat.totient_le params.q₀
  have hA : 0 < (#D.aPlaces : ℝ) := by exact_mod_cast (card_pos.2 ⟨1, by simp [aPlaces]⟩ : 0 < #D.aPlaces)
  have ha : 0 < (D.a : ℝ) := HasLogBound.pos D
  have hsize : 2*(p : ℝ)^3 ≤ D.x₁ := calc
    2*(p : ℝ)^3 ≤ (p : ℝ)^4 := by nlinarith only [mul_le_mul_of_nonneg_right htwo (pow_nonneg hp0.le 3)]
    _ ≤ (p : ℝ)^100 := pow_le_pow_right₀ (by linarith) (by decide : 4 ≤ 100)
    _ = D.natX := by rw [hx, Nat.cast_pow]
    _ ≤ _ := x_le_secondary D
  have hcut : (p : ℝ)^3 < D.x₁ := by linarith [pow_pos hp0 3]
  have hterm := first_active_term_le_deficit hi (by decide : Odd 3) (ho ▸ dvd_rfl) hcut
  have hC : (#D.aPlaces : ℝ) * (D.a/(2*(p:ℝ)^3)) ≤ D.collisionDeficit p ∅ := by
    refine le_trans ?_ hterm
    apply mul_le_mul_of_nonneg_left _ hA.le
    have hdiv := div_le_div_of_nonneg_left ha.le (by positivity : 0 < 2*(p:ℝ)^3) hsize
    have id : 2 * (D.a / (2*(p:ℝ)^3)) = D.a / (p:ℝ)^3 := by ring
    linarith
  have hloss : D.loss p ≤ (#D.aPlaces : ℝ) * D.a * (18480 * (p:ℝ)) := by
    rw [loss, ite_eq_right he.2.1, Nat.cast_one, mul_one, D.f_eq_card_aPlaces_mul, Nat.cast_mul]
    calc (#D.aPlaces : ℝ) * params.q₀.totient * D.logB^2 * (D.a/p) ≤
        #D.aPlaces * 18480 * (p:ℝ)^2 * (D.a/p) := by gcongr
      _ = _ := by field_simp
  have hnum : (2*18480 : ℝ) < (p:ℝ)^2 := by
    have hp' : (34319 : ℝ) < p := by exact_mod_cast hlarge
    nlinarith [sq_nonneg ((p:ℝ)-34319)]
  have hmag : 2*18480*(p:ℝ)^4 < D.m := calc
    2*18480*(p:ℝ)^4 < (p:ℝ)^2*p^4 := mul_lt_mul_of_pos_right hnum (pow_pos hp0 4)
    _ = (p:ℝ)^6 := by ring
    _ ≤ (p:ℝ)^50 := pow_le_pow_right₀ (by linarith) (by decide : 6 ≤ 50)
    _ ≤ _ := by exact_mod_cast hm50
  have hg : D.loss p < D.m * D.collisionDeficit p ∅ := calc
    D.loss p ≤ _ := hloss
    _ = ((#D.aPlaces : ℝ) * D.a * (2*18480*(p:ℝ)^4)) /(2*(p:ℝ)^3) := by field_simp
    _ < ((#D.aPlaces : ℝ) * D.a * D.m)/(2*(p:ℝ)^3) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hmag (mul_pos hA ha)) (by positivity)
    _ = D.m * ((#D.aPlaces : ℝ) * (D.a/(2*(p:ℝ)^3))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg D.m)
  by_contra! hclear
  have budget := (collisionClearance_le_iff (D := D) (p := p) 0).1 hclear
  exact hg.not_ge (by simpa using budget)

/-- The same arbitrarily large exceptional prime has zero clearance at one admissible scale
and positive clearance at another. -/
theorem unbounded_exception_switch (bound : ℕ) :
    ∃ p > bound, p.Prime ∧ ∃ D₀ D₁ : Data params,
      D₀.natX = (p^2+1)^2 ∧ D₁.natX = p^100 ∧ D₀.o₀ p = 3 ∧ D₁.o₀ p = 3 ∧
      D₀.IsSmallNonsplit p ∧ D₁.IsSmallNonsplit p ∧ D₀.IsExceptional p ∧ D₁.IsExceptional p ∧
      D₀.collisionClearance p = 0 ∧ 0 < D₁.collisionClearance p := by
  obtain ⟨x₀, hall⟩ := Filter.eventually_atTop.1 (New.eventually_exists_data params
    (ε := 1/200) (by norm_num) (by norm_num))
  obtain ⟨p, hgt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max bound (max x₀ 34319)) (q := 18480*9239) (a := 34319) (by decide) (by decide)
  have fact : Fact p.Prime := ⟨hp⟩
  have hL := (le_max_right bound (max x₀ 34319)).trans_lt hgt
  have hx₀ : x₀ < p := (le_max_left _ _).trans_lt hL
  have hpbig : 34319 < p := (le_max_right _ _).trans_lt hL
  have early : p < (p^2+1)^2 := by nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) p]
  have late : p < p^100 := by simpa using Nat.pow_lt_pow_of_lt hp.one_lt (by decide : 1 < 100)
  obtain ⟨D₀, h₀, _⟩ := hall ((p^2+1)^2) (hx₀.trans early).le
  obtain ⟨D₁, h₁, _⟩ := hall (p^100) (hx₀.trans late).le
  obtain ⟨hi, o₀⟩ := local_order_three hmod D₀
  have o₁ := (local_order_three hmod D₁).2
  have sm (D : Data params) (hx : p < D.natX) : D.IsSmallNonsplit p :=
    ⟨(show (p:ℝ) < D.natX by exact_mod_cast hx).trans_le (x_le_secondary D), by rw [hi]; norm_num⟩
  have m₀ := (m_at_square D₀ h₀).1
  have hs₁ : D₁.natX = (p^50)^2 := by rw [h₁]; ring
  have m₁ := (m_at_square D₁ hs₁).1
  have hpow : p^2 < p^50 := Nat.pow_lt_pow_of_lt hp.one_lt (by decide)
  exact ⟨p,(le_max_left _ _).trans_lt hgt,hp,D₀,D₁,h₀,h₁,o₀,o₁,sm D₀ (h₀ ▸ early),
    sm D₁ (h₁ ▸ late),exceptional_of_cube D₀ hi o₀ (by omega),exceptional_of_cube D₁ hi o₁ (hpow.trans_le m₁),
    clearance_zero_at_square_window D₀ o₀ h₀,clearance_positive_at_late_scale D₁ hpbig hi o₁ h₁⟩

end New.Data.CollisionPrimeExample
