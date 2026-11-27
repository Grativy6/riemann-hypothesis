module

public import New.Reduction.Zeros.CutoffEntropyBounds
public import New.Reduction.Zeros.PrimePowerBends
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Reading the arithmetic support by sign alone

At three consecutive integers a positive mark exceeds the entire smooth
normalization charge whenever the totient of the modulus is at least four.
-/

@[expose] public section

open Real Finset ArithmeticFunction InformationTheory
open ArithmeticFunction.vonMangoldt
namespace New.PrimeCutoff

noncomputable def unitEntropy (t : ℝ) :=
  (klDiv (endpointLaw (1/2*((t-1)/t)) (1/2*((t+1)/t))) (endpointLaw (1/2) (1/2))).toReal

/-- The ordinary remainder at the middle, minus its reciprocal-weighted endpoint chord. -/
noncomputable def rawBend (d q : ℕ) [Fact d.Prime] [NeZero q] (t : ℝ) :=
  primeRemainder d q t - (1/2*((t-1)/t)*primeRemainder d q (t-1) +
    1/2*((t+1)/t)*primeRemainder d q (t+1))

theorem unit_entropy_bounds {t : ℝ} (ht : 1<t) : 0 < unitEntropy t ∧ unitEntropy t ≤ 1/t^2 := by
  have hpos : 0<t := by linarith
  have mix : (1/2:ℝ)*(t-1)+(1/2)*(t+1)=t := by ring
  have bound := relative_entropy_sandwich (a:=(1/2:ℝ)) (b:=(1/2:ℝ))
    (y:=t-1) (x:=t) (z:=t+1) (by linarith) (by norm_num) (by norm_num) (by norm_num) mix
    (by linarith) (by linarith)
  have delta : (t-(t-1))*(t+1-t)=1 := by ring
  change _ ≤ unitEntropy t ∧ unitEntropy t ≤ _ at bound
  rw [delta] at bound
  have entropy := entropy_of_chord (y:=t-1) (x:=t) (z:=t+1) (by linarith) (by linarith) hpos
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num) mix
  have upper := log_chord_drift (y:=t-1) (x:=t) (z:=t+1) (by linarith) (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num) mix (by linarith) (by linarith)
  rw [delta] at upper
  refine ⟨(by positivity : 0 < 1/(2*t*(t+1))).trans_le bound.1,?_⟩
  rw [unitEntropy,entropy.2.2]
  exact (div_le_div_of_nonneg_right upper hpos.le).trans_eq (by ring)

theorem unit_bend_eq {d q : ℕ} [Fact d.Prime] [NeZero q] (m : ℕ) (hm : 2≤m) :
    rawBend d q m = unitEntropy m / q.totient - lambdaKResidueClass d q m/(2*(m:ℝ)^2) := by
  let t : ℝ := m
  have one : 1<t := by change 1<(m:ℝ);exact_mod_cast hm
  have hy : 0<t-1 := by linarith
  have mix : (1/2:ℝ)*(t-1)+1/2*(t+1)=t := by ring
  have left : t-1≤t := by linarith
  have right : t≤t+1 := by linarith
  have eq := exact_chord_with_entropy (d:=d) (q:=q) hy (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num) mix left right
  rw [← integrated_chord_defect hy (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num) mix left right] at eq
  change rawBend d q t = unitEntropy t/q.totient - _ at eq
  rw [eq]
  congr 1
  rw [← second_difference (d:=d) (q:=q) m hm]
  change _ = t*(integrated d q (t-1)+integrated d q (t+1)-2*integrated d q t)/(2*t^2)
  field

lemma log_two_le_positive_weight {d q m : ℕ} [Fact d.Prime] (hm : 2≤m)
    (positive : 0 < lambdaKResidueClass d q m) : Real.log 2 ≤ lambdaKResidueClass d q m := by
  classical
  by_cases hc : (m:ZMod q)=1
  · by_cases hp : IsPrimePow m
    · have coeff : residueClass (1:ZMod q) m = Real.log m.minFac := by
        simp [residueClass,Set.indicator,hc,vonMangoldt_apply,hp]
      rw [lambdaKResidueClass,coeff] at positive ⊢
      have mark : (1:ℤ) ≤ 1-chiK d m := by
        by_contra! h
        have z : (1:ℤ)-chiK d m ≤ 0 := by omega
        have zz : (1:ℝ)-(chiK d m:ℝ)≤0 := by exact_mod_cast z
        exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (Real.log_natCast_nonneg _) zz)) positive
      have first : (2:ℝ) ≤ m.minFac := by exact_mod_cast (Nat.minFac_prime (by omega : m≠1)).two_le
      exact (Real.log_le_log (by norm_num) first).trans (le_mul_of_one_le_right
        (Real.log_natCast_nonneg _) (by exact_mod_cast mark))
    · simp [lambdaKResidueClass,residueClass,Set.indicator,hc,vonMangoldt_apply,hp] at positive
  · simp [lambdaKResidueClass,residueClass,Set.indicator,hc] at positive

/-- If the modulus has at least four reduced residues, the sign of the raw reading
alone distinguishes every zero weight from every positive arithmetic mark. -/
theorem sign_recovers_support {d q : ℕ} [Fact d.Prime] [NeZero q] (hq : 4≤q.totient)
    (m : ℕ) (hm : 2≤m) :
    (0 < rawBend d q m ↔ lambdaKResidueClass d q m=0) ∧
      (rawBend d q m < 0 ↔ 0 < lambdaKResidueClass d q m) := by
  have mt : (1:ℝ)<m := by exact_mod_cast hm
  have mp : (0:ℝ)<m := by linarith
  have qp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  obtain ⟨jp,ju⟩ := unit_entropy_bounds mt
  rw [unit_bend_eq m hm]
  by_cases zero : lambdaKResidueClass d q m=0
  · simp [zero,div_pos jp qp,(div_pos jp qp).not_gt]
  · have positive := (lambdaKResidueClass_nonneg d q m).lt_of_ne' zero
    have much : (1/2:ℝ) < lambdaKResidueClass d q m :=
      (show (1/2:ℝ)<Real.log 2 by linarith [Real.log_two_gt_d9]).trans_le
        (log_two_le_positive_weight hm positive)
    have lt : unitEntropy m / q.totient < lambdaKResidueClass d q m/(2*(m:ℝ)^2) := calc
      _ ≤ (1/(m:ℝ)^2)/4 := div_le_div₀ (by positivity) ju (by norm_num) (by exact_mod_cast hq)
      _ = (1/2)/(2*(m:ℝ)^2) := by ring
      _ < _ := div_lt_div_of_pos_right much (by positivity)
    simp [zero,positive,sub_neg.2 lt,(sub_neg.2 lt).not_gt]

end New.PrimeCutoff
