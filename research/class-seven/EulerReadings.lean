import Lib.Analytic.EntireLFunction
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Associated

open Nat Finset Complex Filter DirichletCharacter New
open scoped Topology Classical
noncomputable section
namespace Hearthline.EulerReadings

def factor (c : ℂ) (p : ℕ) (s : ℂ) : ℂ := 1 - c * (p : ℂ) ^ (-s)

private theorem analytic_factor (c : ℂ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    AnalyticAt ℂ (factor c p) s := by
  have nz : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold factor
  simp_rw [Complex.cpow_def_of_ne_zero nz]
  fun_prop

private theorem analytic_product (a : ℕ → ℂ) (T : Finset ℕ) (primes : ∀ p ∈ T, p.Prime) (s : ℂ) :
    AnalyticAt ℂ (fun z ↦ ∏ p ∈ T, factor (a p) p z) s := by
  apply Finset.analyticAt_fun_prod
  intro p hp
  exact analytic_factor _ (primes p hp) s

/-- Every finite Euler factor that vanishes has a simple zero, with derivative log p. -/
theorem order_factor (c : ℂ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    analyticOrderAt (factor c p) s = if c * (p : ℂ) ^ (-s) = 1 then 1 else 0 := by
  have analytic := analytic_factor c hp s
  split_ifs with hit
  · have nz : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have dx : HasDerivAt (fun z : ℂ ↦ 1 - c * (p : ℂ) ^ (-z))
        (0 - c * ((p : ℂ)^(-s) * Complex.log p * (-1))) s :=
      (hasDerivAt_const s (1 : ℂ)).sub
        (((hasDerivAt_id s).neg.const_cpow (c := (p : ℂ)) (Or.inl nz)).const_mul c)
    have value : 0 - c * ((p : ℂ)^(-s) * Complex.log p * (-1)) = Complex.log p := by
      linear_combination (Complex.log (p : ℂ)) * hit
    have df : HasDerivAt (factor c p) (Complex.log (p : ℂ)) s := value ▸ dx
    apply analytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    · simp [factor, hit]
    · rw [df.deriv]
      have pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
      exact_mod_cast (show (Real.log (p : ℝ) : ℂ) ≠ 0 by exact_mod_cast pos.ne')
  · exact analytic.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 (Ne.symm hit))

private theorem order_product (a : ℕ → ℂ) (T : Finset ℕ) (primes : ∀ p ∈ T, p.Prime) (s : ℂ) :
    analyticOrderAt (fun z ↦ ∏ p ∈ T, factor (a p) p z) s =
      ((T.filter (fun p ↦ a p * (p : ℂ) ^ (-s) = 1)).card : ℕ∞) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T missing ih =>
    have hp := primes p (mem_insert_self p T)
    have ht (l : ℕ) (hl : l ∈ T) := primes l (mem_insert_of_mem hl)
    have eq : (fun z ↦ ∏ l ∈ insert p T, factor (a l) l z) =
      factor (a p) p * (fun z ↦ ∏ l ∈ T, factor (a l) l z) := by
      funext z
      simp [Finset.prod_insert missing]
    rw [eq, analyticOrderAt_mul (analytic_factor _ hp _) (analytic_product a T ht s),
      order_factor _ hp s, ih ht]
    by_cases h : a p * (p : ℂ) ^ (-s) = 1 <;> simp [Finset.filter_insert, h, missing, add_comm]

private theorem entire_away {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    entireL χ s = (if χ = 1 then s - 1 else 1) * χ.LFunction s := by
  by_cases h : χ = 1
  · subst χ
    simp [entireL, LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar]
  · simp [entireL, h]

/-- The finite product also transports the regularized value at the pole. -/
theorem entire_changeLevel {N L : ℕ} [NeZero N] [NeZero L] (χ : DirichletCharacter ℂ N) (h : N ∣ L) :
    entireL (χ.changeLevel h) =
      entireL χ * (fun s ↦ ∏ p ∈ L.primeFactors, factor (χ p) p s) := by
  have same : χ.changeLevel h = 1 ↔ χ = 1 := by
    rw [← map_one (changeLevel h : DirichletCharacter ℂ N →* DirichletCharacter ℂ L)]
    exact (changeLevel_injective h).eq_iff
  apply Continuous.ext_on (dense_compl_singleton (1 : ℂ))
  · exact continuous_iff_continuousAt.2 fun s ↦ (analyticAt_entireL _ s).continuousAt
  · apply Continuous.mul
    · exact continuous_iff_continuousAt.2 fun s ↦ (analyticAt_entireL _ s).continuousAt
    · exact continuous_iff_continuousAt.2 fun s ↦
        (analytic_product _ L.primeFactors (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp) s).continuousAt
  · intro s hs
    change s ≠ 1 at hs
    change entireL (χ.changeLevel h) s = entireL χ s * _
    rw [entire_away _ hs, entire_away _ hs, LFunction_changeLevel h χ (.inr hs)]
    simp only [same, factor, mul_assoc]

/-- The exact number of extra zeros at any point, with multiplicity. -/
theorem order_changeLevel {N L : ℕ} [NeZero N] [NeZero L] (χ : DirichletCharacter ℂ N)
    (h : N ∣ L) (s : ℂ) :
    analyticOrderNatAt (entireL (χ.changeLevel h)) s = analyticOrderNatAt (entireL χ) s +
      (L.primeFactors.filter (fun p : ℕ ↦ χ p * (p : ℂ) ^ (-s) = 1)).card := by
  have hp (p : ℕ) (mem : p ∈ L.primeFactors) := Nat.prime_of_mem_primeFactors mem
  apply Nat.cast_injective (R := ℕ∞)
  rw [Nat.cast_add, Nat.cast_analyticOrderNatAt (analyticOrderAt_entireL_ne_top _ s),
    Nat.cast_analyticOrderNatAt (analyticOrderAt_entireL_ne_top _ s), entire_changeLevel χ h,
    analyticOrderAt_mul (analyticAt_entireL _ s) (analytic_product _ _ hp s),
    order_product _ _ hp s]

/-- Lifting the classical trivial character from level one counts the distinct erased primes at zero. -/
theorem at_zero (L : ℕ) [NeZero L] :
    analyticOrderNatAt (entireL (1 : DirichletCharacter ℂ L)) 0 = L.primeFactors.card := by
  have low : analyticOrderNatAt (entireL (1 : DirichletCharacter ℂ 1)) 0 = 0 := by
    apply (analyticOrderNatAt_entireL_eq_zero_iff _ 0).2
    apply (entireL_ne_zero_iff _ (by norm_num : (0 : ℂ) ≠ 1)).2
    rw [LFunction_modOne_eq, riemannZeta_zero]
    norm_num
  have eq := order_changeLevel (1 : DirichletCharacter ℂ 1) (Nat.one_dvd L) 0
  simpa [low, MulChar.one_apply (isUnit_of_subsingleton _)] using eq


/-- An Euler factor can change an order only on the imaginary axis. This includes the negative
real-part side of the comparison. -/
theorem hit_forces_re_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hit : χ p * (p : ℂ)^(-s) = 1) : s.re = 0 := by
  by_cases u : IsUnit (p : ZMod N)
  · have normχ : ‖χ p‖ = 1 := by simpa only [u.unit_spec] using χ.unit_norm_eq_one u.unit
    have positive : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have bigger : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have n := congrArg norm hit
    rw [norm_mul, normχ, one_mul, norm_one] at n
    have power : (p : ℝ)^(-s.re) = 1 := by
      simpa only [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos positive,
        Complex.neg_re] using n
    rcases lt_trichotomy s.re 0 with neg | eq | pos
    · exact False.elim ((Real.one_lt_rpow bigger (neg_pos.2 neg)).ne' power)
    · exact eq
    · exact False.elim ((Real.rpow_lt_one_of_one_lt_of_neg bigger (neg_lt_zero.2 pos)).ne power)
  · rw [MulChar.map_nonunit _ u, zero_mul] at hit
    exact (zero_ne_one hit).elim

theorem same_order_off_axis {N L : ℕ} [NeZero N] [NeZero L] (χ : DirichletCharacter ℂ N)
    (h : N ∣ L) {s : ℂ} (off : s.re ≠ 0) :
    analyticOrderNatAt (entireL (χ.changeLevel h)) s = analyticOrderNatAt (entireL χ) s := by
  rw [order_changeLevel]
  have empty : L.primeFactors.filter (fun p : ℕ ↦ χ p * (p : ℂ)^(-s) = 1) = ∅ := by
    ext p
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    exact fun h ↦ off (hit_forces_re_zero χ (Nat.prime_of_mem_primeFactors h.1) h.2)
  simp [empty]

/-- Genuine loss of the converse at zero, at the first single erased prime. -/
theorem levels_one_and_two_at_zero :
    entireL (1 : DirichletCharacter ℂ 1) 0 = 1 / 2 ∧
      entireL (1 : DirichletCharacter ℂ 2) 0 = 0 ∧
      analyticOrderNatAt (entireL (1 : DirichletCharacter ℂ 2)) 0 = 1 := by
  constructor
  · rw [entire_away _ (by norm_num), LFunction_modOne_eq, riemannZeta_zero]
    norm_num
  · have order := at_zero 2
    rw [show (2 : ℕ).primeFactors.card = 1 by decide +kernel] at order
    exact ⟨by
      by_contra h
      have none := (analyticOrderNatAt_entireL_eq_zero_iff (1 : DirichletCharacter ℂ 2) 0).2 h
      omega, order⟩

end Hearthline.EulerReadings

/-!
# Recovering the erased prime support at the pole

The arithmetic uniqueness argument is due in particular to P. Erdős, F. Luca and C. Pomerance,
"On the proportion of numbers coprime to a given integer", §2, proof of Lemma 1 and Algorithm A.
Here it is applied to the unmodified community definition of the entire principal L-function.
-/

open Finset Nat Complex DirichletCharacter New
open scoped Classical
noncomputable section
namespace Hearthline.SupportReading

def readSupport (S : Finset ℕ) : ℚ := ∏ p ∈ S, ((p-1 : ℕ) : ℚ) / (p : ℚ)

private theorem quotient_form (S : Finset ℕ) :
    readSupport S = ((∏ p ∈ S, (p-1)) : ℕ) / (↑(∏ p ∈ S, p : ℕ) : ℚ) := by
  simp only [readSupport, prod_div_distrib, Nat.cast_prod]

/-- A largest prime in the first support survives reduction of the fraction and must be present
in every second support with the same reading. -/
private theorem largest_present {S T : Finset ℕ} (primeS : ∀ p ∈ S, p.Prime)
    (primeT : ∀ p ∈ T, p.Prime) {p : ℕ} (hit : p ∈ S) (top : ∀ q ∈ S, q ≤ p)
    (eq : readSupport S = readSupport T) : p ∈ T := by
  have hp := primeS p hit
  have den (A : Finset ℕ) (pr : ∀ z ∈ A, z.Prime) : (∏ x ∈ A, x) ≠ 0 :=
    prod_ne_zero_iff.2 fun x hx ↦ (pr x hx).ne_zero
  rw [quotient_form, quotient_form, div_eq_div_iff (by exact_mod_cast den S primeS)
    (by exact_mod_cast den T primeT)] at eq
  have cross : (∏ q ∈ S, (q-1)) * (∏ q ∈ T, q) = (∏ q ∈ T, (q-1)) * ∏ q ∈ S, q := by
    exact_mod_cast eq
  have div : p ∣ (∏ q ∈ S, (q-1)) * ∏ q ∈ T, q := by
    rw [cross]
    exact (Finset.dvd_prod_of_mem id hit).trans (dvd_mul_left _ _)
  rcases hp.dvd_mul.1 div with num | denom
  · obtain ⟨q, hq, small⟩ := (hp.prime.dvd_finsetProd_iff _).1 num
    have lo := (primeS q hq).one_lt
    have hi := top q hq
    exact False.elim (Nat.not_dvd_of_pos_of_lt (by omega : 0 < q-1) (by omega : q-1 < p) small)
  · obtain ⟨q, hq, pq⟩ := (hp.prime.dvd_finsetProd_iff _).1 denom
    exact ((Nat.prime_dvd_prime_iff_eq hp (primeT q hq)).1 pq) ▸ hq

/-- Equality of the exact rational reading is equivalent to equality of finite prime supports. -/
theorem readSupport_injective {S T : Finset ℕ} (hs : ∀ p ∈ S, p.Prime) (ht : ∀ p ∈ T, p.Prime)
    (eq : readSupport S = readSupport T) : S = T := by
  induction S using Finset.strongInductionOn generalizing T with
  | _ S ih =>
    by_cases live : S.Nonempty
    · let p := S.max' live
      have sMem : p ∈ S := Finset.max'_mem S live
      have tMem : p ∈ T := largest_present hs ht sMem (fun q hq ↦ S.le_max' q hq) eq
      have nonzero : ((p-1 : ℕ) : ℚ) / p ≠ 0 := div_ne_zero
        (by exact_mod_cast (show p-1 ≠ 0 by have := (hs p sMem).one_lt; omega))
        (by exact_mod_cast (hs p sMem).ne_zero)
      have smaller : readSupport (S.erase p) = readSupport (T.erase p) := by
        apply mul_left_cancel₀ nonzero
        exact (S.mul_prod_erase (fun x : ℕ ↦ ((x-1 : ℕ) : ℚ) / x) sMem).trans
          (eq.trans (T.mul_prod_erase (fun x : ℕ ↦ ((x-1 : ℕ) : ℚ) / x) tMem).symm)
      have same := ih (S.erase p) (Finset.erase_ssubset sMem)
        (fun q hq ↦ hs q (Finset.mem_of_mem_erase hq)) (fun q hq ↦ ht q (Finset.mem_of_mem_erase hq)) smaller
      exact (Finset.insert_erase sMem).symm.trans <| (congrArg (insert p) same).trans (Finset.insert_erase tMem)
    · by_cases other : T.Nonempty
      · have mem := largest_present ht hs (T.max'_mem other) (fun q hq ↦ T.le_max' q hq) eq.symm
        exact False.elim (live ⟨_, mem⟩)
      · simp [Finset.not_nonempty_iff_eq_empty.1 live, Finset.not_nonempty_iff_eq_empty.1 other]

/-- The regularized principal L-function's value at one is the exact rational Euler reading. -/
theorem entire_one (N : ℕ) [NeZero N] :
    entireL (1 : DirichletCharacter ℂ N) 1 = (readSupport N.primeFactors : ℂ) := by
  simp only [entireL, ite_true, LFunctionTrivChar₁, Function.update_self,
    readSupport, Rat.cast_prod, Rat.cast_div, Rat.cast_natCast]
  apply Finset.prod_congr rfl
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have p0 : (p : ℂ) ≠ 0 := by exact_mod_cast pp.ne_zero
  rw [Nat.cast_sub (by exact pp.one_lt.le), Nat.cast_one]
  field_simp

theorem same_pole_iff {M N : ℕ} [NeZero M] [NeZero N] :
    entireL (1 : DirichletCharacter ℂ M) 1 = entireL (1 : DirichletCharacter ℂ N) 1 ↔
      M.primeFactors = N.primeFactors := by
  rw [entire_one, entire_one, Rat.cast_inj]
  exact ⟨readSupport_injective (fun _ h ↦ Nat.prime_of_mem_primeFactors h)
    (fun _ h ↦ Nat.prime_of_mem_primeFactors h), fun h ↦ congrArg readSupport h⟩


/-- The principal function at every complex point is determined by, and determines, the
same finite prime support already readable at the regularized pole. -/
theorem same_function_iff {M N : ℕ} [NeZero M] [NeZero N] :
    entireL (1 : DirichletCharacter ℂ M) = entireL (1 : DirichletCharacter ℂ N) ↔
      M.primeFactors = N.primeFactors := by
  have product (L : ℕ) [NeZero L] : entireL (1 : DirichletCharacter ℂ L) =
      entireL (1 : DirichletCharacter ℂ 1) *
        (fun z ↦ ∏ p ∈ L.primeFactors, Hearthline.EulerReadings.factor 1 p z) := by
    simpa only [map_one, MulChar.one_apply (isUnit_of_subsingleton _)] using
      Hearthline.EulerReadings.entire_changeLevel (1 : DirichletCharacter ℂ 1) (Nat.one_dvd L)
  constructor
  · intro eq
    exact same_pole_iff.1 (congrFun eq 1)
  · intro same
    rw [product M, product N, same]

theorem totient_reading (N : ℕ) [NeZero N] :
    readSupport N.primeFactors = (N.totient : ℚ) / N := by
  rw [eq_div_iff (by exact_mod_cast NeZero.ne N : (N : ℚ) ≠ 0), Nat.totient_eq_mul_prod_factors]
  rw [mul_comm]
  congr 1
  unfold readSupport
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have prime := Nat.prime_of_mem_primeFactors hp
  rw [Nat.cast_sub prime.one_lt.le, Nat.cast_one]
  have pn : (p : ℚ) ≠ 0 := by exact_mod_cast prime.ne_zero
  field_simp

example : [readSupport {2,3,7,43}, readSupport {2,3,7}, readSupport {2,3},
    readSupport {2}, readSupport ∅] = [12/43, 2/7, 1/3, 1/2, 1] := by decide +kernel

example : entireL (1 : DirichletCharacter ℂ 6) = entireL (1 : DirichletCharacter ℂ 12) := by
  apply same_function_iff.2
  decide +kernel

example : analyticOrderNatAt (entireL (1 : DirichletCharacter ℂ 1806)) 0 = 4 ∧
    entireL (1 : DirichletCharacter ℂ 1806) 1 = 12 / 43 := by
  constructor
  · rw [Hearthline.EulerReadings.at_zero]
    decide +kernel
  · rw [entire_one, show (1806:ℕ).primeFactors = {2,3,7,43} by decide +kernel,
      show readSupport {2,3,7,43} = 12/43 by decide +kernel]
    norm_num

end Hearthline.SupportReading
