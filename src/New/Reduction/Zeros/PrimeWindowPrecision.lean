module

public import New.Reduction.Zeros.PrimeWindowRecovery
public import New.Reduction.Zeros.PrimeNumberTheorem
import Mathlib.Tactic

/-!
# Arithmetic precision of the two-cutoff reading

The prime-factor support alone recovers the prefix. Fixed distinct auxiliary primes
can have strictly different readings with an arbitrarily small absolute gap.
-/

@[expose] public section

open Nat Real Set Finset ArithmeticFunction
open ArithmeticFunction.vonMangoldt
namespace New.PrimeWindow

/-- For consecutive cutoffs there is no factorial scale: the corrected difference
is the ordinary cumulative count divided by N(N+1). -/
theorem adjacent_reading {d q N : ℕ} [Fact d.Prime] [NeZero q] (hN : 1≤N) :
    ((N:ℝ)*((N:ℝ)+1)) * (primeRemainder d q ((N:ℝ)+1)-primeRemainder d q N+
      Real.log (((N:ℝ)+1)/N)/q.totient) = ∑ n ∈ Finset.Icc 1 N, lambdaKResidueClass d q n := by
  have eq := increment_eq_window (d:=d) (q:=q) hN (Nat.lt_succ_self N)
  simp only [Nat.cast_add_one] at eq
  rw [eq]
  have sub : Finset.Icc 1 N ⊆ Finset.Icc 1 (N+1) := Finset.Icc_subset_Icc_right (Nat.le_succ N)
  rw [← Finset.sum_subset sub (fun n hn no ↦ by
    have nb : n=N+1 := by
      have mem := Finset.mem_Icc.1 hn
      by_contra! bad
      exact no (Finset.mem_Icc.2 ⟨mem.1,by omega⟩)
    subst n;simp)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [max_eq_left (Finset.mem_Icc.1 hn).2]
  have np : 0<(N:ℝ) := by exact_mod_cast hN
  field

noncomputable def countCode (d q N : ℕ) [Fact d.Prime] : ℕ :=
  ∏ n ∈ Finset.Icc 1 N, n.minFac ^ digit d q n

theorem log_countCode {d q N : ℕ} [Fact d.Prime] :
    Real.log (countCode d q N) = ∑ n ∈ Finset.Icc 1 N, lambdaKResidueClass d q n := by
  rw [countCode,Nat.cast_prod,Real.log_prod (fun n _ ↦ by positivity [Nat.minFac_pos n])]
  exact Finset.sum_congr rfl fun n _ ↦ by simp [weight_digit,Nat.cast_pow,Real.log_pow]

/-- Distinct fixed auxiliary primes leave exact distinct readings indefinitely
once a ramified square is visible. Their gap can nevertheless be below 12/(N+1). -/
theorem distinct_adjacent_within {d r q N : ℕ} [Fact d.Prime] [Fact r.Prime] [NeZero q]
    (hq : 8∣q) (hd : d%8=7) (hr : r%8=7) (diff : d≠r) (sq : (d:ZMod q)^2=1)
    (hN : 1≤N) (enough : d^2≤N) :
    let gap := |(primeRemainder d q ((N:ℝ)+1)-primeRemainder d q N) -
      (primeRemainder r q ((N:ℝ)+1)-primeRemainder r q N)|
    0<gap ∧ gap ≤ 12/((N:ℝ)+1) := by
  dsimp only
  have np : (0:ℝ)<N := by exact_mod_cast hN
  let L (v : ℕ) [Fact v.Prime] := ∑ n ∈ Finset.Icc 1 N, lambdaKResidueClass v q n
  have nonneg (v : ℕ) [Fact v.Prime] : 0≤@L v _ :=
    Finset.sum_nonneg fun n _ ↦ lambdaKResidueClass_nonneg v q n
  have cap (v : ℕ) [Fact v.Prime] : @L v _ ≤ 12*(N:ℝ) := by
    have cheb := sum_Icc_vonMangoldt_le_six_mul (z:=(N:ℝ)) np.le
    rw [Nat.floor_natCast] at cheb
    calc L v ≤ ∑ n ∈ Finset.Icc 1 N, 2*vonMangoldt n :=
          Finset.sum_le_sum fun n _ ↦ lambdaKResidueClass_le_two_mul_vonMangoldt (d:=v) (q:=q) n
      _ ≤ ∑ n ∈ Finset.Icc 0 N, 2*vonMangoldt n := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_left (by decide)) (fun n _ _ ↦ mul_nonneg (by norm_num) vonMangoldt_nonneg)
      _ = 2*∑ n ∈ Finset.Icc 0 N, vonMangoldt n := (Finset.mul_sum ..).symm
      _ ≤ _ := by linarith only [cheb]
  constructor
  · apply abs_pos.2
    intro zero
    apply diff
    exact identify_auxiliary (q:=q) (a:=N) (b:=N+1) hq hd hr hN (by omega) sq (by omega)
      (by simpa using sub_eq_zero.1 zero)
  · have left := adjacent_reading (d:=d) (q:=q) hN
    have right := adjacent_reading (d:=r) (q:=q) hN
    let delta := (primeRemainder d q ((N:ℝ)+1)-primeRemainder d q N) -
      (primeRemainder r q ((N:ℝ)+1)-primeRemainder r q N)
    have exact_gap : (N:ℝ)*((N:ℝ)+1)*delta = L d - L r := by
      dsimp [delta,L];linear_combination left-right
    have bounded : |L d - L r| ≤ 12*(N:ℝ) := abs_le.2
      ⟨by linarith only [cap r,nonneg d],by linarith only [cap d,nonneg r]⟩
    rw [←exact_gap,abs_mul,abs_of_pos (by positivity : 0<(N:ℝ)*((N:ℝ)+1))] at bounded
    change |delta| ≤ 12/((N:ℝ)+1)
    rw [le_div_iff₀ (by positivity)]
    apply le_of_mul_le_mul_left (a:=(N:ℝ)) _ np
    linarith only [bounded]


/-- The radical of the integer certificate already determines the prefix. -/
theorem factors_eq_iff_prefix_eq {d r q a b : ℕ} [Fact d.Prime] [Fact r.Prime] [NeZero q]
    (hq : 8∣q) (hd : d%8=7) (hr : r%8=7) (ha : 1≤a) (hab : a<b) :
    (code d q a b).primeFactors = (code r q a b).primeFactors ↔
      ∀ n : ℕ, n<b → lambdaKResidueClass d q n=lambdaKResidueClass r q n := by
  classical
  constructor
  · intro same n below
    by_cases power : IsPrimePow n
    · obtain ⟨p,j,hp,hj,rfl⟩ := (isPrimePow_nat_iff n).1 power
      have factors := Finset.ext_iff.1 same p
      have observed : p∣code d q a b ↔ p∣code r q a b := by
        simpa [Nat.mem_primeFactors,hp,(code_pos d q a b).ne',(code_pos r q a b).ne'] using factors
      rw [recover_power hq hd ha hab hp hj below,recover_power hq hr ha hab hp hj below]
      by_cases present : p∣code d q a b
      · simp [present,observed.1 present]
      · simp [present,mt observed.2 present]
    · simp [lambdaKResidueClass,residueClass,Set.indicator,vonMangoldt_apply,power]
  · intro records
    exact congrArg Nat.primeFactors ((code_eq_iff_reading_eq ha hab).2
      ((increment_eq_iff_prefix_eq hq hd hr ha hab).2 records))

lemma log_integer_separation {u v : ℕ} (hu : 0<u) (hv : 0<v) (different : u≠v) :
    1/((max u v:ℕ):ℝ) ≤ |Real.log (u:ℝ) - Real.log (v:ℝ)| := by
  wlog small : u<v generalizing u v
  · rw [max_comm,abs_sub_comm]
    exact this hv hu different.symm (by omega)
  have up : (0:ℝ)<u := by exact_mod_cast hu
  have vp : (0:ℝ)<v := by exact_mod_cast hv
  have h := Real.log_le_sub_one_of_pos (div_pos up vp)
  rw [Real.log_div up.ne' vp.ne'] at h
  rw [max_eq_right small.le,abs_of_nonpos (sub_nonpos.2 (Real.log_le_log up (by exact_mod_cast small.le)))]
  have step : (u:ℝ)+1≤v := by exact_mod_cast (show u+1≤v by omega)
  have le : 1/(v:ℝ)≤1-u/v := by
    apply (le_sub_iff_add_le).2
    rw [←add_div]
    exact (div_le_one vp).2 (by linarith)
  linarith only [le,h]

/-- A certified but potentially tiny separation when two exact window integers differ. -/
theorem window_precision_floor {d r q a b : ℕ} [Fact d.Prime] [Fact r.Prime] [NeZero q]
    (ha : 1≤a) (hab : a<b) (different : code d q a b≠code r q a b) :
    1/((b !:ℝ)^2*max (code d q a b : ℝ) (code r q a b : ℝ)) ≤
    |(primeRemainder d q b-primeRemainder d q a)-(primeRemainder r q b-primeRemainder r q a)| := by
  have coarse := log_integer_separation (code_pos d q a b) (code_pos r q a b) different
  rw [log_code ha hab, log_code ha hab, ←mul_sub, add_sub_add_right_eq_sub, abs_mul,
    abs_of_nonneg (sq_nonneg _)] at coarse
  have pos : 0< (b !:ℝ)^2 := by positivity
  rw [Nat.cast_max] at coarse
  calc 1/((b !:ℝ)^2*max (code d q a b : ℝ) (code r q a b : ℝ)) =
        (1/max (code d q a b : ℝ) (code r q a b : ℝ))/(b !:ℝ)^2 := by ring
    _ ≤ _ := (div_le_iff₀ pos).2 (by simpa only [mul_comm] using coarse)

end New.PrimeWindow
