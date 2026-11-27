module

public import New.Reduction.Zeros.Criterion
public import Lib.Analytic.QuadraticTwist
import TauCeti.Analysis.PSeries.Sparse
import Mathlib.Tactic

/-!
# Sampling the primes in the one-sided remainder criterion

The exceptional primes in a fixed zero rectangle obey a power-saving counting bound.
A set that exceeds this bound supplies a zero-free twist at each desired height.
A divergent sum of log p / p is sufficient. In particular, a single invertible
congruence subclass is sufficient, with the remainder measured at the original modulus.
-/

@[expose] public section

open MeasureTheory Nat Real Filter Asymptotics Finset Set Complex
open scoped Classical Nat Topology
namespace New.TwistSelection

/-- The number of the selected positive indices up to the integer cutoff. -/
noncomputable def count (S : Set ℕ) (X : ℕ) : ℝ :=
  ((Finset.Ioc 0 X).filter (· ∈ S)).card

/-- A pool growing faster along some cutoffs than the exceptional-set bound contains
a prime with no twisted zero in the indicated box. -/
theorem exists_clear_prime_of_count {q : ℕ} [NeZero q] {a : ZMod q} {β : ℝ} (hβ : 1/2 < β)
    (S : Set ℕ) (hS : ∀ n ∈ S, n.Prime ∧ (n : ZMod q) = a)
    (hadm : ∀ d : Primes, ((d : ℕ) : ZMod q) = a → (d : ℕ) % 8 = 7 ∧ q.Coprime d)
    (hsize : ¬ (count S =O[atTop] fun x : ℕ ↦ (x : ℝ) ^ (1 - (β - 1/2)/18)))
    (H : ℝ) : ∃ d : Primes, (d : ℕ) ∈ S ∧ ∀ (χ : DirichletCharacter ℂ q) (s : ℂ),
      β ≤ s.re → |s.im| ≤ H → entireL (quadTwist χ d) s ≠ 0 := by
  obtain ⟨δ, defβ⟩ : ∃ δ : ℝ, β = 1/2+9*δ := ⟨(β-1/2)/9, by ring⟩
  have hδ : 0 < δ := by linarith
  have bound := zero_density_quadTwist hδ H (a := a) fun n hn ↦ hadm ⟨n,hn⟩
  by_contra! failed
  have bad (n : ℕ) (hn : n ∈ S) : IsBadPrime a (1/2+9*δ) H n := by
    obtain ⟨hp,ha⟩ := hS n hn
    let d : Primes := ⟨n,hp⟩
    obtain ⟨χ,s,hre,him,hz⟩ := failed d hn
    obtain ⟨h8,hcop⟩ := hadm d ha
    have : Fact n.Prime := ⟨hp⟩
    change n%8=7 at h8
    change entireL (quadTwist χ n) s = 0 at hz
    rw [entireL,ite_eq_right (quadTwist_ne_one χ n (by omega) hcop)] at hz
    exact ⟨ha,χ,⟨s,defβ ▸ hre,him,hz⟩⟩
  apply hsize
  rw [show 1-(β-1/2)/18 = 1-δ/2 by rw [defβ];ring]
  refine .trans (.of_norm_le fun X ↦ ?_) bound
  simp only [count, Real.norm_natCast, Nat.cast_le]
  exact card_le_card (Finset.monotone_filter_right _ fun n _ hn ↦ bad n hn)

/-- On the half-plane only primes in the selected pool need remainder bounds. Each prime
has its own bound A and cutoff. The witness may depend on the height of the zero being tested. -/
theorem nonvanishing_of_selected_count {q : ℕ} [NeZero q] {a : ZMod q} {β : ℝ} (hβ : 1/2 < β)
    (S : Set ℕ) (hS : ∀ n ∈ S, n.Prime ∧ (n : ZMod q) = a)
    (hadm : ∀ d : Primes, ((d : ℕ) : ZMod q) = a → (d : ℕ) % 8 = 7 ∧ q.Coprime d)
    (hsize : ¬ (count S =O[atTop] fun x : ℕ ↦ (x : ℝ) ^ (1 - (β - 1/2)/18)))
    (hbound : ∀ d : Primes, (d : ℕ) ∈ S →
      ∃ A : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ A*x^(β-1))
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (h₁ : ρ ≠ 1) (hρ : β < ρ.re) : χ.LFunction ρ ≠ 0 := by
  obtain ⟨d,hd,clear⟩ := exists_clear_prime_of_count hβ S hS hadm hsize |ρ.im|
  obtain ⟨h8,hcop⟩ := hadm d (hS d hd).2
  obtain ⟨A,hA⟩ := hbound d hd
  have ht (s : ℂ) (hs : β ≤ s.re) (him : |s.im| ≤ |ρ.im|) :
      (∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL (quadTwist ψ d)) s) = 0 :=
    Finset.sum_eq_zero fun ψ _ ↦ (analyticOrderNatAt_entireL_eq_zero_iff _ s).2 (clear ψ s hs him)
  have eq := sum_entireL_orders_eq_twisted_of_primeRemainder_le h8 hcop (by linarith : 0<β) hA
    (fun x hx _ ↦ by rw [ht x hx.le (by simp)]; exact Nat.zero_le _) hρ
  rw [ht ρ hρ.le le_rfl] at eq
  exact (entireL_ne_zero_iff χ h₁).1 ((analyticOrderNatAt_entireL_eq_zero_iff _ ρ).1
    (Finset.sum_eq_zero_iff.1 eq χ (Finset.mem_univ χ)))


/-- Logarithmic weight on the positive integers. Its value at zero is zero. -/
noncomputable def weight (n : ℕ) : ℝ := Real.log n / n

/-- A divergent-weight pool exceeds every fixed sublinear power bound on its counting
function. The zero-free criterion below uses just one of these exponents. -/
theorem not_count_isBigO_of_divergent_weight {S : Set ℕ} (positive : ∀ n ∈ S, 0 < n)
    (diverges : ¬ Summable (weight ∘ (Subtype.val : S → ℕ))) {B : ℝ} (hB : B < 1) :
    ¬ (count S =O[atTop] fun x : ℕ ↦ (x : ℝ) ^ B) := by
  intro bound
  let E := max B 0
  have hE : E < 1 := max_lt hB zero_lt_one
  have hE₀ : 0 ≤ E := le_max_right _ _
  obtain ⟨C,hC,estimate⟩ := bound.exists_nonneg
  apply diverges
  apply S.summable_log_div_of_ncard_isBigO hE
  refine .of_bound C ?_
  filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually estimate.bound,
    eventually_ge_atTop (1 : ℝ)] with x hx hx₁
  have hx₀ := zero_le_one.trans hx₁
  have key : {d ∈ S | (d : ℝ) ≤ x} = (↑((Finset.Ioc 0 ⌊x⌋₊).filter (· ∈ S)) : Set ℕ) := by
    ext d
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨fun ⟨hd, le⟩ ↦ ⟨⟨positive _ hd, Nat.le_floor le⟩,hd⟩,
      fun ⟨⟨_, le⟩,hd⟩ ↦ ⟨hd,(Nat.le_floor_iff hx₀).1 le⟩⟩
  rw [key, Set.ncard_coe_finset]
  change ‖count S ⌊x⌋₊‖ ≤ C*‖x^E‖
  refine hx.trans (mul_le_mul_of_nonneg_left ?_ hC)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    abs_of_nonneg (Real.rpow_nonneg hx₀ _)]
  have hfloor : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.le_floor (by simpa using hx₁) : 1 ≤ ⌊x⌋₊)
  exact (Real.rpow_le_rpow_of_exponent_le hfloor (le_max_left B 0)).trans
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx₀) hE₀)

/-- Any set of auxiliary primes in the admissible class with divergent sum of log p / p
is sufficient. The character and its remainder are still measured at the original modulus. -/
theorem nonvanishing_of_divergent_weight {q : ℕ} [NeZero q] {a : ZMod q} {β : ℝ}
    (hβ : 1/2 < β) (S : Set ℕ) (hS : ∀ n ∈ S, n.Prime ∧ (n : ZMod q) = a)
    (hadm : ∀ d : Primes, ((d : ℕ) : ZMod q) = a → (d : ℕ) % 8 = 7 ∧ q.Coprime d)
    (hweight : ¬ Summable (weight ∘ (Subtype.val : S → ℕ)))
    (hbound : ∀ d : Primes, (d : ℕ) ∈ S →
      ∃ A : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ A*x^(β-1))
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (h₁ : ρ ≠ 1) (hρ : β < ρ.re) : χ.LFunction ρ ≠ 0 :=
  nonvanishing_of_selected_count hβ S hS hadm
    (not_count_isBigO_of_divergent_weight (fun n hn ↦ (hS n hn).1.pos) hweight (by linarith))
    hbound χ h₁ hρ

def primeClass {n : ℕ} (a : ZMod n) : Set ℕ := {p | p.Prime ∧ (p : ZMod n)=a}

/-- The prime weight diverges in each invertible congruence class. -/
theorem weight_diverges_primeClass {m : ℕ} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    ¬ Summable (weight ∘ (Subtype.val : primeClass a → ℕ)) := by
  intro h
  apply ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div ha
  apply (summable_subtype_iff_indicator.1 h).congr
  intro n
  by_cases hp : n.Prime <;> by_cases hc : (n : ZMod m)=a <;>
    simp [primeClass, Set.indicator, hp, hc, weight, ArithmeticFunction.vonMangoldt.residueClass,
      ArithmeticFunction.vonMangoldt_apply_prime]

/-- Restrict the auxiliary primes to one invertible class modulo an arbitrary multiple
m of q. The remainder and the conclusion still use q. -/
theorem nonvanishing_of_refined_class {q m a : ℕ} [NeZero q] [NeZero m] {β : ℝ}
    (hβ : 1/2 < β) (hqm : q ∣ m) (ha : a.Coprime m)
    (hadm : ∀ d : Primes, ((d : ℕ) : ZMod q) = a → (d : ℕ) % 8 = 7 ∧ q.Coprime d)
    (hbound : ∀ d : Primes, (d : ℕ) ≡ a [MOD m] →
      ∃ A : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ A*x^(β-1))
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (h₁ : ρ ≠ 1) (hρ : β < ρ.re) : χ.LFunction ρ ≠ 0 := by
  let S := primeClass (a : ZMod m)
  apply nonvanishing_of_divergent_weight hβ S (a := (a:ZMod q)) ?_ hadm
    (weight_diverges_primeClass ((ZMod.isUnit_iff_coprime a m).2 ha)) ?_ χ h₁ hρ
  · intro n hn
    exact ⟨hn.1,(ZMod.natCast_eq_natCast_iff n a q).2
      (((ZMod.natCast_eq_natCast_iff n a m).1 hn.2).of_dvd hqm)⟩
  · intro d hd
    exact hbound d ((ZMod.natCast_eq_natCast_iff d a m).1 hd.2)

/-- In the q = 18480 frame, one of the sixteen nonzero residue classes modulo seventeen
is sufficient. Each prime in the finer class is 9239 modulo 18480 and 1 modulo 17. -/
theorem one_class_mod_seventeen {β : ℝ} (hβ : 1/2 < β)
    (hbound : ∀ d : Primes, (d : ℕ) ≡ 194039 [MOD 314160] →
      ∃ A : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d 18480 x ≤ A*x^(β-1))
    (χ : DirichletCharacter ℂ 18480) {ρ : ℂ} (h₁ : ρ ≠ 1) (hρ : β < ρ.re) :
    χ.LFunction ρ ≠ 0 := by
  apply nonvanishing_of_refined_class hβ (by decide : 18480 ∣ 314160)
    (by decide : Nat.Coprime 194039 314160) ?_ hbound χ h₁ hρ
  intro d hd
  have hmod := (ZMod.natCast_eq_natCast_iff d 194039 18480).1 hd
  have h8 := hmod.of_dvd (by decide : 8 ∣ 18480)
  exact ⟨h8.trans (by decide : 194039 ≡ 7 [MOD 8]), Nat.Coprime.symm (hmod.gcd_eq.trans (by decide))⟩

end New.TwistSelection
