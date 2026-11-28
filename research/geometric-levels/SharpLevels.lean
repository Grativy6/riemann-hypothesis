import New.Reduction.Data.PrimeConditions
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

open Nat Finset ZMod NumberTheorySymbols
namespace Hearthline.GeometricLevel

/-- A divisor witnessing the half-turn exists exactly when the level contains the first
power of two missing from u. Odd factors and their multiplicities play no part in this test. -/
theorem separation_iff {q u : ℕ} (hu : u ≠ 0) :
    (∃ m : ℕ, m ∣ q ∧ m ∣ 2 * u ∧ ¬m ∣ u) ↔ 2 ^ (u.factorization 2 + 1) ∣ q := by
  have twice : 2 ^ (u.factorization 2 + 1) ∣ 2 * u := by
    rw [pow_succ']
    exact Nat.mul_dvd_mul_left 2 (Nat.ordProj_dvd u 2)
  constructor
  · rintro ⟨m, hmq, ⟨k, hk⟩, hmu⟩
    have odd : Odd k := by
      rcases Nat.even_or_odd k with ⟨a, ha⟩ | ho
      · exfalso
        apply hmu
        refine ⟨a, ?_⟩
        rw [ha, Nat.mul_add] at hk
        omega
      · exact ho
    have cop : Nat.Coprime (2 ^ (u.factorization 2 + 1)) k := odd.coprime_two_left.pow_left _
    exact (cop.dvd_of_dvd_mul_right (hk ▸ twice)).trans hmq
  · intro h
    refine ⟨_, h, twice, fun more ↦ ?_⟩
    have le := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hu).1 more
    omega

/-- If the two-part of q divides d+1 and each prime of q divides d+1, the odd part of q
itself is a positive exponent taking d back to -1 modulo q. -/
theorem odd_part_returns {q d : ℕ} (hq : q ≠ 0)
    (support : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ d + 1)
    (two : ordProj[2] q ∣ d + 1) : q ∣ d ^ ordCompl[2] q + 1 := by
  let v := ordCompl[2] q
  have hv : Odd v := Nat.not_even_iff_odd.1 fun even ↦
    Nat.not_dvd_ordCompl Nat.prime_two hq (even_iff_two_dvd.1 even)
  have hvdiv : v ∣ q := Nat.ordCompl_dvd q 2
  have oddPart : v ∣ d ^ v + 1 := by
    refine (Nat.factorization_le_iff_dvd hv.pos.ne' (Nat.succ_ne_zero _)).1 ?_
    intro p
    by_cases hp : p.Prime
    · by_cases h : p ∣ v
      · have hadd := support p hp (h.trans hvdiv)
        have h2 : p ≠ 2 := fun eq ↦ hv.not_two_dvd_nat (eq ▸ h)
        have hpd : ¬p ∣ d := fun hd ↦ hp.not_dvd_one (by simpa using Nat.dvd_sub hadd hd)
        let : Fact p.Prime := ⟨hp⟩
        have valuation := Nat.multiplicity_pow_add_pow (p := p) (x := d) (y := 1)
          (hp.odd_of_ne_two h2) hadd hpd hv
        simp only [one_pow, Nat.multiplicity_eq_factorization hp] at valuation
        change v.factorization p ≤ (d ^ v + 1).factorization p
        omega
      · simp [Nat.factorization_eq_zero_of_not_dvd h]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have twoPart : ordProj[2] q ∣ d ^ v + 1 := two.trans (by
    simpa only [one_pow] using (hv.nat_add_dvd_pow_add_pow (x := d) (y := 1)))
  have cop : (ordProj[2] q).Coprime v := (Nat.coprime_ordCompl Nat.prime_two hq).pow_left _
  simpa only [v, Nat.ordProj_mul_ordCompl_eq_self] using cop.mul_dvd_of_dvd_of_dvd twoPart oddPart

/-- The converse detector in ordinary divisibility. -/
theorem separation_of_no_return {q d : ℕ} (hq : q ≠ 0)
    (support : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ d + 1) (avoid : ∀ e : ℕ, ¬q ∣ d ^ e + 1) :
    ∃ m : ℕ, m ∣ q ∧ m ∣ 2 * (d + 1) ∧ ¬m ∣ d + 1 := by
  apply (separation_iff (Nat.succ_ne_zero d)).2
  by_contra h
  have cmp : q.factorization 2 ≤ (d + 1).factorization 2 := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hq] at h
    exact Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
  have two : ordProj[2] q ∣ d + 1 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.succ_ne_zero d)).2 cmp
  exact avoid _ (odd_part_returns hq support two)

/-- Under the prime-support condition, the missing minus-one return is exactly one
binary divisibility test. If the test fails the odd part of q supplies a return exponent. -/
theorem no_minus_one_iff {q d : ℕ} (hq : q ≠ 0) (hd : Odd d)
    (support : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ d + 1) :
    (∀ n : ℕ, (d : ZMod q) ^ n ≠ -1) ↔ 2 ^ ((d+1).factorization 2 + 1) ∣ q := by
  constructor
  · intro avoid
    apply (separation_iff (Nat.succ_ne_zero d)).1
    apply separation_of_no_return hq support
    intro n div
    apply avoid n
    have eq := (ZMod.natCast_eq_zero_iff (d^n+1) q).2 div
    push_cast at eq
    linear_combination eq
  · intro bit
    exact New.pow_ne_neg_one_of_separating_divisor hd
      ((separation_iff (Nat.succ_ne_zero d)).2 bit)

/-- A geometric tower that retains the field's full roots of unity and the conductor
absorption, together with its local norm and no-return tests, must contain 1680 in the base. -/
theorem forced_level {q d a s k : ℕ} (hq : q ≠ 0) (h3d : ¬3 ∣ d)
    (eight : 8 ∣ d + 1) (support : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ d + 1)
    (avoid : ∀ e : ℕ, ¬q ∣ d ^ e + 1) (ha : a ≠ 0)
    (roots : 5040 ∣ q * (3 ^ a * 2 ^ s))
    (absorb : q * (3 ^ a * 2 ^ s) * d ∣ (q * d) ^ k) : 1680 ∣ q := by
  have sep := (separation_iff (Nat.succ_ne_zero d)).1 (separation_of_no_return hq support avoid)
  have exp : 3 ≤ (d+1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.succ_ne_zero d)).1 eight
  have h16 : 16 ∣ q := (pow_dvd_pow 2 (by omega : 4 ≤ (d+1).factorization 2 + 1)).trans sep
  have cop : Nat.Coprime 35 (3 ^ a * 2 ^ s) :=
    ((by decide : Nat.Coprime 35 3).pow_right a).mul_right ((by decide : Nat.Coprime 35 2).pow_right s)
  have h35 : 35 ∣ q := cop.dvd_of_dvd_mul_right ((by decide : 35 ∣ 5040).trans roots)
  have left : 3 ∣ q * (3 ^ a * 2 ^ s) * d :=
    ((dvd_pow_self 3 ha).mul_right (2 ^ s) |>.trans (dvd_mul_left _ q)).mul_right d
  have h3 : 3 ∣ q :=
    (Nat.prime_three.dvd_mul.1 (Nat.prime_three.dvd_of_dvd_pow (left.trans absorb))).resolve_right h3d
  have h48 : 48 ∣ q := (by decide : Nat.Coprime 16 3).mul_dvd_of_dvd_of_dvd h16 h3
  exact (by decide : Nat.Coprime 48 35).mul_dvd_of_dvd_of_dvd h48 h35

section
variable {R : Type*} [CommMonoid R]
/-- How the geometric root-of-unity statements pay for the numerical divisibility. -/
example {ω : R} (hω : IsPrimitiveRoot ω 5040) {n : ℕ} (hn : ω ^ n = 1) : 5040 ∣ n :=
  hω.dvd_of_pow_eq_one n hn
end


/-- Two coprime congruences can be assigned to primes past any preassigned cutoff. -/
private theorem prime_in_pair {m l a b : ℕ} (hm : m ≠ 0) (hl : l ≠ 0) (cop : m.Coprime l)
    (am : a.Coprime m) (bl : b.Coprime l) (B : ℕ) :
    ∃ p > B, p.Prime ∧ p ≡ a [MOD m] ∧ p ≡ b [MOD l] := by
  obtain ⟨c, cm, cl⟩ := Nat.chineseRemainder cop a b
  have cm' : c.Coprime m := cm.gcd_eq.trans am
  have cl' : c.Coprime l := cl.gcd_eq.trans bl
  obtain ⟨p, hB, hp, h⟩ := Nat.forall_exists_prime_gt_and_modEq B
    (Nat.mul_ne_zero hm hl) (cm'.mul_right cl')
  exact ⟨p, hB, hp, (h.of_dvd (dvd_mul_right m l)).trans cm,
    (h.of_dvd (dvd_mul_left l m)).trans cl⟩

/-- Every sufficiently large prime of this single reduced progression meets the geometric conditions. -/
def Supports (q M : ℕ) : Prop :=
  ∃ a : ℕ, a.Coprime M ∧ ∃ B : ℕ, ∀ d > B, d.Prime → d ≡ a [MOD M] →
    New.GeometricPrimeConditions q d

/-- A uniformly successful progression must see each odd prime of q and must see eleven.
A dropped prime can be given an incompatible reading by CRT and Dirichlet's theorem. -/
private theorem required_odd {q M a B : ℕ} [NeZero q] (hq : 1680 ∣ q) (hM : M ≠ 0)
    (ha : a.Coprime M) (all : ∀ d > B, d.Prime → d ≡ a [MOD M] → New.GeometricPrimeConditions q d)
    {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hdiv : p ∣ 11 * q) : p ∣ M := by
  by_contra missing
  have cop := (hp.coprime_iff_not_dvd.2 missing).symm
  by_cases p11 : p = 11
  · subst p
    obtain ⟨d, hB, prime, cls, bad⟩ := prime_in_pair hM (by decide : 11 ≠ 0) cop ha
      (by decide : Nat.Coprime 3 11) B
    have ok := all d hB prime cls
    have h8 := ok.norm_divisibility 2 Nat.prime_two ((by decide : 2 ∣ 1680).trans hq)
    have odd : Odd d := Nat.odd_iff.2 (by omega)
    have h44 : d % 44 = 3 := by change d % 11 = 3 % 11 at bad; omega
    have sign := ok.eleven_splits
    change J(((11 : ℕ) : ℤ) | d) = 1 at sign
    rw [jacobiSym.mod_right' 11 odd, show d % (4 * 11) = 3 from h44] at sign
    exact (by decide +kernel : J(11 | 3) ≠ 1) sign
  · have pq : p ∣ q := (hp.dvd_mul.1 hdiv).resolve_left fun div ↦
      p11 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11)).1 div)
    obtain ⟨d, hB, prime, cls, bad⟩ := prime_in_pair hM hp.ne_zero cop ha (Nat.coprime_one_left p) B
    have ok := (all d hB prime cls).norm_divisibility p hp pq
    have dz : p ∣ d + 1 := (dvd_mul_left p 4).trans ok
    have two : p ∣ 2 := Nat.modEq_zero_iff_dvd.1
      ((bad.add_right 1).symm.trans (Nat.modEq_zero_iff_dvd.2 dz))
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 two)

/-- The canonical progression needs precisely four binary digits. Every reduced class with
fewer digits admits a prime equal to -1 on the entire binary part of the geometric level. -/
private theorem required_sixteen {q M a B : ℕ} [NeZero q] (hq : 1680 ∣ q) (hM : M ≠ 0)
    (ha : a.Coprime M) (all : ∀ d > B, d.Prime → d ≡ a [MOD M] → New.GeometricPrimeConditions q d) :
    16 ∣ M := by
  by_contra missing
  have q16 : 16 ∣ q := (by decide : 16 ∣ 1680).trans hq
  have lm : M.factorization 2 ≤ 3 := by
    have nlt : ¬4 ≤ M.factorization 2 := fun le ↦
      missing ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hM).2 le)
    omega
  have lq : 4 ≤ q.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (NeZero.ne q)).1 q16
  have m8 : ordProj[2] M ∣ 8 := pow_dvd_pow 2 lm
  have mq : ordProj[2] M ∣ ordProj[2] q := pow_dvd_pow 2 (by omega)
  obtain ⟨p₀, size₀, prime₀, cls₀⟩ := Nat.forall_exists_prime_gt_and_modEq B hM ha
  have eight := (all p₀ size₀ prime₀ cls₀).norm_divisibility 2 Nat.prime_two
    ((by decide : 2 ∣ 1680).trans hq)
  have aZero : a + 1 ≡ 0 [MOD ordProj[2] M] :=
    ((cls₀.of_dvd (Nat.ordProj_dvd M 2)).add_right 1).symm.trans
      (Nat.modEq_zero_iff_dvd.2 (m8.trans eight))
  let v := ordCompl[2] M
  let t := ordProj[2] q
  have hv : 0 < v := Nat.ordCompl_pos 2 hM
  have ht : 0 < t := pow_pos (by decide : 0 < 2) _
  have ct : (t - 1).Coprime t := by
    have h : t - 1 + 1 = t := by omega
    nth_rw 2 [← h]
    simp
  have c2 : v.Coprime t := (Nat.coprime_ordCompl Nat.prime_two hM).symm.pow_right _
  obtain ⟨d, hB, prime, dv, dt⟩ := prime_in_pair hv.ne' ht.ne' c2
    (ha.of_dvd_right (Nat.ordCompl_dvd M 2)) ct B
  have dz : d + 1 ≡ 0 [MOD t] := by
    have eq : t - 1 + 1 = t := by omega
    have step := dt.add_right 1
    rw [eq] at step
    exact step.trans (Nat.modEq_zero_iff_dvd.2 (dvd_refl t))
  have dm2 : d ≡ a [MOD ordProj[2] M] :=
    Nat.ModEq.add_right_cancel' 1 ((dz.of_dvd mq).trans aZero.symm)
  have dm : d ≡ a [MOD M] := by
    rw [← Nat.ordProj_mul_ordCompl_eq_self M 2]
    exact (Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_ordCompl Nat.prime_two hM).pow_left _)).1
      ⟨dm2, dv⟩
  have stop := (separation_iff (Nat.succ_ne_zero d)).1 (all d hB prime dm).separating_divisor
  have up := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (NeZero.ne q)).1 stop
  have down := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.succ_ne_zero d)).1
    (Nat.modEq_zero_iff_dvd.1 dz)
  omega

/-- Exactly the multiples of the squarefree-odd search modulus can contain a single reduced
class whose sufficiently large primes all satisfy the retained geometric conditions. -/
theorem supports_iff {q M : ℕ} [NeZero q] (hq : 1680 ∣ q) (hM : M ≠ 0) :
    Supports q M ↔ New.twistSearchModulus q ∣ M := by
  constructor
  · rintro ⟨a, unit, B, all⟩
    have h16 := required_sixteen hq hM unit all
    have incl : (11 * q).primeFactors.erase 2 ⊆ M.primeFactors := by
      intro p h
      have former := Nat.mem_primeFactors.1 (Finset.mem_of_mem_erase h)
      exact Nat.mem_primeFactors.2 ⟨former.1, required_odd hq hM unit all former.1
        (Finset.ne_of_mem_erase h) former.2.1, hM⟩
    have hOdd : New.oddPrimeProduct q ∣ M :=
      (Finset.prod_dvd_prod_of_subset _ _ _ incl).trans (Nat.prod_primeFactors_dvd _)
    exact ((New.odd_oddPrimeProduct q).coprime_two_left.pow_left 4).mul_dvd_of_dvd_of_dvd h16 hOdd
  · intro div
    obtain ⟨a, large, prime, cls⟩ := Nat.forall_exists_prime_gt_and_modEq M
      (NeZero.ne (New.twistSearchModulus q)) (New.twistSearchResidue_coprime q)
    have unit : a.Coprime M := prime.coprime_iff_not_dvd.2 fun h ↦
      large.not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) h)
    exact ⟨a, unit, 0, fun d _ _ hd ↦ New.geometricPrimeConditions_of_search hq
      ((hd.of_dvd div).trans cls)⟩

end Hearthline.GeometricLevel
