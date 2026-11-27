module

public import New.Reduction.Zeros.SmallPrimeBudget
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic

/-!
# Independent finite sign prescriptions for zero-free quadratic twists

An invertible refinement imposes the local signs by quadratic reciprocity. The
original zero-density estimate still gives a single arbitrarily large good prime.
-/

@[expose] public section

open Nat Finset Set Filter Asymptotics
open scoped Classical
namespace New.PrimeWindow

private lemma residue_with_symbol {p : ℕ} [Fact p.Prime] (four : p%4=1) (flag : Bool) :
    ∃ v : ℕ, v.Coprime p ∧ legendreSym p v = if flag then -1 else 1 := by
  cases flag with
  | false => exact ⟨1,Nat.coprime_one_left _,by simp⟩
  | true =>
    obtain ⟨u,h⟩ := quadraticChar_exists_neg_one' (F:=ZMod p) (by rw [ZMod.ringChar_zmod_n];omega)
    refine ⟨(u:ZMod p).val, (ZMod.isUnit_iff_coprime _ _).1 (by simpa only [ZMod.natCast_zmod_val] using u.isUnit),?_⟩
    simpa [legendreSym] using h

/-- Adding finitely many independent prime-symbol constraints gives one invertible
congruence class inside the original class. -/
theorem refine_symbols {m a : ℕ} (unit : a.Coprime m) (S : Finset ℕ)
    (good : ∀ p∈S, p.Prime ∧ p%4=1 ∧ p.Coprime m) (flag : ℕ → Bool) :
    ∃ r : ℕ, r.Coprime (m*∏ p ∈ S,p) ∧ r≡a [MOD m] ∧
      ∀ d : Primes, (d:ℕ)≠2 → (d:ℕ)≡r [MOD m*∏ p ∈ S,p] →
        ∀ p∈S, chiK d p = if flag p then -1 else 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨a,by simpa using unit,Nat.ModEq.rfl,by simp⟩
  | @insert p S fresh ih =>
    have restrict (j : ℕ) (hj : j∈S) := good j (Finset.mem_insert_of_mem hj)
    obtain ⟨r,unitR,original,old⟩ := ih restrict
    obtain ⟨prime,four,allowed⟩ := good p (Finset.mem_insert_self _ _)
    let _ : Fact p.Prime := ⟨prime⟩
    obtain ⟨v,unitV,symbol⟩ := residue_with_symbol four (flag p)
    let M := m*∏ j ∈ S,j
    have cop : M.Coprime p := (allowed.mul_right (Nat.Coprime.prod_right (fun j hj ↦
      (Nat.coprime_primes prime (restrict j hj).1).2 (fun eq ↦ fresh (eq ▸ hj))))).symm
    obtain ⟨r',left,right⟩ := Nat.chineseRemainder cop r v
    have eq : (m*∏ j ∈ insert p S,j)=M*p := by rw [Finset.prod_insert fresh];dsimp [M];ring
    rw [eq]
    refine ⟨r',Nat.Coprime.mul_right (show r'.Coprime M from left.gcd_eq.trans unitR) (show r'.Coprime p from right.gcd_eq.trans unitV),
      (left.of_dvd (Nat.dvd_mul_right m _)).trans original,?_⟩
    intro d oddD hclass j hj
    obtain eqj | hj := Finset.mem_insert.1 hj
    · subst j
      have rd := (hclass.of_dvd (Nat.dvd_mul_left p M)).trans right
      have same : legendreSym p (d:ℕ)=legendreSym p v := by
        simpa only [legendreSym,Int.cast_natCast] using
          congrArg (quadraticChar (ZMod p)) ((ZMod.natCast_eq_natCast_iff d v p).2 rd)
      rw [chiK_eq_legendreSym,legendreSym.quadratic_reciprocity_one_mod_four four oddD,same,symbol]
    · exact old d oddD ((hclass.of_dvd (Nat.dvd_mul_right M p)).trans left) j hj

/-- A single large auxiliary prime can realize the prescribed finite signs and
clear the requested zero rectangle for every character of the original modulus q. -/
theorem prescribed_clear_prime {q m a : ℕ} [NeZero q] [NeZero m]
    (eight : 8∣q) (qm : q∣m) (seven : a%8=7) (unit : a.Coprime m)
    (S : Finset ℕ) (good : ∀ p∈S, p.Prime ∧ p%4=1 ∧ p.Coprime m) (flag : ℕ → Bool)
    {β : ℝ} (hβ : 1/2<β) (H : ℝ) (cutoff : ℕ) :
    ∃ d : Primes, cutoff<(d:ℕ) ∧ (d:ℕ)≡a [MOD m] ∧
      (∀ p∈S, chiK d p = if flag p then -1 else 1) ∧
      ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), β≤s.re → |s.im|≤H → entireL (quadTwist χ d) s≠0 := by
  obtain ⟨r,ur,old,symbols⟩ := refine_symbols unit S good flag
  let M := m*∏ j ∈ S,j
  have positive : 0<M := Nat.mul_pos (NeZero.pos m) (Finset.prod_pos (fun j hj ↦ (good j hj).1.pos))
  let _ : NeZero M := ⟨positive.ne'⟩
  let allPrimes := TwistSelection.primeClass (r:ZMod M)
  let pool := TwistSelection.after allPrimes (cutoff+1)
  have uq : a.Coprime q := unit.of_dvd_right qm
  have modm {n : ℕ} (member : n∈pool) : n≡r [MOD M] :=
    (ZMod.natCast_eq_natCast_iff n r M).1 member.1.2
  have inside {n : ℕ} (member : n∈pool) : n≡a [MOD m] :=
    ((modm member).of_dvd (Nat.dvd_mul_right m _)).trans old
  have size (α : ℝ) (h : α<1) : ¬ (TwistSelection.count allPrimes =O[atTop] fun n : ℕ ↦ (n:ℝ)^α) :=
    TwistSelection.not_count_isBigO_of_divergent_weight (S:=allPrimes) (fun n hn ↦ hn.1.pos)
      (TwistSelection.weight_diverges_primeClass ((ZMod.isUnit_iff_coprime r M).2 ur)) h
  obtain ⟨d,hd,clear⟩ := TwistSelection.exists_clear_prime_of_count (q:=q) (a:=(a:ZMod q)) hβ pool
    (fun n hn ↦ ⟨hn.1.1,(ZMod.natCast_eq_natCast_iff n a q).2 ((inside hn).of_dvd qm)⟩)
    (fun d hd ↦ by
      have eq := (ZMod.natCast_eq_natCast_iff d a q).1 hd
      exact ⟨(eq.of_dvd eight).trans (show a≡7 [MOD 8] from seven),Nat.Coprime.symm (eq.gcd_eq.trans uq)⟩)
    (TwistSelection.no_power_saving_after size _ (by linarith)) H
  have d7 : (d:ℕ)%8=7 :=
    ((inside hd).of_dvd (eight.trans qm)).trans (show a≡7 [MOD 8] from seven)
  exact ⟨d,hd.2,inside hd,symbols d (by omega) (modm hd),clear⟩

end New.PrimeWindow
