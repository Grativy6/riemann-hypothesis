module

public import New.UpperBound.Divisibility.SmallerOrbitPrimes
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-!
# The first exceptional prime outside the 72-slot board

The base modulus forces p+1 to be a multiple of 240 and the odd local order to divide 15.
A bounded computation therefore needs only the possible multiples of 240, rather than
the much larger tower order. The surviving rational primes are compared with the actual
gcd determining the arithmetic period.
-/

@[expose] public section
open NumberField Finset
namespace New.Data.CollisionPrimeExample

/-- The four possible odd orders divide 15, so three modular checks select the exponent. -/
def oddExponent (p : ℕ) : ℕ :=
  if 18480 ∣ p+1 then 1 else if 18480 ∣ p^3+1 then 3 else if 18480 ∣ p^5+1 then 5 else 15

def checkedQuotient (p : ℕ) : ℕ := (p^(oddExponent p)+1)/18480
def checkedG (p : ℕ) : ℕ := Nat.gcd 5184 (checkedQuotient p)

lemma necessary_odd_order (D : Data params) {p : ℕ} [Fact p.Prime] (he : D.IsExceptional p) :
    240 ∣ p+1 ∧ 18480 ∣ p^15+1 ∧ D.o₀ p=oddExponent p := by
  have collision : D.IsCollision p ∅ 1 (D.o₀ p) :=
    (D.collision_empty_iff 1 _).2 ⟨by simp [aPlaces],he.chiK_eq_neg_one,he.odd_o₀,dvd_rfl⟩
  have prime240 : -(p : ZMod 240)=1 := by
    simpa only [pow_one] using collision.neg_prime_pow_of_totient
      (by decide : 240 ∣ params.q₀) (k := 6) (t := 1) (by decide)
  have div240 : 240 ∣ p+1 := (ZMod.natCast_eq_zero_iff _ _).1
    (show ((p+1:ℕ):ZMod 240)=0 by push_cast;linear_combination -prime240)
  have phi : params.q₀.totient=2^8*15 := by
    change Nat.totient 18480 = 2^8*15
    rw [show (18480 : ℕ) = 2^4*(3*(5*(7*11))) by decide]
    rw [Nat.totient_mul (by decide : Nat.Coprime (2^4) (3*(5*(7*11)))),
      Nat.totient_mul (by decide : Nat.Coprime 3 (5*(7*11))),
      Nat.totient_mul (by decide : Nat.Coprime 5 (7*11)),
      Nat.totient_mul (by decide : Nat.Coprime 7 11)]
    decide
  have power15 : (-(p : ZMod params.q₀))^15=1 :=
    collision.neg_prime_pow_of_totient dvd_rfl (k := 8) (t := 15) phi
  have small := (dvd_iff_neg_prime_pow (D := D) he.chiK_eq_neg_one 15).2 power15
  have test (e : ℕ) (odd : Odd e) : D.o₀ p ∣ e ↔ 18480 ∣ p^e+1 := by
    rw [dvd_iff_neg_prime_pow he.chiK_eq_neg_one, odd.neg_pow, ← ZMod.natCast_eq_zero_iff]
    change -(p : ZMod 18480)^e=1 ↔ ((p^e+1:ℕ):ZMod 18480)=0
    push_cast
    constructor <;> intro h <;> linear_combination -h
  have bounds := Nat.le_of_dvd (by decide : 0<15) small
  have possibilities : D.o₀ p=1 ∨ D.o₀ p=3 ∨ D.o₀ p=5 ∨ D.o₀ p=15 := by
    have table : ∀ e : Fin 16, e.val∣15 → e.val=1 ∨ e.val=3 ∨ e.val=5 ∨ e.val=15 := by decide
    exact table ⟨D.o₀ p,by omega⟩ small
  refine ⟨div240,(test 15 (by decide)).1 small,?_⟩
  unfold oddExponent
  have one : (D.o₀ p∣1) ↔ 18480∣p+1 := by simpa only [pow_one] using test 1 (by decide)
  simp only [← one,← test 3 (by decide),← test 5 (by decide)]
  rcases possibilities with a|a|a|a <;> rw [a] <;> decide

private def trial (p : ℕ) : Prop := ¬13∣p ∧ ¬19∣p ∧ ¬67∣p ∧ ¬89∣p ∧ ¬127∣p
private instance (p : ℕ) : Decidable (trial p) := inferInstanceAs (Decidable (¬13∣p ∧ ¬19∣p ∧ ¬67∣p ∧ ¬89∣p ∧ ¬127∣p))

private def checkedRow (k : ℕ) : Prop :=
  let p := 240*k-1
  18480 ∣ p^15+1 → trial p →
    checkedQuotient p=checkedG p*(checkedQuotient p/checkedG p) ∧
    Nat.Coprime 2 (checkedQuotient p/checkedG p) ∧ Nat.Coprime 3 (checkedQuotient p/checkedG p) ∧
    (p<72959 → 2*checkedG p ∣ 72 ∨ p=10799 ∨ p=26879 ∨ p=53759) ∧ (p<97919 → checkedG p≠72)
private instance (k : ℕ) : Decidable (checkedRow k) := by unfold checkedRow;infer_instance

set_option maxRecDepth 8192 in
private theorem candidate_table (i : Fin 409) : checkedRow i.val := by
  have batch : ∀ h : Fin 26,∀ l : Fin 16, checkedRow (16*h.val+l.val) := by decide
  have r := batch ⟨i.val/16,by have := i.isLt;omega⟩ ⟨i.val%16,Nat.mod_lt _ (by decide)⟩
  change checkedRow (16*(i.val/16)+i.val%16) at r
  rwa [Nat.div_add_mod] at r

/-- Below 97920 the screened finite gcd agrees with the actual tower gcd. The three
apparently incompatible earlier candidates are split rather than inert. -/
theorem small_period_bounds (D : Data params) {p : ℕ} [hp : Fact p.Prime] (he : D.IsExceptional p)
    (bound : p<97920) : D.returnPairCount p=checkedG p ∧
      (p<72959 → 2*D.returnPairCount p∣72) ∧ (p<97919 → D.returnPairCount p≠72) := by
  obtain ⟨multiple,power,order⟩ := necessary_odd_order D he
  obtain ⟨i,hi⟩ := multiple
  have ib : i<409 := by omega
  have pp : 240*i-1=p := by omega
  have h := candidate_table ⟨i,ib⟩
  unfold checkedRow at h
  rw [pp] at h
  have lower : 127<p := by have := hp.out.two_le;omega
  have avoid (q : ℕ) (hq : 1<q) (hsmall : q≤127) : ¬q∣p := by
    intro eq;rcases (Nat.dvd_prime hp.out).1 eq with eq|eq <;> omega
  have tested : trial p := ⟨avoid 13 (by decide) (by decide),avoid 19 (by decide) (by decide),
    avoid 67 (by decide) (by decide),avoid 89 (by decide) (by decide),avoid 127 (by decide) (by decide)⟩
  obtain ⟨factor,c₂,c₃,first,second⟩ := h power tested
  have ret : D.returnQuotient p=checkedQuotient p := by rw [returnQuotient,order];rfl
  obtain ⟨e,_,hs⟩ := D.exists_m_eq_two_pow
  have cap : 5184 ∣ towerDeg D.towerExp := Nat.mul_dvd_mul
    (pow_dvd_pow 3 (show 4≤Nat.log 3 D.towerExp+5 by omega)) (pow_dvd_pow 2 (show 6≤D.towerExp by omega))
  have gd : checkedG p ∣ towerDeg D.towerExp := (Nat.gcd_dvd_left 5184 _).trans cap
  have cop : (towerDeg D.towerExp).Coprime (checkedQuotient p/checkedG p) :=
    (c₃.pow_left _).mul_left (c₂.pow_left _)
  have realG : D.returnPairCount p=checkedG p := by
    change (towerDeg D.towerExp).gcd (D.returnQuotient p)=_
    rw [ret]
    exact (congrArg (Nat.gcd (towerDeg D.towerExp)) factor).trans (OrbitProbes.gcd_with_coprime_cofactor gd cop)
  rw [realG]
  refine ⟨rfl,?_,second⟩
  intro small
  rcases first small with ok|a|a|a
  · exact ok
  all_goals
    have hχ := he.chiK_eq_neg_one
    have : Fact (Nat.Prime 9239) := ⟨by norm_num1⟩
    change chiK 9239 (p:ℕ) = -1 at hχ
    rw [chiK_eq_legendreSym 9239 p,jacobiSym.legendreSym.to_jacobiSym,a] at hχ
    norm_num at hχ

/-- The first incompatible prime and the first half-period 72 are attained on every
admissible data set. All smaller exceptional rational primes obey the corresponding bound. -/
theorem first_exit_and_first_doubling (D : Data params) :
    (D.IsExceptional (smallerPrime 1) ∧ D.returnPairCount (smallerPrime 1)=48) ∧
    (∀ p : ℕ, ∀ [_hp : Fact p.Prime], D.IsExceptional p →
      ¬2*D.returnPairCount p ∣ 72 → 72959≤p) ∧
    (D.IsExceptional (smallerPrime 3) ∧ D.returnPairCount (smallerPrime 3)=72) ∧
    (∀ p : ℕ, ∀ [_hp : Fact p.Prime], D.IsExceptional p → D.returnPairCount p=72 → 97919≤p) := by
  refine ⟨⟨(small_probe_facts D 1).1,(small_probe_facts D 1).2.2⟩,?_,
    ⟨(small_probe_facts D 3).1,(small_probe_facts D 3).2.2⟩,?_⟩
  · intro p hp he incompatible
    by_contra! small
    exact incompatible ((small_period_bounds D he (by omega)).2.1 small)
  · intro p hp he period
    by_contra! small
    exact (small_period_bounds D he (by omega)).2.2 small period

end New.Data.CollisionPrimeExample
