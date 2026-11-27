module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Minimum signed imbalance when an integer histogram changes period

Integer marks with given old and new residues can be matched and lifted exactly when their
multiplicities agree modulo the gcd. In a common residue block one either fixes the two
sides separately or fixes only their combined mass. Absolute imbalance has an attainable
minimum in both cases.
-/

@[expose] public section
open Finset
namespace ResidueTransport

/-- Two finite labeled populations have joint integer representatives precisely when their
common-residue fibers can be matched. Repeated values keep their individual labels. -/
theorem crt_matching_iff {A B : Type*} [Fintype A] [Fintype B] {N Q : ℕ}
    (nonzero : 0<N.gcd Q) (old : A → ℕ) (fresh : B → ℕ) :
    (∃ e : A ≃ B, ∀ a, ∃ x : ℕ, x ≡ old a [MOD N] ∧ x ≡ fresh (e a) [MOD Q]) ↔
    (∀ r : Fin (N.gcd Q),
      Fintype.card {a : A // old a%(N.gcd Q)=r.val} =
      Fintype.card {b : B // fresh b%(N.gcd Q)=r.val}) := by
  classical
  let f (a : A) : Fin (N.gcd Q) := ⟨old a%(N.gcd Q),Nat.mod_lt _ nonzero⟩
  let g (b : B) : Fin (N.gcd Q) := ⟨fresh b%(N.gcd Q),Nat.mod_lt _ nonzero⟩
  constructor
  · rintro ⟨e,ok⟩ r
    have agree (a : A) : f a = g (e a) := by
      obtain ⟨x,hn,hq⟩ := ok a
      exact Fin.ext ((hn.of_dvd (Nat.gcd_dvd_left _ _)).symm.trans (hq.of_dvd (Nat.gcd_dvd_right _ _)))
    apply Fintype.card_congr
    exact { toFun := fun a ↦ ⟨e a, (congrArg Fin.val (agree a)).symm.trans a.2⟩
            invFun := fun b ↦ ⟨e.symm b, (congrArg Fin.val (agree (e.symm b))).trans (by simpa [g] using b.2)⟩
            left_inv := fun a ↦ Subtype.ext (e.symm_apply_apply a)
            right_inv := fun b ↦ Subtype.ext (e.apply_symm_apply b) }
  · intro sizes
    let iso (r : Fin (N.gcd Q)) : {a // f a=r} ≃ {b // g b=r} :=
      Fintype.equivOfCardEq (by simpa only [f,g,Fin.ext_iff] using sizes r)
    let e := (Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight iso).trans (Equiv.sigmaFiberEquiv g))
    refine ⟨e,fun a ↦ ?_⟩
    have same : g (e a)=f a := (iso (f a) ⟨a,rfl⟩).2
    have rel : old a ≡ fresh (e a) [MOD N.gcd Q] := congrArg Fin.val same.symm
    exact ⟨(Nat.chineseRemainder' rel).val,(Nat.chineseRemainder' rel).property⟩

/-- For common modulus d=gcd(N,2G), either d divides the half-turn G, or it doubles
h=gcd(N,G). In the latter case the two different residues over h are exchanged. -/
lemma common_modulus_cases {N G : ℕ} (hg : 0<G) :
    N.gcd (2*G)=N.gcd G ∨ N.gcd (2*G)=2*N.gcd G ∧ Odd (G/(N.gcd G)) := by
  let h := N.gcd G
  let d := N.gcd (2*G)
  have pos : 0<h := Nat.gcd_pos_of_pos_right _ hg
  have left : h∣N := Nat.gcd_dvd_left _ _
  have right : h∣G := Nat.gcd_dvd_right _ _
  have hd : h∣d := Nat.dvd_gcd left (right.trans (dvd_mul_left _ _))
  have d_two : d∣2*h := by
    change d∣2*(N.gcd G)
    rw [← Nat.gcd_mul_left]
    exact Nat.dvd_gcd ((Nat.gcd_dvd_left N (2*G)).trans (dvd_mul_left _ _)) (Nat.gcd_dvd_right _ _)
  obtain ⟨k,eq⟩ := hd
  have kdiv : k∣2 := by
    have le : h*k∣h*2 := by simpa only [← eq,Nat.mul_comm h 2] using d_two
    exact (Nat.mul_dvd_mul_iff_left pos).1 le
  rcases (Nat.dvd_prime Nat.prime_two).1 kdiv with k1|k2
  · left;change d=h;simpa [k1] using eq
  · have twice : d=2*h := by simpa [k2,Nat.mul_comm] using eq
    refine Or.inr ⟨twice,?_⟩
    by_contra even
    have hdvd : 2∣G/h := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp even)
    have full : 2*h∣G := by
      obtain ⟨q,hq⟩ := hdvd
      refine ⟨q,?_⟩
      calc G = (G/h)*h := (Nat.div_mul_cancel right).symm
        _ = (2*h)*q := by rw [hq];ring
    have many : d∣h := Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (twice ▸ full)
    exact (by omega : ¬2*h≤h) (twice ▸ Nat.le_of_dvd pos many)

inductive Margin where
  | shared (total : ℕ)
  | separate (left right : ℕ)

namespace Margin

def accepts (m : Margin) (l r : ℕ) : Prop :=
  match m with
  | shared n => l+r=n
  | separate a b => l=a ∧ r=b

def minimum : Margin → ℤ
  | shared n => n%2
  | separate a b => |(a:ℤ)-b|

def chosen : Margin → ℕ × ℕ
  | shared n => (n/2,n-n/2)
  | separate a b => (a,b)

lemma chosen_fits (m : Margin) : m.accepts m.chosen.1 m.chosen.2 := by
  cases m <;> simp [chosen,accepts]
  omega

lemma chosen_cost (m : Margin) : |(m.chosen.1:ℤ)-m.chosen.2|=m.minimum := by
  cases m with
  | shared n =>
    change |((n/2:ℕ):ℤ)-(n-n/2:ℕ)|=((n%2:ℕ):ℤ)
    rw [abs_of_nonpos (by omega)];omega
  | separate a b => rfl

lemma lower {m : Margin} {l r : ℕ} (fits : m.accepts l r) : m.minimum ≤ |(l:ℤ)-r| := by
  cases m with
  | shared n =>
    change l+r=n at fits
    change ((n%2:ℕ):ℤ) ≤ |(l:ℤ)-r|
    rcases le_total l r with h|h
    · rw [abs_of_nonpos (by omega)];omega
    · rw [abs_of_nonneg (by omega)];omega
  | separate a b =>
    obtain ⟨rfl,rfl⟩ := fits
    exact le_rfl

end Margin

/-- The exact least imbalance over independently splittable or separately supplied
conjugate pairs in any finite collection of common blocks. The indices in each block
are oriented consistently with its old sides; swapping a fine pair leaves its cost unchanged. -/
theorem least_block_loss {β : Type*} [Fintype β] {I : β → Type*} [∀ b,Fintype (I b)] [∀ b,Nonempty (I b)]
    (m : β → Margin) :
    IsLeast {loss : ℤ | ∃ L R : (b : β) → I b → ℕ,
       (∀ b, (m b).accepts (∑ i,L b i) (∑ i,R b i)) ∧
       loss = ∑ b,∑ i, |(L b i:ℤ)-R b i|} (∑ b,(m b).minimum) := by
  classical
  let a (b : β) := Classical.choice (inferInstance : Nonempty (I b))
  let L (b : β) (i : I b) := if i=a b then (m b).chosen.1 else 0
  let R (b : β) (i : I b) := if i=a b then (m b).chosen.2 else 0
  constructor
  · refine ⟨L,R,?_,?_⟩
    · intro b;simpa [L,R] using (m b).chosen_fits
    · apply sum_congr rfl
      intro b _
      symm
      rw [sum_eq_single (a b)]
      · simpa [L,R] using (m b).chosen_cost
      · intro j _ ne;simp [L,R,ne]
      · simp
  · rintro cost ⟨l,r,fits,rfl⟩
    apply sum_le_sum;intro b _
    have lower := Margin.lower (fits b)
    calc (m b).minimum ≤ |((∑ i,l b i : ℕ):ℤ)-(∑ i,r b i : ℕ)| := lower
      _ = |∑ i,((l b i:ℤ)-r b i)| := by simp [sum_sub_distrib]
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _

end ResidueTransport
