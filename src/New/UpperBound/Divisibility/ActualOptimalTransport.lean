module

public import New.UpperBound.Divisibility.OptimalResidueTransport
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-!
# Attaining the minimum with genuine integer lifts

In each common block the fine pairs are indexed by j. If the old sides are distinct,
swap the names of the two fine sides when j is odd, so that the first side always comes
from the same old residue. Compatible counts then give actual lifts by the Chinese
remainder theorem. No sparseness constraint is imposed in this finite transport problem.
-/

@[expose] public section
open Finset
namespace ResidueTransport

def commonSize (joint : Bool) (H : ℕ) := if joint then H else 2*H
def upperSide (joint side : Bool) (j : ℕ) : Bool :=
  if joint || decide (j%2=0) then side else !side
def outputAddress (joint side : Bool) {H K : ℕ} (b : Fin H) (j : Fin K) : ℕ :=
  b.val + H*(if upperSide joint side j.val then j.val+K else j.val)

def oldCount {A : Type*} [Fintype A] (old : A → ℕ) (m r : ℕ) : ℕ :=
  Fintype.card {a // old a%m=r}

def oldMargin {A : Type*} [Fintype A] (joint : Bool) (old : A → ℕ) {H : ℕ} (b : Fin H) : Margin :=
  if joint then .shared (oldCount old H b.val)
  else .separate (oldCount old (2*H) b.val) (oldCount old (2*H) (b.val+H))

abbrev FineMarks {H K : ℕ} (L R : Fin H → Fin K → ℕ) :=
  Σ b : Fin H, (Σ j : Fin K,Fin (L b j)) ⊕ (Σ j : Fin K,Fin (R b j))

def fineResidue {H K : ℕ} {L R : Fin H → Fin K → ℕ} (joint : Bool) (x : FineMarks L R) : ℕ :=
  x.2.elim (fun q ↦ outputAddress joint false x.1 q.1) (fun q ↦ outputAddress joint true x.1 q.1)

lemma double_mod {r H : ℕ} (hr : r<H) (t : ℕ) : (r+H*t)%(2*H)=r+H*(t%2) := by
  have split : r+H*t = r+H*(t%2)+(2*H)*(t/2) := by
    calc _ = r+H*(t%2+2*(t/2)) := congrArg (fun x ↦ r+H*x) (Nat.mod_add_div t 2).symm
      _ = _ := by ring
  have small : r+H*(t%2)<2*H := by
    rcases (by omega : t%2=0 ∨ t%2=1) with h|h <;> simp [h] <;> omega
  rw [split,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small]

lemma output_color (joint side : Bool) {H K : ℕ} (odd : joint=false → Odd K) (b : Fin H) (j : Fin K) :
    outputAddress joint side b j % commonSize joint H =
      if !joint && side then b.val+H else b.val := by
  cases joint with
  | true => cases side <;> simp [outputAddress,commonSize,upperSide,Nat.mod_eq_of_lt b.isLt]
  | false =>
    obtain ⟨q,hq⟩ := odd rfl
    have parity : (j.val+K)%2 = 1-j.val%2 := by omega
    have jp : j.val%2=0 ∨ j.val%2=1 := by omega
    rcases jp with h|h <;> cases side <;>
      simp [outputAddress,commonSize,upperSide,h,double_mod b.isLt,parity]

lemma card_as_sum {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    Fintype.card {a // p a} = ∑ a,if p a then 1 else 0 := by
  rw [Fintype.card_subtype,Finset.card_filter]

theorem fine_count (joint : Bool) {H K : ℕ} (odd : joint=false → Odd K)
    (L R : Fin H → Fin K → ℕ) (r : ℕ) :
    oldCount (fineResidue (L := L) (R := R) joint) (commonSize joint H) r =
      ∑ b, ((if b.val=r then ∑ j,L b j else 0) +
         if (if joint then b.val else b.val+H)=r then ∑ j,R b j else 0) := by
  classical
  unfold oldCount
  rw [card_as_sum,Fintype.sum_sigma]
  apply sum_congr rfl;intro b _
  rw [Fintype.sum_sum_type,Fintype.sum_sigma,Fintype.sum_sigma]
  simp only [fineResidue,Sum.elim_inl,Sum.elim_inr,output_color joint _ odd, Bool.and_false,
    Bool.and_true,Bool.not_eq_true',sum_const,nsmul_eq_mul,mul_ite,mul_one,mul_zero]
  cases joint <;> by_cases h : b.val=r <;> by_cases h' : b.val+H=r <;> simp_all

lemma upperSide_involutive (joint side : Bool) (j : ℕ) :
    upperSide joint (upperSide joint side j) j=side := by
  unfold upperSide
  split_ifs <;> simp_all

/-- Reorient the odd rows if their reference belongs to the other coarse side. Each
reference below G occurs once by Euclidean division, and the bit selects its side. -/
def orientedPairs (joint : Bool) (H K : ℕ) : (Fin K × Fin H) × Bool ≃ Fin (K*H) × Bool where
  toFun x := (finProdFinEquiv x.1,upperSide joint x.2 x.1.1.val)
  invFun y := (finProdFinEquiv.symm y.1,upperSide joint y.2 (finProdFinEquiv.symm y.1).1.val)
  left_inv := by rintro ⟨x,s⟩;simp [upperSide_involutive]
  right_inv := by
    rintro ⟨x,s⟩
    exact Prod.ext (finProdFinEquiv.apply_symm_apply x) (upperSide_involutive joint s _)

def twoSides (m : ℕ) : Fin m × Bool ≃ Fin (2*m) where
  toFun x := ⟨if x.2 then x.1.val+m else x.1.val,by have := x.1.isLt;split_ifs <;> omega⟩
  invFun x := if h : x.val<m then (⟨x.val,h⟩,false) else (⟨x.val-m,by have := x.isLt;omega⟩,true)
  left_inv := by
    rintro ⟨i,side⟩
    cases side <;> simp [i.isLt]
  right_inv := by
    intro x
    apply Fin.ext
    by_cases h : x.val<m <;> simp [h]
    omega

/-- The output positions used by the optimizer give every residue modulo 2G exactly once. -/
def outputEquiv (joint : Bool) (H K : ℕ) : (Fin K × Fin H) × Bool ≃ Fin (2*(K*H)) :=
  (orientedPairs joint H K).trans (twoSides (K*H))

lemma outputEquiv_address (joint side : Bool) {H K : ℕ} (b : Fin H) (j : Fin K) :
    (outputEquiv joint H K ((j,b),side)).val=outputAddress joint side b j := by
  change (if upperSide joint side j.val then (b.val+H*j.val)+(K*H) else b.val+H*j.val) =
    b.val+H*(if upperSide joint side j.val then j.val+K else j.val)
  cases upperSide joint side j.val <;> simp
  ring

theorem matches_iff_margins {A : Type*} [Fintype A] (old : A → ℕ) {N H K : ℕ}
    (hh : 0<H) (joint : Bool) (d : N.gcd (2*(H*K))=commonSize joint H)
    (odd : joint=false → Odd K) (L R : Fin H → Fin K → ℕ) :
    (∃ e : A ≃ FineMarks L R, ∀ a, ∃ x : ℕ,
       x ≡ old a [MOD N] ∧ x ≡ fineResidue joint (e a) [MOD 2*(H*K)]) ↔
       ∀ b,(oldMargin joint old b).accepts (∑ j,L b j) (∑ j,R b j) := by
  have dp : 0<N.gcd (2*(H*K)) := by rw [d];cases joint <;> simp [commonSize] <;> omega
  rw [crt_matching_iff dp old (fineResidue (L := L) (R := R) joint)]
  change (∀ r : Fin (N.gcd (2*(H*K))), oldCount old (N.gcd (2*(H*K))) r.val=
    oldCount (fineResidue (L := L) (R := R) joint) (N.gcd (2*(H*K))) r.val) ↔ _
  rw [d]
  simp_rw [fine_count joint odd]
  cases joint with
  | true =>
    change (∀ r : Fin H, oldCount old H r.val = _) ↔ _
    simpa [Finset.sum_add_distrib,oldMargin,Margin.accepts,Fin.val_inj] using
      (show (∀ r : Fin H, oldCount old H r.val = (∑ j,L r j)+(∑ j,R r j)) ↔
        ∀ r : Fin H,(∑ j,L r j)+(∑ j,R r j)=oldCount old H r.val from
        ⟨fun h r ↦ (h r).symm,fun h r ↦ (h r).symm⟩)
  | false =>
    have low (b : Fin H) : (∑ v : Fin H,
        ((if v.val=b.val then ∑ j,L v j else 0) + if v.val+H=b.val then ∑ j,R v j else 0)) = ∑ j,L b j := by
      have off (v : Fin H) : v.val+H≠b.val := by have := b.isLt;omega
      simp [off,Fin.val_inj]
    have high (b : Fin H) : (∑ v : Fin H,
        ((if v.val=b.val+H then ∑ j,L v j else 0) + if v.val+H=b.val+H then ∑ j,R v j else 0)) = ∑ j,R b j := by
      have off (v : Fin H) : v.val≠b.val+H := by have := v.isLt;omega
      simp [off,Fin.val_inj]
    change (∀ r : Fin (2*H), oldCount old (2*H) r.val =
      ∑ b, ((if b.val=r.val then ∑ j,L b j else 0) + if b.val+H=r.val then ∑ j,R b j else 0)) ↔
      ∀ b,(∑ j,L b j)=oldCount old (2*H) b.val ∧ (∑ j,R b j)=oldCount old (2*H) (b.val+H)
    constructor
    · intro counts b
      have l := counts ⟨b.val,by have := b.isLt;omega⟩
      have r := counts ⟨b.val+H,by have := b.isLt;omega⟩
      exact ⟨((low b).symm.trans l.symm),((high b).symm.trans r.symm)⟩
    · intro fits r
      by_cases first : r.val<H
      · let b : Fin H := ⟨r.val,first⟩
        exact ((fits b).1).symm.trans (low b).symm
      · let b : Fin H := ⟨r.val-H,by have := r.isLt;omega⟩
        have eq : r.val=b.val+H := by dsimp [b];omega
        rw [eq];exact ((fits b).2).symm.trans (high b).symm

/-- Exact minimum among actual joint integer lifts of the old individual marks. Every
positive pair N,2G has a layout of this form, as shown by exists_layout. -/
theorem least_crt_loss {A : Type*} [Fintype A] (old : A → ℕ) {N H K : ℕ} (hh : 0<H) (hk : 0<K)
    (joint : Bool) (d : N.gcd (2*(H*K))=commonSize joint H) (odd : joint=false → Odd K) :
    IsLeast {loss : ℤ | ∃ L R : Fin H → Fin K → ℕ,
      (∃ e : A ≃ FineMarks L R, ∀ a, ∃ x : ℕ, x ≡ old a [MOD N] ∧
        x ≡ fineResidue joint (e a) [MOD 2*(H*K)]) ∧
      loss=∑ b,∑ j,|(L b j:ℤ)-R b j|} (∑ b : Fin H,(oldMargin joint old b).minimum) := by
  let : NeZero K := ⟨hk.ne'⟩
  simp_rw [matches_iff_margins old hh joint d odd]
  exact least_block_loss (I := fun _ : Fin H ↦ Fin K) (oldMargin joint old)

/-- The two block cases exhaust all positive half-periods for any positive old length.
The pair index is the common residue modulo H followed by a row j below K. -/
theorem exists_layout (N G : ℕ) (hg : 0<G) :
    ∃ H K : ℕ, ∃ joint : Bool, 0<H ∧ 0<K ∧ G=H*K ∧
      N.gcd (2*G)=commonSize joint H ∧ (joint=false → Odd K) := by
  let H := N.gcd G
  have hh : 0<H := Nat.gcd_pos_of_pos_right _ hg
  have hd : H∣G := Nat.gcd_dvd_right _ _
  have hk : 0<G/H := Nat.div_pos (Nat.le_of_dvd hg hd) hh
  have eq : G=H*(G/H) := (Nat.mul_div_cancel' hd).symm
  rcases common_modulus_cases (N := N) hg with one|⟨two,odd⟩
  · exact ⟨H,G/H,true,hh,hk,eq,one,by intro h;cases h⟩
  · exact ⟨H,G/H,false,hh,hk,eq,two,fun _ ↦ odd⟩

end ResidueTransport
