module

public import Lib.Weil.Construction.FourierInversion
import Mathlib.Tactic

/-!
# Selecting a translate by its commutator phase

For L the project's ideal lattice, let the γ's represent L modulo δ̄L.
Weight the signed shifts by their phase at u. On a translate at v of an
L-invariant theta function, this finite sum detects precisely u ≡ v modulo L.
-/

@[expose] public section

open NumberField Complex Pointwise Set Finset
namespace New.ThetaCoordinates

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
local notation "𝓕" => ((InfinitePlace E × n → ℂ) → ℂ)

noncomputable def selector {Γ : Type} [Fintype Γ] (γ : Γ → n → E) (u : n → E) : Module.End ℂ 𝓕 :=
  ∑ j, ratPhase (γ j) u • signedShift (γ j)

lemma signedShift_ratShift (a y : n → E) (F : 𝓕) :
    signedShift a (ratShift y F) = ratPhase a y • ratShift y (signedShift a F) := by
  rw [signedShift_apply, ratShift_comm a y, signedShift_apply, map_smul, smul_comm]

lemma translate_ne_zero {F : 𝓕} (ne : F ≠ 0) (v : n → E) : ratShift (-v) F ≠ 0 := by
  intro h
  have eq := congrArg (ratShift v) h
  rw [map_zero] at eq
  apply ne
  simpa only [neg_neg] using (ratShift_neg_ratShift (F := F) (-v)).symm.trans (by simpa only [neg_neg] using eq)

variable [DecidableEq n] {δ : E} {Y Γ : Type} [Fintype Y] [Fintype Γ]
  {γ : Γ → n → E} {y : Y → n → E}

open Classical in
/-- The frequency u−v is measured on the same δ⁻¹L/ L on which the translates live. -/
theorem selector_translate {u v : n → E} (hu : u ∈ δ⁻¹ • idealLattice E n)
    (hv : v ∈ δ⁻¹ • idealLattice E n) (hδ : δ ≠ 0)
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    {F : 𝓕} (hF : IsThetaFunction (idealLattice E n) F) :
    selector γ u (ratShift (-v) F) =
      if u - v ∈ idealLattice E n then (Fintype.card Γ : ℂ) • ratShift (-v) F else 0 := by
  classical
  have shift (j : Γ) : signedShift (γ j) (ratShift (-v) F) = ratPhase (γ j) (-v) • ratShift (-v) F := by
    rw [signedShift_ratShift, hF.signedShift_eq _ (hγ.mem j)]
  calc _ = ∑ j, ratPhase (γ j) (u - v) • ratShift (-v) F := by
             simp only [selector, LinearMap.sum_apply, LinearMap.smul_apply, shift, smul_smul,
               sub_eq_add_neg, ratPhase_add_right]
       _ = (∑ j, ratPhase (γ j) (u - v)) • ratShift (-v) F := (Finset.sum_smul ..).symm
       _ = _ := by
             rw [sum_ratPhase_star_smul hγ hδ (sub_mem hu hv)]
             split_ifs <;> simp

omit [Fintype Y] in
open Classical in
theorem selector_at_rep (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n)) (hδ : δ ≠ 0)
    {F : 𝓕} (hF : IsThetaFunction (idealLattice E n) F) (i k : Y) :
    selector γ (y i) (ratShift (-y k) F) =
      if i = k then (Fintype.card Γ : ℂ) • ratShift (-y k) F else 0 := by
  have eq : y i - y k ∈ idealLattice E n ↔ i = k := ⟨hy.eq_of_sub_mem, fun h ↦ by simp [h]⟩
  simp only [selector_translate (hy.mem i) (hy.mem k) hδ hγ hF, eq]

theorem selector_sum (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n)) (hδ : δ ≠ 0)
    {F : 𝓕} (hF : IsThetaFunction (idealLattice E n) F) (c : Y → ℂ) (i : Y) :
    selector γ (y i) (∑ k, c k • ratShift (-y k) F) = c i • (Fintype.card Γ : ℂ) • ratShift (-y i) F := by
  classical
  simp only [map_sum, map_smul, selector_at_rep hy hγ hδ hF, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [Fintype n] [DecidableEq n] in
lemma characterCount_ne_zero (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n)) :
    (Fintype.card Γ : ℂ) ≠ 0 := by
  obtain ⟨j, _⟩ := hγ.exists_mem_iff_eq
  let _ : Nonempty Γ := ⟨j⟩
  exact_mod_cast Fintype.card_ne_zero

/-- The translates of any nonzero invariant theta function indexed by distinct
classes are linearly independent. The selector isolates each coefficient. -/
theorem independent_translates (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n)) (hδ : δ ≠ 0)
    {F : 𝓕} (hF : IsThetaFunction (idealLattice E n) F) (ne : F ≠ 0) :
    LinearIndependent ℂ (fun i : Y ↦ ratShift (-y i) F) := by
  rw [Fintype.linearIndependent_iff]
  intro c zero i
  have h := congrArg (selector γ (y i)) zero
  rw [map_zero, selector_sum hy hγ hδ hF] at h
  exact (smul_eq_zero.1 h).resolve_right (smul_ne_zero (characterCount_ne_zero hγ) (translate_ne_zero ne _))

/-- On the admissible translates two selector positions define the same
operator precisely when their difference is a lattice vector. -/
theorem selector_eq_iff {u v : n → E} (hu : u ∈ δ⁻¹ • idealLattice E n)
    (hv : v ∈ δ⁻¹ • idealLattice E n) (hδ : δ ≠ 0)
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    {F : 𝓕} (hF : IsThetaFunction (idealLattice E n) F) (ne : F ≠ 0) :
    selector γ u = selector γ v ↔ u - v ∈ idealLattice E n := by
  classical
  constructor
  · intro same
    by_contra diff
    have e := congrArg (fun op : Module.End ℂ 𝓕 ↦ op (ratShift (-v) F)) same
    simp only [selector_translate hu hv hδ hγ hF, selector_translate hv hv hδ hγ hF,
      diff, ite_false, sub_self, zero_mem, ite_true] at e
    exact smul_ne_zero (characterCount_ne_zero hγ) (translate_ne_zero ne _) e.symm
  · intro diff
    have same (j : Γ) : ratPhase (γ j) u = ratPhase (γ j) v := by
      have one := (mem_idealLattice_iff_ratPhase.1 (hγ.mem j)) (u - v) diff
      calc ratPhase (γ j) u = ratPhase (γ j) ((u - v) + v) := by rw [sub_add_cancel]
           _ = _ := by rw [ratPhase_add_right, one, one_mul]
    simp only [selector, same]

end New.ThetaCoordinates
