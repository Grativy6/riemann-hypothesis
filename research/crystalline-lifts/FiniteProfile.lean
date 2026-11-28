import DepthProfile
import TauCeti.Algebra.Module.DiscreteValuationRing
import Mathlib.Tactic

noncomputable section
open Module Submodule IsLocalRing
namespace Hearthline.RelationLattices

variable {O Γ n : Type*} [CommRing O] [New.DVR O] [Fintype n] [DecidableEq n]
  (Z : Submodule O (Γ → n → O)) [Module.Finite O Z]

omit [Fintype n] [DecidableEq n] in
/-- The saturation defect is torsion, so its finite elementary-divisor presentation has
no free factor. Every exponent returned by the structure theorem is positive. -/
theorem exists_defect_type {π : O} (hπ : Irreducible π) :
    ∃ (r : ℕ) (e : Fin r → ℕ), (∀ i, 0 < e i) ∧
      Nonempty (defect Z ≃ₗ[O] ∀ i, O ⧸ maximalIdeal O ^ e i) := by
  classical
  have : Module.Finite O (saturation Z) := finite_saturation Z
  let Y := Z.submoduleOf (saturation Z)
  obtain ⟨nfree, r, e, positive, ⟨b⟩⟩ :=
    TauCeti.Module.equiv_pi_prod_pi_quotient_span_pow O (defect Z) hπ
  have free_zero : nfree = 0 := by
    by_contra h
    let v : (Fin nfree → O) × ((i : Fin r) → O ⧸ O ∙ π ^ e i) := (fun _ ↦ 1, 0)
    obtain ⟨w, hw⟩ := Y.mkQ_surjective (b.symm v)
    obtain ⟨a, ha, hmem⟩ := w.property
    have zero : a • (b.symm v) = 0 := by
      rw [← hw, ← map_smul]
      exact (Submodule.Quotient.mk_eq_zero _).2 hmem
    have applied := congrArg (fun x ↦ (b x).1 ⟨0, Nat.pos_of_ne_zero h⟩) zero
    exact ha (by simpa [v] using applied)
  subst nfree
  have unitIdeal := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  refine ⟨r, e, positive, ⟨b ≪≫ₗ LinearEquiv.uniqueProd ≪≫ₗ LinearEquiv.piCongrRight ?_⟩⟩
  intro i
  apply Submodule.quotEquivOfEq
  rw [Ideal.submodule_span_eq, ← Ideal.span_singleton_pow, ← unitIdeal]

/-- Every finite lattice has a finite list of positive loss exponents governing all its
reductions. The list exists before a precision is chosen. -/
theorem exists_loss_profile {π : O} (hπ : Irreducible π) :
    ∃ (r : ℕ) (e : Fin r → ℕ), (∀ i, 0 < e i) ∧ ∀ k : ℕ,
      New.relLength (New.obeying (New.relationsOn Z) (New.QuotSpan (π^k)))
        (Z.map (reduction (π^k))) = ∑ i, min k (e i) := by
  obtain ⟨r, e, pos, ⟨f⟩⟩ := exists_defect_type Z hπ
  exact ⟨r, e, pos, fun k ↦ precision_profile Z f hπ.ne_zero
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ).symm k⟩

end Hearthline.RelationLattices
