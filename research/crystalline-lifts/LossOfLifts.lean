import IntegralEnvelope

noncomputable section
open Module LinearMap Submodule
namespace Hearthline.RelationLattices

variable {O Γ n : Type*} [CommRing O] [New.DVR O] [Fintype n] [DecidableEq n]
  (Z : Submodule O (Γ → n → O)) [Module.Finite O Z]

abbrev reduction (a : O) : (Γ → n → O) →ₗ[O] (Γ → n → New.QuotSpan a) :=
  (((Ideal.span {a}).mkQ.compLeft n).compLeft Γ)

abbrev defect := (saturation Z) ⧸ Z.submoduleOf (saturation Z)

/-- For every nonzero modulus, the quotient of the admissible readings by the ones that
actually lift is canonically the saturation defect reduced by the same modulus. Here it is
identified with its image in the ambient quotient of all readings by the liftable readings. -/
def quotientReadingsEquiv {a : O} (ha : a ≠ 0) :
    ↥((New.obeying (New.relationsOn Z) (New.QuotSpan a)).map (Z.map (reduction a)).mkQ) ≃ₗ[O]
      (defect Z) ⧸ (lsmul O (defect Z) a).range := by
  let S := saturation Z
  let Y := Z.submoduleOf S
  let A := Z.map (reduction a)
  let r := reduction a ∘ₗ S.subtype
  let f := A.mkQ ∘ₗ r
  have rrange : r.range = New.obeying (New.relationsOn Z) (New.QuotSpan a) := by
    rw [show r = reduction a ∘ₗ S.subtype from rfl, LinearMap.range_comp, range_subtype]
    exact read_saturation Z ha
  have frange : f.range = (New.obeying (New.relationsOn Z) (New.QuotSpan a)).map A.mkQ :=
    (LinearMap.range_comp r A.mkQ).trans (by rw [rrange])
  have Ymap : Y.map r = A := by
    change Y.map (reduction a ∘ₗ S.subtype) = A
    rw [Submodule.map_comp, map_subtype_submoduleOf, inf_eq_left.2 (le_saturation Z)]
  let T := (lsmul O S a).range
  have rker : r.ker = T := by
    ext z
    constructor
    · intro hz
      have hdiv (g : Γ) (j : n) : a ∣ z.val g j :=
        (Ideal.Quotient.eq_zero_iff_dvd a _).1 (congrFun (congrFun hz g) j)
      choose y h using hdiv
      have eq : z.val = a • y := funext fun g ↦ funext (h g)
      exact ⟨⟨y, divide_in_saturation ha y (eq ▸ z.property)⟩, Subtype.ext eq.symm⟩
    · rintro ⟨w, rfl⟩
      exact funext fun g ↦ funext fun j ↦ (Ideal.Quotient.eq_zero_iff_dvd a _).2 ⟨w.val g j, rfl⟩
  have fker : f.ker = Y ⊔ T := by
    rw [show f = A.mkQ ∘ₗ r from rfl, LinearMap.ker_comp, ker_mkQ, ← Ymap, comap_map_eq, rker]
  have scalar_range : T.map Y.mkQ = (lsmul O (defect Z) a).range := by
    ext v
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨Y.mkQ u, (map_smul Y.mkQ a u).symm⟩
    · rintro ⟨u, rfl⟩
      obtain ⟨w, rfl⟩ := Y.mkQ_surjective u
      exact ⟨a • w, ⟨w, rfl⟩, map_smul Y.mkQ a w⟩
  exact (LinearEquiv.ofEq _ _ frange.symm) ≪≫ₗ f.quotKerEquivRange.symm ≪≫ₗ
    quotEquivOfEq _ _ fker ≪≫ₗ (quotientQuotientEquivQuotientSup Y T).symm ≪≫ₗ
    quotEquivOfEq _ _ scalar_range

theorem length_lost {a : O} (ha : a ≠ 0) :
    New.relLength (New.obeying (New.relationsOn Z) (New.QuotSpan a)) (Z.map (reduction a)) =
      length O ((defect Z) ⧸ (lsmul O (defect Z) a).range) := by
  rw [New.relLength_eq_length_map_mkQ]
  exact (quotientReadingsEquiv Z ha).length_eq

end Hearthline.RelationLattices
