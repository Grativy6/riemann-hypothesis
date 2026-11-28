import SaturationTest

noncomputable section
open Module Submodule New
namespace Hearthline.InfiniteReadings

variable (O : Type*) [CommRing O] [New.DVR O]

/-- Integral rows on a countable board that are eventually all zero. -/
def finiteRows : Submodule O (ℕ → Unit → O) where
  carrier := {z | ∃ B : ℕ, ∀ i ≥ B, z i () = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨max m n, fun i hi ↦ by simp [hm i ((le_max_left _ _).trans hi), hn i ((le_max_right _ _).trans hi)]⟩
  smul_mem' := by
    rintro a x ⟨m, hm⟩
    exact ⟨m, fun i hi ↦ by simp [hm i hi]⟩

/-- This lattice is saturated even though there is no uniform finite support bound. -/
theorem saturated {a : O} (ha : a ≠ 0) {z : ℕ → Unit → O} (hz : a • z ∈ finiteRows O) :
    z ∈ finiteRows O := by
  obtain ⟨B, h⟩ := hz
  exact ⟨B, fun i hi ↦ (mul_eq_zero.mp (h i hi)).resolve_left ha⟩

private def initialOnes (N : ℕ) (i : ℕ) (_ : Unit) : O := if i < N then 1 else 0
omit [New.DVR O] in
private theorem prefix_mem (N : ℕ) : initialOnes O N ∈ finiteRows O :=
  ⟨N, fun _ hi ↦ by simp [initialOnes, hi.not_gt]⟩

omit [New.DVR O] in
/-- At any proper modulus the constant reading 1 passes every integral matrix relation
and agrees with an integral lift on every finite prefix. It has no single lift of finite support. -/
theorem every_prefix_no_lift {a : O} (hn : ¬IsUnit a) :
    let w : ℕ → Unit → QuotSpan a := fun _ _ ↦ 1
    (∀ N : ℕ, ∃ z ∈ finiteRows O, ∀ i < N, RelationLattices.reduction a z i = w i) ∧
    w ∈ obeying (relationsOn (finiteRows O)) (QuotSpan a) ∧
    w ∉ (finiteRows O).map (RelationLattices.reduction a) := by
  classical
  intro w
  have prefix_reads (N i : ℕ) (h : i < N) : RelationLattices.reduction a (initialOnes O N) i = w i := by
    ext j
    change Ideal.Quotient.mk _ (if i < N then (1 : O) else 0) = 1
    simp [h]
  refine ⟨fun N ↦ ⟨initialOnes O N, prefix_mem O N, prefix_reads N⟩, ?_, ?_⟩
  · apply mem_obeying.2
    intro f hf
    let N := f.support.sup id + 1
    have hit (i : ℕ) (hi : i ∈ f.support) : i < N :=
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
    have eq : relEval (QuotSpan a) f w = relEval (QuotSpan a) f (RelationLattices.reduction a (initialOnes O N)) := by
      simp only [relEval_apply, Finsupp.sum]
      exact Finset.sum_congr rfl fun i hi ↦ by rw [prefix_reads N i (hit i hi)]
    exact eq.trans <| mem_obeying.1 (mkQ_mem_obeying_relationsOn (a := a) (initialOnes O N) (prefix_mem O N)) f hf
  · rintro ⟨z, ⟨N, hz⟩, eq⟩
    have v : Ideal.Quotient.mk (Ideal.span {a}) (z N ()) = 1 :=
      congrFun (congrFun eq N) ()
    have onezero : (1 : QuotSpan a) = 0 := by rw [← v, hz N le_rfl, map_zero]
    exact hn <| isUnit_of_dvd_one <| (Ideal.Quotient.eq_zero_iff_dvd a (1 : O)).1 (by simpa)

/-- The finite-generation hypothesis of the local lifting theorem has a concrete failure. -/
theorem not_finitely_generated {a : O} (ha : a ≠ 0) (hn : ¬IsUnit a) :
    ¬ Module.Finite O (finiteRows O) := by
  intro fin
  obtain ⟨_, all, missing⟩ := every_prefix_no_lift O hn
  exact missing (New.map_mkQ_eq_obeying_relationsOn (finiteRows O) ha
    (fun w hw ↦ saturated O ha hw) ▸ all)

end Hearthline.InfiniteReadings
