module

public import New.Reduction.Data.AdmissibleData
import Lib.General.NumberTheory.FirstReturn
import Mathlib.Tactic

/-!
# Concentrating a sparse set in one residue class

Above the negative base class there are at most k residues modulo k times the base modulus.
Take the largest fiber and translate it to the negative unit. The translation preserves all
ratios tested by sparseness.
-/

@[expose] public section

open Finset Real
namespace New.Parameters

/-- Deleting places preserves sparseness since every forbidden triple in the subset was already present. -/
lemma IsSparse.mono {P : Parameters} {s L : ℕ} {S T : Finset (P.Φ s)}
    (hs : P.IsSparse s L S) (ht : T ⊆ S) : P.IsSparse s L T := by
  intro l hl hb i j hi hij hj φ
  rintro ⟨σ, hσ, τ, hτ, ρ, hρ, e, e', h₁, h₂⟩
  exact hs l hl hb i j hi hij hj ⟨σ, ht hσ, τ, ht hτ, ρ, ht hρ, e, e', h₁, h₂⟩


/-- Translating all places together preserves every ratio in the sparseness condition. -/
lemma IsSparse.translate {P : Parameters} {s L : ℕ} {S : Finset (P.Φ s)}
    (hs : P.IsSparse s L S) (g : P.Φ s) : P.IsSparse s L (S.image (g * ·)) := by
  intro l hl hb i j hi hij hj φ
  rintro ⟨σ, hσ, τ, hτ, ρ, hρ, e, e', h₁, h₂⟩
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hσ
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hτ
  obtain ⟨z, hz, rfl⟩ := mem_image.1 hρ
  exact hs l hl hb i j hi hij hj ⟨x, hx, y, hy, z, hz, e, e',
    by simpa using h₁, by simpa using h₂⟩

/-- All places in the set reduce to minus one at the indicated multiple of the base modulus. -/
def NegOneFiber (P : Parameters) (s k : ℕ) (S : Finset (P.Φ s)) : Prop :=
  ∃ d : k * P.q₀ ∣ P.q₁ s, ∀ σ ∈ S, P.placeClass d σ = -1

lemma NegOneFiber.base {P : Parameters} {s k : ℕ} {S : Finset (P.Φ s)}
    (h : P.NegOneFiber s k S) {σ : P.Φ s} (hσ : σ ∈ S) :
    P.placeClass (P.q₀.dvd_mul_right (towerDeg s)) σ = -1 := by
  obtain ⟨d, h⟩ := h
  have hm : P.q₀ ∣ k * P.q₀ := dvd_mul_left _ _
  have reduce : ZMod.unitsMap hm (P.placeClass d σ) = P.placeClass (hm.trans d) σ :=
    DFunLike.congr_fun (ZMod.unitsMap_comp hm d) (P.placeMulEquiv s σ)
  rw [h σ hσ] at reduce
  apply Units.ext
  simpa [ZMod.unitsMap_val] using (congrArg (fun z : (ZMod P.q₀)ˣ ↦ (z : ZMod P.q₀)) reduce.symm)

lemma NegOneFiber.mono {P : Parameters} {s k : ℕ} {S T : Finset (P.Φ s)}
    (h : P.NegOneFiber s k S) (ht : T ⊆ S) : P.NegOneFiber s k T := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, fun σ hσ ↦ hd σ (ht hσ)⟩

/-- Take the largest residue fiber above the negative base class and translate it to the
specified negative unit. This retains at least one kth of the original set. -/
theorem focus_sparse_negative_unit (P : Parameters) {s L k : ℕ} [NeZero k]
    (hk : k ∣ towerDeg s) {S : Finset (P.Φ s)} (pos : S.Nonempty)
    (hclass : ∀ σ ∈ S, P.placeClass (P.q₀.dvd_mul_right (towerDeg s)) σ = -1)
    (hs : P.IsSparse s L S) :
    ∃ T : Finset (P.Φ s), #S ≤ k * #T ∧ P.IsSparse s L T ∧ P.NegOneFiber s k T := by
  classical
  have hd : k * P.q₀ ∣ P.q₁ s := by
    rw [mul_comm k]
    exact Nat.mul_dvd_mul_left _ hk
  have hm : P.q₀ ∣ k * P.q₀ := dvd_mul_left _ _
  let read := P.placeClass hd
  let v := fun σ : P.Φ s ↦ (read σ : ZMod (k*P.q₀))
  let V := univ.filter (fun r : ZMod (k*P.q₀) ↦ ZMod.castHom hm (ZMod P.q₀) r = -1)
  have cap : #V = k := Nat.eq_of_mul_eq_mul_right (NeZero.pos P.q₀)
    (ReturnQuotient.card_cast_fiber_mul hm (-1))
  have maps (σ : P.Φ s) (hσ : σ ∈ S) : v σ ∈ V := by
    apply mem_filter.2 ⟨mem_univ _, ?_⟩
    have reduce : ZMod.unitsMap hm (read σ) = P.placeClass (hm.trans hd) σ :=
      DFunLike.congr_fun (ZMod.unitsMap_comp hm hd) (P.placeMulEquiv s σ)
    have eq : ZMod.unitsMap hm (read σ) = -1 := reduce.trans (hclass σ hσ)
    simpa [ZMod.unitsMap_val, ZMod.castHom_apply, v] using
      congrArg (fun z : (ZMod P.q₀)ˣ ↦ (z : ZMod P.q₀)) eq
  obtain ⟨w, hw⟩ := pos
  obtain ⟨r, _, maximal⟩ := V.exists_max_image (fun r ↦ #(S.filter fun σ ↦ v σ = r)) ⟨v w, maps w hw⟩
  let U := S.filter (fun σ ↦ v σ = r)
  have size : #S ≤ k * #U := calc
    #S = ∑ r ∈ V, #(S.filter fun σ ↦ v σ = r) := card_eq_sum_card_fiberwise maps
    _ ≤ ∑ _ ∈ V, #U := sum_le_sum fun x hx ↦ maximal x hx
    _ = _ := by simp [cap]
  have upos : 0 < #U := by
    by_contra! hu
    rw [Nat.eq_zero_of_le_zero hu, Nat.mul_zero] at size
    exact (card_pos.2 ⟨w,hw⟩).not_ge size
  obtain ⟨τ,hτ⟩ := card_pos.1 upos
  let anchor := P.placeOfInt s (-1)
  let g := anchor / τ
  have same (σ : P.Φ s) (hσ : σ ∈ U) : read σ = read τ :=
    Units.ext ((mem_filter.1 hσ).2.trans (mem_filter.1 hτ).2.symm)
  have mark : read anchor = -1 := Units.ext (by
    simpa [read, anchor] using (P.placeClass_placeOfInt (s := s) (ν := -1) (h_dvd := hd) (show IsCoprime (-1 : ℤ) P.q₀ from ⟨-1, 0, by ring⟩)))
  refine ⟨U.image (g*·), ?_, (hs.mono (filter_subset _ _)).translate g, hd, ?_⟩
  · rw [card_image_of_injective U (show Function.Injective (fun z : P.Φ s ↦ g*z) from fun _ _ heq ↦ mul_left_cancel heq)]
    exact size
  · intro σ hσ
    obtain ⟨z,hz,rfl⟩ := mem_image.1 hσ
    change read (g*z) = -1
    simp [g, map_div, same z hz, mark]

end New.Parameters

namespace New.Data

variable {P : Parameters}

/-- Translate the high places and their attached weights by the same base-trivial unit.
The level window only sees the sum of the logarithms of the weights, so the very same chosen
level prime and norm generators fit the translated data. -/
noncomputable def translateHighPlaces (D : Data P) (g : D.Φ)
    (hg : P.placeClass (P.q₀.dvd_mul_right (towerDeg D.towerExp)) g = 1) : Data P := by
  classical
  let S := D.bPlaces.image (fun τ ↦ g*τ)
  have cardS : #S = #D.bPlaces :=
    card_image_of_injective _ (show Function.Injective (fun z : D.Φ ↦ g*z) from fun _ _ eq ↦ mul_left_cancel eq)
  have memS (σ : D.Φ) : σ ∈ S ↔ g⁻¹ * σ ∈ D.bPlaces := by
    constructor
    · intro h
      obtain ⟨τ,hτ,rfl⟩ := mem_image.1 h
      simpa using hτ
    · intro h
      exact mem_image.2 ⟨g⁻¹ * σ,h,by simp⟩
  have logs : (∑ τ : D.Φ, log (D.weight (g⁻¹*τ))) = ∑ τ : D.Φ, log (D.weight τ) :=
    Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun τ : D.Φ ↦ log (D.weight τ))
  exact { D with
    bPlaces := S
    weight := fun σ ↦ D.weight (g⁻¹*σ)
    placeClass_of_mem_bPlaces := by
      intro σ hσ
      obtain ⟨τ,hτ,rfl⟩ := mem_image.1 hσ
      rw [map_mul, hg, one_mul]
      exact D.placeClass_of_mem_bPlaces _ hτ
    towerDeg_le_card_bPlaces_mul := by rw [cardS]; exact D.towerDeg_le_card_bPlaces_mul
    sparse := D.sparse.translate g
    weight_eq := by intro σ; simp only [D.weight_eq, memS σ]
    log_N_mem := by simpa only [Parameters.logLevelMin, logs] using D.log_N_mem }

/-- The translation preserves the number of high places as well as all scalar fields of the data. -/
lemma card_translateHighPlaces (D : Data P) (g : D.Φ) (hg) :
    #(D.translateHighPlaces g hg).bPlaces = #D.bPlaces :=
  card_image_of_injective _ (show Function.Injective (fun z : D.Φ ↦ g*z) from fun _ _ eq ↦ mul_left_cancel eq)

/-- Every sum that reads a place only by its weight is invariant under the translation.
Choosing singleton multisets as the readout preserves the whole multiset of weights. -/
theorem translateHighPlaces_weight_sum {A : Type*} [AddCommMonoid A] (D : Data P) (g : D.Φ)
    (hg) (F : ℕ → A) :
    ∑ τ : D.Φ, F ((D.translateHighPlaces g hg).weight τ) = ∑ τ : D.Φ, F (D.weight τ) :=
  Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun τ : D.Φ ↦ F (D.weight τ))

end New.Data
