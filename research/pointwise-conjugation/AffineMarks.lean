import Triangle

noncomputable section
namespace Hearthline.ThreeMarks
open LinearMap

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

/-- The affine interpolation problem on the three marked inputs. The linear part is an
actual map on the entire coordinate plane. -/
def AffineExtension (m : R) (y : Fin 3 → W) : Prop :=
  ∃ b : W, ∃ T : R × R →ₗ[R] W, ∀ i, b + T (mark m i) = y i

/-- The first two marks determine the translation and first column; the third asks for
division of its displacement by m inside the target module. -/
theorem affine_extension_iff (m : R) (y : Fin 3 → W) :
    AffineExtension m y ↔ ∃ v : W, m • v = y 2 - y 0 := by
  constructor
  · rintro ⟨b, T, h⟩
    have zeroMark : mark m 0 = 0 := rfl
    have hb : b = y 0 := by simpa only [zeroMark, map_zero, add_zero] using h 0
    have last : b + m • T (0, 1) = y 2 := by
      simpa [← map_smul, mark] using h 2
    exact ⟨T (0,1), by rw [← last, ← hb]; abel⟩
  · rintro ⟨v, hv⟩
    let T : R × R →ₗ[R] W :=
      ((LinearMap.id : R →ₗ[R] R).smulRight (y 1 - y 0)).comp (fst R R R) +
      ((LinearMap.id : R →ₗ[R] R).smulRight v).comp (snd R R R)
    refine ⟨y 0, T, fun i ↦ ?_⟩
    fin_cases i <;> simp [mark, T, hv]

private theorem mark_first (m : R) (i : Fin 3) :
    (mark m i).1 = if i = 1 then 1 else 0 := by fin_cases i <;> simp [mark]
private theorem mark_second (m : R) (i : Fin 3) :
    (mark m i).2 = m * (if i = 2 then 1 else 0) := by fin_cases i <;> simp [mark]

/-- Exactly which permutations of the three labels extend to affine maps of the ambient
plane. When m is a nonunit the vertex (1,0) must stay put. -/
theorem symmetry_iff (m : R) (s : Equiv.Perm (Fin 3)) :
    AffineExtension m (mark m ∘ s) ↔ IsUnit m ∨ s 1 = 1 := by
  classical
  rw [affine_extension_iff]
  constructor
  · rintro ⟨v, hv⟩
    by_cases keep : s 1 = 1
    · exact Or.inr keep
    left
    have divides : m ∣ (mark m (s 2)).1 - (mark m (s 0)).1 :=
      ⟨v.1, (congrArg Prod.fst hv).symm⟩
    rw [mark_first, mark_first] at divides
    obtain ⟨i, hi⟩ := s.surjective 1
    fin_cases i
    · change s 0 = 1 at hi
      have ne₂ : s 2 ≠ 1 := fun he ↦ (by decide : (2:Fin 3) ≠ 0) (s.injective (he.trans hi.symm))
      exact isUnit_of_dvd_one (by simpa [hi, ne₂] using divides)
    · exact False.elim (keep hi)
    · change s 2 = 1 at hi
      have ne₀ : s 0 ≠ 1 := fun he ↦ (by decide : (0:Fin 3) ≠ 2) (s.injective (he.trans hi.symm))
      exact isUnit_of_dvd_one (by simpa [hi, ne₀] using divides)
  · rintro (⟨u, rfl⟩ | keep)
    · exact ⟨(↑(u⁻¹) : R) • ((mark (u : R) (s 2)) - (mark (u : R) (s 0))), by simp [smul_smul]⟩
    · have h0 : s 0 ≠ 1 := fun eq ↦ (by decide : (0:Fin 3) ≠ 1) (s.injective (eq.trans keep.symm))
      have h2 : s 2 ≠ 1 := fun eq ↦ (by decide : (2:Fin 3) ≠ 1) (s.injective (eq.trans keep.symm))
      refine ⟨(0, (if s 2 = 2 then 1 else 0) - (if s 0 = 2 then 1 else 0)), ?_⟩
      apply Prod.ext
      · simp [Function.comp_apply, mark_first, h0, h2]
      · simp [Function.comp_apply, mark_second, mul_sub]

/-- A bijective labeling always gives permutations on the observed range. -/
def rangeAction {I X : Type*} (f : I → X) (hf : Function.Injective f) :
    Equiv.Perm I →* Equiv.Perm (Set.range f) := (Equiv.permCongrHom (Equiv.ofInjective f hf)).toMonoidHom

/-- At modulus 289 the range still realizes all six permutations. Only the two fixing
the middle label extend affinely to the entire plane. -/
example : (Finset.univ.filter (fun s : Equiv.Perm (Fin 3) ↦ s 1 = 1)).card = 2 ∧
    Fintype.card (Equiv.Perm (Fin 3)) = 6 := by decide +kernel

example : ¬AffineExtension (17 : ZMod 289) (mark (17 : ZMod 289) ∘ Equiv.swap (1:Fin 3) 2) := by
  rw [symmetry_iff]
  refine not_or.2 ⟨fun h ↦ (by decide : ¬Nat.Coprime 17 289) ((ZMod.isUnit_iff_coprime 17 289).1 h), ?_⟩
  decide

end Hearthline.ThreeMarks
