module

public import Lib.Weil.Construction.ThetaPhaseBasis
import Mathlib.Tactic

/-!
# Which phase observations determine a theta function?

A change of representatives may rescale a basis vector. The selector itself
depends only on the class. An arbitrary set of selector locations determines
all the actual theta functions exactly when it meets every class.
-/

@[expose] public section

open NumberField Complex Pointwise Set Finset
namespace New.ThetaCoordinates

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
local notation "𝓕" => ((InfinitePlace E × n → ℂ) → ℂ)

/-- Scalar incurred in changing the lift v to v + l in the basis convention
T_(-v). Its modulus is one. -/
noncomputable def liftPhase (v l : n → E) : ℂ :=
  stdLattice.semichar (finiteImage (-l)) * Complex.exp (Real.pi * I * ratRiemannForm (-v) (-l))

omit [DecidableEq n] in
theorem norm_liftPhase (v l : n → E) : ‖liftPhase v l‖ = 1 := by
  rw [liftPhase, norm_mul, (stdLattice.isOfFinOrder_semichar _).norm_eq_one, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

omit [DecidableEq n] in
theorem change_translate_lift {F : 𝓕} (hF : IsThetaFunction (idealLattice E n) F)
    (v : n → E) {l : n → E} (hl : l ∈ idealLattice E n) :
    liftPhase v l • ratShift (-(v + l)) F = ratShift (-v) F := by
  have shift := congrArg (ratShift (-v)) (hF.signedShift_eq (-l) (neg_mem hl))
  rw [signedShift_apply, map_smul, ratShift_ratShift, smul_smul] at shift
  simpa only [liftPhase, neg_add] using shift

variable {δ : E} {N : ℕ} {Y Γ : Type} [Fintype Y] [Fintype Γ] {y : Y → n → E} {γ : Γ → n → E}

theorem moving_together {u v t : n → E} (hu : u ∈ δ⁻¹ • idealLattice E n)
    (hv : v ∈ δ⁻¹ • idealLattice E n) (ht : t ∈ δ⁻¹ • idealLattice E n) (dn : δ ≠ 0)
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    {F : 𝓕} (hF : IsThetaFunction (idealLattice E n) F) (ne : F ≠ 0) :
    selector γ (u + t) (ratShift (-(v + t)) F) = 0 ↔ selector γ u (ratShift (-v) F) = 0 := by
  classical
  rw [selector_translate (add_mem hu ht) (add_mem hv ht) dn hγ hF, selector_translate hu hv dn hγ hF,
    add_sub_add_right_eq_sub]
  by_cases e : u - v ∈ idealLattice E n
  · simp only [ite_eq_left e]
    exact iff_of_false (smul_ne_zero (characterCount_ne_zero hγ) (translate_ne_zero ne (v + t)))
      (smul_ne_zero (characterCount_ne_zero hγ) (translate_ne_zero ne v))
  · simp [e]

/-- Repeated measurements carry one class. A family with any index type, including
an empty family, determines every theta function precisely when its locations
cover the quotient. -/
theorem injective_readings_iff_cover {A : Type*} (u : A → n → E)
    (hu : ∀ a, u a ∈ δ⁻¹ • idealLattice E n)
    (hy : IsRepresentativeSystem y (δ⁻¹ • idealLattice E n) (idealLattice E n))
    (hγ : IsRepresentativeSystem γ (idealLattice E n) (star δ • idealLattice E n))
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN : N ≠ 0) (norm : δ * star δ = N) :
    Function.Injective (fun F : thetaFunctions (star δ • idealLattice E n) ↦ fun a ↦ selector γ (u a) (F : 𝓕)) ↔
      ∀ k : Y, ∃ a : A, u a - y k ∈ idealLattice E n := by
  classical
  let V := stdSpace E n
  have dn := ne_zero_of_mul_star_eq hN norm
  have hVac := V.isThetaFunction_vacElem
  have nzVac := V.entireTheta_vacElem_ne_zero
  constructor
  · intro inj k
    by_contra! missing
    let f := vacuumTranslate V (y k)
    have fm : f ∈ thetaFunctions (star δ • idealLattice E n) := vacuumTranslate_mem V (hy.mem k) hδ dn
    let H := thetaFunctions (star δ • idealLattice E n)
    have e : (fun a ↦ selector γ (u a) f) = fun a ↦ selector γ (u a) ((0 : H) : 𝓕) := by
      funext a
      simp only [f, vacuumTranslate, selector_translate (hu a) (hy.mem k) dn hγ hVac, missing a, ite_false,
        ZeroMemClass.coe_zero, map_zero]
    have equal : (⟨f, fm⟩ : H) = 0 := inj e
    exact (translate_ne_zero nzVac (y k)) (congrArg Subtype.val equal)
  · intro covers F G data_eq
    let H := thetaFunctions (star δ • idealLattice E n)
    have mem : (F : 𝓕) - (G : 𝓕) ∈ H := H.sub_mem F.property G.property
    obtain ⟨c, hc, _⟩ := existsUnique_coordinates V hy hγ hδ hN norm mem
    have zero (k : Y) : c k = 0 := by
      obtain ⟨a, hit⟩ := covers k
      have same := (selector_eq_iff (hu a) (hy.mem k) dn hγ hVac nzVac).2 hit
      have eq := congrFun data_eq a
      change selector γ (u a) (F : 𝓕) = selector γ (u a) (G : 𝓕) at eq
      rw [same] at eq
      have eq₀ : selector γ (y k) ((F : 𝓕) - (G : 𝓕)) = 0 := by rw [map_sub, eq, sub_self]
      rw [← hc] at eq₀
      change selector γ (y k) (∑ i, c i • ratShift (-y i) (Space.entireTheta V.vacElem)) = 0 at eq₀
      rw [selector_sum hy hγ dn hVac] at eq₀
      exact (smul_eq_zero.1 eq₀).resolve_right (smul_ne_zero (characterCount_ne_zero hγ) (translate_ne_zero nzVac _))
    have vanished : (F : 𝓕) - (G : 𝓕) = 0 := hc.symm.trans (by simp [zero])
    exact Subtype.ext (sub_eq_zero.1 vanished)

end New.ThetaCoordinates
