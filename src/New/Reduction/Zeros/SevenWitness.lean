module

public import New.Reduction.Zeros.Criterion
import New.Reduction.Zeros.RefinedSelection

/-!
# The one-sided criterion in a search class that meets seven

Use one selected prime for the finite box and the fixed-prime comparison of zero orders.
Only class-seven primes coprime to the character level need a remainder estimate here.
-/

@[expose] public section

open Complex Filter Nat Real Topology

namespace New

theorem LFunction_ne_zero_of_seven_witness {N Q : ℕ} [NeZero N] [NeZero Q] {a : ℕ}
    (eight : 8 ∣ Q) (seven : a ≡ 7 [MOD 8]) (ha : a.Coprime Q) {β : ℝ} (hβ : 1 / 2 < β)
    (bound : ∀ d : Nat.Primes, (d : ℕ) ≡ a [MOD Q] →
      ∃ A : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d N x ≤ A * x ^ (β - 1))
    (ψ : DirichletCharacter ℂ N) {ρ : ℂ} (hρ₁ : ρ ≠ 1) (hρ : β < ρ.re) :
    ψ.LFunction ρ ≠ 0 := by
  obtain ⟨d, cls, h7, cop, good⟩ :=
    exists_seven_at_independent_level (N := N) eight seven ha hβ |ρ.im|
  obtain ⟨A, upper⟩ := bound d cls
  have no_orders (s : ℂ) (hs : β ≤ s.re) (ht : |s.im| ≤ |ρ.im|) :
      (∑ χ : DirichletCharacter ℂ N, analyticOrderNatAt (entireL (quadTwist χ d)) s) = 0 :=
    Finset.sum_eq_zero fun χ _ ↦ (analyticOrderNatAt_entireL_eq_zero_iff _ s).2 (good χ s hs ht)
  have equal := sum_entireL_orders_eq_twisted_of_primeRemainder_le h7 cop
    (by linarith : 0 < β) upper (fun x hx _ ↦ by
      rw [no_orders x hx.le (by simp)]
      exact Nat.zero_le _) hρ
  rw [no_orders ρ hρ.le le_rfl] at equal
  exact (entireL_ne_zero_iff ψ hρ₁).1 <| (analyticOrderNatAt_entireL_eq_zero_iff ψ ρ).1
    (Finset.sum_eq_zero_iff.1 equal ψ (Finset.mem_univ ψ))

end New
