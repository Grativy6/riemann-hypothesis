import IntegralEnvelope
import New.Congruences.Selmer.SelmerData

noncomputable section
open Module Submodule New New.Selmer

namespace Hearthline.RelationLattices

/-- For the maintained Selmer datum the local equation space has exactly the bound used by
the caller. Any slack is the colength of the image of restriction in that equation space. -/
theorem local_restriction_balance {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E] {S₀ : Finset (FinPlace E)}
    {g₀ : Gal(Ω/E)} {O n : Type} [CommRing O] [PadicIntegerRing O ℓ] [Fintype n] [DecidableEq n]
    (T : SelmerDatum ℓ S₀ g₀ O n) {a : O} (ha : a ≠ 0) (w : placesDividing E ℓ) :
    let G := localCocycles T.ρ T.localRelations (placeOver w.val) (QuotSpan a)
    let W := obeying (relationsOn (T.Z w)) (QuotSpan a)
    length O G + relLength W G = finrank O (T.Z w) * length O (QuotSpan a) := by
  intro G W
  have : Module.Finite O (T.Z w) := T.finite_Z w
  have inc : G ≤ W := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨_, _, h, _⟩ := mem_selmerModule_iff.1 hz
    exact T.mem_obeying_localRelations_iff.1 h w
  calc
    length O G + relLength W G = length O W := by
      have split := relLength_add_length_inf W G
      rw [inf_eq_right.2 inc, add_comm] at split
      exact split
    _ = _ := length_readings (T.Z w) ha

end Hearthline.RelationLattices
