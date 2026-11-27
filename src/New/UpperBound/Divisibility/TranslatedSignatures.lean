module

public import New.UpperBound.Divisibility.PopulationFibers
import Mathlib.Tactic

/-!
# Moving the signed prime measurements through the whole tower orbit

The offset of a translated place is read by multiplying its unit representative. Four slots
per input type allow both count-preserving exchanges to survive all three probe shifts.
-/

@[expose] public section

open Finset NumberField ThreePrimeEnvelope ColoredSparse
namespace New.Data
variable {P : Parameters} (D : Data P)

/-- Multiplication of two lift representatives adds a cross term to the offset.
This computes the offset of each individual translated place. -/
theorem shifted_offset_at_place {k : ℕ} (hd : k*P.q₀ ∣ D.q₁) (t : ℕ)
    (z : D.Φ) (hz : z ∈ D.bPlaces) :
    (D.translateOffset t).negativeOffset (D.distinguishedLift t*z) ≡
      t+D.negativeOffset z+P.q₀*t*D.negativeOffset z [MOD k] := by
  classical
  let u := D.negativeOffset z
  let moved := D.distinguishedLift t*z
  let r := (D.translateOffset t).negativeOffset moved
  have mem : moved ∈ (D.translateOffset t).bPlaces :=
    mem_image.2 ⟨z,hz,rfl⟩
  have movedShape := (D.translateOffset t).negativePlace_eq_offset
    ((D.translateOffset t).placeClass_of_mem_bPlaces _ mem)
  have original := D.negativePlace_eq_offset (D.placeClass_of_mem_bPlaces _ hz)
  change D.distinguishedLift t*z = D.distinguishedLift r*D.placeOfInt (-1) at movedShape
  change z = D.distinguishedLift u*D.placeOfInt (-1) at original
  have same : D.distinguishedLift t * D.distinguishedLift u = D.distinguishedLift r := by
    apply mul_right_cancel (b := D.placeOfInt (-1))
    rw [mul_assoc,← original,movedShape]
  have v := congrArg (fun a ↦ (P.placeClass hd a : ZMod (k*P.q₀))) same
  simp only [map_mul,Units.val_mul,D.distinguishedLift_val] at v
  have natEq : ((1+P.q₀*r : ℕ): ZMod (k*P.q₀)) =
      ((1+P.q₀*(t+u+P.q₀*t*u) : ℕ) : ZMod (k*P.q₀)) := by
    calc _ = ((1+P.q₀*t:ℕ):ZMod (k*P.q₀))*((1+P.q₀*u:ℕ):ZMod (k*P.q₀)) := v.symm
      _ = _ := by push_cast;ring
  rw [ZMod.natCast_eq_natCast_iff,mul_comm k] at natEq
  exact (lifted_offsets_modEq (P := P) k _ _).1 natEq

end New.Data

namespace New.SixSignatures

/-- Offsets in the four slots that represent one occurrence of each of the six types. -/
def microRow (c : Fin 6) : Fin 4 → ℕ :=
  ![![0,0,0,0],![36,36,36,36],![24,24,60,60],![6,6,42,42],![10,46,28,64],![1,1,1,1]] c

def translatedSum (t : ℕ) (c : Fin 6) (i : Fin 3) : ℤ :=
  ∑ j : Fin 4, signAt (probePeriod i) (t+microRow c j+18480*t*microRow c j)

lemma translatedSum_periodic (t : ℕ) (c : Fin 6) (i : Fin 3) :
    translatedSum (t%72) c i = translatedSum t c i := by
  have p := Nat.mod_modEq t 72
  have period : ∀ i : Fin 3, 2*probePeriod i ∣ 72 := by decide
  apply sum_congr rfl
  intro j _
  exact signAt_congr ((p.add_right _).add ((p.mul_left _).mul_right _)) (period i)

set_option maxRecDepth 4096 in
lemma exchange_at_every_translation (t : ℕ) (i : Fin 3) :
    translatedSum t 0 i+translatedSum t 1 i = 2*translatedSum t 2 i ∧
    translatedSum t 2 i+translatedSum t 3 i = 2*translatedSum t 4 i := by
  have table : ∀ t : Fin 72, ∀ i : Fin 3,
      translatedSum t 0 i+translatedSum t 1 i = 2*translatedSum t 2 i ∧
      translatedSum t 2 i+translatedSum t 3 i = 2*translatedSum t 4 i := by decide
  simpa only [translatedSum_periodic] using table ⟨t%72,Nat.mod_lt _ (by decide)⟩ i

/-- A linear measurement on six bins factors through the report if it respects its two
generating exchanges. -/
theorem weighted_sum_eq_of_exchanges {a b : Fin 6 → ℤ} (eq : report a=report b) (F : Fin 6 → ℤ)
    (ab : F 0+F 1=2*F 2) (ec : F 2+F 3=2*F 4) : ∑ c, a c * F c = ∑ c, b c * F c := by
  obtain ⟨t,u,h₀,h₁,h₂,h₃,h₄,h₅⟩ := (same_report_iff _ _).1 eq
  simp [Fin.sum_univ_succ,h₀,h₁,h₂,h₃,h₄,h₅]
  linear_combination -t * ab - u * ec

/-- Equal ordinary integer reports have the same three signed sums at every shift for
this four-slot encoding. -/
theorem score_eq_all_shifts {a b : Fin 6 → ℤ} (eq : report a=report b) (s : ℕ) (i : Fin 3) :
    ∑ c, a c * translatedSum s c i = ∑ c, b c * translatedSum s c i :=
  weighted_sum_eq_of_exchanges eq _ (exchange_at_every_translation s i).1 (exchange_at_every_translation s i).2

end New.SixSignatures
