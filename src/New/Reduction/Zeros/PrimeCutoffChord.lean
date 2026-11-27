module

public import New.Reduction.Zeros.PrimeCutoffRamps
import Mathlib.Tactic

/-!
# Upper interpolation between two cutoffs

Only the known logarithmic centring can lift the value above a common endpoint bound.
Its tangent inequality costs the product of the distances to the two endpoints.
-/

@[expose] public section

open Nat Real
namespace New.PrimeCutoff

/-- The linear tangent inequality for log bounds the precise logarithmic correction
by the product of the two endpoint distances. -/
lemma log_chord_drift {a b y x z : ℝ} (hy : 0<y) (ha : 0≤a) (hb : 0≤b)
    (weights : a+b=1) (mix : a*y+b*z=x) (left : y≤x) (right : x≤z) :
    a*y*Real.log (y/x)+b*z*Real.log (z/x) ≤ (x-y)*(z-x)/x := by
  have hx := hy.trans_le left
  have hz := hx.trans_le right
  have tangent (v : ℝ) (hv : 0<v) : Real.log (v/x) ≤ (v-x)/x := by
    calc _ ≤ v/x-1 := Real.log_le_sub_one_of_pos (div_pos hv hx)
      _ = _ := by field
  have variance : a*y*(y-x)+b*z*(z-x)=(x-y)*(z-x) := by
    linear_combination (y+z-x)*mix - y*z*weights
  calc _ ≤ a*y*((y-x)/x)+b*z*((z-x)/x) :=
        add_le_add (mul_le_mul_of_nonneg_left (tangent y hy) (mul_nonneg ha hy.le))
          (mul_le_mul_of_nonneg_left (tangent z hz) (mul_nonneg hb hz.le))
    _ = (a*y*(y-x)+b*z*(z-x))/x := by ring
    _ = _ := by rw [variance]

/-- A common upper bound at two cutoffs extends throughout the gap at quadratic
cost. Only nonnegative weights and the explicit logarithmic centring enter. -/
theorem remainder_le_of_endpoint_bounds {d q : ℕ} [Fact d.Prime] [NeZero q] {y x z M : ℝ}
    (hy : 0<y) (left : y≤x) (right : x≤z) (endpoint : y<z)
    (first : primeRemainder d q y ≤ M) (last : primeRemainder d q z ≤ M) :
    primeRemainder d q x ≤ M + (x-y)*(z-x)/(x^2*q.totient) := by
  let a := (z-x)/(z-y)
  let b := (x-y)/(z-y)
  have hx := hy.trans_le left
  have hz := hx.trans_le right
  have gap := sub_pos.2 endpoint
  have ha : 0≤a := div_nonneg (sub_nonneg.2 right) gap.le
  have hb : 0≤b := div_nonneg (sub_nonneg.2 left) gap.le
  have weights : a+b=1 := by dsimp [a,b]; field
  have mix : a*y+b*z=x := by dsimp [a,b]; field
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have chord := integrated_le_chord (d:=d) (q:=q) hy ha hb weights mix left right
  have accounting : a*integrated d q y + b*integrated d q z - integrated d q x =
      a*y*(primeRemainder d q y-M) + b*z*(primeRemainder d q z-M) - x*(primeRemainder d q x-M)
       + (a*y*Real.log (y/x) + b*z*Real.log (z/x))/q.totient := by
    rw [Real.log_div hy.ne' hx.ne',Real.log_div hz.ne' hx.ne']
    unfold integrated
    linear_combination ((logDerivMean d q 1).re + M + Real.log x/q.totient)*mix
  have upper : x*(primeRemainder d q x-M) ≤ (a*y*Real.log (y/x)+b*z*Real.log (z/x))/q.totient := by
    linarith only [accounting,chord,
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hy.le) (sub_nonpos.2 first),
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hb hz.le) (sub_nonpos.2 last)]
  have bound := upper.trans (div_le_div_of_nonneg_right (log_chord_drift hy ha hb weights mix left right) hφ.le)
  apply sub_le_iff_le_add'.1
  calc primeRemainder d q x-M ≤ ((x-y)*(z-x)/x/q.totient)/x :=
        (le_div_iff₀ hx).2 (by rwa [mul_comm])
    _ = _ := by field

end New.PrimeCutoff
