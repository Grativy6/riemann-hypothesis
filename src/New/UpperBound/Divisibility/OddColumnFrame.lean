module

public import New.UpperBound.Divisibility.FlatColumnProfiles
import Lib.Analytic.Primes
import Mathlib.Tactic

/-!
# An odd number of copies of every slot

The fifth-power estimate leaves enough room to delete at most one complete group before
choosing the level. This arranges odd multiplicity at all eight addresses of a uniform column.
-/

@[expose] public section
open Finset Filter NumberField Real ColoredSparse ThreePrimeEnvelope
namespace New.Data.CollisionPrimeExample

lemma trim_column_to_odd {s : ℕ} {B : Finset (params.Φ s)} {W : ℝ}
    (hW : 4≤W) (budget : (towerDeg s:ℝ) ≤ 2*(#B:ℝ)*W^5)
    (pop : HasPopulation originColumn s B (fun _ : Fin 8 ↦ 1)) :
    ∃ U ⊆ B, (towerDeg s:ℝ) ≤ #U*W^6 ∧ HasPopulation originColumn s U (fun _ : Fin 8 ↦ 1) ∧
      Odd (#U/8) := by
  classical
  let word := fun _ : Fin 8 ↦ (1:ℕ)
  obtain ⟨hd,k,hk,f,Bshape,addr⟩ := pop
  let j := 2*((k-1)/2)+1
  have jp : 0<j := by dsimp [j];omega
  have jk : j≤k := by dsimp [j];omega
  have kj : k≤2*j := by dsimp [j];omega
  let keep : Sample j word ↪ Sample k word :=
    ⟨fun x ↦ (⟨x.1.val,x.1.isLt.trans_le jk⟩,x.2), fun a b h ↦ Prod.ext
      (Fin.ext (congrArg (fun z : Sample k word ↦ z.1.val) h))
      (congrArg (fun z : Sample k word ↦ z.2) h)⟩
  let selected := keep.trans f
  let U := univ.map selected
  have total : (∑ i,word i)=8 := by decide
  have cu : #U=8*j := by
    change #(univ.map selected)=_
    rw [card_map,card_univ,sample_card,total,mul_comm]
  have cb : #B=8*k := by
    rw [Bshape,card_map,card_univ,sample_card]
    change k*(∑ i,word i)=_
    rw [total,mul_comm]
  have ratio : 2*(#B:ℝ) ≤ 4*(#U:ℝ) := by exact_mod_cast (show 2*#B≤4*#U by omega)
  refine ⟨U,?_,?_,⟨hd,j,jp,selected,rfl,fun a ↦ addr (keep a)⟩,?_⟩
  · intro z hz
    obtain ⟨a,_,rfl⟩ := mem_map.1 hz
    rw [Bshape]
    exact mem_map.2 ⟨keep a,mem_univ _,rfl⟩
  · calc (towerDeg s:ℝ) ≤ 2*(#B:ℝ)*W^5 := budget
      _ ≤ (4*(#U:ℝ))*W^5 := mul_le_mul_of_nonneg_right ratio (by positivity)
      _ = (#U:ℝ)*(4*W^5) := by ring
      _ ≤ (#U:ℝ)*(W*W^5) := by gcongr
      _ = _ := by ring
  · rw [cu,Nat.mul_div_cancel_left _ (by decide : 0<8)]
    exact ⟨(k-1)/2,rfl⟩

/-- The parity is arranged before the level-window calculation, at every sufficiently
large integer scale. All later translations inherit that chosen level. -/
theorem eventually_odd_column :
    ∀ᶠ x : ℕ in atTop, ∃ D : Data params, D.natX=x ∧
      HasPopulation originColumn D.towerExp D.bPlaces (fun _ : Fin 8 ↦ 1) ∧ Odd (#D.bPlaces/8) := by
  let ε : ℝ := 1/200
  obtain ⟨n,large⟩ := params.exists_eventually_isLargeScale (ε := ε) (by norm_num [ε]) (by norm_num [ε])
  have four : 4 ∣ params.q₀*params.d := by decide
  have grow : Tendsto (fun x : ℕ ↦ (x:ℝ)^(ε/6)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [ε])).comp tendsto_natCast_atTop_atTop
  let word := fun _ : Fin 8 ↦ (1:ℕ)
  have total : (∑ i,word i)=8 := by decide
  have pos : 0<∑ i,word i := by rw [total];decide
  filter_upwards [large,grow.eventually (exists_prime_modEq_one_log_mem _ (n+7) four)] with x hx window
  let Q := fun (s : ℕ) (T : Finset (params.Φ s)) ↦ HasPopulation originColumn s T word ∧ Odd (#T/8)
  obtain ⟨m,r,s,b,B,g,α,N,β,adm,evidence⟩ :=
    hx.exists_isAdmissibleData_selecting (fun _ _ s T ↦ Q s T) window (by
      intro m r s hm hr pow hs hW upper
      have room : (∑ i,word i)≤m := by
        rw [total]
        have real : (8:ℝ)≤m := by linarith [Real.add_one_le_exp (Real.log x/2),hx.hundred_le]
        exact_mod_cast real
      obtain ⟨old,base,_,sparse,pop,_,margin⟩ := population_from_ranks_with_margin originColumn word pos
        (by linarith [hx.hundred_le]) hx.n_pos hm hr pow hs hW upper
        (by linarith [hx.mul_y_le_W]) hx.pow_le hx.mul_two_pow_le room
      obtain ⟨U,sub,dense,ok,odd⟩ := trim_column_to_odd
        (by linarith [hx.mul_y_le_W,hx.hundred_le]) margin pop
      exact ⟨U,fun z hz ↦ base z (sub hz),dense,sparse.mono sub,ok,odd⟩)
  obtain ⟨D,fields,_,_,_,preserve⟩ := adm.exists_hasFields_preserving Q hx
  exact ⟨D,fields.natX_eq,preserve.2 evidence⟩

end New.Data.CollisionPrimeExample
