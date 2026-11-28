import CofinalSeven
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Units
import Mathlib.Tactic

open Nat Set Filter New ZMod TauCeti
open scoped Topology Classical
noncomputable section
namespace Hearthline.FiniteReadings

abbrev RingOfReadings := Additive zHat.{0}

/-- A closure test in the actual ring of profinite integers. A finite list of coordinates
can be read at their common multiple. Compactness supplies the reverse direction. -/
theorem closure_iff_coordinates (S : Set RingOfReadings) (x : RingOfReadings) :
    x ∈ closure S ↔ ∀ m : ℕ+, ∃ y ∈ S, zHat.toZMod m y = zHat.toZMod m x := by
  constructor
  · intro hx m
    let U := (zHat.toZMod m : RingOfReadings → ZMod m) ⁻¹' {zHat.toZMod m x}
    have op : IsOpen U := (zHat.continuous_toZMod m).isOpen_preimage _ (isOpen_discrete _)
    obtain ⟨y, hy, hs⟩ := (mem_closure_iff.1 hx) U op (by simp [U])
    exact ⟨y, hs, hy⟩
  · intro readings
    let C := closure S
    have : CompactSpace C := isCompact_iff_compactSpace.1 (isClosed_closure.isCompact : IsCompact C)
    obtain ⟨y, hy⟩ := zHat.exists_eq_of_forall_exists_toZMod_eq
      (continuous_subtypeVal : Continuous (Subtype.val : C → RingOfReadings)) x (fun m ↦ by
        obtain ⟨q, hq, eq⟩ := readings m
        exact ⟨⟨q, subset_closure hq⟩, eq⟩)
    exact hy ▸ y.prop

private lemma reduce {n m : ℕ+} (h : (m : ℕ) ∣ (n : ℕ)) {d : ℕ} {x : RingOfReadings}
    (hd : (d : ZMod n) = zHat.toZMod n x) : (d : ZMod m) = zHat.toZMod m x := by
  calc (d : ZMod m) = ZMod.castHom h (ZMod m) (d : ZMod n) := (map_natCast _ d).symm
       _ = zHat.toZMod m x := by rw [hd]; exact zHat.cast_toZMod h x

def Good (N : ℕ) [NeZero N] (β H : ℝ) (d : Nat.Primes) : Prop :=
  (d : ℕ) % 8 = 7 ∧ N.Coprime d ∧ ∀ (χ : DirichletCharacter ℂ N) (s : ℂ),
    β ≤ s.re → |s.im| ≤ H → entireL (quadTwist χ d) s ≠ 0

def primePoints (N : ℕ) [NeZero N] (β H : ℝ) : Set RingOfReadings :=
  {x | ∃ d : Nat.Primes, Good N β H d ∧ ((d : ℕ) : RingOfReadings) = x}

def unitSeven : Set RingOfReadings := {x | IsUnit x ∧ zHat.toZMod 8 x = 7}

/-- Every finite coordinate of a unit in the seven cylinder is realized by an arbitrarily
large actual good prime. -/
theorem match_unit {N : ℕ} [NeZero N] {β : ℝ} (hβ : 1/2 < β) (H : ℝ) {x : RingOfReadings}
    (hx : x ∈ unitSeven) (m : ℕ+) (B : ℕ) :
    ∃ d : Nat.Primes, B < (d : ℕ) ∧ Good N β H d ∧ ((d : ℕ) : ZMod m) = zHat.toZMod m x := by
  let L : ℕ+ := m * 8
  let a := (zHat.toZMod L x).val
  have rep : (a : ZMod L) = zHat.toZMod L x := ZMod.natCast_zmod_val _
  have unit : a.Coprime (L : ℕ) := (ZMod.isUnit_iff_coprime a L).1 (rep ▸ hx.1.map (zHat.toZMod L))
  have h8 : (8 : ℕ) ∣ (L : ℕ) := dvd_mul_left 8 (m : ℕ)
  have seven : a ≡ 7 [MOD 8] := (ZMod.natCast_eq_natCast_iff a 7 8).1
    ((reduce (m := (8 : ℕ+)) (n := L) h8 rep).trans hx.2)
  obtain ⟨d, large, cls, sev, cop, good⟩ := exists_seven_twist_in_class (N := N) unit
    (seven.of_dvd (Nat.gcd_dvd_right _ _)) hβ H B
  have hit : ((d : ℕ) : ZMod L) = zHat.toZMod L x :=
    ((ZMod.natCast_eq_natCast_iff d a L).2 cls).trans rep
  exact ⟨d, large, ⟨sev,cop,good⟩, reduce (dvd_mul_right (m : ℕ) 8) hit⟩

/-- The closure is the actual isolated prime points together with precisely the class-seven
profinite units. A nonunit reading can only belong to the one ordinary prime that divides it. -/
theorem exact_closure (N : ℕ) [NeZero N] {β : ℝ} (hβ : 1/2 < β) (H : ℝ) :
    closure (primePoints N β H) = primePoints N β H ∪ unitSeven := by
  ext x
  constructor
  · intro hx
    have sample (m : ℕ+) :
        ∃ d : Nat.Primes, Good N β H d ∧ ((d : ℕ) : ZMod m) = zHat.toZMod m x := by
      obtain ⟨y, ⟨d, good, rfl⟩, eq⟩ := (closure_iff_coordinates _ _).1 hx m
      exact ⟨d, good, by simpa only [map_natCast] using eq⟩
    by_cases unit : IsUnit x
    · apply Or.inr
      obtain ⟨d, good, eq⟩ := sample 8
      exact ⟨unit, eq.symm.trans ((ZMod.natCast_eq_natCast_iff d 7 8).2 good.1)⟩
    · apply Or.inl
      obtain ⟨m, bad⟩ : ∃ m : ℕ+, ¬IsUnit (zHat.toZMod m x) := by
        simpa only [zHat.isUnit_iff_toZMod, not_forall] using unit
      obtain ⟨p, good, readP⟩ := sample m
      have divisor : (p : ℕ) ∣ (m : ℕ) := by
        by_contra miss
        exact bad (readP ▸ (ZMod.isUnit_iff_coprime p m).2 (p.prop.coprime_iff_not_dvd.2 miss))
      refine ⟨p, good, zHat.ext_of_toZMod (fun n ↦ ?_)⟩
      obtain ⟨e, _, he⟩ := sample (m*n)
      have dm : ((e : ℕ) : ZMod m) = p :=
        (reduce (dvd_mul_right (m : ℕ) (n : ℕ)) he).trans readP.symm
      have pe : (p : ℕ) ∣ (e : ℕ) :=
        (((ZMod.natCast_eq_natCast_iff e p m).1 dm).dvd_iff divisor).2 (dvd_refl _)
      have same : e = p := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.prop e.prop).1 pe).symm
      rw [map_natCast, ← same]
      exact reduce (dvd_mul_left (n : ℕ) (m : ℕ)) he
  · rintro (actual | unit)
    · exact subset_closure actual
    · apply (closure_iff_coordinates _ _).2
      intro m
      obtain ⟨d, _, good, read⟩ := match_unit (N := N) hβ H unit m 0
      exact ⟨((d : ℕ) : RingOfReadings), ⟨d, good, rfl⟩, by simpa only [map_natCast] using read⟩

/-- A single prime-coordinate reading isolates each actual prime point from the full closure. -/
theorem zero_coordinate (N : ℕ) [NeZero N] {β : ℝ} (hβ : 1/2 < β) (H : ℝ) (p : Nat.Primes)
    (x : RingOfReadings) :
    (x ∈ closure (primePoints N β H) ∧ zHat.toZMod ⟨p.val, p.prop.pos⟩ x = 0) ↔
      x = (p.val : RingOfReadings) ∧ Good N β H p := by
  let m : ℕ+ := ⟨p.val, p.prop.pos⟩
  have : Fact m.val.Prime := ⟨p.prop⟩
  constructor
  · rintro ⟨hx, hz⟩
    rw [exact_closure N hβ H] at hx
    rcases hx with ⟨e, good, rfl⟩ | unit
    · rw [map_natCast] at hz
      have dvd := (ZMod.natCast_eq_zero_iff (e : ℕ) (p : ℕ)).1 hz
      have ep : e = p := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.prop e.prop).1 dvd).symm
      simpa only [ep] using And.intro (rfl : (e.val : RingOfReadings) = _) good
    · have hu : IsUnit (zHat.toZMod m x) := unit.1.map (zHat.toZMod m)
      have zero : zHat.toZMod m x = 0 := hz
      rw [zero] at hu
      exact False.elim (not_isUnit_zero hu)
  · rintro ⟨rfl, good⟩
    exact ⟨subset_closure ⟨p, good, rfl⟩, by rw [map_natCast]; exact ZMod.natCast_self p.val⟩


/-- A prescribed additional residue is an open and closed condition. It cuts both the
ordinary prime points and the unit limit points by exactly the same finite observation. -/
theorem closure_at_residue (N : ℕ) [NeZero N] {β : ℝ} (hβ : 1/2 < β) (H : ℝ)
    (m : ℕ+) (a : ZMod m) :
    closure (primePoints N β H ∩ {x | zHat.toZMod m x = a}) =
      (primePoints N β H ∪ unitSeven) ∩ {x | zHat.toZMod m x = a} := by
  let U : Set RingOfReadings := (zHat.toZMod m) ⁻¹' {a}
  have op : IsOpen U := (zHat.continuous_toZMod m).isOpen_preimage _ (isOpen_discrete _)
  have cl : IsClosed U := isClosed_singleton.preimage (zHat.continuous_toZMod m)
  rw [← exact_closure N hβ H]
  change closure (primePoints N β H ∩ U) = closure (primePoints N β H) ∩ U
  exact Set.Subset.antisymm (closure_minimal (fun y hy ↦ ⟨subset_closure hy.1, hy.2⟩)
    (isClosed_closure.inter cl)) op.closure_inter

theorem no_fixed_prime_passes_every_level (d : Nat.Primes) : ¬∀ m : ℕ+, m.val.Coprime d := by
  intro all
  have h := all ⟨d, d.prop.pos⟩
  exact d.prop.ne_one ((Nat.coprime_self d.val).1 h)

private def chain (pick : ℕ → ℕ → Nat.Primes) : ℕ → Nat.Primes
  | 0 => pick 0 0
  | n+1 => pick (n+1) (chain pick n).val

/-- A single increasing sequence approaches any prescribed unit in the seven cylinder.
For each fixed character level and fixed box to the right of one half, all sufficiently
late indices simultaneously supply zero-free twists for every character of that level. -/
theorem diagonal (x : RingOfReadings) (unit : x ∈ unitSeven) :
    ∃ seq : ℕ → Nat.Primes, StrictMono (fun n ↦ (seq n : ℕ)) ∧
      Tendsto (fun n ↦ ((seq n : ℕ) : RingOfReadings)) atTop (𝓝 x) ∧
      ∀ (m : ℕ+) (β H : ℝ), 1/2 < β → ∀ᶠ n : ℕ in atTop, Good m β H (seq n) := by
  let level (n : ℕ) : ℕ+ := ⟨(n+1).factorial, Nat.factorial_pos _⟩
  let beta (n : ℕ) : ℝ := 1/2 + 1/((n : ℝ)+1)
  have offers (n B : ℕ) := match_unit (N := (level n : ℕ)) (β := beta n)
    (by dsimp only [beta]; linarith [show 0 < 1 / ((n:ℝ)+1) by positivity])
    ((n:ℝ)+1) unit (level n) B
  choose pick larger good reads using offers
  let seq := chain pick
  have rows (n : ℕ) : Good (level n) (beta n) ((n:ℝ)+1) (seq n) ∧
      ((seq n : ℕ) : ZMod (level n)) = zHat.toZMod (level n) x := by
    cases n with
    | zero => exact ⟨good 0 0, reads 0 0⟩
    | succ n => exact ⟨good (n+1) (seq n), reads (n+1) (seq n)⟩
  have coord (m : ℕ+) : ∀ᶠ n : ℕ in atTop, ((seq n : ℕ) : ZMod m) = zHat.toZMod m x := by
    filter_upwards [eventually_ge_atTop m.val] with n hn
    exact reduce (m := m) (n := level n) (Nat.dvd_factorial m.property (by omega : m.val ≤ n+1)) (rows n).2
  refine ⟨seq, strictMono_nat_of_lt_succ (fun n ↦ larger (n+1) (seq n)), ?_, ?_⟩
  · let f (z : RingOfReadings) := fun m : ℕ+ ↦ zHat.toZMod m z
    have cont : Continuous f := continuous_pi fun m ↦ zHat.continuous_toZMod m
    have inj : Function.Injective f := fun u v eq ↦ zHat.ext_of_toZMod fun m ↦ congrFun eq m
    apply (cont.isClosedEmbedding inj).isEmbedding.isInducing.tendsto_nhds_iff.2
    apply tendsto_pi_nhds.2
    intro m
    apply tendsto_nhds_of_eventually_eq
    exact (coord m).mono fun n eq ↦ by simpa only [Function.comp_apply, f, map_natCast] using eq
  · intro m b H hb
    have limit : Tendsto beta atTop (𝓝 (1/2)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1/2:ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have bh : ∀ᶠ n in atTop, beta n < b := limit.eventually (gt_mem_nhds hb)
    have th : ∀ᶠ n : ℕ in atTop, H ≤ (n : ℝ) := tendsto_natCast_atTop_atTop.eventually_ge_atTop H
    filter_upwards [bh, th, eventually_ge_atTop m.val] with n hb' hH hm
    have div : (m : ℕ) ∣ level n := Nat.dvd_factorial m.property (by omega)
    obtain ⟨sev, cop, all⟩ := (rows n).1
    refine ⟨sev, cop.of_dvd_left div, fun χ s hs hi ↦ ?_⟩
    apply entireL_ne_zero_of_changeLevel (quadTwist χ (seq n))
      (Nat.mul_dvd_mul_right div (seq n : ℕ))
    rw [← quadTwist_changeLevel_eq]
    exact all (χ.changeLevel div) s (hb'.le.trans hs) (by linarith)

end Hearthline.FiniteReadings
