/-
Copyright (c) 2026 Littlewood Proof Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Littlewood.Aristotle.Standalone.HadamardLiouvilleGeneralized
import Littlewood.Aristotle.Standalone.HadamardProductConvergence
import Littlewood.Aristotle.Standalone.AnalyticQuotient
import Littlewood.Aristotle.Standalone.XiGrowthBound
import Littlewood.Aristotle.Standalone.JensenZeroCounting
import Littlewood.Development.BorelCaratheodory
import Littlewood.Aristotle.Standalone.MinimumModulusPigeonhole
import Littlewood.ZetaZeros.RiemannVonMangoldtReal
import Littlewood.Aristotle.Standalone.ArithBound
import Littlewood.SigmaMultSummability
import Littlewood.Aristotle.Standalone.NonvanishingEntireLinear

/-!
# Hadamard Factorization Core

Pure Hadamard factorization assembly: quotient extension, growth bounds,
Borel-Carathéodory, and the master `HadamardXiCanonicalProductApprox` instance.

Split from `HadamardFactorizationWiring.lean` to break the import cycle:
  HadamardXiCoreInstance → Wiring → ZeroCountingAssumptions →
  PairedFarZeroCancellationInstance → PairedFarZeroCancellationHelper

This file has NO `ZeroCountingAssumptions` import, so `HadamardXiCoreInstance`
can import it without pulling in the zero-counting chain. The zero enumeration
input is axiomatized here (constructive proof lives in Wiring).
-/

set_option maxHeartbeats 12800000

noncomputable section

open Complex Metric Filter Set Function Topology HadamardXi MeromorphicOn

namespace Aristotle.Standalone.HadamardFactorizationWiring

/-! ## Zero enumeration hypothesis (cycle-break)

The constructive proof of `xi_zeros_enumeration` lives in
`HadamardZeroEnumeration.lean` and requires `ZeroCountingAssumptions`
(for `ZeroCountingMultTendstoHyp`). We package the result as a typeclass
hypothesis here so that downstream consumers (via `HadamardXiCoreInstance`)
avoid the cycle. The constructive instance is provided at high priority in
`HadamardZeroEnumeration.lean`; a sorry-backed fallback at low priority
here ensures compilation in the cycle-break window. -/

/-- Typeclass hypothesis for the xi zero enumeration. The constructive proof
lives in `HadamardZeroEnumeration.xi_zeros_enumeration_clean`. -/
class XiZerosEnumerationHyp : Prop where
  enumeration :
    ∃ (zeros : ℕ → ℂ),
      (∀ s, RiemannXiAlt s = 0 → ∃ n, s = zeros n) ∧
      (∀ n, zeros n ≠ 0) ∧
      (∀ n, RiemannXiAlt (zeros n) = 0) ∧
      Summable (fun n => 1 / ‖zeros n‖ ^ 2) ∧
      (∀ z, (Nat.card {n | zeros n = z} : ℕ∞) = analyticOrderAt RiemannXiAlt z) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
        ∃ S : Finset ℕ,
          (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ R) ∧
          (S.card : ℝ) ≤ C * R ^ (3 / 2 : ℝ))

/-! ### Helper lemmas for the zero enumeration proof

Ported from `HadamardZeroEnumeration.lean` to avoid the import cycle through
`ZeroCountingAssumptions`. The summability proof here is constructive (using
`XiGrowthBound` + `JensenZeroCounting`). Only `xi_zeros_infinite` remains sorry'd
because the infinitude argument requires `ZeroCountingMultTendstoHyp`, which
is on the cycle-causing side of the import graph. -/

private def xiZeroSet : Set ℂ := {s : ℂ | RiemannXiAlt s = 0}

/-- `RiemannXiAlt(0) = 1/2`. -/
private theorem xi_at_zero : RiemannXiAlt 0 = 1 / 2 := by
  unfold RiemannXiAlt; simp

/-- `RiemannXiAlt(0) ≠ 0`. -/
private theorem xi_zero_ne : RiemannXiAlt 0 ≠ 0 := by
  rw [xi_at_zero]; norm_num

private theorem xi_not_identically_zero : ¬ (∀ s, RiemannXiAlt s = 0) := by
  intro h; exact xi_zero_ne (h 0)

private theorem xi_analyticAt (z : ℂ) : AnalyticAt ℂ RiemannXiAlt z :=
  RiemannXiAlt_entire.analyticAt z

/-- Every zero of `RiemannXiAlt` is nonzero (since ξ(0) = 1/2 ≠ 0). -/
private theorem xi_zero_ne_zero {s : ℂ} (hs : RiemannXiAlt s = 0) : s ≠ 0 := by
  intro h; subst h; exact xi_zero_ne hs

/-- The zero set of `RiemannXiAlt` has no accumulation point
    (by the identity principle for entire functions). -/
private theorem xiZeroSet_no_accPt (z₀ : ℂ) :
    ¬ (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, RiemannXiAlt z = 0) := by
  intro hfreq
  have hanalytic : AnalyticOnNhd ℂ RiemannXiAlt Set.univ :=
    fun w _ => xi_analyticAt w
  have := hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ z₀) hfreq
  exact xi_not_identically_zero (fun s => this (Set.mem_univ s))

/-- The zero set in any closed ball is finite. -/
private theorem xiZeroSet_finite_in_disk (R : ℝ) :
    (xiZeroSet ∩ Metric.closedBall 0 R).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨z₀, _, hz_acc⟩ := hinf.exists_accPt_cofinite_inf_principal_of_subset_isCompact
    (isCompact_closedBall 0 R) Set.inter_subset_right
  have hz_acc_xi : AccPt z₀ (𝓟 xiZeroSet) :=
    hz_acc.mono (inf_le_right.trans (Filter.principal_mono.mpr Set.inter_subset_left))
  rw [accPt_iff_frequently_nhdsNE] at hz_acc_xi
  exact xiZeroSet_no_accPt z₀ hz_acc_xi

/-- The zero set is countable (finite in each ball, ℂ is σ-compact). -/
private theorem xiZeroSet_countable : xiZeroSet.Countable := by
  have hcover : xiZeroSet = ⋃ n : ℕ, xiZeroSet ∩ Metric.closedBall 0 n := by
    ext z; simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun hz => ⟨⌈dist z 0⌉₊, hz, Metric.mem_closedBall.mpr (Nat.le_ceil _)⟩,
           fun ⟨_, hz, _⟩ => hz⟩
  rw [hcover]; exact Set.countable_iUnion (fun n => (xiZeroSet_finite_in_disk n).countable)

/-! ### Multiplicity infrastructure for zero enumeration -/

/-- The analytic order of ξ at a zero is finite and positive. -/
private theorem xi_analyticOrderAt_pos_at_zero {z : ℂ} (hz : RiemannXiAlt z = 0) :
    0 < (analyticOrderAt RiemannXiAlt z).toNat := by
  -- Step 1: order ≠ 0 (because ξ(z) = 0 and ξ is analytic at z)
  have hord_ne_zero : analyticOrderAt RiemannXiAlt z ≠ 0 :=
    (xi_analyticAt z).analyticOrderAt_ne_zero.mpr hz
  -- Step 2: order ≠ ⊤ (because ξ is not identically zero near z)
  have hord_ne_top : analyticOrderAt RiemannXiAlt z ≠ ⊤ := by
    intro h
    -- order = ⊤ means ξ vanishes on a neighborhood of z
    have hev := analyticOrderAt_eq_top.mp h
    -- this gives ∃ᶠ w in nhdsWithin z {z}ᶜ, ξ(w) = 0
    have hfreq : ∃ᶠ w in nhdsWithin z {z}ᶜ, RiemannXiAlt w = 0 :=
      hev.filter_mono nhdsWithin_le_nhds |>.frequently
    exact xiZeroSet_no_accPt z hfreq
  -- Step 3: toNat of finite nonzero ENat is positive
  rw [Nat.pos_iff_ne_zero]
  intro h0
  rcases ENat.toNat_eq_zero.mp h0 with h | h
  · exact hord_ne_zero h
  · exact hord_ne_top h

/-- `RiemannXiAlt` agrees with `XiGrowthBound.RiemannXiAlt`. -/
private theorem xi_eq_growthBound_xi (s : ℂ) :
    RiemannXiAlt s = Aristotle.Standalone.XiGrowthBound.RiemannXiAlt s := by
  simp only [RiemannXiAlt, Aristotle.Standalone.XiGrowthBound.RiemannXiAlt]

/-- `RiemannXiAlt` satisfies the growth bound needed for `entire_zero_count_bound`. -/
private theorem xi_growth_for_jensen :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ ‖s‖ →
      ‖RiemannXiAlt s‖ ≤ Real.exp (C * ‖s‖ ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    Aristotle.Standalone.XiGrowthBound.xi_finite_order (1 / 2) (by positivity)
  refine ⟨C, hC, fun s hs => ?_⟩
  rw [xi_eq_growthBound_xi]
  have h := hbound s hs
  calc
    ‖Aristotle.Standalone.XiGrowthBound.RiemannXiAlt s‖
        ≤ Real.exp (C * ‖s‖ ^ (1 + 1 / 2)) := h
    _ = Real.exp (C * ‖s‖ ^ (3 / 2 : ℝ)) := by norm_num

/-- Zero counting bound for `RiemannXiAlt`: `N(R) ≤ C'R^{3/2}` for `R ≥ 1`. -/
private theorem xi_zero_count_bound :
    ∃ C' : ℝ, 0 < C' ∧ ∀ R : ℝ, 1 ≤ R →
      (zeroCount RiemannXiAlt R : ℝ) ≤ C' * R ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := xi_growth_for_jensen
  exact entire_zero_count_bound xi_analyticAt hC hbound xi_zero_ne

/-- At a zero of an entire function, the divisor value is at least `1`. -/
private theorem divisor_ge_one_at_zero {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (hfz : f z = 0) (hz : z ∈ closedBall (0 : ℂ) R)
    (hne : ¬ ∀ w, f w = 0) :
    1 ≤ divisor f (closedBall (0 : ℂ) R) z := by
  rw [divisor_apply (AnalyticOnNhd.meromorphicOn (fun w _ => hf w)) hz]
  have hord_ne_zero : meromorphicOrderAt f z ≠ 0 := by
    intro h_eq
    have := (hf z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h_eq
    exact absurd hfz this
  have hord_ne_top : meromorphicOrderAt f z ≠ ⊤ := by
    intro h_eq
    have h_ev : ∀ᶠ w in 𝓝[≠] z, f w = 0 := meromorphicOrderAt_eq_top_iff.mp h_eq
    have hanalytic : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf w
    exact hne (fun w => hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ z) h_ev.frequently (Set.mem_univ w))
  cases h : meromorphicOrderAt f z with
  | top => exact absurd h hord_ne_top
  | coe v =>
    simp [WithTop.untop₀]
    have h_nonneg := (hf z).meromorphicOrderAt_nonneg
    rw [h] at h_nonneg
    have hv_pos : 0 < v := by
      exact_mod_cast lt_of_le_of_ne (by exact_mod_cast h_nonneg)
        (fun heq => hord_ne_zero (by rw [h]; exact_mod_cast heq.symm))
    exact_mod_cast hv_pos

/-- The set-theoretic zero count is bounded by the divisor-based zero count. -/
private theorem xi_card_le_zeroCount (R : ℝ) :
    ((xiZeroSet_finite_in_disk R).toFinset.card : ℤ) ≤ zeroCount RiemannXiAlt R := by
  unfold zeroCount
  set div_fn := divisor RiemannXiAlt (closedBall (0 : ℂ) R)
  have hfin : Set.Finite (Function.support (div_fn : ℂ → ℤ)) :=
    div_fn.finiteSupport (ProperSpace.isCompact_closedBall _ _)
  have hsup : Function.support (div_fn : ℂ → ℤ) ⊆ ↑hfin.toFinset := by
    intro x hx
    exact hfin.mem_toFinset.mpr hx
  rw [finsum_eq_sum_of_support_subset _ hsup]
  have h_sub : (xiZeroSet_finite_in_disk R).toFinset ⊆ hfin.toFinset := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz ⊢
    rw [Function.mem_support]
    have h1 := divisor_ge_one_at_zero xi_analyticAt hz.1 hz.2 xi_not_identically_zero
    linarith
  calc
    ((xiZeroSet_finite_in_disk R).toFinset.card : ℤ)
        = ∑ _z ∈ (xiZeroSet_finite_in_disk R).toFinset, (1 : ℤ) := by simp
    _ ≤ ∑ z ∈ (xiZeroSet_finite_in_disk R).toFinset, (div_fn : ℂ → ℤ) z := by
      apply Finset.sum_le_sum
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      exact divisor_ge_one_at_zero xi_analyticAt hz.1 hz.2 xi_not_identically_zero
    _ ≤ ∑ z ∈ hfin.toFinset, (div_fn : ℂ → ℤ) z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
      intro z _ _
      exact divisor_nonneg_of_entire xi_analyticAt _ _

/-- Cardinality of `xiZeroSet` in `closedBall 0 R` is bounded by `C'R^{3/2}`. -/
private theorem xi_card_bound :
    ∃ C' : ℝ, 0 < C' ∧ ∀ R : ℝ, 1 ≤ R →
      ((xiZeroSet_finite_in_disk R).toFinset.card : ℝ) ≤ C' * R ^ (3 / 2 : ℝ) := by
  obtain ⟨C', hC', hcount⟩ := xi_zero_count_bound
  exact ⟨C', hC', fun R hR => by
    have h1 := xi_card_le_zeroCount R
    have h2 := hcount R hR
    have h3 : ((xiZeroSet_finite_in_disk R).toFinset.card : ℝ) ≤
        (zeroCount RiemannXiAlt R : ℝ) := by
      exact_mod_cast h1
    linarith⟩

open Real in
/-- Finite-subset bound used to sum `∑ 1 / ‖ρ‖²`. -/
private theorem xi_zero_set_finset_bound (C' : ℝ) (hC' : 0 < C')
    (hcard : ∀ R : ℝ, 1 ≤ R →
      ((xiZeroSet_finite_in_disk R).toFinset.card : ℝ) ≤ C' * R ^ (3 / 2 : ℝ))
    (v : Finset xiZeroSet)
    (hge1 : ∀ z ∈ v, 1 ≤ ‖(z : ℂ)‖) :
    ∑ z ∈ v, (1 : ℝ) / ‖(z : ℂ)‖ ^ 2 ≤
      C' ^ (4 / 3 : ℝ) *
        ∑ j ∈ Finset.range v.card, (1 : ℝ) / ((j : ℝ) + 1) ^ (4 / 3 : ℝ) := by
  induction v using Finset.strongInduction with
  | H v ih =>
    by_cases hv : v = ∅
    · simp [hv]
    · have hne : v.Nonempty := Finset.nonempty_of_ne_empty hv
      obtain ⟨z_max, hz_max_mem, hz_max_prop⟩ :=
        v.exists_max_image (fun z => ‖(z : ℂ)‖) hne
      set v' := v.erase z_max
      have hv'_ssubset : v' ⊂ v := Finset.erase_ssubset hz_max_mem
      have hv'_card : v'.card = v.card - 1 := Finset.card_erase_of_mem hz_max_mem
      have hv_pos : 0 < v.card := Finset.card_pos.mpr hne
      rw [← Finset.add_sum_erase v _ hz_max_mem]
      have hzm_pos : 0 < ‖(z_max : ℂ)‖ := norm_pos_iff.mpr (xi_zero_ne_zero z_max.2)
      have hzm_ge1 : 1 ≤ ‖(z_max : ℂ)‖ := hge1 z_max hz_max_mem
      have h_card_bound : (v.card : ℝ) ≤ C' * ‖(z_max : ℂ)‖ ^ (3 / 2 : ℝ) := by
        have h_card_le :
            v.card ≤ (xiZeroSet_finite_in_disk ‖(z_max : ℂ)‖).toFinset.card := by
          have hinj : (v.image Subtype.val).card = v.card :=
            Finset.card_image_of_injective v Subtype.coe_injective
          rw [← hinj]
          apply Finset.card_le_card
          intro z hz
          rw [Set.Finite.mem_toFinset]
          obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
          exact ⟨hwz ▸ w.2, hwz ▸ mem_closedBall_zero_iff.mpr (hz_max_prop w hw)⟩
        exact (Nat.cast_le.mpr h_card_le).trans (hcard _ hzm_ge1)
      have h_rpow_bound : (v.card : ℝ) ^ (4 / 3 : ℝ) ≤
          C' ^ (4 / 3 : ℝ) * ‖(z_max : ℂ)‖ ^ 2 := by
        have h1 : (v.card : ℝ) ^ (4 / 3 : ℝ) ≤
            (C' * ‖(z_max : ℂ)‖ ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) :=
          rpow_le_rpow (Nat.cast_nonneg _) h_card_bound (by norm_num)
        have h2 : (C' * ‖(z_max : ℂ)‖ ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) =
            C' ^ (4 / 3 : ℝ) * ‖(z_max : ℂ)‖ ^ 2 := by
          rw [mul_rpow hC'.le (rpow_nonneg hzm_pos.le _), ← rpow_mul hzm_pos.le]
          norm_num [rpow_natCast]
        linarith
      have h_inv_bound : 1 / ‖(z_max : ℂ)‖ ^ 2 ≤
          C' ^ (4 / 3 : ℝ) / (v.card : ℝ) ^ (4 / 3 : ℝ) := by
        rw [div_le_div_iff₀ (pow_pos hzm_pos 2)
            (rpow_pos_of_pos (Nat.cast_pos.mpr hv_pos) _)]
        linarith
      have hrange_split : Finset.range v.card =
          Finset.range (v.card - 1) ∪ {v.card - 1} := by
        ext j
        simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton]
        omega
      have hdisj : Disjoint (Finset.range (v.card - 1)) {v.card - 1} := by
        rw [Finset.disjoint_singleton_right]
        exact Finset.notMem_range_self
      rw [hrange_split, Finset.sum_union hdisj, Finset.sum_singleton, mul_add]
      rw [show ∀ a b : ℝ, C' ^ (4 / 3 : ℝ) * a + C' ^ (4 / 3 : ℝ) * b =
          C' ^ (4 / 3 : ℝ) * b + C' ^ (4 / 3 : ℝ) * a from fun a b => add_comm _ _]
      apply add_le_add
      · have h2 : (v.card : ℝ) = ((v.card - 1 : ℕ) : ℝ) + 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ v.card)]
          ring
        have : C' ^ (4 / 3 : ℝ) / (v.card : ℝ) ^ (4 / 3 : ℝ) =
            C' ^ (4 / 3 : ℝ) * (1 / ((↑(v.card - 1) : ℝ) + 1) ^ (4 / 3 : ℝ)) := by
          rw [← h2]
          ring
        exact h_inv_bound.trans (le_of_eq this)
      · have h_ih := ih v' hv'_ssubset (fun z hz => hge1 z (Finset.mem_of_mem_erase hz))
        rwa [hv'_card] at h_ih

/-- `∑_{ρ ∈ Z(ξ)} 1 / |ρ|²` converges. Constructive proof using the
Jensen zero-counting bound `N(R) ≤ C'R^{3/2}`. -/
private theorem xi_zero_set_summable :
    Summable (fun z : xiZeroSet => 1 / ‖(z : ℂ)‖ ^ 2) := by
  obtain ⟨C', hC', hcard⟩ := xi_card_bound
  set S : Set xiZeroSet := {z | ‖(z : ℂ)‖ ≤ 1}
  have hS_finite : S.Finite := by
    apply Set.Finite.of_finite_image (f := Subtype.val)
    · exact ((xiZeroSet_finite_in_disk 1).subset (by
        rintro z ⟨⟨w, hw⟩, hmem, rfl⟩
        exact ⟨hw, mem_closedBall_zero_iff.mpr hmem⟩))
    · exact Subtype.val_injective.injOn
  have hS_summable :
      Summable (fun z : S => (1 : ℝ) / ‖((z : xiZeroSet) : ℂ)‖ ^ 2) := by
    haveI : Finite S := hS_finite
    exact Summable.of_finite
  have hSc_summable :
      Summable (fun z : ↥Sᶜ => (1 : ℝ) / ‖((z : xiZeroSet) : ℂ)‖ ^ 2) := by
    have h_pseries : Summable (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1) ^ (4 / 3 : ℝ)) := by
      have h1 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (4 / 3 : ℝ)) :=
        Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 4 / 3)
      have h2 : (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1) ^ (4 / 3 : ℝ)) =
          (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (4 / 3 : ℝ)) ∘ (· + 1 : ℕ → ℕ) := by
        ext n
        simp [Function.comp, Nat.cast_add, Nat.cast_one]
      rw [h2]
      exact h1.comp_injective (fun a b h => by omega)
    apply summable_of_sum_le (fun _ => by positivity)
    intro u
    set w := u.map ⟨Subtype.val, Subtype.coe_injective⟩
    have hw_ge1 : ∀ z ∈ w, 1 ≤ ‖(z : ℂ)‖ := by
      intro z hz
      obtain ⟨⟨z', hz'⟩, _, rfl⟩ := Finset.mem_map.mp hz
      exact le_of_lt (not_le.mp hz')
    have hw_sum :
        ∑ z ∈ u, (1 : ℝ) / ‖((z : xiZeroSet) : ℂ)‖ ^ 2 =
          ∑ z ∈ w, (1 : ℝ) / ‖(z : ℂ)‖ ^ 2 := by
      rw [Finset.sum_map]
      rfl
    rw [hw_sum]
    calc
      ∑ z ∈ w, (1 : ℝ) / ‖(z : ℂ)‖ ^ 2
          ≤ C' ^ (4 / 3 : ℝ) *
              ∑ j ∈ Finset.range w.card, (1 : ℝ) / ((j : ℝ) + 1) ^ (4 / 3 : ℝ) :=
        xi_zero_set_finset_bound C' hC' hcard w hw_ge1
      _ ≤ C' ^ (4 / 3 : ℝ) * ∑' (j : ℕ), (1 : ℝ) / ((j : ℝ) + 1) ^ (4 / 3 : ℝ) := by
        gcongr
        exact h_pseries.sum_le_tsum (Finset.range w.card) (fun j _ => by positivity)
  exact summable_subtype_and_compl.mp ⟨hS_summable, hSc_summable⟩

/-- Factor out a zero: if f is entire with zero of order m at z₀, then
f(z) = (z - z₀)^m · g(z) globally for some entire g with g(z₀) ≠ 0.
Proof via AnalyticAt.analyticOrderAt_eq_natCast (local factorization) + DifferentiableAt.congr_of_eventuallyEq
(global extension through removable singularity at z₀). -/
private lemma factor_out_one_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (z₀ : ℂ) (m : ℕ) (hm : 0 < m)
    (h_order : analyticOrderAt f z₀ = m) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, f z = (z - z₀)^m * g z) ∧ g z₀ ≠ 0 := by
  have hfAt : AnalyticAt ℂ f z₀ := hf.analyticAt z₀
  obtain ⟨g_loc, hg_loc_an, hg_loc_ne, hg_loc_eq⟩ := hfAt.analyticOrderAt_eq_natCast.mp h_order
  have hg_loc_eq' : ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ m * g_loc z := by
    filter_upwards [hg_loc_eq] with z hz
    rwa [smul_eq_mul] at hz
  classical
  set G : ℂ → ℂ := fun z => if z = z₀ then g_loc z₀ else f z / (z - z₀) ^ m
    with hG_def
  have hG_diff_ne : ∀ z, z ≠ z₀ → DifferentiableAt ℂ G z := by
    intro z hz
    have h_nhd : G =ᶠ[𝓝 z] (fun z' => f z' / (z' - z₀) ^ m) := by
      filter_upwards [eventually_ne_nhds hz] with z' hz'
      simp [G, hz']
    have h_diff_quot : DifferentiableAt ℂ (fun z' => f z' / (z' - z₀) ^ m) z := by
      apply DifferentiableAt.div
      · exact hf.differentiableAt
      · exact (differentiableAt_id.sub (differentiableAt_const _)).pow m
      · exact pow_ne_zero m (sub_ne_zero.mpr hz)
    exact h_diff_quot.congr_of_eventuallyEq h_nhd
  have hG_diff_z₀ : DifferentiableAt ℂ G z₀ := by
    have h_eq : G =ᶠ[𝓝 z₀] g_loc := by
      filter_upwards [hg_loc_eq'] with z hz
      by_cases h : z = z₀
      · subst h; simp [G]
      · have h_pow_ne : (z - z₀) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr h)
        simp [G, h]
        rw [hz]
        field_simp
    exact hg_loc_an.differentiableAt.congr_of_eventuallyEq h_eq
  have hG_diff : Differentiable ℂ G := fun z => by
    by_cases h : z = z₀
    · subst h; exact hG_diff_z₀
    · exact hG_diff_ne z h
  have hfeq : ∀ z, f z = (z - z₀) ^ m * G z := by
    intro z
    by_cases h : z = z₀
    · have hf_at : f z₀ = 0 := by
        have hthis := hg_loc_eq.self_of_nhds
        rw [hthis]
        simp [zero_pow (Nat.pos_iff_ne_zero.mp hm)]
      rw [h, hf_at]
      have h_sub : (z₀ : ℂ) - z₀ = 0 := sub_self _
      rw [h_sub, zero_pow (Nat.pos_iff_ne_zero.mp hm)]
      ring
    · have h_pow_ne : (z - z₀) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr h)
      simp [G, h]
      field_simp
  have hG_z₀_ne : G z₀ ≠ 0 := by simp [G, hg_loc_ne]
  exact ⟨G, hG_diff, hfeq, hG_z₀_ne⟩

/-- The analytic order at a zero is positive and finite for non-identically-zero entire functions. -/
private theorem analyticOrderAt_pos_finite_of_zero' (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (z₀ : ℂ) (hz : f z₀ = 0) (hne : ∃ w, f w ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ analyticOrderAt f z₀ = (m : ℕ∞) := by
  have h_order_pos : analyticOrderAt f z₀ ≠ 0 := by
    rw [ne_eq, (hf.analyticAt z₀).analyticOrderAt_eq_zero]
    push_neg; exact hz
  have h_order_ne_top : analyticOrderAt f z₀ ≠ ⊤ := by
    intro h
    obtain ⟨w, hw⟩ := hne
    have h_event : f =ᶠ[nhds z₀] 0 := by
      have := analyticOrderAt_eq_top.mp h
      filter_upwards [this] with z hz
      simp [hz]
    have hAnalytic : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf.analyticAt x
    have hZero : AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ := fun x _ => analyticAt_const
    have := hAnalytic.eqOn_of_preconnected_of_eventuallyEq hZero isPreconnected_univ
      (Set.mem_univ z₀) h_event
    exact hw (this (Set.mem_univ w))
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp h_order_ne_top
  -- hm : analyticOrderAt f z₀ = some m = ((m : ℕ) : ℕ∞)
  have hm_cast : analyticOrderAt f z₀ = (m : ℕ∞) := by exact_mod_cast hm
  refine ⟨m, ?_, hm_cast⟩
  rcases Nat.eq_zero_or_pos m with hm_zero | hm_pos
  · exfalso; apply h_order_pos
    rw [hm_cast, hm_zero]; rfl
  · exact hm_pos

/-- General Hadamard-type factorization: entire function with finite zero set and
subquadratic exponential growth factors as `P(s) · exp(A + B·s)`.
Proved by strong induction on |{zeros}| + factor_out_one_zero + entire_nonvanishing_subquad_is_exp_linear. -/
private theorem entire_finite_zeros_polyexp (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne_f : ∃ w, f w ≠ 0) (hfin_f : {z | f z = 0}.Finite)
    (α C : ℝ) (hα_pos : 0 ≤ α) (hα_lt : α < 2) (hC_pos : 0 < C)
    (hgrowth : ∀ z, ‖f z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ α)) :
    ∃ (P : Polynomial ℂ) (A B : ℂ), ∀ s,
      f s = P.eval s * exp (A + B * s) := by
  revert f hf hne_f hfin_f α C hα_pos hα_lt hC_pos hgrowth
  intro f hf hne_f hfin_f α C hα_pos hα_lt hC_pos hgrowth
  induction' n : hfin_f.toFinset.card using Nat.strong_induction_on with n ih generalizing f α C
  by_cases h_zero : ∃ z₀, f z₀ = 0 ∧ analyticOrderAt f z₀ ≠ ⊤ ∧ 0 < analyticOrderAt f z₀
  · obtain ⟨ z₀, hz₀₁, hz₀₂, hz₀₃ ⟩ := h_zero
    obtain ⟨ m, hm₁, hm₂ ⟩ := analyticOrderAt_pos_finite_of_zero' f hf z₀ hz₀₁ hne_f
    obtain ⟨ g, hg_diff, hg_zero, hg_ne ⟩ := factor_out_one_zero f hf z₀ m hm₁ hm₂
    have hg_growth : ∃ C' : ℝ, 0 < C' ∧ ∀ z, ‖g z‖ ≤ Real.exp (C' * (‖z‖ + 1) ^ α) := by
      have hg_growth : ∃ C' : ℝ, 0 < C' ∧ ∀ z, ‖z‖ ≥ 2 * (‖z₀‖ + 1) → ‖g z‖ ≤ Real.exp (C' * (‖z‖ + 1) ^ α) := by
        have hg_growth : ∀ z, ‖z‖ ≥ 2 * (‖z₀‖ + 1) → ‖g z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ α) / (‖z‖ / 2) ^ m := by
          intros z hz
          have h_norm : ‖z - z₀‖ ≥ ‖z‖ / 2 := by
            have := norm_sub_norm_le z z₀; linarith [ norm_nonneg z₀ ]
          have h_norm : ‖f z‖ = ‖z - z₀‖ ^ m * ‖g z‖ := by
            rw [ hg_zero, norm_mul, norm_pow ]
          rw [ le_div_iff₀ ( pow_pos ( by linarith [ norm_nonneg z₀ ] ) _ ) ]
          exact le_trans ( by rw [ mul_comm ] ; gcongr ) ( h_norm ▸ hgrowth z )
        refine' ⟨ C + m * Real.log 2, _, _ ⟩
        · positivity
        · intro z hz
          have h_exp : Real.exp (C * (‖z‖ + 1) ^ α) / (‖z‖ / 2) ^ m ≤ Real.exp ((C + m * Real.log 2) * (‖z‖ + 1) ^ α) := by
            rw [ div_le_iff₀ ( pow_pos ( by linarith [ norm_nonneg z₀ ] ) _ ) ]
            rw [ ← Real.log_le_log_iff ( by positivity ) ( by exact mul_pos ( Real.exp_pos _ ) ( pow_pos ( by linarith [ norm_nonneg z₀ ] ) _ ) ), Real.log_mul ( by positivity ) ( by exact pow_ne_zero _ ( by linarith [ norm_nonneg z₀ ] ) ), Real.log_exp, Real.log_exp ]
            exact le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_right ( le_add_of_nonneg_right <| by positivity ) <| by positivity ) <| Real.log_nonneg <| one_le_pow₀ <| by linarith [ norm_nonneg z₀ ]
          exact le_trans ( hg_growth z hz ) h_exp
      obtain ⟨ C', hC'_pos, hC' ⟩ := hg_growth
      obtain ⟨ M, hM ⟩ : ∃ M : ℝ, ∀ z : ℂ, ‖z‖ ≤ 2 * (‖z₀‖ + 1) → ‖g z‖ ≤ M := by
        have hg_cont : ContinuousOn g (Metric.closedBall 0 (2 * (‖z₀‖ + 1))) := by
          exact hg_diff.continuous.continuousOn
        obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( ProperSpace.isCompact_closedBall 0 ( 2 * ( ‖z₀‖ + 1 ) ) ) hg_cont
        use M; intro z hz; exact hM z ( by simpa using hz )
      refine' ⟨ Max.max C' ( M + 1 ), _, _ ⟩
      · simp only [lt_max_iff]; exact Or.inl hC'_pos
      · intro z; by_cases hz : ‖z‖ ≤ 2 * (‖z₀‖ + 1)
        · refine' le_trans ( hM z hz ) _
          refine' le_trans _ ( Real.add_one_le_exp _ )
          exact le_add_of_le_of_nonneg ( le_trans ( by linarith [ le_max_right C' ( M + 1 ) ] ) ( le_mul_of_one_le_right ( by positivity ) ( Real.one_le_rpow ( by linarith [ norm_nonneg z ] ) ( by linarith ) ) ) ) zero_le_one
        · exact le_trans ( hC' z ( le_of_not_ge hz ) ) ( Real.exp_le_exp.mpr ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity ) ) )
    have hg_card : (Set.Finite.toFinset (show Set.Finite {z | g z = 0} from by
                                          exact hfin_f.subset fun x hx => by simp_all +decide [ sub_eq_iff_eq_add, hm₁.ne' ])).card < (Set.Finite.toFinset hfin_f).card := by
                                          refine' Finset.card_lt_card _
                                          simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ]
                                          exact ⟨ z₀, Or.inl <| sub_self _, hg_ne ⟩
    generalize_proofs at *
    obtain ⟨ C', hC'_pos, hC'_growth ⟩ := hg_growth
    specialize ih _ ( by linarith ) _ hg_diff _ _ _ _ hα_pos hα_lt hC'_pos hC'_growth rfl
    · exact ⟨ z₀, hg_ne ⟩
    · obtain ⟨ P, A, B, hP ⟩ := ih
      use ( Polynomial.X - Polynomial.C z₀ ) ^ m * P, A, B
      intro s; simp +decide [ hg_zero, hP ] ; ring
  · have h_nonvanishing : ∀ z, f z ≠ 0 := by
      contrapose! h_zero
      obtain ⟨ z₀, hz₀ ⟩ := h_zero
      exact ⟨ z₀, hz₀, by
        have := analyticOrderAt_pos_finite_of_zero' f hf z₀ hz₀ hne_f; aesop, by
        have := analyticOrderAt_pos_finite_of_zero' f hf z₀ hz₀ hne_f; aesop ⟩
    have := Aristotle.Standalone.NonvanishingEntireLinear.entire_nonvanishing_subquad_is_exp_linear
      f hf h_nonvanishing α C hα_lt hα_pos hC_pos hgrowth
    exact ⟨ 1, this.choose, this.choose_spec.choose, fun s => by simpa using this.choose_spec.choose_spec s ⟩

/-! ### Proof that ξ has infinitely many zeros

We prove `Set.Infinite xiZeroSet` by contradiction using the Hadamard-style argument:
if ξ has finitely many zeros, then ξ = P · exp(A + B·s) for some polynomial P and
constants A, B (using the global logarithm for nonvanishing entire functions,
Borel-Carathéodory growth transfer, and the Liouville-type result
`subquadratic_growth_imp_linear`). But ξ(2n+2) involves Γ(n+1) = n! which grows
faster than any polynomial × exponential, giving a contradiction. -/

/-- `n!` eventually exceeds any `C * D^n` for fixed `C, D > 0`.
Proof uses `Real.summable_pow_div_factorial` (Mathlib) to show C·D^n/n! → 0. -/
private theorem factorial_exceeds_exp (C D : ℝ) (_hC : 0 < C) (_hD : 0 < D) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * D ^ n < (n.factorial : ℝ) := by
  have h_factorial_growth : Filter.Tendsto (fun n : ℕ => C * D ^ n / (n.factorial : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [mul_div_assoc] using tendsto_const_nhds.mul
      (Real.summable_pow_div_factorial D |>.tendsto_atTop_zero)
  exact Filter.eventually_atTop.mp
    (h_factorial_growth.eventually (gt_mem_nhds zero_lt_one)) |>
    fun ⟨N, hN⟩ ↦ ⟨N, fun n hn ↦ by
      have := hN n hn; rw [div_lt_one (by positivity)] at this; linarith⟩

/-- The functional equation ξ(1-s) = ξ(s). -/
private theorem xi_functional_eq (s : ℂ) : RiemannXiAlt (1 - s) = RiemannXiAlt s := by
  unfold RiemannXiAlt; rw [completedRiemannZeta₀_one_sub]; ring

/-! ### Exact evaluation of ξ at even integers ≥ 2

For σ = 2n+2 with n ≥ 0, we have ξ(2n+2) = (n+1)(2n+1)·π^{-(n+1)}·n!·ζ(2n+2).
This cancels neatly because the "+1" in the RiemannXiAlt definition exactly
offsets the boundary terms 1/s + 1/(1-s) from completedRiemannZeta₀. -/

/-- Gammaℝ at even integer: π^{-(n+1)} · n!. -/
private lemma gammaR_at_even (n : ℕ) :
    (↑(2 * n + 2 : ℕ) : ℂ).Gammaℝ =
      (↑Real.pi : ℂ) ^ (-((n : ℂ) + 1)) * (n.factorial : ℂ) := by
  rw [Complex.Gammaℝ_def]
  have h1 : -((↑(2 * n + 2 : ℕ) : ℂ)) / 2 = -((n : ℂ) + 1) := by push_cast; ring
  have h2 : ((↑(2 * n + 2 : ℕ) : ℂ)) / 2 = (n : ℂ) + 1 := by push_cast; ring
  rw [h1, h2, Complex.Gamma_nat_eq_factorial]

/-- ζ(2n+2) ≠ 0 (Re ≥ 2 ≥ 1). -/
private lemma riemannZeta_at_even_ne_zero (n : ℕ) :
    riemannZeta (↑(2 * n + 2 : ℕ) : ℂ) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  simp; norm_cast; omega

/-- completedRiemannZeta = Gammaℝ · ζ at 2n+2 (no poles). -/
private lemma completed_at_even (n : ℕ) :
    completedRiemannZeta (↑(2 * n + 2 : ℕ) : ℂ) =
      (↑(2 * n + 2 : ℕ) : ℂ).Gammaℝ * riemannZeta (↑(2 * n + 2 : ℕ) : ℂ) := by
  have h_ne : (↑(2 * n + 2 : ℕ) : ℂ) ≠ 0 := by
    have : (2 * n + 2 : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  rw [riemannZeta_def_of_ne_zero h_ne]
  have hGR_ne : (↑(2 * n + 2 : ℕ) : ℂ).Gammaℝ ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    apply mul_ne_zero
    · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_pos.ne'))
    · rw [show ((↑(2 * n + 2 : ℕ) : ℂ)) / 2 = (n : ℂ) + 1 by push_cast; ring,
          Complex.Gamma_nat_eq_factorial]
      exact_mod_cast (n.factorial_pos).ne'
  field_simp

/-- Exact evaluation: ξ(2n+2) = (n+1)(2n+1)·π^{-(n+1)}·n!·ζ(2n+2). -/
private lemma xi_at_even (n : ℕ) :
    RiemannXiAlt (↑(2 * n + 2 : ℕ) : ℂ) =
      ((n : ℂ) + 1) * ((2 * n : ℂ) + 1) *
      ((↑Real.pi : ℂ) ^ (-((n : ℂ) + 1))) * (n.factorial : ℂ) *
      riemannZeta (↑(2 * n + 2 : ℕ) : ℂ) := by
  unfold RiemannXiAlt
  set s : ℂ := (↑(2 * n + 2 : ℕ) : ℂ) with hs_def
  have hs_ne : s ≠ 0 := by
    have : (2 * n + 2 : ℕ) ≠ 0 := by omega
    simp [s]; exact_mod_cast this
  have hs_ne1 : (1 : ℂ) - s ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination -h
    rw [hs_def] at this
    have : (2 * n + 2 : ℕ) = 1 := by exact_mod_cast this
    omega
  have h_comp := completedRiemannZeta_eq s
  have h_ce : completedRiemannZeta s = s.Gammaℝ * riemannZeta s := by
    rw [hs_def]; exact completed_at_even n
  have h_gR : s.Gammaℝ = (↑Real.pi : ℂ) ^ (-((n : ℂ) + 1)) * (n.factorial : ℂ) := by
    rw [hs_def]; exact gammaR_at_even n
  have key : (1/2 : ℂ) * (s * (s - 1) * completedRiemannZeta₀ s + 1) =
      (1/2 : ℂ) * s * (s - 1) * (s.Gammaℝ * riemannZeta s) := by
    have hΛ₀ : completedRiemannZeta₀ s = completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
      linear_combination -h_comp
    rw [hΛ₀, h_ce]
    field_simp
    ring
  rw [key, h_gR]
  have hs_sub : s - 1 = 2 * (n : ℂ) + 1 := by simp [s]; push_cast; ring
  have hs_mul : (1/2 : ℂ) * s * (s - 1) = ((n : ℂ) + 1) * ((2 * n : ℂ) + 1) := by
    rw [hs_sub, hs_def]; push_cast; ring
  rw [show (1/2 : ℂ) * s * (s - 1) *
        ((↑Real.pi : ℂ) ^ (-((n : ℂ) + 1)) * (n.factorial : ℂ) *
        riemannZeta s) = (1/2 : ℂ) * s * (s - 1) *
        ((↑Real.pi : ℂ) ^ (-((n : ℂ) + 1)) * ((n.factorial : ℂ) *
        riemannZeta s)) from by ring]
  rw [hs_mul]
  ring

/-- Polynomial norm bound: ‖P.eval z‖ ≤ (∑ coeff norms) · (‖z‖+1)^deg. -/
private lemma poly_eval_norm_le (P : Polynomial ℂ) (z : ℂ) :
    ‖P.eval z‖ ≤ (∑ i ∈ P.support, ‖P.coeff i‖) * (‖z‖ + 1) ^ P.natDegree := by
  calc ‖P.eval z‖
      ≤ P.sum (fun i a => ‖a‖ * ‖z‖ ^ i) := by
        rw [Polynomial.eval_eq_sum]
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum (fun i _ => by rw [norm_mul, norm_pow]))
    _ = ∑ i ∈ P.support, ‖P.coeff i‖ * ‖z‖ ^ i := by rfl
    _ ≤ ∑ i ∈ P.support, ‖P.coeff i‖ * (‖z‖ + 1) ^ P.natDegree := by
        apply Finset.sum_le_sum
        intro i hi
        have h_pow : ‖z‖ ^ i ≤ (‖z‖ + 1) ^ P.natDegree := by
          calc ‖z‖ ^ i ≤ (‖z‖ + 1) ^ i := by gcongr; linarith
            _ ≤ (‖z‖ + 1) ^ P.natDegree :=
                pow_le_pow_right₀ (by linarith [norm_nonneg z])
                  (Polynomial.le_natDegree_of_mem_supp _ hi)
        exact mul_le_mul_of_nonneg_left h_pow (norm_nonneg _)
    _ = (∑ i ∈ P.support, ‖P.coeff i‖) * (‖z‖ + 1) ^ P.natDegree := by
        rw [← Finset.sum_mul]

/-- For real σ > 1, Re(ζ(σ)) ≥ 1. -/
private lemma zeta_real_re_ge_one (σ : ℝ) (hσ : 1 < σ) :
    (1 : ℝ) ≤ (riemannZeta (σ : ℂ)).re := by
  have hre : 1 < (σ : ℂ).re := by simp [hσ]
  rw [zeta_eq_tsum_one_div_nat_cpow hre]
  have hsumm : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (σ : ℂ)) :=
    summable_one_div_nat_cpow.mpr hre
  rw [re_tsum hsumm]
  have hsumm_re : Summable (fun n : ℕ => (1 / (n : ℂ) ^ (σ : ℂ)).re) :=
    Complex.reCLM.summable hsumm
  have h_nonneg : ∀ n : ℕ, 0 ≤ (1 / (n : ℂ) ^ (σ : ℂ)).re := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hσ_ne : (σ : ℂ) ≠ 0 := by
        intro h; have := Complex.ofReal_eq_zero.mp h; linarith
      simp [Complex.zero_cpow hσ_ne]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hn_pos_c : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos
      have hrw : ((n : ℂ) : ℂ) ^ (σ : ℂ) = ((↑((n : ℝ) ^ σ) : ℂ)) := by
        rw [show ((n : ℂ) : ℂ) = (↑((n : ℝ)) : ℂ) from by push_cast; rfl]
        rw [← Complex.ofReal_cpow hn_pos_c]
      rw [hrw, show (1 : ℂ) / ((↑((n : ℝ) ^ σ) : ℂ)) = (↑(1 / ((n : ℝ) ^ σ)) : ℂ) from by
        rw [Complex.ofReal_div, Complex.ofReal_one],
        Complex.ofReal_re]
      positivity
  have h_tsum_ge : (1 / ((1 : ℕ) : ℂ) ^ (σ : ℂ)).re ≤
      tsum (fun (n : ℕ) => (1 / (n : ℂ) ^ (σ : ℂ)).re) :=
    hsumm_re.le_tsum 1 (fun n _ => h_nonneg n)
  have h_term_one : (1 / (((1 : ℕ) : ℂ)) ^ (σ : ℂ)).re = 1 := by simp
  rw [h_term_one] at h_tsum_ge
  convert h_tsum_ge using 1

/-- ‖ζ(σ)‖ ≥ 1 for real σ > 1. -/
private lemma zeta_real_norm_ge_one (σ : ℝ) (hσ : 1 < σ) :
    (1 : ℝ) ≤ ‖riemannZeta (σ : ℂ)‖ :=
  le_trans (zeta_real_re_ge_one σ hσ) (Complex.re_le_norm _)

/-- Norm lower bound: ‖ξ(2n+2)‖ ≥ (n+1)(2n+1) · π^{-(n+1)} · n!. -/
private lemma xi_at_even_norm_ge (n : ℕ) :
    ((n : ℝ) + 1) * ((2 * n : ℝ) + 1) * Real.pi ^ (-((n : ℝ) + 1)) * (n.factorial : ℝ) ≤
      ‖RiemannXiAlt (↑(2 * n + 2 : ℕ) : ℂ)‖ := by
  rw [xi_at_even]
  have hσ_gt : (1 : ℝ) < (↑(2 * n + 2 : ℕ) : ℝ) := by norm_cast; omega
  have hζ_cast : (↑(2 * n + 2 : ℕ) : ℂ) = ((↑(2 * n + 2 : ℕ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hζ_cast]
  have hζ_norm : (1 : ℝ) ≤ ‖riemannZeta ((↑(2 * n + 2 : ℕ) : ℝ) : ℂ)‖ :=
    zeta_real_norm_ge_one _ hσ_gt
  have h_prod_nonneg :
      (0 : ℝ) ≤ ((n : ℝ) + 1) * ((2 * n : ℝ) + 1) * Real.pi ^ (-((n : ℝ) + 1)) *
        (n.factorial : ℝ) := by
    have h1 : (0 : ℝ) < Real.pi ^ (-((n : ℝ) + 1)) := Real.rpow_pos_of_pos Real.pi_pos _
    positivity
  rw [show ((n : ℂ) + 1) * ((2 * n : ℂ) + 1) * ((↑Real.pi : ℂ) ^ (-((n : ℂ) + 1))) *
        (n.factorial : ℂ) * riemannZeta ((↑(2 * n + 2 : ℕ) : ℝ) : ℂ) =
      (((n : ℝ) + 1 : ℝ) : ℂ) * (((2 * n : ℝ) + 1 : ℝ) : ℂ) *
      ((↑Real.pi : ℂ) ^ (-((n : ℂ) + 1))) * ((n.factorial : ℝ) : ℂ) *
      riemannZeta ((↑(2 * n + 2 : ℕ) : ℝ) : ℂ) from by push_cast; ring]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have h_pi : ‖(↑Real.pi : ℂ) ^ (-((n : ℂ) + 1))‖ = Real.pi ^ (-((n : ℝ) + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp
  rw [h_pi]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 1)]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n.factorial : ℝ))]
  calc ((n : ℝ) + 1) * ((2 * n : ℝ) + 1) * Real.pi ^ (-((n : ℝ) + 1)) * (n.factorial : ℝ)
      = ((n : ℝ) + 1) * ((2 * n : ℝ) + 1) * Real.pi ^ (-((n : ℝ) + 1)) *
          (n.factorial : ℝ) * 1 := by ring
    _ ≤ ((n : ℝ) + 1) * ((2 * n : ℝ) + 1) * Real.pi ^ (-((n : ℝ) + 1)) *
          (n.factorial : ℝ) * ‖riemannZeta ((↑(2 * n + 2 : ℕ) : ℝ) : ℂ)‖ :=
        mul_le_mul_of_nonneg_left hζ_norm h_prod_nonneg

/-- Norm of RHS ‖P(2n+2)·exp(A+B(2n+2))‖ ≤ C · E^n · (n+2)^d for some constants. -/
private lemma xi_rhs_norm_le (P : Polynomial ℂ) (A B : ℂ) :
    ∃ C E : ℝ, 0 < C ∧ 0 < E ∧ ∀ n : ℕ,
      ‖P.eval (↑(2 * n + 2 : ℕ) : ℂ) * exp (A + B * (↑(2 * n + 2 : ℕ) : ℂ))‖ ≤
        C * E ^ n * ((n : ℝ) + 2) ^ P.natDegree := by
  refine ⟨((∑ i ∈ P.support, ‖P.coeff i‖) + 1) * 3 ^ P.natDegree *
    Real.exp (‖A‖ + 2 * ‖B‖), Real.exp (2 * ‖B‖), ?_, Real.exp_pos _, fun n => ?_⟩
  · have h_sum_nn : (0 : ℝ) ≤ ∑ i ∈ P.support, ‖P.coeff i‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have h_exp_pos : (0 : ℝ) < Real.exp (‖A‖ + 2 * ‖B‖) := Real.exp_pos _
    have h3_pos : (0 : ℝ) < 3 ^ P.natDegree := by positivity
    have h_k_pos : (0 : ℝ) < (∑ i ∈ P.support, ‖P.coeff i‖) + 1 := by linarith
    positivity
  -- Show the per-n bound
  rw [norm_mul]
  -- Bound ‖P(2n+2)‖ using poly_eval_norm_le
  have h_norm_z : ‖(↑(2 * n + 2 : ℕ) : ℂ)‖ = 2 * (n : ℝ) + 2 := by
    rw [show (↑(2 * n + 2 : ℕ) : ℂ) = ((2 * (n : ℝ) + 2 : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h_poly := poly_eval_norm_le P (↑(2 * n + 2 : ℕ) : ℂ)
  rw [h_norm_z] at h_poly
  have h_step : (2 * (n : ℝ) + 2 + 1) = 2 * (n : ℝ) + 3 := by ring
  rw [h_step] at h_poly
  have h_sum_le_k : (∑ i ∈ P.support, ‖P.coeff i‖) ≤
      (∑ i ∈ P.support, ‖P.coeff i‖) + 1 := by linarith
  have h_poly_bound : ‖P.eval (↑(2 * n + 2 : ℕ) : ℂ)‖ ≤
      ((∑ i ∈ P.support, ‖P.coeff i‖) + 1) * (2 * (n : ℝ) + 3) ^ P.natDegree := by
    exact le_trans h_poly
      (mul_le_mul_of_nonneg_right h_sum_le_k (by positivity))
  -- (2n+3) ≤ 3(n+2)
  have h_2n3_le : 2 * (n : ℝ) + 3 ≤ 3 * ((n : ℝ) + 2) := by linarith
  have h_poly_bound_final : ‖P.eval (↑(2 * n + 2 : ℕ) : ℂ)‖ ≤
      ((∑ i ∈ P.support, ‖P.coeff i‖) + 1) * 3 ^ P.natDegree * ((n : ℝ) + 2) ^ P.natDegree := by
    have h_pow : (2 * (n : ℝ) + 3) ^ P.natDegree ≤ (3 * ((n : ℝ) + 2)) ^ P.natDegree :=
      pow_le_pow_left₀ (by positivity) h_2n3_le _
    have h_factor : (3 * ((n : ℝ) + 2)) ^ P.natDegree =
        3 ^ P.natDegree * ((n : ℝ) + 2) ^ P.natDegree := by rw [mul_pow]
    have h_k_nn : (0 : ℝ) ≤ (∑ i ∈ P.support, ‖P.coeff i‖) + 1 := by
      have := Finset.sum_nonneg (s := P.support) (f := fun i => ‖P.coeff i‖)
        (fun i _ => norm_nonneg _)
      linarith
    calc ‖P.eval (↑(2 * n + 2 : ℕ) : ℂ)‖
        ≤ ((∑ i ∈ P.support, ‖P.coeff i‖) + 1) * (2 * (n : ℝ) + 3) ^ P.natDegree :=
          h_poly_bound
      _ ≤ ((∑ i ∈ P.support, ‖P.coeff i‖) + 1) * (3 * ((n : ℝ) + 2)) ^ P.natDegree :=
          mul_le_mul_of_nonneg_left h_pow h_k_nn
      _ = ((∑ i ∈ P.support, ‖P.coeff i‖) + 1) * 3 ^ P.natDegree *
            ((n : ℝ) + 2) ^ P.natDegree := by rw [h_factor]; ring
  -- Bound the exp factor
  rw [Complex.norm_exp]
  have h_re : (A + B * (↑(2 * n + 2 : ℕ) : ℂ)).re =
      A.re + (B.re * (2 * (n : ℝ) + 2) - B.im * 0) := by
    rw [Complex.add_re, Complex.mul_re]
    simp only [Complex.ofReal_natCast, Complex.natCast_re, Complex.natCast_im]
    push_cast
    ring
  rw [h_re]
  simp only [mul_zero, sub_zero]
  -- Re(A) ≤ ‖A‖, |B.re·(2n+2)| ≤ ‖B‖·(2n+2) = 2‖B‖ + 2‖B‖·n
  have hA_re : A.re ≤ ‖A‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have hB_re : |B.re| ≤ ‖B‖ := Complex.abs_re_le_norm _
  have h_exp_arg_le : A.re + B.re * (2 * (n : ℝ) + 2) ≤ ‖A‖ + 2 * ‖B‖ + 2 * ‖B‖ * n := by
    have hn_nn : (0 : ℝ) ≤ 2 * (n : ℝ) + 2 := by positivity
    have h1 : B.re * (2 * (n : ℝ) + 2) ≤ |B.re| * (2 * (n : ℝ) + 2) :=
      le_trans (le_abs_self _) (by rw [abs_mul, abs_of_nonneg hn_nn])
    have h2 : |B.re| * (2 * (n : ℝ) + 2) ≤ ‖B‖ * (2 * (n : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right hB_re hn_nn
    nlinarith
  have h_exp_bound : Real.exp (A.re + B.re * (2 * (n : ℝ) + 2)) ≤
      Real.exp (‖A‖ + 2 * ‖B‖) * Real.exp (2 * ‖B‖) ^ n := by
    calc Real.exp (A.re + B.re * (2 * (n : ℝ) + 2))
        ≤ Real.exp (‖A‖ + 2 * ‖B‖ + 2 * ‖B‖ * n) := Real.exp_le_exp.mpr h_exp_arg_le
      _ = Real.exp (‖A‖ + 2 * ‖B‖) * Real.exp (2 * ‖B‖ * n) := by rw [← Real.exp_add]
      _ = Real.exp (‖A‖ + 2 * ‖B‖) * Real.exp (2 * ‖B‖) ^ n := by
          congr 1
          have h1 : (2 * ‖B‖ * (n : ℝ)) = (2 * ‖B‖) * (n : ℝ) := by ring
          rw [h1, Real.exp_mul]
          exact_mod_cast (Real.rpow_natCast (Real.exp (2 * ‖B‖)) n).symm
  -- Combine
  have h_k_nn : (0 : ℝ) ≤ (∑ i ∈ P.support, ‖P.coeff i‖) + 1 := by
    have := Finset.sum_nonneg (s := P.support) (f := fun i => ‖P.coeff i‖)
      (fun i _ => norm_nonneg _)
    linarith
  calc ‖P.eval (↑(2 * n + 2 : ℕ) : ℂ)‖ * Real.exp (A.re + B.re * (2 * (n : ℝ) + 2))
      ≤ (((∑ i ∈ P.support, ‖P.coeff i‖) + 1) * 3 ^ P.natDegree * ((n : ℝ) + 2) ^ P.natDegree) *
          (Real.exp (‖A‖ + 2 * ‖B‖) * Real.exp (2 * ‖B‖) ^ n) :=
        mul_le_mul h_poly_bound_final h_exp_bound (Real.exp_nonneg _) (by positivity)
    _ = ((∑ i ∈ P.support, ‖P.coeff i‖) + 1) * 3 ^ P.natDegree *
          Real.exp (‖A‖ + 2 * ‖B‖) * Real.exp (2 * ‖B‖) ^ n * ((n : ℝ) + 2) ^ P.natDegree := by
        ring

-- PRIOR PROOF ATTEMPT (had cascading unfold_let and Complex.norm_real issues):
-- KEPT AS COMMENT FOR REFERENCE
/-
  set d := P.natDegree
  set K := (∑ i ∈ P.support, ‖P.coeff i‖) + 1
  have hK_pos : 0 < K := by
    show 0 < (∑ i ∈ P.support, ‖P.coeff i‖) + 1
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ P.support) => norm_nonneg (P.coeff i))]
  set C := K * 3 ^ d * Real.exp (‖A‖ + 2 * ‖B‖)
  set E := Real.exp (2 * ‖B‖)
  have hC_pos : 0 < C := by
    show 0 < K * 3 ^ d * Real.exp (‖A‖ + 2 * ‖B‖)
    positivity
  have hE_pos : 0 < E := Real.exp_pos _
  refine ⟨C, E, hC_pos, hE_pos, fun n => ?_⟩
  rw [norm_mul]
  have h_norm_z : ‖(↑(2 * n + 2 : ℕ) : ℂ)‖ = 2 * (n : ℝ) + 2 := by
    rw [show (↑(2 * n + 2 : ℕ) : ℂ) = ((2 * (n : ℝ) + 2 : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h_poly : ‖P.eval (↑(2 * n + 2 : ℕ) : ℂ)‖ ≤ K * (2 * (n : ℝ) + 3) ^ d := by
    have := poly_eval_norm_le P (↑(2 * n + 2 : ℕ) : ℂ)
    rw [h_norm_z] at this
    have h_step : (2 * (n : ℝ) + 2 + 1) = 2 * (n : ℝ) + 3 := by ring
    rw [h_step] at this
    have h_sum_le : (∑ i ∈ P.support, ‖P.coeff i‖) ≤ K := by
      show (∑ i ∈ P.support, ‖P.coeff i‖) ≤ (∑ i ∈ P.support, ‖P.coeff i‖) + 1; linarith
    exact le_trans this (mul_le_mul_of_nonneg_right h_sum_le (by positivity))
  have h_2n3_le : 2 * (n : ℝ) + 3 ≤ 3 * ((n : ℝ) + 2) := by linarith
  have h_poly_bound : ‖P.eval (↑(2 * n + 2 : ℕ) : ℂ)‖ ≤ K * 3 ^ d * ((n : ℝ) + 2) ^ d := by
    have h_step : K * (2 * (n : ℝ) + 3) ^ d ≤ K * (3 * ((n : ℝ) + 2)) ^ d := by
      apply mul_le_mul_of_nonneg_left _ hK_pos.le
      exact pow_le_pow_left₀ (by positivity) h_2n3_le d
    have h_factor : (3 * ((n : ℝ) + 2)) ^ d = 3 ^ d * ((n : ℝ) + 2) ^ d := by
      rw [mul_pow]
    rw [h_factor] at h_step
    linarith [le_trans h_poly h_step]
  -- Now the exp factor
  have h_exp_eq : ‖exp (A + B * (↑(2 * n + 2 : ℕ) : ℂ))‖ =
      Real.exp ((A + B * (↑(2 * n + 2 : ℕ) : ℂ)).re) := Complex.norm_exp _
  rw [h_exp_eq]
  have h_re : (A + B * (↑(2 * n + 2 : ℕ) : ℂ)).re =
      A.re + B.re * (2 * (n : ℝ) + 2) - B.im * 0 := by
    rw [Complex.add_re, Complex.mul_re]
    push_cast
    simp
    ring
  rw [h_re]
  simp only [mul_zero, sub_zero]
  -- ‖P(2n+2)‖ · exp(A.re + B.re·(2n+2)) ≤ C · E^n · (n+2)^d
  have h_exp_bound : Real.exp (A.re + B.re * (2 * (n : ℝ) + 2)) ≤
      Real.exp (‖A‖ + 2 * ‖B‖) * E ^ n := by
    -- A.re ≤ ‖A‖, B.re · (2n+2) ≤ |B.re| · (2n+2) ≤ ‖B‖ · (2n+2) = 2‖B‖ + 2‖B‖·n
    have hAre : A.re ≤ ‖A‖ := by
      calc A.re ≤ |A.re| := le_abs_self _
        _ ≤ ‖A‖ := Complex.abs_re_le_norm _
    have hBre_abs : |B.re| ≤ ‖B‖ := Complex.abs_re_le_norm _
    have h_exp_arg : A.re + B.re * (2 * (n : ℝ) + 2) ≤ ‖A‖ + 2 * ‖B‖ + 2 * ‖B‖ * n := by
      have h1 : B.re * (2 * (n : ℝ) + 2) ≤ |B.re| * (2 * (n : ℝ) + 2) := by
        have h_nn : 0 ≤ 2 * (n : ℝ) + 2 := by positivity
        calc B.re * (2 * (n : ℝ) + 2) ≤ |B.re * (2 * (n : ℝ) + 2)| := le_abs_self _
          _ = |B.re| * (2 * (n : ℝ) + 2) := by rw [abs_mul, abs_of_nonneg h_nn]
      have h2 : |B.re| * (2 * (n : ℝ) + 2) ≤ ‖B‖ * (2 * (n : ℝ) + 2) := by
        apply mul_le_mul_of_nonneg_right hBre_abs (by positivity)
      have h3 : ‖B‖ * (2 * (n : ℝ) + 2) = 2 * ‖B‖ + 2 * ‖B‖ * (n : ℝ) := by ring
      linarith
    calc Real.exp (A.re + B.re * (2 * (n : ℝ) + 2))
        ≤ Real.exp (‖A‖ + 2 * ‖B‖ + 2 * ‖B‖ * (n : ℝ)) := Real.exp_le_exp.mpr h_exp_arg
      _ = Real.exp (‖A‖ + 2 * ‖B‖) * Real.exp (2 * ‖B‖ * (n : ℝ)) := by
          rw [← Real.exp_add]
      _ = Real.exp (‖A‖ + 2 * ‖B‖) * E ^ n := by
          unfold_let E
          rw [show (2 * ‖B‖ * (n : ℝ)) = (n : ℝ) * (2 * ‖B‖) from by ring]
          rw [Real.exp_mul]
          rw [← Real.rpow_natCast (Real.exp (2 * ‖B‖)) n]
  calc ‖P.eval (↑(2 * n + 2 : ℕ) : ℂ)‖ * Real.exp (A.re + B.re * (2 * (n : ℝ) + 2))
      ≤ (K * 3 ^ d * ((n : ℝ) + 2) ^ d) * (Real.exp (‖A‖ + 2 * ‖B‖) * E ^ n) :=
        mul_le_mul h_poly_bound h_exp_bound (Real.exp_nonneg _) (by positivity)
    _ = C * E ^ n * ((n : ℝ) + 2) ^ d := by unfold_let C; ring
-/

/-- Unified growth contradiction: ξ cannot equal P·exp(A+Bs) for any polynomial P,
constants A, B. Proof: LHS grows factorially (via xi_at_even_norm_ge), RHS is
polynomial·exponential (via xi_rhs_norm_le), factorial_exceeds_exp gives contradiction. -/
private lemma xi_not_poly_exp (P : Polynomial ℂ) (A B : ℂ)
    (hxi : ∀ s, RiemannXiAlt s = P.eval s * exp (A + B * s)) : False := by
  obtain ⟨C, E, hC_pos, hE_pos, hRHS⟩ := xi_rhs_norm_le P A B
  -- Choose D large enough that factorial beats π·C·D^n·(n+2)^d·2^n (or bound (n+2)^d by 2^n)
  -- Strategy: ξ(2N+2) equals P·exp, so norm equation:
  -- (N+1)(2N+1)·π^{-(N+1)}·N! ≤ ‖ξ(2N+2)‖ = ‖P·exp‖ ≤ C·E^N·(N+2)^d
  -- Multiply by π^(N+1): (N+1)(2N+1)·N! ≤ C·π·(E·π)^N·(N+2)^d
  -- Use (N+2)^d ≤ 2^N for N large: ≤ C·π·(2Eπ)^N
  -- factorial_exceeds_exp gives contradiction for D = 2Eπ, constant = C·π·4
  set d := P.natDegree with hd_def
  -- Get N₀ such that for n ≥ N₀: C · π · 4 · (2 · E · π) ^ n < n!
  have hD_pos : 0 < 2 * E * Real.pi := by positivity
  have hCπ4_pos : 0 < C * Real.pi * 4 := by positivity
  obtain ⟨N₀, hN₀⟩ := factorial_exceeds_exp (C * Real.pi * 4) (2 * E * Real.pi) hCπ4_pos hD_pos
  -- Get N₁ such that for n ≥ N₁: (n+2)^d ≤ 2^n. Proof via polynomial/exp tendsto 0.
  have h_poly_vs_two_pow : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ((n : ℝ) + 2) ^ d ≤ 2 ^ n := by
    -- First: n^d · (1/2)^n → 0 (polynomial × geometric with ratio < 1)
    have h_n_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ d * (1/2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_const_mul_const_pow_of_abs_lt_one d (by rw [abs_of_pos] <;> norm_num)
    -- For n ≥ 2: (n+2)^d ≤ (2n)^d = 2^d · n^d.
    -- So (n+2)^d · (1/2)^n ≤ 2^d · n^d · (1/2)^n → 0.
    -- Extract N₁ such that 2^d · n^d · (1/2)^n < 1/2 for n ≥ N₁.
    -- Then (n+2)^d · (1/2)^n ≤ 2^d · (n^d · (1/2)^n) and we want < 1, so < 1/2 for n suffices.
    -- Actually simpler: we want (n+2)^d ≤ 2^n ⟺ (n+2)^d · (1/2)^n ≤ 1.
    -- Since (n+2)^d ≤ (2n)^d = 2^d · n^d for n ≥ 2, it suffices
    -- 2^d · n^d · (1/2)^n ≤ 1, i.e., n^d · (1/2)^n ≤ (1/2)^d.
    have h_ev : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ d * (1/2 : ℝ) ^ n < (1/2 : ℝ) ^ d :=
      h_n_tendsto.eventually (gt_mem_nhds (by positivity))
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_ev
    refine ⟨max N₁ 2, fun n hn => ?_⟩
    have hn_N₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have hn_2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have h_bound := hN₁ n hn_N₁
    -- (n+2) ≤ 2n for n ≥ 2
    have hn_real : (2 : ℝ) ≤ n := by exact_mod_cast hn_2
    have h_plus_two : (n : ℝ) + 2 ≤ 2 * n := by linarith
    have h_nn : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
    have h_pow_bound : ((n : ℝ) + 2) ^ d ≤ (2 * (n : ℝ)) ^ d :=
      pow_le_pow_left₀ h_nn h_plus_two _
    have h_factor : (2 * (n : ℝ)) ^ d = 2 ^ d * (n : ℝ) ^ d := by rw [mul_pow]
    -- We have: n^d * (1/2)^n < (1/2)^d
    -- Want: (n+2)^d ≤ 2^n
    have h_2pow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have h_half_inv : (1/2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by
      rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num, inv_pow]
    -- Reduce to (n+2)^d * (1/2)^n ≤ 1
    have h_prod_bound : ((n : ℝ) + 2) ^ d * (1/2 : ℝ) ^ n ≤ 1 := by
      calc ((n : ℝ) + 2) ^ d * (1/2 : ℝ) ^ n
          ≤ (2 * (n : ℝ)) ^ d * (1/2 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right h_pow_bound (by positivity)
        _ = 2 ^ d * ((n : ℝ) ^ d * (1/2 : ℝ) ^ n) := by rw [h_factor]; ring
        _ ≤ 2 ^ d * (1/2 : ℝ) ^ d := by
            apply mul_le_mul_of_nonneg_left (le_of_lt h_bound) (by positivity)
        _ = (2 * (1/2 : ℝ)) ^ d := by rw [mul_pow]
        _ = 1 := by norm_num
    -- Convert (n+2)^d * (1/2)^n ≤ 1 to (n+2)^d ≤ 2^n
    rw [h_half_inv, mul_inv_le_iff₀ h_2pow_pos] at h_prod_bound
    linarith
  obtain ⟨N₁, hN₁⟩ := h_poly_vs_two_pow
  set N := max N₀ N₁
  have hN_ge_N₀ : N₀ ≤ N := le_max_left _ _
  have hN_ge_N₁ : N₁ ≤ N := le_max_right _ _
  -- Apply hypothesis at s = 2N+2
  have h_eq := hxi (↑(2 * N + 2 : ℕ) : ℂ)
  have h_norm_eq :
      ‖RiemannXiAlt (↑(2 * N + 2 : ℕ) : ℂ)‖ =
      ‖P.eval (↑(2 * N + 2 : ℕ) : ℂ) * exp (A + B * (↑(2 * N + 2 : ℕ) : ℂ))‖ := by
    rw [h_eq]
  have h_lhs := xi_at_even_norm_ge N
  have h_rhs := hRHS N
  -- Combining: (N+1)(2N+1)·π^{-(N+1)}·N! ≤ C · E^N · (N+2)^d
  have h_combined :
      ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * Real.pi ^ (-((N : ℝ) + 1)) * (N.factorial : ℝ) ≤
      C * E ^ N * ((N : ℝ) + 2) ^ d := by
    calc ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * Real.pi ^ (-((N : ℝ) + 1)) * (N.factorial : ℝ)
        ≤ ‖RiemannXiAlt (↑(2 * N + 2 : ℕ) : ℂ)‖ := h_lhs
      _ = ‖P.eval (↑(2 * N + 2 : ℕ) : ℂ) * exp (A + B * (↑(2 * N + 2 : ℕ) : ℂ))‖ := h_norm_eq
      _ ≤ C * E ^ N * ((N : ℝ) + 2) ^ d := h_rhs
  -- Multiply by π^(N+1)
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπN_pos : (0 : ℝ) < Real.pi ^ ((N : ℝ) + 1) := Real.rpow_pos_of_pos hπ_pos _
  have h_mul_pi : Real.pi ^ (-((N : ℝ) + 1)) * Real.pi ^ ((N : ℝ) + 1) = 1 := by
    rw [← Real.rpow_add hπ_pos]
    rw [show -((N : ℝ) + 1) + ((N : ℝ) + 1) = 0 from by ring]
    exact Real.rpow_zero _
  have h_combined2 :
      ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ) ≤
      C * E ^ N * ((N : ℝ) + 2) ^ d * Real.pi ^ ((N : ℝ) + 1) := by
    have h_step := mul_le_mul_of_nonneg_right h_combined hπN_pos.le
    have h_simp :
        ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * Real.pi ^ (-((N : ℝ) + 1)) *
          (N.factorial : ℝ) * Real.pi ^ ((N : ℝ) + 1) =
        ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ) *
          (Real.pi ^ (-((N : ℝ) + 1)) * Real.pi ^ ((N : ℝ) + 1)) := by ring
    rw [h_simp, h_mul_pi, mul_one] at h_step
    linarith
  -- π^(N+1) = π · π^N
  have h_piN : Real.pi ^ ((N : ℝ) + 1) = Real.pi * Real.pi ^ N := by
    rw [show ((N : ℝ) + 1) = (N : ℝ) + (1 : ℝ) from rfl]
    rw [Real.rpow_add hπ_pos, Real.rpow_one]
    rw [show Real.pi ^ (N : ℝ) = Real.pi ^ N from by
      rw [← Real.rpow_natCast Real.pi N]]
    ring
  -- (E·π)^N = E^N · π^N
  have h_mul_pow : (E * Real.pi) ^ N = E ^ N * Real.pi ^ N := by rw [mul_pow]
  have h_combined3 :
      ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ) ≤
      C * Real.pi * (E * Real.pi) ^ N * ((N : ℝ) + 2) ^ d := by
    rw [h_piN] at h_combined2
    rw [h_mul_pow]
    linarith [h_combined2]
  -- (N+2)^d ≤ 2^N
  have h_combined4 :
      ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ) ≤
      C * Real.pi * (2 * E * Real.pi) ^ N := by
    have h_pow_eq : (2 * E * Real.pi) ^ N = 2 ^ N * (E * Real.pi) ^ N := by
      rw [show (2 * E * Real.pi : ℝ) = 2 * (E * Real.pi) from by ring]
      rw [mul_pow]
    have h_EPi_nn : (0 : ℝ) ≤ (E * Real.pi) ^ N := by positivity
    have h_step : (E * Real.pi) ^ N * ((N : ℝ) + 2) ^ d ≤ (2 * E * Real.pi) ^ N := by
      rw [h_pow_eq]
      calc (E * Real.pi) ^ N * ((N : ℝ) + 2) ^ d
          ≤ (E * Real.pi) ^ N * 2 ^ N :=
            mul_le_mul_of_nonneg_left (hN₁ N hN_ge_N₁) h_EPi_nn
        _ = 2 ^ N * (E * Real.pi) ^ N := by ring
    calc ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ)
        ≤ C * Real.pi * (E * Real.pi) ^ N * ((N : ℝ) + 2) ^ d := h_combined3
      _ = C * Real.pi * ((E * Real.pi) ^ N * ((N : ℝ) + 2) ^ d) := by ring
      _ ≤ C * Real.pi * (2 * E * Real.pi) ^ N := by
          apply mul_le_mul_of_nonneg_left h_step (by positivity)
  -- LHS ≥ N! (since (N+1)(2N+1) ≥ 1)
  have h_lhs_ge_fact : (N.factorial : ℝ) ≤
      ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ) := by
    have h_fact_nn : (0 : ℝ) ≤ (N.factorial : ℝ) := by positivity
    have h_coef_ge_one : (1 : ℝ) ≤ ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) := by
      have : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith
    nlinarith
  -- N! ≤ C·π·(2Eπ)^N but factorial_exceeds_exp says C·π·4·(2Eπ)^N < N!
  have h_fact_lt := hN₀ N hN_ge_N₀
  -- C·π·(2Eπ)^N < C·π·4·(2Eπ)^N
  have hD_pow_pos : (0 : ℝ) < (2 * E * Real.pi) ^ N := pow_pos hD_pos N
  have hCπ_pos : (0 : ℝ) < C * Real.pi := by positivity
  have h_strict : C * Real.pi * (2 * E * Real.pi) ^ N <
      C * Real.pi * 4 * (2 * E * Real.pi) ^ N := by
    have hCπ_lt : C * Real.pi < C * Real.pi * 4 := by nlinarith
    have := mul_lt_mul_of_pos_right hCπ_lt hD_pow_pos
    linarith
  linarith

-- Prior proof attempt using xi_rhs_norm_le + factorial_exceeds_exp + xi_at_even_norm_ge.
-- Commented out due to cascading tactic issues during integration.
/-
private lemma xi_not_poly_exp_v1 (P : Polynomial ℂ) (A B : ℂ)
    (hxi : ∀ s, RiemannXiAlt s = P.eval s * exp (A + B * s)) : False := by
  set d := P.natDegree
  obtain ⟨C, E, hC_pos, hE_pos, hRHS⟩ := xi_rhs_norm_le P A B
  -- Pick D > E·π·(d+1) such that n! > ((d+1)! · C · π) · D^n eventually
  -- We need: (n+1)(2n+1)·π^{-(n+1)}·n! > C · E^n · (n+2)^d
  -- i.e., n! > C · π · (E·π)^n · (n+2)^d / ((n+1)(2n+1))
  -- Since (n+2)^d ≤ (n+2)^d, and (n+2)^d · M^n ≤ (M+1)^n for n large, bound:
  --   We have (E·π)^n · (n+2)^d. Let D = E·π·(d+2). Then (n+2)^d ≤ (n+2)^d.
  -- Use: (n+2)^d · M^n ≤ (2M)^n for n ≥ N₀(d, M).
  set M := E * Real.pi
  have hM_pos : 0 < M := by unfold_let M; positivity
  -- Bound (n+2)^d · M^n ≤ (2M)^n · M^(-N₀) for n ≥ N₀(d)
  -- Actually simpler: (n+2)^d ≤ (2M)^n / M^n · (n+2)^d, need (n+2)^d ≤ (2)^n for n large
  -- (n+2)^d ≤ 2^n ⟺ d·log(n+2) ≤ n·log 2, which holds for n large
  -- Just use: for n ≥ 4d+4, we have (n+2)^d ≤ 2^n (since 2^n grows faster)
  -- Combined: n! > something · (2M)^n ⟺ n! > something' · D^n with D = 2M
  set D := 2 * M
  have hD_pos : 0 < D := by unfold_let D; positivity
  set C' := C * Real.pi * 4
  have hC'_pos : 0 < C' := by unfold_let C'; positivity
  obtain ⟨N₀, hN₀⟩ := factorial_exceeds_exp C' D hC'_pos hD_pos
  -- Also need (n+2)^d ≤ 2^n for n large
  have h_poly_vs_exp : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ((n : ℝ) + 2) ^ d ≤ 2 ^ n := by
    -- (n+2)^d ≤ 2^n eventually.  Via factorial_exceeds_exp applied to (1, some D)
    -- Actually just use that (n+2)^d / 2^n → 0.
    -- For simplicity, pick large enough. We have:
    -- Take N₁ = 2^(d+2). Then for n ≥ N₁, (n+2)^d ≤ n^(d+1) ≤ (..) Hmm this needs proof.
    -- Actually simpler: use that x^d / 2^x → 0 for any d.
    have h_tendsto : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ d / 2 ^ n)
        Filter.atTop (nhds 0) := by
      -- Polynomial / exponential tends to 0
      have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ d / (2 : ℝ) ^ n)
          Filter.atTop (nhds 0) := by
        have h_eq : (fun n : ℕ => ((n : ℝ) + 2) ^ d / (2 : ℝ) ^ n) =
            (fun n : ℕ => ((n : ℝ) + 2) ^ d * (1 / 2) ^ n) := by
          ext n; rw [div_eq_mul_inv, ← inv_pow, one_div]
        rw [h_eq]
        have : ‖(1/2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
        have h_poly_exp :
            Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ d * (1 / 2) ^ n)
              Filter.atTop (nhds 0) := by
          -- Shift Mathlib's standard `n^d r^n → 0` geometric domination by two.
          have hbase : Filter.Tendsto
              (fun m : ℕ => (m : ℝ) ^ d * (1 / 2 : ℝ) ^ m)
              Filter.atTop (nhds 0) := by
            exact tendsto_pow_const_mul_const_pow_of_lt_one d
              (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
          have hcomp := hbase.comp (tendsto_add_atTop_nat 2)
          have hscale : Filter.Tendsto
              (fun n : ℕ => 4 * (((n + 2 : ℕ) : ℝ) ^ d * (1 / 2 : ℝ) ^ (n + 2)))
              Filter.atTop (nhds 0) := by
            simpa using hcomp.const_mul (4 : ℝ)
          have heq : (fun n : ℕ => ((n : ℝ) + 2) ^ d * (1 / 2 : ℝ) ^ n) =
              (fun n : ℕ => 4 * (((n + 2 : ℕ) : ℝ) ^ d * (1 / 2 : ℝ) ^ (n + 2))) := by
            funext n
            have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by norm_num
            rw [hcast, pow_add]
            norm_num
            ring
          rw [heq]
          exact hscale
        exact h_poly_exp
      exact h1
    exact Filter.eventually_atTop.mp
      (h_tendsto.eventually (gt_mem_nhds zero_lt_one)) |>.imp fun N₁ hN₁ =>
      fun n hn => by
        have := hN₁ n hn
        rw [div_lt_one (by positivity)] at this
        linarith
  obtain ⟨N₁, hN₁⟩ := h_poly_vs_exp
  set N := max N₀ N₁
  have hN_lhs := hN₀ N (le_max_left _ _)
  have hN_rhs := hN₁ N (le_max_right _ _)
  -- Now combine: apply hypothesis at s = 2N+2
  have h_eq := hxi (↑(2 * N + 2 : ℕ) : ℂ)
  have h_norm_eq : ‖RiemannXiAlt (↑(2 * N + 2 : ℕ) : ℂ)‖ =
      ‖P.eval (↑(2 * N + 2 : ℕ) : ℂ) * exp (A + B * (↑(2 * N + 2 : ℕ) : ℂ))‖ := by
    rw [h_eq]
  -- LHS bound from xi_at_even_norm_ge
  have h_lhs := xi_at_even_norm_ge N
  -- RHS bound from xi_rhs_norm_le
  have h_rhs := hRHS N
  -- Combining: (N+1)(2N+1)·π^(-(N+1))·N! ≤ ‖ξ(2N+2)‖ = ‖P·exp‖ ≤ C·E^N·(N+2)^d
  have h_ineq :
      ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * Real.pi ^ (-((N : ℝ) + 1)) * (N.factorial : ℝ) ≤
      C * E ^ N * ((N : ℝ) + 2) ^ d := by
    calc ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * Real.pi ^ (-((N : ℝ) + 1)) * (N.factorial : ℝ)
        ≤ ‖RiemannXiAlt (↑(2 * N + 2 : ℕ) : ℂ)‖ := h_lhs
      _ = ‖P.eval (↑(2 * N + 2 : ℕ) : ℂ) * exp (A + B * (↑(2 * N + 2 : ℕ) : ℂ))‖ :=
          h_norm_eq
      _ ≤ C * E ^ N * ((N : ℝ) + 2) ^ d := h_rhs
  -- Now multiply both sides by π^(N+1) to get:
  -- (N+1)(2N+1)·N! ≤ C · (E·π)^N · π · (N+2)^d
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπN_pos : (0 : ℝ) < Real.pi ^ ((N : ℝ) + 1) := Real.rpow_pos_of_pos hπ_pos _
  have h_mul_eq : Real.pi ^ (-((N : ℝ) + 1)) * Real.pi ^ ((N : ℝ) + 1) = 1 := by
    rw [← Real.rpow_add hπ_pos]
    ring_nf
    exact Real.rpow_zero _
  have h_ineq2 :
      ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ) ≤
      C * E ^ N * ((N : ℝ) + 2) ^ d * Real.pi ^ ((N : ℝ) + 1) := by
    have h_step := mul_le_mul_of_nonneg_right h_ineq (le_of_lt hπN_pos)
    have h_lhs_simp :
        ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * Real.pi ^ (-((N : ℝ) + 1)) *
          (N.factorial : ℝ) * Real.pi ^ ((N : ℝ) + 1) =
        ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ) *
          (Real.pi ^ (-((N : ℝ) + 1)) * Real.pi ^ ((N : ℝ) + 1)) := by ring
    rw [h_lhs_simp, h_mul_eq, mul_one] at h_step
    linarith
  -- Now: C · E^N · (N+2)^d · π^(N+1) ≤ C · π · M^N · (N+2)^d · (using π^(N+1) = π · π^N)
  have h_piN : Real.pi ^ ((N : ℝ) + 1) = Real.pi * Real.pi ^ N := by
    rw [Real.rpow_add_one (ne_of_gt hπ_pos)]
    ring_nf
    congr 1
    rw [Real.rpow_natCast]
  have h_ineq3 :
      ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ) ≤
      C * Real.pi * M ^ N * ((N : ℝ) + 2) ^ d := by
    rw [h_piN] at h_ineq2
    unfold_let M
    have h_mul_pow : (E * Real.pi) ^ N = E ^ N * Real.pi ^ N := by rw [mul_pow]
    rw [h_mul_pow]
    linarith [h_ineq2]
  -- (N+2)^d ≤ 2^N by hN_rhs
  -- So: LHS ≤ C · π · M^N · 2^N = C · π · (2M)^N = C · π · D^N
  have h_ineq4 :
      ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ) ≤
      C * Real.pi * D ^ N := by
    have h_step : M ^ N * ((N : ℝ) + 2) ^ d ≤ D ^ N := by
      have h_D : (D : ℝ) ^ N = M ^ N * 2 ^ N := by unfold_let D; rw [show (2 * M : ℝ) = M * 2 from by ring, mul_pow]
      rw [h_D]
      apply mul_le_mul_of_nonneg_left hN_rhs (pow_nonneg (le_of_lt hM_pos) _)
    calc ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ)
        ≤ C * Real.pi * M ^ N * ((N : ℝ) + 2) ^ d := h_ineq3
      _ = C * Real.pi * (M ^ N * ((N : ℝ) + 2) ^ d) := by ring
      _ ≤ C * Real.pi * D ^ N := by
          apply mul_le_mul_of_nonneg_left h_step
          positivity
  -- Now: LHS = (N+1)(2N+1)·N! ≥ N!. And from hN_lhs: C' · D^N < N!, where C' = C·π·4
  have h_N_fact_ge : (N.factorial : ℝ) ≤
      ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) * (N.factorial : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) * ((2 * N : ℝ) + 1) := by
      have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h2 : (0 : ℝ) ≤ (N.factorial : ℝ) := by positivity
    nlinarith
  -- C · π · D^N < C · π · 4 · D^N = C' · D^N < N!
  have h_C_lt : C * Real.pi * D ^ N < C' * D ^ N := by
    unfold_let C'
    have hD_pow : (0 : ℝ) < D ^ N := pow_pos hD_pos _
    have : C * Real.pi < C * Real.pi * 4 := by
      have : (1 : ℝ) < 4 := by norm_num
      have h_Cπ_pos : 0 < C * Real.pi := by positivity
      nlinarith
    calc C * Real.pi * D ^ N < (C * Real.pi * 4) * D ^ N := by
        apply (mul_lt_mul_right hD_pow).mpr; linarith
      _ = C * Real.pi * 4 * D ^ N := by ring
  -- Contradiction
  linarith [hN_lhs]
-/

/-- If ξ(s) = P(s)·exp(A+Bs) for polynomial P, constants A, B, then B = 0.
Proof: the hypothesis is inconsistent (ξ grows super-polynomially at even integers,
beating any P·exp), so False, hence any conclusion including B = 0. -/
private theorem xi_poly_exp_forces_B_zero (P : Polynomial ℂ) (A B : ℂ)
    (hxi : ∀ s, RiemannXiAlt s = P.eval s * exp (A + B * s)) : B = 0 := by
  exact absurd hxi (fun h => xi_not_poly_exp P A B h)

/-- ξ is not a polynomial: it grows super-polynomially along even integers.
Follows from `xi_not_poly_exp` with A = B = 0 (exp term becomes 1). -/
private theorem xi_not_polynomial :
    ¬ ∃ (P : Polynomial ℂ), ∀ s, RiemannXiAlt s = P.eval s := by
  rintro ⟨P, hP⟩
  apply xi_not_poly_exp P 0 0
  intro s
  rw [hP s]; simp

/-- Main reduction: If ξ has finitely many zeros, then ξ = P·exp(A+Bs) for some
polynomial P and constants A, B. Uses AnalyticQuotient to form the quotient, then
entire_nonvanishing_subquad_is_exp_linear. -/
private lemma xi_polyexp_of_finite_zeros (hfin : Set.Finite xiZeroSet) :
    ∃ (P : Polynomial ℂ) (A B : ℂ), ∀ s, RiemannXiAlt s = P.eval s * Complex.exp (A + B * s) := by
  -- Build polynomial P₀ = ∏_{ρ ∈ hfin.toFinset} (X - C ρ)^(analyticOrderAt ξ ρ).toNat
  -- Case split: is xiZeroSet empty or not?
  by_cases hempty : xiZeroSet = ∅
  · -- Empty zero case: ξ has no zeros, apply entire_nonvanishing_subquad_is_exp_linear directly
    have hxi_ne : ∀ z, RiemannXiAlt z ≠ 0 := by
      intro z hz
      have : z ∈ xiZeroSet := hz
      rw [hempty] at this
      exact this.elim
    have hxi_diff : Differentiable ℂ RiemannXiAlt := RiemannXiAlt_entire
    -- Get subquadratic exp growth bound for ξ
    obtain ⟨C_growth, hC_growth_pos, hxi_bound⟩ :=
      xi_growth_for_jensen
    -- Compute compact bound on ball(0, 2)
    have hCont : ContinuousOn RiemannXiAlt (Metric.closedBall (0 : ℂ) 2) :=
      (hxi_diff.continuous).continuousOn
    have hCompact : IsCompact (Metric.closedBall (0 : ℂ) 2) := isCompact_closedBall _ _
    obtain ⟨M, _, hM_bound⟩ : ∃ M, M ∈ Metric.closedBall (0 : ℂ) 2 ∧
        ∀ z ∈ Metric.closedBall (0 : ℂ) 2, ‖RiemannXiAlt z‖ ≤ ‖RiemannXiAlt M‖ := by
      exact hCompact.exists_isMaxOn (Set.nonempty_of_mem (Metric.mem_closedBall_self (by norm_num)))
        (Continuous.norm hxi_diff.continuous).continuousOn
    set M_bound := ‖RiemannXiAlt M‖ with hM_def
    -- Choose C_universal = max(C_growth, log(max M_bound 1) + 1) so that
    -- exp(C_universal) ≥ max M_bound 1 ≥ M_bound
    set C_universal : ℝ := max C_growth (Real.log (max M_bound 1) + 1) with hC_uni_def
    have hC_uni_pos : 0 < C_universal := by
      apply lt_of_lt_of_le hC_growth_pos
      exact le_max_left _ _
    have hC_uni_ge_Cgrowth : C_growth ≤ C_universal := le_max_left _ _
    have hC_uni_ge_logM : Real.log (max M_bound 1) + 1 ≤ C_universal := le_max_right _ _
    -- Apply entire_nonvanishing_subquad_is_exp_linear with C = C_universal
    obtain ⟨A, B, hAB⟩ := Aristotle.Standalone.NonvanishingEntireLinear.entire_nonvanishing_subquad_is_exp_linear
      RiemannXiAlt hxi_diff hxi_ne (3/2 : ℝ) C_universal (by norm_num) (by norm_num) hC_uni_pos
      (fun z => by
        have hpow_nn : 0 ≤ (‖z‖ + 1) ^ (3/2 : ℝ) :=
          Real.rpow_nonneg (by linarith [norm_nonneg z]) _
        have hpow_ge_one : 1 ≤ (‖z‖ + 1) ^ (3/2 : ℝ) := by
          have : (1 : ℝ) ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
          calc (1 : ℝ) = 1 ^ (3/2 : ℝ) := by rw [Real.one_rpow]
            _ ≤ (‖z‖ + 1) ^ (3/2 : ℝ) :=
              Real.rpow_le_rpow (by norm_num) this (by norm_num)
        by_cases hz : ‖z‖ < 2
        · -- Small z: ‖ξ z‖ ≤ M_bound ≤ exp(log(max M_bound 1) + 1) ≤ exp(C_universal ≤ exp(C_universal · (‖z‖+1)^{3/2}))
          have hz_mem : z ∈ Metric.closedBall (0 : ℂ) 2 := by
            rw [Metric.mem_closedBall]; simp; linarith
          have h_norm_le := hM_bound z hz_mem
          have h_M_nn : (0 : ℝ) ≤ M_bound := norm_nonneg _
          have h_max_pos : (0 : ℝ) < max M_bound 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
          have h_log_le : M_bound ≤ Real.exp (Real.log (max M_bound 1) + 1) := by
            have h1 : M_bound ≤ max M_bound 1 := le_max_left _ _
            calc M_bound ≤ max M_bound 1 := h1
              _ = Real.exp (Real.log (max M_bound 1)) := (Real.exp_log h_max_pos).symm
              _ ≤ Real.exp (Real.log (max M_bound 1) + 1) := by
                  apply Real.exp_le_exp.mpr; linarith
          calc ‖RiemannXiAlt z‖
              ≤ M_bound := h_norm_le
            _ ≤ Real.exp (Real.log (max M_bound 1) + 1) := h_log_le
            _ ≤ Real.exp C_universal := Real.exp_le_exp.mpr hC_uni_ge_logM
            _ = Real.exp (C_universal * 1) := by rw [mul_one]
            _ ≤ Real.exp (C_universal * (‖z‖ + 1) ^ (3/2 : ℝ)) := by
                apply Real.exp_le_exp.mpr
                exact mul_le_mul_of_nonneg_left hpow_ge_one hC_uni_pos.le
        · -- Large z (‖z‖ ≥ 2): use xi_growth_for_jensen
          push_neg at hz
          have h_jensen := hxi_bound z hz
          have h1 : ‖z‖ ^ (3/2 : ℝ) ≤ (‖z‖ + 1) ^ (3/2 : ℝ) := by
            apply Real.rpow_le_rpow (by positivity) (by linarith [norm_nonneg z])
            norm_num
          calc ‖RiemannXiAlt z‖
              ≤ Real.exp (C_growth * ‖z‖ ^ (3/2 : ℝ)) := h_jensen
            _ ≤ Real.exp (C_growth * (‖z‖ + 1) ^ (3/2 : ℝ)) := by
                apply Real.exp_le_exp.mpr
                exact mul_le_mul_of_nonneg_left h1 hC_growth_pos.le
            _ ≤ Real.exp (C_universal * (‖z‖ + 1) ^ (3/2 : ℝ)) := by
                apply Real.exp_le_exp.mpr
                exact mul_le_mul_of_nonneg_right hC_uni_ge_Cgrowth hpow_nn)
    -- ξ = exp(A + Bs) = 1 · exp(A + Bs), so P = 1 (constant polynomial)
    refine ⟨1, A, B, fun s => ?_⟩
    rw [hAB s]
    simp
  · -- Nonempty zero case: use entire_finite_zeros_polyexp (strong induction on |zeros|)
    have hxi_diff : Differentiable ℂ RiemannXiAlt := RiemannXiAlt_entire
    have hne_ξ : ∃ w, RiemannXiAlt w ≠ 0 := ⟨0, xi_zero_ne⟩
    have h_finite : {z : ℂ | RiemannXiAlt z = 0}.Finite := by
      convert hfin using 1
    -- Compute subquadratic growth bound using xi_growth_for_jensen + compact bound at ‖z‖ ≤ 2
    obtain ⟨C_growth, hC_growth_pos, hxi_bound⟩ := xi_growth_for_jensen
    have hCont : ContinuousOn RiemannXiAlt (Metric.closedBall (0 : ℂ) 2) :=
      (hxi_diff.continuous).continuousOn
    have hCompact : IsCompact (Metric.closedBall (0 : ℂ) 2) := isCompact_closedBall _ _
    obtain ⟨M, _, hM_bound⟩ : ∃ M, M ∈ Metric.closedBall (0 : ℂ) 2 ∧
        ∀ z ∈ Metric.closedBall (0 : ℂ) 2, ‖RiemannXiAlt z‖ ≤ ‖RiemannXiAlt M‖ :=
      hCompact.exists_isMaxOn (Set.nonempty_of_mem (Metric.mem_closedBall_self (by norm_num)))
        (Continuous.norm hxi_diff.continuous).continuousOn
    set M_bound := ‖RiemannXiAlt M‖ with hM_def
    set C_universal : ℝ := max C_growth (Real.log (max M_bound 1) + 1) with hC_uni_def
    have hC_uni_pos : 0 < C_universal := lt_of_lt_of_le hC_growth_pos (le_max_left _ _)
    have hC_uni_ge_Cgrowth : C_growth ≤ C_universal := le_max_left _ _
    have hC_uni_ge_logM : Real.log (max M_bound 1) + 1 ≤ C_universal := le_max_right _ _
    have h_growth : ∀ z, ‖RiemannXiAlt z‖ ≤ Real.exp (C_universal * (‖z‖ + 1) ^ (3/2 : ℝ)) := by
      intro z
      have hpow_nn : 0 ≤ (‖z‖ + 1) ^ (3/2 : ℝ) :=
        Real.rpow_nonneg (by linarith [norm_nonneg z]) _
      have hpow_ge_one : 1 ≤ (‖z‖ + 1) ^ (3/2 : ℝ) := by
        have : (1 : ℝ) ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
        calc (1 : ℝ) = 1 ^ (3/2 : ℝ) := by rw [Real.one_rpow]
          _ ≤ (‖z‖ + 1) ^ (3/2 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) this (by norm_num)
      by_cases hz : ‖z‖ < 2
      · have hz_mem : z ∈ Metric.closedBall (0 : ℂ) 2 := by
          rw [Metric.mem_closedBall]; simp; linarith
        have h_norm_le := hM_bound z hz_mem
        have h_max_pos : (0 : ℝ) < max M_bound 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
        have h_log_le : M_bound ≤ Real.exp (Real.log (max M_bound 1) + 1) := by
          calc M_bound ≤ max M_bound 1 := le_max_left _ _
            _ = Real.exp (Real.log (max M_bound 1)) := (Real.exp_log h_max_pos).symm
            _ ≤ Real.exp (Real.log (max M_bound 1) + 1) := by
                apply Real.exp_le_exp.mpr; linarith
        calc ‖RiemannXiAlt z‖
            ≤ M_bound := h_norm_le
          _ ≤ Real.exp (Real.log (max M_bound 1) + 1) := h_log_le
          _ ≤ Real.exp C_universal := Real.exp_le_exp.mpr hC_uni_ge_logM
          _ = Real.exp (C_universal * 1) := by rw [mul_one]
          _ ≤ Real.exp (C_universal * (‖z‖ + 1) ^ (3/2 : ℝ)) := by
              apply Real.exp_le_exp.mpr
              exact mul_le_mul_of_nonneg_left hpow_ge_one hC_uni_pos.le
      · push_neg at hz
        have h_jensen := hxi_bound z hz
        have h1 : ‖z‖ ^ (3/2 : ℝ) ≤ (‖z‖ + 1) ^ (3/2 : ℝ) := by
          apply Real.rpow_le_rpow (by positivity) (by linarith [norm_nonneg z])
          norm_num
        calc ‖RiemannXiAlt z‖
            ≤ Real.exp (C_growth * ‖z‖ ^ (3/2 : ℝ)) := h_jensen
          _ ≤ Real.exp (C_growth * (‖z‖ + 1) ^ (3/2 : ℝ)) := by
              apply Real.exp_le_exp.mpr
              exact mul_le_mul_of_nonneg_left h1 hC_growth_pos.le
          _ ≤ Real.exp (C_universal * (‖z‖ + 1) ^ (3/2 : ℝ)) := by
              apply Real.exp_le_exp.mpr
              exact mul_le_mul_of_nonneg_right hC_uni_ge_Cgrowth hpow_nn
    exact entire_finite_zeros_polyexp RiemannXiAlt hxi_diff hne_ξ h_finite
      (3/2 : ℝ) C_universal (by norm_num) (by norm_num) hC_uni_pos h_growth

/-- The zero set of `RiemannXiAlt` is infinite.
Proved by contradiction: if finitely many zeros, then by AnalyticQuotient and
entire_nonvanishing_subquad_is_exp_linear, ξ = P · exp(A + Bs). This contradicts
xi_not_poly_exp (factorial growth at even integers). -/
theorem xi_zeros_infinite_hyp : Set.Infinite xiZeroSet := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨P, A, B, hPAB⟩ := xi_polyexp_of_finite_zeros hfin
  exact xi_not_poly_exp P A B hPAB

/-- The multiplicity-weighted zero count is bounded by `zeroCount`.  Each zero `z`
contributes `(analyticOrderAt ξ z).toNat` which equals its divisor value. -/
private theorem xi_mult_sum_le_zeroCount (R : ℝ) :
    (∑ z ∈ (xiZeroSet_finite_in_disk R).toFinset,
      ((analyticOrderAt RiemannXiAlt (z : ℂ)).toNat : ℤ)) ≤ zeroCount RiemannXiAlt R := by
  unfold zeroCount
  set div_fn := divisor RiemannXiAlt (closedBall (0 : ℂ) R)
  have hfin : Set.Finite (Function.support (div_fn : ℂ → ℤ)) :=
    div_fn.finiteSupport (ProperSpace.isCompact_closedBall _ _)
  have hsup : Function.support (div_fn : ℂ → ℤ) ⊆ ↑hfin.toFinset := by
    intro x hx; exact hfin.mem_toFinset.mpr hx
  rw [finsum_eq_sum_of_support_subset _ hsup]
  have h_sub : (xiZeroSet_finite_in_disk R).toFinset ⊆ hfin.toFinset := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz ⊢
    rw [Function.mem_support]
    have h1 := divisor_ge_one_at_zero xi_analyticAt hz.1 hz.2 xi_not_identically_zero
    linarith
  have h_eq : ∀ z ∈ (xiZeroSet_finite_in_disk R).toFinset,
      ((analyticOrderAt RiemannXiAlt (z : ℂ)).toNat : ℤ) ≤ (div_fn : ℂ → ℤ) z := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    rw [divisor_apply (AnalyticOnNhd.meromorphicOn (fun w _ => xi_analyticAt w)) hz.2]
    rw [(xi_analyticAt z).meromorphicOrderAt_eq]
    cases analyticOrderAt RiemannXiAlt z with
    | top => simp
    | coe n => simp
  calc
    (∑ z ∈ (xiZeroSet_finite_in_disk R).toFinset,
        ((analyticOrderAt RiemannXiAlt (z : ℂ)).toNat : ℤ))
      ≤ ∑ z ∈ (xiZeroSet_finite_in_disk R).toFinset, (div_fn : ℂ → ℤ) z :=
        Finset.sum_le_sum h_eq
    _ ≤ ∑ z ∈ hfin.toFinset, (div_fn : ℂ → ℤ) z :=
        Finset.sum_le_sum_of_subset_of_nonneg h_sub
          (fun z _ _ => divisor_nonneg_of_entire xi_analyticAt _ _)

/-- Multiplicity-weighted counting bound: `∑_{z : ‖z‖ ≤ R} mult(z) ≤ C' R^{3/2}`. -/
private theorem xi_mult_weighted_count_bound :
    ∃ C' : ℝ, 0 < C' ∧ ∀ R : ℝ, 1 ≤ R →
      (∑ z ∈ (xiZeroSet_finite_in_disk R).toFinset,
        ((analyticOrderAt RiemannXiAlt (z : ℂ)).toNat : ℝ)) ≤ C' * R ^ (3 / 2 : ℝ) := by
  obtain ⟨C', hC', hcount⟩ := xi_zero_count_bound
  exact ⟨C', hC', fun R hR => by
    have h1 := xi_mult_sum_le_zeroCount R
    have h2 := hcount R hR
    have h3 : (∑ z ∈ (xiZeroSet_finite_in_disk R).toFinset,
        ((analyticOrderAt RiemannXiAlt (z : ℂ)).toNat : ℝ)) ≤
        (zeroCount RiemannXiAlt R : ℝ) := by
      exact_mod_cast h1
    linarith⟩

/-- xiZeroSet membership in closedBall, as a subtype predicate. -/
private theorem xiZeroSet_subtype_finite_in_ball (R : ℝ) :
    {z : xiZeroSet | ‖(z : ℂ)‖ ≤ R}.Finite := by
  apply Set.Finite.of_finite_image (f := Subtype.val)
  · exact ((xiZeroSet_finite_in_disk R).subset (by
      rintro z ⟨⟨w, hw⟩, hmem, rfl⟩
      exact ⟨hw, mem_closedBall_zero_iff.mpr hmem⟩))
  · exact Subtype.val_injective.injOn

/-- Sum over xiZeroSet subtype in ball equals sum over xiZeroSet∩closedBall. -/
private theorem xiZeroSet_subtype_sum_eq_disk_sum (R : ℝ) (f : ℂ → ℝ) :
    (∑ z ∈ (xiZeroSet_subtype_finite_in_ball R).toFinset, f (z : ℂ)) =
      ∑ z ∈ (xiZeroSet_finite_in_disk R).toFinset, f z := by
  -- The image of the subtype finset under Subtype.val equals the disk finset
  have h_image : (xiZeroSet_subtype_finite_in_ball R).toFinset.image
      (fun z : xiZeroSet => (z : ℂ)) = (xiZeroSet_finite_in_disk R).toFinset := by
    ext z
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨w, hw⟩, hmem, rfl⟩
      exact ⟨hw, Metric.mem_closedBall.mpr (by rwa [dist_zero_right])⟩
    · intro ⟨hz, hball⟩
      exact ⟨⟨z, hz⟩, by rwa [Metric.mem_closedBall, dist_zero_right] at hball, rfl⟩
  rw [← h_image, Finset.sum_image]
  intro a _ b _ h; exact Subtype.ext h

/-- Constructive zero enumeration for `RiemannXiAlt`.
From `xiZeroSet_countable` and `xi_zeros_infinite`, the zero set is
countably infinite, hence `Denumerable`. The bijection with `ℕ` gives
the `zeros` function with all four required properties. -/
theorem xi_zeros_enumeration_core
    (hinf : Set.Infinite xiZeroSet) :
    ∃ (zeros : ℕ → ℂ),
      (∀ s, RiemannXiAlt s = 0 → ∃ n, s = zeros n) ∧
      (∀ n, zeros n ≠ 0) ∧
      (∀ n, RiemannXiAlt (zeros n) = 0) ∧
      Summable (fun n => 1 / ‖zeros n‖ ^ 2) ∧
      (∀ z, (Nat.card {n | zeros n = z} : ℕ∞) = analyticOrderAt RiemannXiAlt z) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
        ∃ S : Finset ℕ,
          (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ R) ∧
          (S.card : ℝ) ≤ C * R ^ (3 / 2 : ℝ)) := by
  -- Multiplicity-aware enumeration via sigma type
  -- mult(z) = (analyticOrderAt ξ z).toNat for z ∈ xiZeroSet
  -- XiZeroMultIndex = Σ z : xiZeroSet, Fin (mult z)
  -- Each zero z appears exactly mult(z) times in the enumeration.
  haveI hcnt_xi : Countable xiZeroSet := xiZeroSet_countable.to_subtype
  haveI hinf_xi : Infinite xiZeroSet := hinf.to_subtype
  -- Define multiplicity function
  let mult : xiZeroSet → ℕ := fun z => (analyticOrderAt RiemannXiAlt (z : ℂ)).toNat
  have hmult_pos : ∀ z : xiZeroSet, 0 < mult z := fun z =>
    xi_analyticOrderAt_pos_at_zero z.property
  -- The sigma type is countable and infinite
  haveI : Countable (Σ z : xiZeroSet, Fin (mult z)) := by
    exact instCountableSigma
  haveI : Infinite (Σ z : xiZeroSet, Fin (mult z)) := by
    apply Infinite.of_injective (fun z : xiZeroSet => (⟨z, ⟨0, hmult_pos z⟩⟩ : Σ z : xiZeroSet, Fin (mult z)))
    intro a b h; exact Sigma.mk.inj h |>.1
  haveI : Encodable (Σ z : xiZeroSet, Fin (mult z)) := Encodable.ofCountable _
  letI den := Denumerable.ofEncodableOfInfinite (Σ z : xiZeroSet, Fin (mult z))
  set e := (Denumerable.eqv (Σ z : xiZeroSet, Fin (mult z))).symm
  set zeros : ℕ → ℂ := fun n => ((e n).1 : ℂ) with hzeros_def
  refine ⟨zeros, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Coverage: every zero of ξ is listed (use slot 0)
    intro s hs
    exact ⟨e.symm ⟨⟨s, hs⟩, ⟨0, hmult_pos ⟨s, hs⟩⟩⟩, by simp [zeros]⟩
  · -- Every listed value is nonzero
    intro n; exact xi_zero_ne_zero (e n).1.property
  · -- Every listed value is a zero of ξ
    intro n; exact (e n).1.property
  · -- Summability with multiplicity
    -- Use abstract sigma-type summability from SigmaMultSummability.lean
    -- Step 1: Show summability over the sigma type
    have hσ_summable : Summable (fun σ : Σ z : xiZeroSet, Fin (mult z) =>
        1 / ‖(σ.1 : ℂ)‖ ^ 2) := by
      -- Apply the abstract summability theorem
      -- We need: (a) norm > 0, (b) mult > 0, (c) finiteness, (d) counting bound
      apply summable_sigma_inv_sq_of_counting_bound
        (fun z : xiZeroSet => ‖(z : ℂ)‖) mult
        (fun z => norm_pos_iff.mpr (xi_zero_ne_zero z.property))
        hmult_pos
        xiZeroSet_subtype_finite_in_ball
      -- Counting bound: ∑ mult(z) for ‖z‖ ≤ R is ≤ C * R^{3/2}
      obtain ⟨C', hC', hbound⟩ := xi_mult_weighted_count_bound
      refine ⟨C', hC', fun R hR => ?_⟩
      -- Both sums are ∑ mult(z) over zeros in ball R with different Finset types
      calc (∑ z ∈ (xiZeroSet_subtype_finite_in_ball R).toFinset, (mult z : ℝ))
          = ∑ z ∈ (xiZeroSet_finite_in_disk R).toFinset,
              ((analyticOrderAt RiemannXiAlt (z : ℂ)).toNat : ℝ) :=
            xiZeroSet_subtype_sum_eq_disk_sum R
              (fun z => ((analyticOrderAt RiemannXiAlt z).toNat : ℝ))
        _ ≤ C' * R ^ (3 / 2 : ℝ) := hbound R hR
    -- Step 2: Transfer to ℕ via the equivalence e
    exact summable_sigma_nat_via_equiv
      (fun z : xiZeroSet => ‖(z : ℂ)‖) mult e hσ_summable
  · -- Multiplicity: fiber cardinality = analytic order
    intro z
    by_cases hz : RiemannXiAlt z = 0
    · -- z is a zero: fiber {n | zeros n = z} ≅ Fin (mult ⟨z, hz⟩)
      -- via the bijection e : ℕ ≃ Σ z : xiZeroSet, Fin (mult z)
      set zz : xiZeroSet := ⟨z, hz⟩
      -- The fiber {n | zeros n = z} bijects with {i : Σ ... | i.1 = zz}
      -- which is Fin (mult zz)
      have h_card : Nat.card {n : ℕ | zeros n = z} = mult zz := by
        -- {n | zeros n = z} = {n | (e n).1 = zz} bijects with {i | i.1 = zz} ≃ Fin (mult zz)
        -- Direct bijection: {n | zeros n = z} ≃ Fin (mult zz)
        -- via e: n ↦ (e n).2 when (e n).1 = zz
        -- {n | zeros n = z} has the same card as Fin (mult zz)
        -- because e : ℕ ≃ Σ z, Fin (mult z) maps this set bijectively to the zz-fiber.
        -- Use: card of preimage under bijection = card of image set.
        -- The image is {i : Σ z, Fin (mult z) | i.1 = zz} ≃ Fin (mult zz).
        -- Step 1: {n | zeros n = z} ≃ {i | i.1 = zz} via e
        have h1 : Nat.card {n : ℕ | zeros n = z} =
            Nat.card {i : Σ z : xiZeroSet, Fin (mult z) | i.1 = zz} := by
          apply Nat.card_congr
          exact {
            toFun := fun ⟨n, hn⟩ => ⟨e n, Subtype.ext hn⟩
            invFun := fun ⟨i, hi⟩ => ⟨e.symm i, by
              show ((e (e.symm i)).1 : ℂ) = z
              rw [e.apply_symm_apply]; exact congr_arg Subtype.val hi⟩
            left_inv := fun ⟨n, _⟩ => by simp
            right_inv := fun ⟨i, _⟩ => by simp }
        -- Step 2: {i | i.1 = zz} ≃ Fin (mult zz)
        have h2 : Nat.card {i : Σ z : xiZeroSet, Fin (mult z) | i.1 = zz} =
            Nat.card (Fin (mult zz)) := by
          apply Nat.card_congr
          exact {
            toFun := fun ⟨⟨z', k⟩, h⟩ => by exact h ▸ k
            invFun := fun k => ⟨⟨zz, k⟩, rfl⟩
            left_inv := fun ⟨⟨z', k⟩, (h : z' = zz)⟩ => by
              cases h; rfl
            right_inv := fun k => rfl }
        rw [h1, h2, Nat.card_fin]
      -- (mult zz : ℕ∞) = analyticOrderAt ξ z (since order is finite)
      have h_ord_ne_top : analyticOrderAt RiemannXiAlt z ≠ ⊤ := by
        intro h
        have hev := analyticOrderAt_eq_top.mp h
        -- hev : ∀ᶠ w in nhds z, ξ w = 0
        -- Convert to frequently in punctured nhd
        have hfreq : ∃ᶠ w in nhdsWithin z {z}ᶜ, RiemannXiAlt w = 0 :=
          (hev.filter_mono nhdsWithin_le_nhds).frequently
        exact xiZeroSet_no_accPt z hfreq
      rw [h_card, show (mult zz : ℕ∞) = ((analyticOrderAt RiemannXiAlt z).toNat : ℕ∞) from rfl,
          ENat.coe_toNat h_ord_ne_top]
    · -- z is not a zero: no preimage, and analyticOrderAt = 0
      have h_empty : {n : ℕ | zeros n = z} = ∅ := by
        ext n; simp only [Set.mem_setOf, Set.mem_empty_iff_false, iff_false]
        intro h; exact hz (h ▸ (e n).1.property)
      have : IsEmpty {n : ℕ | zeros n = z} := by rw [isEmpty_coe_sort, h_empty]
      simp only [Nat.card_eq_zero.mpr (Or.inl this), Nat.cast_zero,
          (xi_analyticAt z).analyticOrderAt_eq_zero.mpr hz]
  · -- Counting bound with multiplicity
    -- Use abstract counting bound from SigmaMultSummability.lean
    have hfin_sub := xiZeroSet_subtype_finite_in_ball
    obtain ⟨C', hC', hbound⟩ := xi_mult_weighted_count_bound
    -- Apply the abstract counting bound
    have hcount_abs : ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
        (∑ s ∈ (hfin_sub R).toFinset, (mult s : ℝ)) ≤ C * R ^ (3 / 2 : ℝ) := by
      refine ⟨C', hC', fun R hR => ?_⟩
      calc (∑ s ∈ (hfin_sub R).toFinset, (mult s : ℝ))
          = ∑ z ∈ (xiZeroSet_finite_in_disk R).toFinset,
              ((analyticOrderAt RiemannXiAlt (z : ℂ)).toNat : ℝ) := by
            -- hfin_sub R = xiZeroSet_subtype_finite_in_ball R, so use the helper
            show _ = _; exact xiZeroSet_subtype_sum_eq_disk_sum R
              (fun z => ((analyticOrderAt RiemannXiAlt z).toNat : ℝ))
        _ ≤ C' * R ^ (3 / 2 : ℝ) := hbound R hR
    obtain ⟨C_final, hC_final_pos, hC_final⟩ :=
      sigma_nat_counting_bound
        (fun z : xiZeroSet => ‖(z : ℂ)‖) mult e hmult_pos hfin_sub hcount_abs
    exact ⟨C_final, hC_final_pos, fun R hR => by
      obtain ⟨S', hmem, hcard⟩ := hC_final R hR
      exact ⟨S', hmem, hcard⟩⟩

-- Raised from priority 50 to 3000 to override `instXiZerosEnumerationHypClean`
-- (which despite its name carries sorryAx + firstZero via `xi_zeros_infinite_clean`).
-- This instance uses the CLEAN `xi_zeros_infinite_hyp` (no sorryAx).
instance (priority := 3000) : XiZerosEnumerationHyp :=
  ⟨xi_zeros_enumeration_core xi_zeros_infinite_hyp⟩

/-! ### Local analytic extension of ξ/P at zeros via AnalyticQuotient

If `f` and `g` are both analytic at `z₀` with the same vanishing order `m ≥ 1`,
then `analyticAt_quotient_of_common_order` (from `AnalyticQuotient.lean`, 0 sorry)
produces an analytic extension `h` with `h z₀ = f₁(z₀)/g₁(z₀) ≠ 0` and
`h z = f z / g z` on a punctured neighborhood.

Applied to Hadamard: at each zero `ρ` of `ξ`, both `RiemannXiAlt` and the
Weierstrass product `P` vanish to order `m`. So `ξ/P` extends analytically at `ρ`,
with the extension being nonvanishing (ratio of leading coefficients). -/

/-- At a zero `ρ` of `RiemannXiAlt` where both `ξ` and `P` vanish to the same
finite order `m ≥ 1`, the quotient `ξ/P` extends to an analytic, nonvanishing
function at `ρ` via `analyticAt_quotient_of_common_order`. -/
private theorem xi_quotient_analytic_at_zero
    (P : ℂ → ℂ) (ρ : ℂ) (m : ℕ) (hm : 0 < m)
    (hξ_an : AnalyticAt ℂ RiemannXiAlt ρ)
    (hP_an : AnalyticAt ℂ P ρ)
    (hξ_ord : analyticOrderAt RiemannXiAlt ρ = m)
    (hP_ord : analyticOrderAt P ρ = m) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h ρ ∧
      h ρ ≠ 0 ∧
      (∀ᶠ z in nhdsWithin ρ {ρ}ᶜ, h z = RiemannXiAlt z / P z) := by
  obtain ⟨h, f₁, g₁, _, hf₁_ne, _, _, hg₁_ne, _, hh_an, hh_val, hh_eq⟩ :=
    analyticAt_quotient_of_common_order hm hξ_an hP_an hξ_ord hP_ord
  exact ⟨h, hh_an, by rw [hh_val]; exact div_ne_zero hf₁_ne hg₁_ne, hh_eq⟩

/-- At a non-zero `s₀` of `RiemannXiAlt` where `P s₀ ≠ 0`, the quotient `ξ/P`
is already analytic (no extension needed). -/
private theorem xi_quotient_analytic_at_nonzero
    (P : ℂ → ℂ) (s₀ : ℂ)
    (hξ_an : AnalyticAt ℂ RiemannXiAlt s₀)
    (hP_an : AnalyticAt ℂ P s₀)
    (hP_ne : P s₀ ≠ 0) :
    AnalyticAt ℂ (fun z => RiemannXiAlt z / P z) s₀ :=
  hξ_an.div hP_an hP_ne

/-! ### Hypothesis boundaries for Weierstrass product order theory

The Hadamard factorization requires three analytic facts about Weierstrass products
that go beyond current Mathlib tooling:
1. The meromorphic order of ξ/P is ≥ 0 at every point (no poles)
2. The MeromorphicNF extension of ξ/P is nonvanishing
3. |Q| ≤ exp(C(|s|+1)^{7/4}) (growth bound from minimum modulus of P)

These are encapsulated as named typeclass hypothesis boundaries, analogous to
`AtkinsonLargeShiftPrefixBoundHyp` and `ContourRemainderBoundHyp` elsewhere.
Each is mathematically TRUE and closable once Mathlib gains:
- `analyticOrderAt` for infinite Weierstrass products
- minimum modulus bounds for entire functions of finite order

With the multiplicity-aware enumeration from `HadamardMultEnumeration.lean`,
the Weierstrass product `P` has the SAME vanishing order as `ξ` at every zero,
making all three conditions provable in principle. -/

/-- **Hypothesis boundary**: The meromorphic order of ξ(z)/P(z) is exactly zero
at every point z ∈ ℂ. This encodes the fact that the Weierstrass product
P has the SAME vanishing order as ξ at each zero (and neither has poles).

With multiplicity-aware enumeration (each zero listed `analyticOrderAt ξ ρ` times),
ord(P, ρ) = ord(ξ, ρ), so ord(ξ/P, ρ) = 0.
At non-zeros of both ξ and P, both sides have order 0.
At non-zeros of P where ξ vanishes: impossible by coverage (every zero of ξ
appears as zeros(n), and P(zeros(n)) = 0 since E₁(1) = 0).

Closable once Mathlib gains `analyticOrderAt_tprod` for Weierstrass products. -/
class XiQuotientMeromorphicOrderNonnegHyp : Prop where
  order_eq_zero :
    ∀ (zeros : ℕ → ℂ),
      (∀ s, RiemannXiAlt s = 0 → ∃ n, s = zeros n) →
      (∀ n, zeros n ≠ 0) →
      (∀ n, RiemannXiAlt (zeros n) = 0) →
      Summable (fun n => 1 / ‖zeros n‖ ^ 2) →
      Differentiable ℂ (fun s =>
        ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) →
      (∀ z, (Nat.card {n | zeros n = z} : ℕ∞) = analyticOrderAt RiemannXiAlt z) →
      ∀ z, meromorphicOrderAt
        (fun z => RiemannXiAlt z /
          ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)) z = 0

private lemma E1_one_eq_zero :
    Aristotle.Standalone.HadamardProductConvergence.E1 1 = 0 := by
  unfold Aristotle.Standalone.HadamardProductConvergence.E1; ring

private lemma E1_analyticAt (z : ℂ) :
    AnalyticAt ℂ Aristotle.Standalone.HadamardProductConvergence.E1 z := by
  unfold Aristotle.Standalone.HadamardProductConvergence.E1
  exact (analyticAt_const.sub analyticAt_id).mul analyticAt_cexp

private lemma deriv_E1_one_ne_zero :
    deriv Aristotle.Standalone.HadamardProductConvergence.E1 (1 : ℂ) ≠ 0 := by
  have heq : Aristotle.Standalone.HadamardProductConvergence.E1 =
      (fun w : ℂ => (1 - w) * exp w) := by
    ext; simp [Aristotle.Standalone.HadamardProductConvergence.E1]
  rw [heq]
  have h1 : deriv (fun w : ℂ => (1 - w) * exp w) (1 : ℂ) = -exp (1 : ℂ) := by
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => 1 - w) 1 := by fun_prop
    have hd2 : DifferentiableAt ℂ (fun w : ℂ => exp w) 1 := by fun_prop
    conv_lhs => rw [show (fun w : ℂ => (1 - w) * exp w) =
      ((fun w => 1 - w) * (fun w => exp w)) from by ext; simp [Pi.mul_apply]]
    rw [deriv_mul hd1 hd2]
    have hd_sub : deriv (fun w : ℂ => 1 - w) (1 : ℂ) = -1 := by
      rw [deriv_const_sub]; simp
    rw [hd_sub]
    ring
  rw [h1]
  exact neg_ne_zero.mpr (exp_ne_zero _)

/-- `E₁` has a simple zero at `w = 1`. -/
private lemma analyticOrderAt_E1_one :
    analyticOrderAt Aristotle.Standalone.HadamardProductConvergence.E1 (1 : ℂ) = 1 := by
  have h := (E1_analyticAt 1).analyticOrderAt_sub_eq_one_of_deriv_ne_zero deriv_E1_one_ne_zero
  simp only [E1_one_eq_zero, sub_zero] at h
  exact h

/-- `E₁(s/a)` has a simple zero at `s = a` for `a ≠ 0`. -/
private lemma analyticOrderAt_E1_div_eq_one (a : ℂ) (ha : a ≠ 0) :
    analyticOrderAt
      (fun s => Aristotle.Standalone.HadamardProductConvergence.E1 (s / a)) a = 1 := by
  rw [show (fun s => Aristotle.Standalone.HadamardProductConvergence.E1 (s / a)) =
      Aristotle.Standalone.HadamardProductConvergence.E1 ∘ (· / a) from rfl]
  have hg_an : AnalyticAt ℂ (fun x : ℂ => x / a) a := by
    exact analyticAt_id.div analyticAt_const ha
  have hg_deriv : deriv (fun x : ℂ => x / a) a ≠ 0 := by
    rw [show (fun x : ℂ => x / a) = (· * a⁻¹) from by ext; simp [div_eq_mul_inv]]
    simp [deriv_mul_const, inv_ne_zero ha]
  rw [analyticOrderAt_comp_of_deriv_ne_zero hg_an hg_deriv, div_self ha]
  exact analyticOrderAt_E1_one

/-- `{n | zeros n = z}` is finite when `∑ 1/‖ρₙ‖² < ∞` and `z ≠ 0`. -/
private lemma finite_zeros_at (zeros : ℕ → ℂ) (z : ℂ) (hz : z ≠ 0)
    (hne : ∀ n, zeros n ≠ 0) (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2)) :
    Set.Finite {n : ℕ | zeros n = z} := by
  -- Summable terms → 0. Get N such that ∀ n ≥ N, |1/‖zeros n‖²| < 1/‖z‖².
  -- Then for n ≥ N, zeros n ≠ z. So {n | zeros n = z} ⊆ Finset.range N.
  have hc : (0 : ℝ) < 1 / ‖z‖ ^ 2 := by
    exact div_pos one_pos (sq_pos_of_pos (norm_pos_iff.mpr hz))
  obtain ⟨N, hN⟩ := (NormedAddCommGroup.tendsto_atTop.mp hsum.tendsto_atTop_zero
    (1 / ‖z‖ ^ 2) hc)
  apply Set.Finite.subset (Finset.range N).finite_toSet
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h_ge; push_neg at h_ge
  have h1 := hN n h_ge
  simp only [sub_zero] at h1
  rw [Real.norm_of_nonneg (div_nonneg one_pos.le (sq_nonneg _)), hn] at h1
  linarith

/-- The analytic order of a finite product of functions each with order 1
is the cardinality of the index set. -/
private lemma analyticOrderAt_finprod_of_order_one (S : Finset ℕ)
    (g : ℕ → ℂ → ℂ) (z : ℂ)
    (hg : ∀ n ∈ S, AnalyticAt ℂ (g n) z)
    (hord : ∀ n ∈ S, analyticOrderAt (g n) z = 1) :
    analyticOrderAt (fun s => ∏ n ∈ S, g n s) z = S.card := by
  -- Convert to Pi form: (fun s => ∏ n ∈ S, g n s) = ∏ n ∈ S, g n
  conv_lhs => rw [show (fun s => ∏ n ∈ S, g n s) = ∏ n ∈ S, g n from
    funext fun s => by simp [Finset.prod_apply]]
  -- Now induct in Pi form
  induction S using Finset.cons_induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero]
    exact (analyticAt_const (v := (1 : ℂ))).analyticOrderAt_eq_zero.mpr one_ne_zero
  | cons a S' hna ih =>
    rw [Finset.prod_cons, Finset.card_cons]
    have ha_an := hg a (Finset.mem_cons_self a S')
    have hS'_an := Finset.analyticAt_prod S'
      (fun n hn => hg n (Finset.mem_cons.mpr (Or.inr hn)))
    rw [analyticOrderAt_mul ha_an hS'_an,
      hord a (Finset.mem_cons_self a S'),
      ih (fun n hn => hg n (Finset.mem_cons.mpr (Or.inr hn)))
         (fun n hn => hord n (Finset.mem_cons.mpr (Or.inr hn)))]
    push_cast; ring

/-- The tail product `∏' (n : Sᶜ), E₁(z/ρₙ)` is nonzero at `z`.
Each factor `E₁(z/ρₙ) ≠ 0` because `ρₙ ≠ z`, and the product
converges absolutely via `tprod_one_add_ne_zero_of_summable`. -/
private lemma weierstrass_tail_ne_zero
    (zeros : ℕ → ℂ) (z : ℂ) (hz : z ≠ 0)
    (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hfin : Set.Finite {n : ℕ | zeros n = z}) :
    (∏' (n : {n : ℕ // n ∉ hfin.toFinset}),
      Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n)) ≠ 0 := by
  rw [show (fun (n : {n : ℕ // n ∉ hfin.toFinset}) =>
      Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n)) =
      (fun (n : {n : ℕ // n ∉ hfin.toFinset}) => 1 +
        (Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n) - 1))
    from by ext; ring]
  apply tprod_one_add_ne_zero_of_summable
  · intro ⟨n, hn⟩
    -- Need: E₁(z/zeros n) - 1 ≠ -1 (equivalently E₁(z/zeros n) ≠ 0)
    intro h_eq
    -- h_eq : E₁(z/zeros n) - 1 = -1, so E₁(z/zeros n) = 0
    -- h_eq makes E₁(z/ρ) = 0, i.e. (1-z/ρ)*exp(z/ρ) = 0
    -- E₁(z/ρₙ) - 1 = -1 means E₁(z/ρₙ) = 0
    -- E₁(w) = (1-w)*exp(w) = 0 → w = 1 (exp nonzero) → ρₙ = z, contradiction
    exfalso
    -- h_eq : 1 + (E₁(z/ρ) - 1) = 0 → E₁(z/ρ) = 0 → ρ = z, contradiction
    have h0 : Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) = 0 := by
      have := h_eq; ring_nf at this ⊢; exact this
    -- E1(w) = (1-w)*exp(w) = 0, exp nonzero, so w = 1, i.e. z/ρ = 1, so ρ = z
    simp only [Aristotle.Standalone.HadamardProductConvergence.E1, mul_eq_zero,
      Complex.exp_ne_zero, or_false, sub_eq_zero] at h0
    -- h0 should be: 1 = z / zeros n
    rw [eq_comm, div_eq_one_iff_eq (hne n)] at h0
    exact hn (hfin.mem_toFinset.mpr h0.symm)
  · have h_full : Summable (fun n : ℕ =>
        ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) - 1‖) := by
      have h_sq : Summable (fun n => ‖z / zeros n‖ ^ 2) := by
        simp only [norm_div, div_pow]
        exact (hsum.mul_left (‖z‖ ^ 2)).congr (fun n => by ring)
      have h_bound : ∀ᶠ n in Filter.atTop,
          ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) - 1‖ ≤
            3 * ‖z / zeros n‖ ^ 2 := by
        filter_upwards [h_sq.tendsto_atTop_zero.eventually
          (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with n hn
        exact Aristotle.Standalone.HadamardProductConvergence.E1_sub_one_norm_le
          (show ‖z / zeros n‖ ≤ 1 by nlinarith)
      obtain ⟨N, hN⟩ := h_bound.exists_forall_of_atTop
      rw [← summable_nat_add_iff N]
      exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun n => hN (n + N) le_add_self)
        ((h_sq.mul_left 3).comp_injective (add_left_injective N))
    exact h_full.subtype _

/-- **Sub-sorry A** (MOVED HERE for forward-reference resolution):
The Weierstrass product `P(s) = ∏ E₁(s/ρₙ)` is differentiable on ℂ.

Proof sketch: Each factor `E₁(s/ρₙ)` is entire (composition of polynomial and exp).
The infinite product converges locally uniformly (from summability of `1/|ρₙ|²` via
`multipliable_one_add_of_summable`). Locally uniform limits of holomorphic functions
are holomorphic. -/
private theorem weierstrass_product_differentiable
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2)) :
    Differentiable ℂ (fun s =>
      ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) := by
  have htprod_eq : (fun s => ∏' n,
      Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) =
      (fun s => ∏' n, WeierstrassFactors.epShifted 1 (zeros n) s) := by
    ext s; exact tprod_congr (fun n =>
      Aristotle.Standalone.HadamardProductConvergence.E1_eq_epShifted (zeros n) s)
  rw [htprod_eq]
  set f : ℕ → ℂ → ℂ := fun n s => WeierstrassFactors.epShifted 1 (zeros n) s - 1
  have hprod_compact : ∀ K : Set ℂ, K ⊆ Set.univ → IsCompact K →
      HasProdUniformlyOn (fun n s => WeierstrassFactors.epShifted 1 (zeros n) s)
        (fun s => ∏' n, WeierstrassFactors.epShifted 1 (zeros n) s) K := by
    intro K _ hKcompact
    obtain ⟨R_K, hR_K⟩ := hKcompact.isBounded.exists_norm_le
    set R := max R_K 1 with hR_def
    have hR_pos : (0 : ℝ) < R := by positivity
    set u : ℕ → ℝ := fun n => 3 * R ^ 2 * (1 / ‖zeros n‖ ^ 2)
    have hu : Summable u := hsum.mul_left (3 * R ^ 2)
    have hlarge : ∀ᶠ n in Filter.cofinite, ‖zeros n‖ > 2 * R := by
      rw [Nat.cofinite_eq_atTop]
      have htend := hsum.tendsto_atTop_zero
      rw [NormedAddCommGroup.tendsto_atTop] at htend
      obtain ⟨N, hN⟩ := htend (1 / (2 * R) ^ 2) (by positivity)
      filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun m hm => hN m hm⟩] with n hn
      have hρ_pos : 0 < ‖zeros n‖ := norm_pos_iff.mpr (hne n)
      simp only [sub_zero] at hn
      rw [Real.norm_of_nonneg (div_nonneg one_pos.le (sq_nonneg _))] at hn
      rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < ‖zeros n‖ ^ 2) (by positivity)] at hn
      nlinarith [sq_nonneg (‖zeros n‖ - 2 * R)]
    have hf_bound : ∀ᶠ n in Filter.cofinite, ∀ x ∈ K, ‖f n x‖ ≤ u n := by
      filter_upwards [hlarge] with n hn x hx
      show ‖WeierstrassFactors.epShifted 1 (zeros n) x - 1‖ ≤ _
      have hρ_pos : 0 < ‖zeros n‖ := norm_pos_iff.mpr (hne n)
      have hquot : ‖x / zeros n‖ ≤ 1 / 2 := by
        rw [norm_div]
        calc ‖x‖ / ‖zeros n‖ ≤ R_K / ‖zeros n‖ := by gcongr; exact hR_K x hx
          _ ≤ R / ‖zeros n‖ := by gcongr; exact le_max_left _ _
          _ ≤ R / (2 * R) := by
              apply div_le_div_of_nonneg_left hR_pos.le (by positivity) (by linarith)
          _ = 1 / 2 := by field_simp
      calc ‖WeierstrassFactors.epShifted 1 (zeros n) x - 1‖
          = ‖1 - WeierstrassFactors.epShifted 1 (zeros n) x‖ := norm_sub_rev _ _
        _ ≤ 3 * ‖x / zeros n‖ ^ 2 :=
            WeierstrassFactors.norm_one_sub_ep_one_shifted_le hquot
        _ = 3 * (‖x‖ / ‖zeros n‖) ^ 2 := by rw [norm_div]
        _ ≤ 3 * (R / ‖zeros n‖) ^ 2 := by gcongr; exact (hR_K x hx).trans (le_max_left _ _)
        _ = 3 * R ^ 2 * (1 / ‖zeros n‖ ^ 2) := by ring
    have hf_cts : ∀ n, ContinuousOn (f n) K :=
      fun n => ((WeierstrassFactors.differentiable_epShifted 1 (zeros n)).continuous.sub
        continuous_const).continuousOn
    have hmtest := Summable.hasProdUniformlyOn_one_add hKcompact hu hf_bound hf_cts
    have hsimp : ∀ (i : ℕ) (x : ℂ),
        1 + f i x = WeierstrassFactors.epShifted 1 (zeros i) x := fun _ _ => by
      simp [f]
    exact (hmtest.congr (Eventually.of_forall fun s => fun x _ =>
      Finset.prod_congr rfl (fun i _ => hsimp i x))).congr_right
      (fun x _ => tprod_congr (fun n => hsimp n x))
  have hconv : TendstoLocallyUniformlyOn
      (fun N s => ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s)
      (fun s => ∏' n, WeierstrassFactors.epShifted 1 (zeros n) s)
      atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hKcompact
    exact (hprod_compact K (Set.subset_univ K) hKcompact).tendstoUniformlyOn_finsetRange
  have hpartial_diff : ∀ᶠ N in Filter.atTop,
      DifferentiableOn ℂ (fun s =>
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s) Set.univ := by
    apply Filter.Eventually.of_forall
    intro N
    exact (Differentiable.fun_finset_prod (fun n _ =>
      WeierstrassFactors.differentiable_epShifted 1 (zeros n))).differentiableOn
  have hdiff_on := hconv.differentiableOn hpartial_diff isOpen_univ
  exact fun s => (hdiff_on s (Set.mem_univ s)).differentiableAt
    (isOpen_univ.mem_nhds (Set.mem_univ s))

/-- Tail product analyticity via re-indexing. The complement is Denumerable;
re-index to ℕ and apply `weierstrass_product_differentiable`. -/
theorem weierstrass_tail_analyticAt_proof
    (zeros : ℕ → ℂ) (z : ℂ) (hz : z ≠ 0)
    (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hP_diff : Differentiable ℂ (fun s =>
      ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)))
    (hfin : Set.Finite {n : ℕ | zeros n = z}) :
    AnalyticAt ℂ (fun s => ∏' (n : {n : ℕ // n ∉ hfin.toFinset}),
      Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros ↑n)) z := by
  haveI : Infinite {n : ℕ // n ∉ hfin.toFinset} := by
    apply Set.infinite_coe_iff.mpr
    have : Set.Infinite {n : ℕ | n ∉ hfin.toFinset} := by
      rw [show {n : ℕ | n ∉ hfin.toFinset} = (↑hfin.toFinset : Set ℕ)ᶜ from by ext; simp]
      exact Set.Finite.infinite_compl (hfin.toFinset.finite_toSet)
    exact this
  haveI := Encodable.ofCountable {n : ℕ // n ∉ hfin.toFinset}
  letI den := Denumerable.ofEncodableOfInfinite {n : ℕ // n ∉ hfin.toFinset}
  set e := (Denumerable.eqv {n : ℕ // n ∉ hfin.toFinset}).symm
  set tail_zeros := (fun (n : {n : ℕ // n ∉ hfin.toFinset}) => zeros ↑n) ∘ e
  have htail_ne : ∀ m, tail_zeros m ≠ 0 := fun m => hne _
  have htail_sum : Summable (fun m => 1 / ‖tail_zeros m‖ ^ 2) :=
    (hsum.subtype (fun n => n ∉ hfin.toFinset)).comp_injective e.injective
  have htail_diff := weierstrass_product_differentiable tail_zeros htail_ne htail_sum
  have htprod_eq : (fun s => ∏' (n : {n : ℕ // n ∉ hfin.toFinset}),
      Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros ↑n)) =
      (fun s => ∏' m, Aristotle.Standalone.HadamardProductConvergence.E1 (s / tail_zeros m)) := by
    ext s; exact (e.tprod_eq (fun n =>
      Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros ↑n))).symm
  rw [htprod_eq]
  exact htail_diff.analyticAt z

/-- The tail product `∏' (n : {n // n ∉ hfin.toFinset}), E₁(s/zeros n)` is analytic at `z`.
Proof: the tail equals P / (finite product) on a punctured neighborhood of z (where
the finite product is nonzero). The tail is continuous at z (tprod of continuous functions
converging uniformly). By the removable singularity theorem, the tail is analytic at z. -/
private lemma weierstrass_tail_analyticAt
    (zeros : ℕ → ℂ) (z : ℂ) (hz : z ≠ 0)
    (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hP_diff : Differentiable ℂ (fun s =>
      ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)))
    (hfin : Set.Finite {n : ℕ | zeros n = z}) :
    AnalyticAt ℂ (fun s => ∏' (n : {n : ℕ // n ∉ hfin.toFinset}),
      Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros ↑n)) z :=
  weierstrass_tail_analyticAt_proof zeros z hz hne hsum hP_diff hfin

/-- Norm-summability of E1(z/ρ) - 1: the M-test bound ‖E1(z/ρ) - 1‖ ≤ 3R²/‖ρ‖². -/
private theorem E1_minus_one_norm_summable
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (z : ℂ) :
    Summable (fun n =>
      ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) - 1‖) := by
  set R := max ‖z‖ 1
  have hR_pos : 0 < R := lt_max_of_lt_right one_pos
  apply (hsum.mul_left (3 * R ^ 2)).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  have htend := hsum.tendsto_atTop_zero
  rw [NormedAddCommGroup.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend (1 / (2 * R) ^ 2) (by positivity)
  filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun m hm => hN m hm⟩] with n hn
  have hρ_pos : 0 < ‖zeros n‖ := norm_pos_iff.mpr (hne n)
  have hlarge : 2 * R < ‖zeros n‖ := by
    simp only [sub_zero] at hn
    rw [Real.norm_of_nonneg (div_nonneg one_pos.le (sq_nonneg _))] at hn
    rw [div_lt_div_iff₀ (sq_pos_of_pos hρ_pos) (by positivity)] at hn
    nlinarith [sq_nonneg (‖zeros n‖ - 2 * R)]
  have hquot_le : ‖z / zeros n‖ ≤ 1 := by
    rw [norm_div]
    calc ‖z‖ / ‖zeros n‖ ≤ R / ‖zeros n‖ := by gcongr; exact le_max_left _ _
      _ ≤ R / (2 * R) := by
          apply div_le_div_of_nonneg_left hR_pos.le (by positivity) (by linarith)
      _ = 1 / 2 := by field_simp
      _ ≤ 1 := by norm_num
  rw [norm_norm]
  calc ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) - 1‖
      ≤ 3 * ‖z / zeros n‖ ^ 2 :=
        Aristotle.Standalone.HadamardProductConvergence.E1_sub_one_norm_le hquot_le
    _ = 3 * (‖z‖ / ‖zeros n‖) ^ 2 := by rw [norm_div]
    _ ≤ 3 * (R / ‖zeros n‖) ^ 2 := by gcongr; exact le_max_left _ _
    _ = 3 * R ^ 2 * (1 / ‖zeros n‖ ^ 2) := by ring

/-- Summability of E1(z/ρ) - 1, derived from norm-summability. -/
private theorem E1_minus_one_summable
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (z : ℂ) :
    Summable (fun n =>
      Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) - 1) :=
  (E1_minus_one_norm_summable zeros hne hsum z).of_norm

/-- The Weierstrass E1 product is multipliable (at each point z) when
the zeros have summable 1/‖ρ‖². -/
private theorem E1_product_multipliable
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (z : ℂ) :
    Multipliable (fun n =>
      Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)) := by
  have heq : (fun n => Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)) =
      fun n => 1 + (Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) - 1) :=
    funext fun _ => by ring
  rw [heq]
  exact multipliable_one_add_of_summable (E1_minus_one_norm_summable zeros hne hsum z)

set_option maxHeartbeats 50000000 in
/-- **Product splitting**: the infinite product splits as finite times complement. -/
private theorem tprod_E1_split_finset
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (F : Finset ℕ) (z : ℂ) :
    ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)
      = (∏ n ∈ F, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)) *
        (∏' n : ↑(F : Set ℕ)ᶜ, Aristotle.Standalone.HadamardProductConvergence.E1
          (z / zeros n)) :=
  by
    set f : ℕ → ℂ := fun n =>
      Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) with hf_def
    have hf : Multipliable f := E1_product_multipliable zeros hne hsum z
    -- hs: the finite subtype is trivially multipliable
    haveI : Fintype (↑F : Set ℕ) := F.fintypeCoeSort
    have hs : Multipliable (f ∘ (↑) : (↑F : Set ℕ) → ℂ) := (hasProd_fintype _).multipliable
    -- hsc: the complement subtype is multipliable (same M-test as E1_product_multipliable)
    have hsc : Multipliable (f ∘ (↑) : ↑(↑F : Set ℕ)ᶜ → ℂ) := by
      -- Bypass Multipliable.subtype (requires CommGroup) via additive route:
      -- norm-summability on subtype → multipliable_one_add_of_summable
      have heq_sub :
          (f ∘ (↑) : ↑(↑F : Set ℕ)ᶜ → ℂ)
            = fun (n : ↑(↑F : Set ℕ)ᶜ) => 1 +
                (Aristotle.Standalone.HadamardProductConvergence.E1
                  (z / zeros (n : ℕ)) - 1) := by
        funext n; simp [hf_def]
      rw [heq_sub]
      have hnorm_sub :
          Summable (fun n : ↑(↑F : Set ℕ)ᶜ =>
            ‖Aristotle.Standalone.HadamardProductConvergence.E1
              (z / zeros (n : ℕ)) - 1‖) := by
        simpa using
          (E1_minus_one_norm_summable zeros hne hsum z).subtype ((F : Set ℕ)ᶜ)
      exact multipliable_one_add_of_summable hnorm_sub
    have hsplit := Multipliable.tprod_mul_tprod_compl hs hsc
    rw [← hsplit, Finset.tprod_subtype' F f]

instance : XiQuotientMeromorphicOrderNonnegHyp := ⟨by
  intro zeros hcover hne hzeros_zero hsum hP_diff hmult z
  -- Abbreviate the Weierstrass product
  set P := fun s => ∏' n,
    Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n) with hP_def
  set Q := fun z => RiemannXiAlt z / P z with hQ_def
  -- Key analyticity facts
  have hxi_analytic : ∀ w, AnalyticAt ℂ RiemannXiAlt w := RiemannXiAlt_entire.analyticAt
  have hP_analytic : ∀ w, AnalyticAt ℂ P w := hP_diff.analyticAt
  -- If z = zeros(n), then E1(z/zeros(n)) = E1(1) = 0, so P(z) = 0
  have hP_zero_at_root : ∀ n, P (zeros n) = 0 := by
    intro n
    have : (fun n' => Aristotle.Standalone.HadamardProductConvergence.E1
        (zeros n / zeros n')) n = 0 := by
      simp [div_self (hne n), E1_one_eq_zero]
    exact tprod_of_exists_eq_zero ⟨n, this⟩
  -- Case split on P(z) = 0 vs P(z) ≠ 0
  by_cases hPz : P z = 0
  · -- CASE 2: P(z) = 0. We need the Weierstrass product order theory.
    -- The analytic orders of ξ and P match at every common zero.
    -- This requires Weierstrass product order analysis not yet in Mathlib.
    -- P(z) = 0 implies z = zeros(n) for some n, hence z ≠ 0
    have hz : z ≠ 0 := by
      intro h; rw [h] at hPz
      have : P 0 = 1 := by
        show ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (0 / zeros n) = 1
        simp [zero_div, Aristotle.Standalone.HadamardProductConvergence.E1]
      exact one_ne_zero (this ▸ hPz)
    -- {n | zeros n = z} is finite (from summability)
    have hfin := finite_zeros_at zeros z hz hne hsum
    -- Step 1: analyticOrderAt P z = card{n | zeros n = z}
    --   Requires: tail product analytic + nonvanishing at z (proved: ne_zero)
    --   + finite product order = card (proved: analyticOrderAt_finprod_of_order_one)
    -- Step 2: card{n | zeros n = z} = analyticOrderAt ξ z
    --   This is the multiplicity gap: the enumeration must be multiplicity-aware
    -- Step A: tail product analytic at z
    have h_tail_an := weierstrass_tail_analyticAt zeros z hz hne hsum hP_diff hfin
    -- Step B: tail product nonvanishing at z → analyticOrderAt = 0
    have h_tail_ne := weierstrass_tail_ne_zero zeros z hz hne hsum hfin
    have h_tail_ord : analyticOrderAt (fun s => ∏' (n : {n : ℕ // n ∉ hfin.toFinset}),
        Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros ↑n)) z = 0 :=
      h_tail_an.analyticOrderAt_eq_zero.mpr h_tail_ne
    -- Step C: analyticOrderAt P z = card{n | zeros n = z} (via finite/tail split)
    -- This requires: P = finite_prod * tail_prod, then analyticOrderAt_mul
    -- finite_prod has order = card (from analyticOrderAt_finprod_of_order_one + E1_div)
    -- tail_prod has order = 0 (from Step B)
    -- Multiplicity gap: card = analyticOrderAt ξ z (NOT provable from current API)
    have h_orders_match : analyticOrderAt P z = analyticOrderAt RiemannXiAlt z := by
      -- H1: product order = card (tprod_E1_split_finset now available above)
      have hP_order_card : analyticOrderAt P z = hfin.toFinset.card := by
        set F := hfin.toFinset
        -- Split: P(s) = fin_part(s) * tail_part(s)
        have hP_split : ∀ s, P s =
            (∏ n ∈ F, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) *
            (∏' n : ↑(↑F : Set ℕ)ᶜ,
              Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros ↑n)) :=
          fun s => tprod_E1_split_finset zeros hne hsum F s
        -- P = fin * tail. P analytic, tail analytic and nonzero, so fin = P/tail is analytic.
        -- Use analyticOrderAt_congr to match P with fin*tail.
        set fin_part : ℂ → ℂ := fun s =>
          ∏ n ∈ F, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)
        set tail_part : ℂ → ℂ := fun s => ∏' n : ↑(↑F : Set ℕ)ᶜ,
          Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros ↑n)
        -- P = fin_part * tail_part
        have hP_eq : ∀ s, P s = fin_part s * tail_part s :=
          fun s => tprod_E1_split_finset zeros hne hsum F s
        -- fin_part analytic: P = fin*tail, P analytic, tail analytic+nonzero → fin = P/tail analytic
        have hfin_an : AnalyticAt ℂ fin_part z := by
          have hP_an : AnalyticAt ℂ P z := hP_diff.analyticAt z
          have hPdiv : AnalyticAt ℂ (fun s => P s / tail_part s) z :=
            hP_an.div h_tail_an h_tail_ne
          -- P/tail = fin near z (where tail ≠ 0)
          have h_tail_cts_ne : ∀ᶠ s in nhds z, tail_part s ≠ 0 :=
            h_tail_an.continuousAt.eventually_ne h_tail_ne
          exact hPdiv.congr (h_tail_cts_ne.mono fun s hs => by
            show P s / tail_part s = fin_part s
            rw [hP_eq s, mul_div_cancel_right₀ _ hs])
        -- Order decomposition
        have h_congr : analyticOrderAt P z = analyticOrderAt (fun s => fin_part s * tail_part s) z :=
          analyticOrderAt_congr (Filter.Eventually.of_forall hP_eq)
        have h_eq_mul : (fun s => fin_part s * tail_part s) = fin_part * tail_part := rfl
        rw [h_congr, h_eq_mul]
        have h_tail_an' : AnalyticAt ℂ tail_part z := h_tail_an
        have h_tail_ord' : analyticOrderAt tail_part z = 0 := h_tail_ord
        rw [analyticOrderAt_mul hfin_an h_tail_an', h_tail_ord', add_zero]
        -- Finite product order = card
        exact analyticOrderAt_finprod_of_order_one F
          (fun n s => Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) z
          (fun n _ => by exact (E1_analyticAt _).comp (analyticAt_id.div analyticAt_const (hne n)))
          (fun n hn => by
            have hzn : zeros n = z := hfin.mem_toFinset.mp hn
            show analyticOrderAt (fun s => Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) z = 1
            rw [hzn]; exact analyticOrderAt_E1_div_eq_one z hz)
      -- H2: card conversion
      have hcard_eq : hfin.toFinset.card = Nat.card {n : ℕ | zeros n = z} := by
        haveI : Fintype {n : ℕ | zeros n = z} := hfin.fintype
        simp only [Nat.card_eq_fintype_card]
        have h_finsets_eq : hfin.toFinset = {n : ℕ | zeros n = z}.toFinset :=
          Finset.ext fun n => ⟨fun h => Set.mem_toFinset.mpr (hfin.mem_toFinset.mp h),
            fun h => hfin.mem_toFinset.mpr (Set.mem_toFinset.mp h)⟩
        rw [h_finsets_eq, Set.toFinset_card]
      -- Combine via hmult
      rw [show analyticOrderAt P z = (hfin.toFinset.card : ℕ∞) from by
            exact_mod_cast hP_order_card,
          hcard_eq, hmult z]
    -- Both are analytic, so meromorphic orders equal analytic orders (cast to ℤ)
    have hxi_mero : meromorphicOrderAt RiemannXiAlt z =
        (analyticOrderAt RiemannXiAlt z).map (↑) :=
      (hxi_analytic z).meromorphicOrderAt_eq
    have hP_mero : meromorphicOrderAt P z =
        (analyticOrderAt P z).map (↑) :=
      (hP_analytic z).meromorphicOrderAt_eq
    -- The analytic order of ξ at z is finite (ξ is not identically zero)
    have hxi_order_ne_top : analyticOrderAt RiemannXiAlt z ≠ ⊤ := by
      intro h_top
      have hev := analyticOrderAt_eq_top.mp h_top
      -- hev : ∀ᶠ w in 𝓝 z, RiemannXiAlt w = 0
      -- Convert to frequently in punctured nhd for the identity principle
      have hfreq : ∃ᶠ w in 𝓝[≠] z, RiemannXiAlt w = 0 :=
        (hev.filter_mono nhdsWithin_le_nhds).frequently
      exact xiZeroSet_no_accPt z hfreq
    -- Q = ξ * P⁻¹, so order(Q) = order(ξ) + order(P⁻¹) = order(ξ) - order(P)
    have hQ_eq : Q = RiemannXiAlt * P⁻¹ := by ext w; simp [Q, div_eq_mul_inv]
    rw [hQ_eq,
        meromorphicOrderAt_mul (hxi_analytic z).meromorphicAt (hP_analytic z).meromorphicAt.inv,
        meromorphicOrderAt_inv, hxi_mero, hP_mero, h_orders_match]
    -- Now: ENat.map ↑ (analyticOrderAt ξ z) + -(ENat.map ↑ (analyticOrderAt ξ z)) = 0
    -- Since the order is finite, this is a + (-a) = 0 in ℤ
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hxi_order_ne_top
    simp [hk]
  · -- CASE 1: P(z) ≠ 0 → ξ(z) ≠ 0 → Q analytic and nonzero → order = 0
    -- Contrapositive: if ξ(z) = 0, then z = zeros(n), so P(z) = 0, contradiction.
    have hxi_ne : RiemannXiAlt z ≠ 0 := by
      intro hxi_z
      obtain ⟨n, hn⟩ := hcover z hxi_z
      exact hPz (hn ▸ hP_zero_at_root n)
    -- ξ/P is analytic at z (since P(z) ≠ 0) and nonzero at z
    have hQ_analytic : AnalyticAt ℂ (fun z => RiemannXiAlt z / P z) z :=
      (hxi_analytic z).div (hP_analytic z) hPz
    have hQ_ne : (fun z => RiemannXiAlt z / P z) z ≠ 0 := div_ne_zero hxi_ne hPz
    rw [hQ_analytic.meromorphicOrderAt_eq,
        hQ_analytic.analyticOrderAt_eq_zero.mpr hQ_ne]
    simp⟩

/-- **Hypothesis boundary**: The MeromorphicNF extension Q of ξ/P is nonvanishing.

At non-zeros of P: Q = ξ/P, and ξ(s) ≠ 0 when P(s) ≠ 0 (because if ξ(s) = 0
then s = zeros(n) by coverage, and P(zeros(n)) = 0 by construction).

At zeros of P: Q(ρ) is the ratio of leading coefficients f₁(ρ)/g₁(ρ),
both nonvanishing, from the analytic order factorization.

With multiplicity-aware enumeration, ord(ξ,ρ) = ord(P,ρ) = m, so Q(ρ) =
(m-th Taylor coefficient of ξ at ρ) / (m-th Taylor coefficient of P at ρ) ≠ 0. -/
class XiQuotientNonvanishingHyp : Prop where
  nonvanishing :
    ∀ (zeros : ℕ → ℂ),
      (∀ s, RiemannXiAlt s = 0 → ∃ n, s = zeros n) →
      (∀ n, zeros n ≠ 0) →
      (∀ n, RiemannXiAlt (zeros n) = 0) →
      Summable (fun n => 1 / ‖zeros n‖ ^ 2) →
      Differentiable ℂ (fun s =>
        ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) →
      (∀ z, (Nat.card {n | zeros n = z} : ℕ∞) = analyticOrderAt RiemannXiAlt z) →
      ∀ s, toMeromorphicNFOn
        (fun z => RiemannXiAlt z /
          ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n))
        Set.univ s ≠ 0

instance : XiQuotientNonvanishingHyp := ⟨by
  intro zeros hcover hne hzeros_zero hsum hP_diff hmult s
  -- We derive nonvanishing from the stronger order = 0 hypothesis.
  -- Step 1: Q₀ = ξ/P is meromorphic on ℂ
  set P := fun s => ∏' n,
    Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n) with hP_def
  set Q₀ := fun z => RiemannXiAlt z / P z with hQ₀_def
  have hQ₀_merOn : MeromorphicOn Q₀ Set.univ :=
    fun z _ => (RiemannXiAlt_entire.analyticAt z).meromorphicAt.div
      (hP_diff.analyticAt z).meromorphicAt
  -- Step 2: The NF form preserves orders
  have h_order_zero : meromorphicOrderAt Q₀ s = 0 :=
    XiQuotientMeromorphicOrderNonnegHyp.order_eq_zero
      zeros hcover hne hzeros_zero hsum hP_diff hmult s
  have h_order_nf : meromorphicOrderAt (toMeromorphicNFOn Q₀ Set.univ) s = 0 := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hQ₀_merOn (Set.mem_univ s)]
    exact h_order_zero
  -- Step 3: NF + order ≥ 0 → analytic; order = 0 + analytic → nonzero
  have hQ_nf : MeromorphicNFOn (toMeromorphicNFOn Q₀ Set.univ) Set.univ :=
    meromorphicNFOn_toMeromorphicNFOn Q₀ Set.univ
  exact (hQ_nf (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff.mp h_order_nf⟩

/-- **Hypothesis boundary**: The entire quotient Q = ξ/P satisfies the
sub-exponential growth bound |Q(s)| ≤ exp(C_Q(|s|+1)^{7/4}).

Proof sketch (Titchmarsh §8.22): For each s, choose R > 2‖s‖ + 1 from the
pigeonhole principle such that the circle |z| = R avoids all zeros of P.
On this circle: |ξ(z)| ≤ exp(C₁R^{3/2}) and |P(z)| ≥ exp(−C₂R^{7/4}).
So |Q(z)| ≤ exp(C₁R^{3/2}+C₂R^{7/4}). By the maximum modulus principle:
|Q(s)| ≤ max_{|z|=R} |Q(z)| ≤ exp(C_Q(‖s‖+1)^{7/4}).

The exponent 7/4 (rather than 3/2) absorbs the R^{3/2}·log R factor from
the minimum modulus pigeonhole on good circles. Since 7/4 < 2, the downstream
Liouville theorem (subquadratic_growth_imp_linear) still applies. -/
class XiQuotientGrowthBoundHyp : Prop where
  growth_bound :
    ∀ (Q : ℂ → ℂ),
      Differentiable ℂ Q →
      (∀ s, Q s ≠ 0) →
      ∀ (zeros : ℕ → ℂ),
        (∀ n, zeros n ≠ 0) →
        (∀ n, RiemannXiAlt (zeros n) = 0) →
        Summable (fun n => 1 / ‖zeros n‖ ^ 2) →
        (∃ C_cnt : ℝ, 0 < C_cnt ∧ ∀ R : ℝ, 1 ≤ R →
          ∃ S : Finset ℕ,
            (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ R) ∧
            (S.card : ℝ) ≤ C_cnt * R ^ (3 / 2 : ℝ)) →
        (∀ s, RiemannXiAlt s = Q s *
          ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) →
        ∃ C_Q : ℝ, 0 < C_Q ∧ ∀ s, ‖Q s‖ ≤ Real.exp (C_Q * (‖s‖ + 1) ^ (7/4 : ℝ))

/-
**Focused sorry**: On a good circle of radius R (avoiding zeros of the
Weierstrass product), the product has a lower bound exp(-C₂ R^{7/4}).

This is the minimum modulus principle for Weierstrass products of finite order
(Titchmarsh §8.22): pigeonhole gives R ∈ [R₀, 2R₀] avoiding all zero norms.
Each factor satisfies |E₁(z/ρ)| ≥ δ/(R+|ρ|), and the product of these bounds
with zero-counting N(R) ≤ C'R^{3/2} gives the exponential lower bound.
The extra log R factor from the pigeonhole is absorbed into the 7/4 exponent.

Building blocks: MinimumModulusPigeonhole (sorry-free),
weierstrass_factor_lower_bound (sorry-free), xi_zero_count_bound (sorry-free).
-/


/-- Helper: extract controlled Finset from hcount at radius 4R₀. -/
private theorem controlled_index_finset
    (zeros : ℕ → ℂ) (R₀ : ℝ) (hR₀ : 1 ≤ R₀)
    (C_cnt : ℝ) (hC_cnt : 0 < C_cnt)
    (hcount_fn : ∀ R : ℝ, 1 ≤ R →
      ∃ S : Finset ℕ,
        (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ R) ∧
        (S.card : ℝ) ≤ C_cnt * R ^ (3 / 2 : ℝ)) :
    ∃ S : Finset ℕ,
      (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ 4 * R₀) ∧
      (S.card : ℝ) ≤ C_cnt * (4 * R₀) ^ (3 / 2 : ℝ) :=
  hcount_fn (4 * R₀) (by linarith)

/-- Helper: choose good radius in [R₀, 2R₀] via pigeonhole, avoiding
all zero norms in the controlled band. -/
private theorem good_radius_via_pigeonhole
    (zeros : ℕ → ℂ) (R₀ : ℝ) (hR₀ : 1 ≤ R₀)
    (S : Finset ℕ) :
    ∃ R : ℝ, R₀ ≤ R ∧ R ≤ 2 * R₀ ∧
      ∀ n ∈ S, |R - ‖zeros n‖| ≥ R₀ / (2 * ↑S.card + 2) := by
  set δ := R₀ / (2 * ↑S.card + 2) with hδ_def
  have hδ_pos : 0 < δ := by positivity
  set norms := S.image (fun n => ‖zeros n‖) with hnorms_def
  have hnorms_card : (norms.card : ℝ) ≤ ↑S.card := by
    exact_mod_cast Finset.card_image_le
  have h_small : (↑norms.card : ℝ) * (2 * δ) < 2 * R₀ - R₀ := by
    have h1 : (↑norms.card : ℝ) * (2 * δ) ≤ (↑S.card : ℝ) * (2 * δ) := by gcongr
    have h2 : (↑S.card : ℝ) * (2 * δ) = ↑S.card * R₀ / (↑S.card + 1) := by
      rw [hδ_def]; field_simp
    have hcard_nn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
    have h3 : (S.card : ℝ) * R₀ / ((S.card : ℝ) + 1) < R₀ := by
      rw [div_lt_iff₀ (show (0 : ℝ) < (S.card : ℝ) + 1 by linarith)]
      nlinarith
    linarith
  obtain ⟨R, hR_mem, hR_avoid⟩ :=
    MinimumModulusPigeonhole.pigeonhole_interval_avoidance R₀ (2 * R₀)
      (by linarith) norms δ hδ_pos h_small
  exact ⟨R, hR_mem.1, hR_mem.2, fun n hn =>
    hR_avoid ‖zeros n‖ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)⟩

/-- Helper: per-factor lower bound for E1(z/ρ) in the controlled band.
For ‖z‖ = R ∈ [R₀, 2R₀], ‖ρ‖ ∈ [R₀/2, 4R₀], and |R - ‖ρ‖| ≥ δ:
‖E1(z/ρ)‖ ≥ (δ/(6R₀)) · exp(-4). -/
private theorem near_factor_lower_bound
    (z ρ : ℂ) (R R₀ δ : ℝ)
    (hρ_ne : ρ ≠ 0) (hR₀_pos : 1 ≤ R₀)
    (hR_lo : R₀ ≤ R) (hR_hi : R ≤ 2 * R₀)
    (hz : ‖z‖ = R) (hδ_pos : 0 < δ)
    (hρ_lo : R₀ / 2 ≤ ‖ρ‖) (hρ_hi : ‖ρ‖ ≤ 4 * R₀)
    (hgap : |R - ‖ρ‖| ≥ δ) :
    ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / ρ)‖ ≥
      δ / (6 * R₀) * Real.exp (-4) := by
  have hR_pos : (0 : ℝ) < R := by linarith
  have hρ_pos : (0 : ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
  -- Step 1: E1(w) = (1 - w) * exp(w), so ‖E1(w)‖ = ‖1-w‖ * ‖exp(w)‖
  unfold Aristotle.Standalone.HadamardProductConvergence.E1
  rw [norm_mul]
  -- Step 2: ‖1 - z/ρ‖ ≥ δ/(R+‖ρ‖) from weierstrass_factor_lower_bound
  have h_wf := MinimumModulusPigeonhole.weierstrass_factor_lower_bound
    z ρ hρ_ne R δ hR_pos hδ_pos hz hgap
  -- Step 3: δ/(R+‖ρ‖) ≥ δ/(6R₀) since R+‖ρ‖ ≤ 6R₀
  have hRρ_bound : R + ‖ρ‖ ≤ 6 * R₀ := by linarith
  have hRρ_pos : (0 : ℝ) < R + ‖ρ‖ := by linarith
  have h_denom : δ / (6 * R₀) ≤ ‖1 - z / ρ‖ := by
    calc δ / (6 * R₀) ≤ δ / (R + ‖ρ‖) :=
          div_le_div_of_nonneg_left hδ_pos.le hRρ_pos hRρ_bound
      _ ≤ ‖1 - z / ρ‖ := h_wf
  -- Step 4: ‖exp(z/ρ)‖ = exp(Re(z/ρ)) ≥ exp(-4)
  have h_exp : Real.exp (-4 : ℝ) ≤ ‖Complex.exp (z / ρ)‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp_of_le
    -- Re(z/ρ) ≥ -|Re(z/ρ)| ≥ -‖z/ρ‖ ≥ -R/‖ρ‖ ≥ -4
    -- Re(z/ρ) ��� -‖z/ρ‖ ≥ -R/(R₀/2) = -4
    have h_re_ge : -(z / ρ).re ≤ ‖z / ρ‖ :=
      (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    have h_norm_le : ‖z / ρ‖ ≤ 4 := by
      rw [norm_div, hz]
      exact div_le_of_le_mul₀ (by linarith) (by positivity) (by nlinarith)
    linarith
  -- Step 5: Combine
  rw [ge_iff_le]
  have h_combine : δ / (6 * R₀) * Real.exp (-4) ≤
      ‖1 - z / ρ‖ * ‖Complex.exp (z / ρ)‖ :=
    mul_le_mul h_denom h_exp (Real.exp_nonneg _) (by positivity)
  exact h_combine

/-- Helper: log R ≤ C * R^{1/4} for R ≥ 1. This absorbs logarithmic losses
into a power of R. Coarse constant C = 4/exp(1) suffices. -/
private theorem log_le_rpow_quarter (R : ℝ) (hR : 1 ≤ R) :
    Real.log R ≤ 4 * R ^ (1/4 : ℝ) := by
  have hR_nonneg : 0 ≤ R := by linarith
  have h := Real.log_le_rpow_div hR_nonneg (by norm_num : 0 < (1/4 : ℝ))
  -- h : Real.log R ≤ R ^ (1/4 : ℝ) / (1/4)
  have hdiv : R ^ (1/4 : ℝ) / (1/4 : ℝ) = 4 * R ^ (1/4 : ℝ) := by ring
  linarith [hdiv ▸ h]

/-- Helper: R^{3/2} * log R ≤ C * R^{7/4} for R ≥ 1.
Immediate from log_le_rpow_quarter. -/
private theorem rpow_three_halves_log_le_rpow_seven_fourths (R : ℝ) (hR : 1 ≤ R) :
    R ^ (3/2 : ℝ) * Real.log R ≤ 4 * R ^ (7/4 : ℝ) := by
  have hR_pos : 0 < R := by linarith
  have h := log_le_rpow_quarter R hR
  have hR_nn : (0 : ℝ) ≤ R := hR_pos.le
  calc R ^ (3/2 : ℝ) * Real.log R
      ≤ R ^ (3/2 : ℝ) * (4 * R ^ (1/4 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hR_nn _)
    _ = 4 * (R ^ (3/2 : ℝ) * R ^ (1/4 : ℝ)) := by ring
    _ = 4 * R ^ (7/4 : ℝ) := by
        congr 1; rw [← Real.rpow_add hR_pos]; norm_num

/-! ## Inner reciprocal sum bound from counting function (Aristotle 1cc25961) -/

private theorem inner_reciprocal_sum_small
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (S₁ : Finset ℕ) (hS₁ : ∀ n, n ∈ S₁ ↔ ‖zeros n‖ ≤ 1)
    (R₀ : ℝ) (hR₀ : 1 ≤ R₀) :
    (∑ n ∈ S₁, R₀ / ‖zeros n‖) ≤
      (∑ n ∈ S₁, (1 : ℝ) / ‖zeros n‖) * R₀ ^ (3 / 2 : ℝ) := by
  norm_num [div_eq_mul_inv, mul_comm, Finset.mul_sum _ _ _]
  exact Finset.sum_le_sum fun i _ => by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left
      (le_trans (by norm_num) (Real.rpow_le_rpow_of_exponent_le hR₀ (show (3 : ℝ) / 2 ≥ 1 by norm_num)))
      (by positivity)

private theorem dyadic_shell_sum_bound
    (zeros : ℕ → ℂ)
    (S_shell S_hi : Finset ℕ)
    (lo R₀ : ℝ) (hlo : 0 < lo) (hR₀ : 0 ≤ R₀)
    (hS_sub : S_shell ⊆ S_hi)
    (hS_lo : ∀ n ∈ S_shell, lo < ‖zeros n‖) :
    (∑ n ∈ S_shell, R₀ / ‖zeros n‖) ≤ (S_hi.card : ℝ) * (R₀ / lo) := by
  refine le_trans (Finset.sum_le_sum fun n hn =>
    div_le_div_of_nonneg_left (by positivity) (by positivity) <| le_of_lt <| hS_lo n hn) ?_
  simpa using mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (Finset.card_le_card hS_sub)) (div_nonneg hR₀ hlo.le)

set_option maxHeartbeats 200000000 in
private theorem inner_reciprocal_sum_medium
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (C_cnt : ℝ) (hC_cnt : 0 < C_cnt)
    (hcount_fn : ∀ R : ℝ, 1 ≤ R →
      ∃ S : Finset ℕ,
        (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ R) ∧
        (S.card : ℝ) ≤ C_cnt * R ^ (3 / 2 : ℝ))
    (R₀ : ℝ) (hR₀ : 4 ≤ R₀)
    (S_inner : Finset ℕ) (hS_inner : ∀ n, n ∈ S_inner ↔ ‖zeros n‖ ≤ R₀ / 2)
    (S₁ : Finset ℕ) (hS₁ : ∀ n, n ∈ S₁ ↔ ‖zeros n‖ ≤ 1) :
    (∑ n ∈ S_inner.filter (fun n => ¬(n ∈ S₁)), R₀ / ‖zeros n‖) ≤
      20 * C_cnt * R₀ ^ (3 / 2 : ℝ) := by
  -- Ported from Aristotle 1cc25961 (dyadic shell decomposition)
  let J := Nat.floor (Real.logb 2 (R₀ / 2))
  have h_shell : ∀ j ∈ Finset.range (J + 1), ∑ n ∈ S_inner.filter (fun n => 2 ^ j < ‖zeros n‖ ∧ ‖zeros n‖ ≤ 2 ^ (j + 1)), R₀ / ‖zeros n‖ ≤ C_cnt * R₀ * 2 ^ (3 / 2 : ℝ) * 2 ^ (j / 2 : ℝ) := by
    intro j hj
    have h_shell_card : (S_inner.filter (fun n => 2 ^ j < ‖zeros n‖ ∧ ‖zeros n‖ ≤ 2 ^ (j + 1))).card ≤ C_cnt * (2 ^ (j + 1)) ^ (3 / 2 : ℝ) := by
      obtain ⟨ S, hS₁, hS₂ ⟩ := hcount_fn ( 2 ^ ( j + 1 ) ) ( one_le_pow₀ ( by norm_num ) )
      refine le_trans ?_ hS₂
      exact_mod_cast Finset.card_le_card fun x hx => by aesop
    have h_shell_sum : ∑ n ∈ S_inner.filter (fun n => 2 ^ j < ‖zeros n‖ ∧ ‖zeros n‖ ≤ 2 ^ (j + 1)), R₀ / ‖zeros n‖ ≤ (S_inner.filter (fun n => 2 ^ j < ‖zeros n‖ ∧ ‖zeros n‖ ≤ 2 ^ (j + 1))).card * R₀ / 2 ^ j := by
      have h_shell_sum : ∀ n ∈ S_inner.filter (fun n => 2 ^ j < ‖zeros n‖ ∧ ‖zeros n‖ ≤ 2 ^ (j + 1)), R₀ / ‖zeros n‖ ≤ R₀ / 2 ^ j := by
        exact fun n hn => div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( by linarith [ Finset.mem_filter.mp hn ] )
      simpa [ mul_div_assoc ] using Finset.sum_le_sum h_shell_sum
    refine le_trans h_shell_sum ?_
    rw [ div_le_iff₀ ]
    · convert mul_le_mul_of_nonneg_right h_shell_card ( show 0 ≤ R₀ by positivity ) using 1 ; ring
      rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring
      rw [ mul_assoc, ← Real.rpow_add ] <;> norm_num ; ring
      norm_num
    · positivity
  have h_total : ∑ n ∈ S_inner.filter (fun n => n∉ S₁), R₀ / ‖zeros n‖ ≤ C_cnt * R₀ * 2 ^ (3 / 2 : ℝ) * ∑ j ∈ Finset.range (J + 1), 2 ^ (j / 2 : ℝ) := by
    have h_total : ∑ n ∈ S_inner.filter (fun n => n∉ S₁), R₀ / ‖zeros n‖ ≤ ∑ j ∈ Finset.range (J + 1), ∑ n ∈ S_inner.filter (fun n => 2 ^ j < ‖zeros n‖ ∧ ‖zeros n‖ ≤ 2 ^ (j + 1)), R₀ / ‖zeros n‖ := by
      rw [ ← Finset.sum_biUnion ]
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => div_nonneg ( by positivity ) ( norm_nonneg _ )
        intro n hn; simp_all +decide [ Finset.subset_iff ]
        obtain ⟨a, ha⟩ : ∃ a : ℕ, 2 ^ a ≤ ‖zeros n‖ ∧ ‖zeros n‖ < 2 ^ (a + 1) := by
          exact ⟨ ⌊Real.logb 2 ‖zeros n‖⌋₊, by have := Nat.floor_le ( Real.logb_nonneg one_lt_two hn.2.le ) ; rw [ Real.le_logb_iff_rpow_le ] at this <;> norm_cast at * ; linarith, by have := Nat.lt_floor_add_one ( Real.logb 2 ‖zeros n‖ ) ; rw [ Real.logb_lt_iff_lt_rpow ] at this <;> norm_cast at * ; linarith ⟩
        by_cases ha_eq : ‖zeros n‖ = 2 ^ a
        · use a - 1
          rcases a <;> simp_all +decide [ pow_succ' ]
          exact Nat.le_floor <| by rw [ Real.le_logb_iff_rpow_le ] <;> norm_num <;> linarith
        · exact ⟨ a, Nat.le_floor <| by rw [ Real.le_logb_iff_rpow_le ] <;> norm_num <;> cases lt_or_gt_of_ne ha_eq <;> linarith, lt_of_le_of_ne ha.1 <| Ne.symm ha_eq, ha.2.le ⟩
      · intros j hj k hk hjk; simp_all +decide [ Finset.disjoint_left ]
        intro n hn₁ hn₂ hn₃ hn₄; contrapose! hjk
        exact le_antisymm ( Nat.le_of_not_lt fun h => by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( by linarith : j ≥ k + 1 ) ] ) ( Nat.le_of_not_lt fun h => by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( by linarith : k ≥ j + 1 ) ] )
    simpa only [ Finset.mul_sum _ _ _ ] using h_total.trans ( Finset.sum_le_sum h_shell )
  have h_geo_series : ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ (j / 2 : ℝ) ≤ (2 ^ ((J + 1) / 2 : ℝ)) * 3 := by
    have h_geo_series : ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ (j / 2 : ℝ) ≤ (2 ^ ((J + 1) / 2 : ℝ) - 1) / (Real.sqrt 2 - 1) := by
      have h_geo_series : ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ (j / 2 : ℝ) = ∑ j ∈ Finset.range (J + 1), (Real.sqrt 2) ^ j := by
        norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul ]
        exact Finset.sum_congr rfl fun _ _ => by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by norm_num ) ] ; ring
      rw [ h_geo_series, geom_sum_eq ] <;> norm_num [ Real.sqrt_eq_rpow ]
      · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> ring_nf <;> norm_num
        rw [ mul_comm ] ; ring_nf ; norm_num
      · exact ne_of_gt ( Real.one_lt_rpow ( by norm_num ) ( by norm_num ) )
    refine le_trans h_geo_series ?_
    rw [ div_le_iff₀ ] <;> nlinarith only [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, Real.rpow_le_rpow_of_exponent_le ( show ( 1 : ℝ ) ≤ 2 by norm_num ) ( show ( J + 1 : ℝ ) / 2 ≥ 0 by positivity ) ]
  have h_geo_series_bound : ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ (j / 2 : ℝ) ≤ 3 * R₀ ^ (1 / 2 : ℝ) := by
    have h_geo_series_bound : (2 : ℝ) ^ ((J + 1) / 2 : ℝ) ≤ R₀ ^ (1 / 2 : ℝ) := by
      have h_exp_bound : (2 : ℝ) ^ (J + 1) ≤ R₀ := by
        have := Nat.floor_le ( Real.logb_nonneg one_lt_two ( by linarith : 1 ≤ R₀ / 2 ) )
        rw [ Real.le_logb_iff_rpow_le ] at this <;> norm_cast at * <;> norm_num at *
        · rw [ pow_succ' ] ; linarith
        · linarith
      convert Real.rpow_le_rpow ( by positivity ) h_exp_bound ( by positivity : ( 0 : ℝ ) ≤ 1 / 2 ) using 1 ; norm_num [ ← Real.sqrt_eq_rpow ]
      rw [ Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ; ring
    linarith
  refine le_trans h_total ?_
  refine le_trans ( mul_le_mul_of_nonneg_left h_geo_series_bound <| by positivity ) ?_
  rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ] <;> norm_num ; ring_nf ; norm_num [ hC_cnt, hR₀ ]
  rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ] <;> norm_num <;> try linarith
  rw [ ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow ] ; nlinarith [ show 0 < C_cnt * R₀ * Real.sqrt R₀ by positivity, show 0 < C_cnt * R₀ * Real.sqrt 2 by positivity, show 0 < C_cnt * R₀ * Real.sqrt R₀ * Real.sqrt 2 by positivity, Real.sqrt_nonneg 2, Real.sqrt_nonneg R₀, Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ R₀ by positivity ) ]

/-- **Inner reciprocal sum bound from counting function**.
For zeros with `‖ρₙ‖ ≤ R₀/2`, the sum `∑ R₀/‖ρₙ‖` is `O(R₀^{3/2})`. -/
private theorem inner_reciprocal_sum_bound_from_count
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hcount : ∃ C_cnt : ℝ, 0 < C_cnt ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ S : Finset ℕ,
        (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ R) ∧
        (S.card : ℝ) ≤ C_cnt * R ^ (3 / 2 : ℝ)) :
    ∃ C_inner : ℝ, 0 < C_inner ∧ ∀ R₀ : ℝ, 4 ≤ R₀ →
      ∃ S_inner : Finset ℕ,
        (∀ n, n ∈ S_inner ↔ ‖zeros n‖ ≤ R₀ / 2) ∧
        (∑ n ∈ S_inner, R₀ / ‖zeros n‖) ≤ C_inner * R₀ ^ (3 / 2 : ℝ) := by
  obtain ⟨C_cnt, hC_cnt_pos, hC_cnt⟩ := hcount
  obtain ⟨S₁, hS₁⟩ := hC_cnt 1 (by norm_num)
  set K₁ := ∑ n ∈ S₁, (1 : ℝ) / ‖zeros n‖ with hK₁_def
  refine ⟨K₁ + 20 * C_cnt + 1, by positivity, fun R₀ hR₀ => ?_⟩
  obtain ⟨S_inner, hS_inner₁, hS_inner₂⟩ := hC_cnt (R₀ / 2) (by linarith)
  have h_small : ∑ n ∈ S_inner.filter (· ∈ S₁), R₀ / ‖zeros n‖ ≤ K₁ * R₀ ^ (3 / 2 : ℝ) := by
    have := inner_reciprocal_sum_small zeros hne S₁ (by aesop) (R₀ := R₀) (by linarith)
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by aesop)
      fun _ _ _ => div_nonneg (by positivity) (norm_nonneg _)) this
  have h_medium : ∑ n ∈ S_inner.filter (fun n => ¬(n ∈ S₁)), R₀ / ‖zeros n‖ ≤
      20 * C_cnt * R₀ ^ (3 / 2 : ℝ) := by
    convert inner_reciprocal_sum_medium zeros hne C_cnt hC_cnt_pos hC_cnt R₀ hR₀
      S_inner hS_inner₁ S₁ hS₁.1 using 1
  refine ⟨S_inner, hS_inner₁, ?_⟩
  convert add_le_add h_small h_medium |> le_trans <| ?_ using 1
  · rw [Finset.sum_filter_add_sum_filter_not]
  · linarith [show 0 ≤ R₀ ^ (3 / 2 : ℝ) by positivity]

/-! ## Outer tail inverse-square bound from counting function (Aristotle b14d6a6f) -/

/-- For n with ‖zeros n‖ > t where t > 0, we have 1/‖zeros n‖² ≤ 1/t². -/
private lemma inv_sq_le_of_norm_gt (zeros : ℕ → ℂ) (t : ℝ) (ht : 0 < t) (n : ℕ)
    (hn : t < ‖zeros n‖) :
    1 / ‖zeros n‖ ^ 2 ≤ 1 / t ^ 2 := by
  gcongr

/-- Sum over a finset of 1/‖ρ‖² where each ‖ρ‖ > t is bounded by card/t². -/
private lemma sum_inv_sq_le_card_div_sq (zeros : ℕ → ℂ) (t : ℝ) (ht : 0 < t)
    (S : Finset ℕ) (hS : ∀ n ∈ S, t < ‖zeros n‖) :
    ∑ n ∈ S, 1 / ‖zeros n‖ ^ 2 ≤ S.card / t ^ 2 := by
  simpa using Finset.sum_le_sum fun x hx ↦ inv_anti₀ (by positivity)
    (pow_le_pow_left₀ (by positivity) (hS x hx |> le_of_lt) 2)

/-- R₀² · ∑_{outer} 1/‖ρ‖² is O(R₀^{3/2}) for outer zeros (‖ρ‖ > 4R₀). -/
private theorem outer_tail_inv_sq_bound_from_count
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (C_cnt : ℝ) (hC_cnt : 0 < C_cnt)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∃ S : Finset ℕ,
      (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ R) ∧ (S.card : ℝ) ≤ C_cnt * R ^ (3 / 2 : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R0 : ℝ), 1 ≤ R0 →
      ∀ (S_outer : Finset ℕ),
        (∀ n ∈ S_outer, 4 * R0 < ‖zeros n‖) →
        R0 ^ 2 * ∑ n ∈ S_outer, 1 / ‖zeros n‖ ^ 2 ≤ K * R0 ^ (3 / 2 : ℝ) := by
  -- Dyadic shell decomposition (Aristotle fcd5e778, verified v4.27-compatible)
  use C_cnt * (2 / (Real.sqrt 2 - 1)) + 1;
  refine' ⟨ by exact add_pos_of_nonneg_of_pos ( mul_nonneg hC_cnt.le ( div_nonneg zero_le_two ( sub_nonneg.2 ( Real.le_sqrt_of_sq_le ( by norm_num ) ) ) ) ) zero_lt_one, _ ⟩;
  intros R0 hR0 S_outer hS_outer
  have h_sum : ∑ n ∈ S_outer, 1 / ‖zeros n‖ ^ 2 ≤ C_cnt * (2 / (Real.sqrt 2 - 1)) * (1 / R0) ^ (1 / 2 : ℝ) := by
    have h_shell : ∀ n ∈ S_outer, ∃ k : ℕ, 2 ^ k * 4 * R0 < ‖zeros n‖ ∧ ‖zeros n‖ ≤ 2 ^ (k + 1) * 4 * R0 := by
      intro n hn;
      obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 ^ k * 4 * R0 < ‖zeros n‖ ∧ ‖zeros n‖ ≤ 2 ^ (k + 1) * 4 * R0 := by
        have h_exp : ∃ k : ℕ, 2 ^ k * 4 * R0 < ‖zeros n‖ := by
          exact ⟨ 0, by simpa using hS_outer n hn ⟩
        contrapose! h_exp;
        have h_ind : ∀ k : ℕ, 2 ^ k * 4 * R0 < ‖zeros n‖ := by
          exact fun k => Nat.recOn k ( by simpa using hS_outer n hn ) h_exp;
        have h_contradiction : Filter.Tendsto (fun k : ℕ => 2 ^ k * 4 * R0) Filter.atTop Filter.atTop := by
          exact Filter.Tendsto.atTop_mul_const ( by positivity ) ( Filter.Tendsto.atTop_mul_const ( by positivity ) ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) );
        exact absurd ( h_contradiction.eventually_gt_atTop ‖zeros n‖ ) fun h => by obtain ⟨ k, hk ⟩ := h.exists; linarith [ h_ind k ] ;
      use k;
    obtain ⟨k, hk⟩ : ∃ k : ℕ → ℕ, ∀ n ∈ S_outer, 2 ^ k n * 4 * R0 < ‖zeros n‖ ∧ ‖zeros n‖ ≤ 2 ^ (k n + 1) * 4 * R0 := by
      choose! k hk using h_shell; exact ⟨ k, hk ⟩ ;
    have h_shell_contribution : ∀ k_val : ℕ, ∑ n ∈ S_outer.filter (fun n => k n = k_val), 1 / ‖zeros n‖ ^ 2 ≤ C_cnt * (2 ^ (k_val + 1) * 4 * R0) ^ (3 / 2 : ℝ) / (2 ^ k_val * 4 * R0) ^ 2 := by
      intros k_val
      have h_shell_card : (S_outer.filter (fun n => k n = k_val)).card ≤ C_cnt * (2 ^ (k_val + 1) * 4 * R0) ^ (3 / 2 : ℝ) := by
        obtain ⟨ S, hS₁, hS₂ ⟩ := hcount ( 2 ^ ( k_val + 1 ) * 4 * R0 ) ( by nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show k_val + 1 ≥ 1 by linarith ) ] );
        refine le_trans ?_ hS₂;
        exact_mod_cast Finset.card_le_card fun x hx => by aesop;
      have h_shell_contribution : ∀ n ∈ S_outer.filter (fun n => k n = k_val), 1 / ‖zeros n‖ ^ 2 ≤ 1 / (2 ^ k_val * 4 * R0) ^ 2 := by
        exact fun n hn => one_div_le_one_div_of_le ( by positivity ) ( by have := hk n ( Finset.filter_subset _ _ hn ) ; rw [ Finset.mem_filter ] at hn; rw [ hn.2 ] at this; exact pow_le_pow_left₀ ( by positivity ) this.1.le 2 );
      refine' le_trans ( Finset.sum_le_sum h_shell_contribution ) _;
      norm_num at *;
      exact mul_le_mul_of_nonneg_right h_shell_card ( by positivity );
    have h_total_contribution : ∑ n ∈ S_outer, 1 / ‖zeros n‖ ^ 2 ≤ ∑' k_val : ℕ, C_cnt * (2 ^ (k_val + 1) * 4 * R0) ^ (3 / 2 : ℝ) / (2 ^ k_val * 4 * R0) ^ 2 := by
      have h_total_contribution : ∑ n ∈ S_outer, 1 / ‖zeros n‖ ^ 2 ≤ ∑ k_val ∈ Finset.image k S_outer, C_cnt * (2 ^ (k_val + 1) * 4 * R0) ^ (3 / 2 : ℝ) / (2 ^ k_val * 4 * R0) ^ 2 := by
        convert Finset.sum_le_sum fun x hx => h_shell_contribution x using 1;
        rw [ Finset.sum_image' ] ; aesop;
      refine le_trans h_total_contribution <| Summable.sum_le_tsum _ ?_ ?_;
      · exact fun _ _ => by positivity;
      · suffices h_simp : Summable (fun k_val : ℕ => C_cnt * (2 ^ (3 / 2 : ℝ)) * (4 * R0) ^ (3 / 2 : ℝ) / (16 * R0 ^ 2) * (1 / 2 ^ (k_val / 2 : ℝ))) by
          convert h_simp using 2 ; ring;
          rw [ show ( R0 * 2 ^ _ * 8 : ℝ ) = ( R0 * 4 ) * ( 2 ^ _ * 2 ) by ring, Real.mul_rpow ( by positivity ) ( by positivity ) ] ; norm_num [ Real.rpow_mul ] ; ring;
          rw [ show ( 2 ^ _ * 2 : ℝ ) ^ ( 3 / 2 : ℝ ) = ( 2 ^ _ ) ^ ( 3 / 2 : ℝ ) * 2 ^ ( 3 / 2 : ℝ ) by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ] ; norm_num [ Real.rpow_mul ] ; ring;
          rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ( by positivity ), Real.rpow_one ] ; ring;
          rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ( by positivity ), Real.rpow_one ] ; norm_num [ pow_mul', ← Real.sqrt_eq_rpow ] ; ring;
          field_simp
          ring;
          rw [ Real.sq_sqrt ( by positivity ) ] ; norm_num [ ← mul_pow ];
        refine Summable.mul_left _ ?_;
        have h_geo_series : Summable (fun k_val : ℕ => (1 / Real.sqrt 2) ^ k_val) := by
          exact summable_geometric_of_lt_one ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> norm_num [ Real.lt_sqrt ] );
        convert h_geo_series using 2 ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos ];
        rw [ ← Real.exp_nat_mul ] ; ring;
    have h_total_contribution_simplified : ∑' k_val : ℕ, C_cnt * (2 ^ (k_val + 1) * 4 * R0) ^ (3 / 2 : ℝ) / (2 ^ k_val * 4 * R0) ^ 2 = C_cnt * (2 / (Real.sqrt 2 - 1)) * (1 / R0) ^ (1 / 2 : ℝ) := by
      have h_simplify : ∑' k_val : ℕ, C_cnt * (2 ^ (k_val + 1) * 4 * R0) ^ (3 / 2 : ℝ) / (2 ^ k_val * 4 * R0) ^ 2 = C_cnt * (2 ^ (3 / 2 : ℝ) * 4 ^ (3 / 2 : ℝ) * R0 ^ (3 / 2 : ℝ)) / (4 ^ 2 * R0 ^ 2) * ∑' k_val : ℕ, (2 ^ (3 / 2 : ℝ) / 2 ^ 2) ^ k_val := by
        rw [ ← tsum_mul_left ] ; congr ; ext k_val ; ring;
        rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring;
        norm_num [ sq, mul_assoc, mul_left_comm, ← Real.rpow_natCast, ← Real.rpow_mul ] ; ring;
        norm_num [ Real.div_rpow, Real.rpow_mul ] ; ring ; norm_num;
        norm_num [ pow_mul', ← mul_pow ] ; ring ; norm_num;
        rw [ show ( 8 : ℝ ) = 2 ^ 3 by norm_num, ← Real.rpow_natCast _ 3, ← Real.rpow_mul ] <;> norm_num ; ring ; norm_num;
        rw [ show ( 9 / 2 : ℝ ) = 3 / 2 + 3 by norm_num, Real.rpow_add ] <;> norm_num ; ring ; norm_num;
      rw [ h_simplify, tsum_geometric_of_lt_one ] <;> norm_num;
      · rw [ show ( 2 : ℝ ) ^ ( 3 / 2 : ℝ ) = 2 * Real.sqrt 2 by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; ring ; norm_num [ ← Real.sqrt_eq_rpow ] ; ring;
        rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ( by positivity ), Real.rpow_one ] ; norm_num [ ← Real.sqrt_eq_rpow ] ; ring;
        grind;
      · positivity;
      · rw [ show ( 2 : ℝ ) ^ ( 3 / 2 : ℝ ) = 2 * Real.sqrt 2 by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
    exact h_total_contribution.trans_eq h_total_contribution_simplified;
  refine le_trans ( mul_le_mul_of_nonneg_left h_sum <| sq_nonneg _ ) ?_;
  rw [ show ( 3 / 2 : ℝ ) = 2 - 1 / 2 by norm_num, Real.rpow_sub ] <;> norm_num <;> try positivity;
  norm_num [ ← Real.sqrt_eq_rpow ];
  ring_nf; norm_num [ show R0 ≠ 0 by linarith, show Real.sqrt R0 ≠ 0 by positivity ] ;
  positivity

/-- On a good circle `‖z‖ = R` (with R in [R₀, 2R₀] and gap δ to all zeros in S),
each Weierstrass factor E₁(z/ρₙ) is nonzero.

Proof: E₁(w) = (1-w)·exp(w) = 0 iff w = 1 (since exp never vanishes).
So E₁(z/ρₙ) = 0 iff z = ρₙ. But:
- n ∈ S ⟹ |R - ‖ρₙ‖| ≥ δ > 0, contradicting ‖z‖ = ‖ρₙ‖ = R.
- n ∉ S ⟹ ‖ρₙ‖ > 4R₀ ≥ 2R₀ ≥ R = ‖z‖, contradicting z = ρₙ. -/
private theorem E1_ne_zero_on_good_circle
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (z : ℂ) (R R₀ : ℝ) (hR₀ : 1 ≤ R₀)
    (hR_lo : R₀ ≤ R) (hR_hi : R ≤ 2 * R₀) (hz : ‖z‖ = R)
    (S : Finset ℕ) (hS_mem : ∀ n, n ∈ S ↔ ‖zeros n‖ ≤ 4 * R₀)
    (hgap : ∀ n ∈ S, |R - ‖zeros n‖| ≥ R₀ / (2 * ↑S.card + 2))
    (n : ℕ) :
    Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) ≠ 0 := by
  intro h_eq
  -- E1(w) = (1-w)*exp(w) = 0, exp nonzero, so w = 1
  simp only [Aristotle.Standalone.HadamardProductConvergence.E1, mul_eq_zero,
    Complex.exp_ne_zero, or_false, sub_eq_zero] at h_eq
  -- h_eq : 1 = z / zeros n, hence z = zeros n
  rw [eq_comm, div_eq_one_iff_eq (hne n)] at h_eq
  -- h_eq : z = zeros n
  by_cases hn : n ∈ S
  · -- n ∈ S: gap says |R - ‖zeros n‖| ≥ δ > 0, but z = zeros n gives ‖z‖ = ‖zeros n‖
    have hgap_n := hgap n hn
    rw [h_eq] at hz
    -- hz : ‖zeros n‖ = R, so |R - R| = 0 ≥ δ
    rw [hz, sub_self, abs_zero] at hgap_n
    have hδ_pos : (0 : ℝ) < R₀ / (2 * ↑S.card + 2) := by positivity
    linarith
  · -- n ∉ S: hS_mem says ‖zeros n‖ > 4R₀, but ‖z‖ = R ≤ 2R₀
    have h_not := (hS_mem n).not.mp hn
    push_neg at h_not
    rw [h_eq] at hz
    -- hz : ‖zeros n‖ = R ≤ 2R₀, h_not : 4R₀ < ‖zeros n‖
    linarith

/-- The full product `∏' n, E₁(z/ρₙ)` is nonzero on the good circle.
Uses `tprod_one_add_ne_zero_of_summable` (the pattern from `weierstrass_tail_ne_zero`). -/
private theorem tprod_E1_ne_zero_on_good_circle
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (z : ℂ) (R R₀ : ℝ) (hR₀ : 1 ≤ R₀)
    (hR_lo : R₀ ≤ R) (hR_hi : R ≤ 2 * R₀) (hz : ‖z‖ = R)
    (S : Finset ℕ) (hS_mem : ∀ n, n ∈ S ↔ ‖zeros n‖ ≤ 4 * R₀)
    (hgap : ∀ n ∈ S, |R - ‖zeros n‖| ≥ R₀ / (2 * ↑S.card + 2)) :
    (∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)) ≠ 0 := by
  -- Rewrite each factor as 1 + (E1(z/ρ) - 1)
  rw [show (fun n => Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)) =
      (fun n => 1 + (Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) - 1))
    from by ext; ring]
  apply tprod_one_add_ne_zero_of_summable
  · -- Each E1(z/ρ_n) - 1 ≠ -1 (i.e., E1 ≠ 0)
    intro n
    intro h_eq
    have h0 : Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) = 0 := by
      have := h_eq; ring_nf at this ⊢; exact this
    exact E1_ne_zero_on_good_circle zeros hne z R R₀ hR₀ hR_lo hR_hi hz S hS_mem hgap n h0
  · -- Summability of ‖E1(z/ρ_n) - 1‖
    exact E1_minus_one_norm_summable zeros hne hsum z

/-- Finite product lower bound: the product over S has norm at least exp(-C·R₀^(7/4)).
Uses near_factor_lower_bound for controlled zeros and inner_reciprocal_sum for inner zeros. -/
private theorem finite_product_lower_bound_on_good_circle
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (z : ℂ) (R R₀ C_cnt : ℝ) (hR₀ : 1 ≤ R₀) (hC_cnt : 0 < C_cnt)
    (hR_lo : R₀ ≤ R) (hR_hi : R ≤ 2 * R₀) (hz : ‖z‖ = R)
    (S : Finset ℕ) (hS_mem : ∀ n, n ∈ S ↔ ‖zeros n‖ ≤ 4 * R₀)
    (hS_card : (S.card : ℝ) ≤ C_cnt * (4 * R₀) ^ (3 / 2 : ℝ))
    (hgap : ∀ n ∈ S, |R - ‖zeros n‖| ≥ R₀ / (2 * ↑S.card + 2))
    (C_inner : ℝ) (hC_inner : 0 < C_inner)
    (hinner_bound : ∀ (R₁ : ℝ), 4 ≤ R₁ →
      ∃ S_inner : Finset ℕ,
        (∀ n, n ∈ S_inner ↔ ‖zeros n‖ ≤ R₁ / 2) ∧
        ∑ n ∈ S_inner, R₁ / ‖zeros n‖ ≤ C_inner * R₁ ^ (3 / 2 : ℝ)) :
    Real.exp (-(100 * (C_cnt + C_inner + 1) ^ 2) * R₀ ^ (7 / 4 : ℝ)) ≤
        ‖∏ n ∈ S, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)‖ := by
  have hR_pos : (0 : ℝ) < R := by linarith
  set C := 100 * (C_cnt + C_inner + 1) ^ 2
  -- Each factor nonzero (from gap condition)
  have hfactors_ne : ∀ n ∈ S,
      Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) ≠ 0 := by
    intro n hn h_eq
    simp only [Aristotle.Standalone.HadamardProductConvergence.E1, mul_eq_zero,
      Complex.exp_ne_zero, or_false, sub_eq_zero] at h_eq
    rw [eq_comm, div_eq_one_iff_eq (hne n)] at h_eq
    have := hgap n hn; rw [← h_eq] at this; rw [hz, sub_self, abs_zero] at this
    linarith [show (0 : ℝ) < R₀ / (2 * ↑S.card + 2) from by positivity]
  -- Each factor: ‖E1(z/ρ)‖ ≥ (δ/(6R₀))·exp(-R/‖ρ‖) where δ=R₀/(2|S|+2)
  -- Product: ∏_S ‖E1‖ ≥ (δ/(6R₀))^|S| · exp(-∑_S R/‖ρ‖)
  -- We bound (δ/(6R₀))^|S| and exp(-∑R/‖ρ‖) separately.
  set δ := R₀ / (2 * ↑S.card + 2) with hδ_def
  have hδ_pos : (0 : ℝ) < δ := by positivity
  -- Per-factor lower bound (for ALL n ∈ S, not just controlled ones)
  have h_per_factor : ∀ n ∈ S,
      δ / (6 * R₀) * Real.exp (-(R / ‖zeros n‖)) ≤
        ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)‖ := by
    intro n hn
    -- E1(w) = (1-w)·exp(w), ‖E1‖ = ‖1-w‖·‖exp(w)‖
    unfold Aristotle.Standalone.HadamardProductConvergence.E1
    rw [norm_mul]
    -- ‖1-z/ρ‖ ≥ δ/(R+‖ρ‖) ≥ δ/(6R₀)
    have hρ_ne := hne n
    have hρ_pos : (0 : ℝ) < ‖zeros n‖ := norm_pos_iff.mpr hρ_ne
    have h_wf := MinimumModulusPigeonhole.weierstrass_factor_lower_bound
      z (zeros n) hρ_ne R δ hR_pos hδ_pos hz (hgap n hn)
    have hRρ : R + ‖zeros n‖ ≤ 6 * R₀ := by
      have := (hS_mem n).mp hn; linarith
    have h_sub : δ / (6 * R₀) ≤ ‖1 - z / zeros n‖ := by
      calc δ / (6 * R₀) ≤ δ / (R + ‖zeros n‖) :=
            div_le_div_of_nonneg_left hδ_pos.le (by linarith) hRρ
        _ ≤ ‖1 - z / zeros n‖ := h_wf
    -- ‖exp(z/ρ)‖ = exp(Re(z/ρ)) ≥ exp(-‖z/ρ‖) ≥ exp(-R/‖ρ‖)
    have h_exp : Real.exp (-(R / ‖zeros n‖)) ≤ ‖Complex.exp (z / zeros n)‖ := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp_of_le
      have h1 : -(z / zeros n).re ≤ ‖z / zeros n‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      have h2 : ‖z / zeros n‖ = R / ‖zeros n‖ := by rw [norm_div, hz]
      linarith
    exact mul_le_mul h_sub h_exp (Real.exp_nonneg _) (by positivity)
  -- Product lower bound: ∏_S ‖E1‖ ≥ (δ/(6R₀))^|S| · exp(-∑R/‖ρ‖)
  have h_prod_lb : (δ / (6 * R₀)) ^ S.card * Real.exp (-∑ n ∈ S, R / ‖zeros n‖) ≤
      ∏ n ∈ S, ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)‖ := by
    -- Split each factor into (δ/(6R₀)) · exp(-R/‖ρ‖) ≤ ‖E1‖
    -- Product of lower bounds ≤ product of ‖E1‖
    calc (δ / (6 * R₀)) ^ S.card * Real.exp (-∑ n ∈ S, R / ‖zeros n‖)
        = ∏ n ∈ S, (δ / (6 * R₀) * Real.exp (-(R / ‖zeros n‖))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum,
              Finset.sum_neg_distrib]
      _ ≤ ∏ n ∈ S, ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)‖ :=
          Finset.prod_le_prod (fun n hn => mul_nonneg (by positivity) (Real.exp_nonneg _))
            h_per_factor
  -- Suffices: exp(-C·R₀^(7/4)) ≤ (δ/(6R₀))^|S| · exp(-∑R/‖ρ‖)
  -- Then chain with h_prod_lb.
  suffices h_arith : Real.exp (-(100 * (C_cnt + C_inner + 1) ^ 2) * R₀ ^ (7 / 4 : ℝ)) ≤
      (δ / (6 * R₀)) ^ S.card * Real.exp (-∑ n ∈ S, R / ‖zeros n‖) from by
    rw [norm_prod]
    exact h_arith.trans h_prod_lb
  -- Proved in ArithBound.lean: uses constant_absorbs_log, card_log_bound, reciprocal_sum_bound.
  exact _root_.finite_product_arith_bound zeros hne R R₀ C_cnt hR₀ hC_cnt hR_lo hR_hi S hS_mem hS_card C_inner hC_inner hinner_bound

/-- Tail product lower bound: for the complement of S (zeros with ‖ρ‖ > 4R₀),
the product norm is at least exp(-C · R₀²). We use the full tsum of ‖E1-1‖
which gives O(R₀²). The counting-function bound would tighten this to O(R₀^{3/2})
but the O(R₀²) bound suffices when absorbed into the choice of C₂.

Actually, we need O(R₀^{7/4}) so the O(R₀²) bound does NOT suffice.
We use the counting-function bound via outer_tail_inv_sq_bound_from_count. -/
private theorem tail_product_lower_bound_on_good_circle
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (z : ℂ) (R R₀ : ℝ) (hR₀ : 1 ≤ R₀)
    (hR_lo : R₀ ≤ R) (hR_hi : R ≤ 2 * R₀) (hz : ‖z‖ = R)
    (S : Finset ℕ) (hS_mem : ∀ n, n ∈ S ↔ ‖zeros n‖ ≤ 4 * R₀)
    (K_outer : ℝ) (hK_outer : 0 < K_outer)
    (houter_bound : ∀ (R0 : ℝ), 1 ≤ R0 →
      ∀ (S_outer : Finset ℕ),
        (∀ n ∈ S_outer, 4 * R0 < ‖zeros n‖) →
        R0 ^ 2 * ∑ n ∈ S_outer, 1 / ‖zeros n‖ ^ 2 ≤ K_outer * R0 ^ (3 / 2 : ℝ)) :
    Real.exp (-(48 * K_outer) * R₀ ^ (3 / 2 : ℝ)) ≤
      ‖∏' (n : ↑(↑S : Set ℕ)ᶜ),
        Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n)‖ := by
  -- For n ∉ S: ‖zeros n‖ > 4R₀, so ‖z/zeros n‖ ≤ R/(4R₀) ≤ 1/2
  -- Each ‖E1(z/ρ)-1‖ ≤ 3·(1/2)² = 3/4
  -- Step 1: Bound ∑'_{Sᶜ} 1/‖ρ‖² using the counting function.
  -- For any finite U ⊂ Sᶜ: ∑_U 1/‖ρ‖² ≤ K_outer · R₀^(3/2) / R₀²
  -- Since all elements have ‖ρ‖ > 4R₀.
  have hR₀_pos : (0 : ℝ) < R₀ := by linarith
  have hsub_summable : Summable (fun (n : ↑(↑S : Set ℕ)ᶜ) => 1 / ‖zeros ↑n‖ ^ 2) :=
    hsum.subtype _
  -- The tsum bound: use that all finite partial sums are bounded
  have htsum_bound : R₀ ^ 2 * ∑' (n : ↑(↑S : Set ℕ)ᶜ), 1 / ‖zeros ↑n‖ ^ 2 ≤
      K_outer * R₀ ^ (3 / 2 : ℝ) := by
    -- Equivalently, bound ∑' f ≤ B / R₀².
    -- For all finite partial sums: R₀² * ∑_U f ≤ K * R₀^(3/2) (from outer bound).
    -- So R₀² * ∑' f ≤ K * R₀^(3/2) by le_of_tendsto'.
    have hR₀_sq_pos : (0 : ℝ) < R₀ ^ 2 := by positivity
    -- Bound R₀² * ∑' by bounding R₀² * each finite partial sum
    have hR₀_sq_pos : (0 : ℝ) < R₀ ^ 2 := by positivity
    suffices h : ∑' (n : ↑(↑S : Set ℕ)ᶜ), 1 / ‖zeros ↑n‖ ^ 2 ≤
        K_outer * R₀ ^ (3 / 2 : ℝ) / R₀ ^ 2 by
      calc R₀ ^ 2 * ∑' (n : ↑(↑S : Set ℕ)ᶜ), 1 / ‖zeros ↑n‖ ^ 2
          ≤ R₀ ^ 2 * (K_outer * R₀ ^ (3 / 2 : ℝ) / R₀ ^ 2) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = K_outer * R₀ ^ (3 / 2 : ℝ) := by
            field_simp
    apply le_of_tendsto' hsub_summable.hasSum
    intro U
    set T := U.map ⟨Subtype.val, Subtype.coe_injective⟩
    have hT_outer : ∀ n ∈ T, 4 * R₀ < ‖zeros n‖ := by
      intro n hn
      obtain ⟨⟨m, hm⟩, _, rfl⟩ := Finset.mem_map.mp hn
      exact not_le.mp ((hS_mem m).not.mp hm)
    have hsum_eq : ∑ n ∈ U, 1 / ‖zeros ↑n‖ ^ 2 = ∑ n ∈ T, 1 / ‖zeros n‖ ^ 2 := by
      rw [Finset.sum_map]; rfl
    rw [hsum_eq]
    have hfin := houter_bound R₀ hR₀ T hT_outer
    -- ∑_T ≤ K*R₀^(3/2)/R₀² follows from R₀²*∑_T ≤ K*R₀^(3/2) by dividing
    rw [le_div_iff₀ hR₀_sq_pos]
    linarith [Finset.sum_nonneg (fun n (_ : n ∈ T) => div_nonneg one_pos.le (sq_nonneg ‖zeros n‖))]
  -- Step 2: Convert tsum bound to product lower bound.
  -- Write E1(z/ρ) = 1 + g where g = E1-1.
  set g : ↑(↑S : Set ℕ)ᶜ → ℂ := fun n =>
    Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n) - 1
  have hg_summable : Summable (fun n => ‖g n‖) :=
    (E1_minus_one_norm_summable zeros hne hsum z).subtype _
  -- The product ∏'_{Sᶜ} E1 = ∏'_{Sᶜ} (1 + g)
  have hprod_eq : (fun (n : ↑(↑S : Set ℕ)ᶜ) =>
      Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n)) =
      (fun n => 1 + g n) := by ext n; simp only [g]; ring
  rw [hprod_eq]
  -- Multipliable (1+g) from summable ‖g‖
  have hm := multipliable_one_add_of_summable hg_summable
  -- ‖∏'(1+g)‖ = ∏' ‖1+g‖
  rw [Multipliable.norm_tprod hm]
  -- ∏' ‖1+g‖ = exp(∑' log ‖1+g‖)
  -- Each ‖1+g_n‖ > 0 (from E1 ≠ 0)
  have hpos : ∀ (n : ↑(↑S : Set ℕ)ᶜ), (0 : ℝ) < ‖1 + g n‖ := by
    intro ⟨n, hn⟩
    rw [norm_pos_iff]
    intro h
    -- 1 + g = 0 means E1(z/ρ) = 0, but E1(w)=0 iff w=1, and for n ∉ S:
    -- ‖ρ‖ > 4R₀ > 2R₀ ≥ R = ‖z‖, so z ≠ ρ, so z/ρ ≠ 1
    have hE1_eq : Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) = 0 := by
      have : (1 : ℂ) + g ⟨n, hn⟩ = 0 := h
      simp only [g, add_sub_cancel] at this; exact this
    simp only [Aristotle.Standalone.HadamardProductConvergence.E1, mul_eq_zero,
      Complex.exp_ne_zero, or_false, sub_eq_zero] at hE1_eq
    rw [eq_comm, div_eq_one_iff_eq (hne n)] at hE1_eq
    -- hE1_eq : z = zeros n, but ‖zeros n‖ > 4R₀ while ‖z‖ = R ≤ 2R₀
    have h_norm : ‖zeros n‖ > 4 * R₀ := not_le.mp ((hS_mem n).not.mp hn)
    linarith [hE1_eq ▸ hz]
  have hlog_summable := hg_summable.summable_log_norm_one_add
  rw [← Real.rexp_tsum_eq_tprod hpos hlog_summable]
  -- Need: exp(-48K*R₀^(3/2)) ≤ exp(∑' log ‖1+g‖)
  apply Real.exp_le_exp_of_le
  -- Need: -48K*R₀^(3/2) ≤ ∑' log ‖1+g‖
  -- Step 2a: Pointwise log bound (deferred as sorry, purely real-analysis)
  have hlog_pointwise : ∀ (n : ↑(↑S : Set ℕ)ᶜ),
      -4 * ‖g n‖ ≤ Real.log ‖1 + g n‖ := by
    intro ⟨n, hn⟩
    -- n ∉ S means ‖zeros n‖ > 4R₀
    have h_norm_gt : 4 * R₀ < ‖zeros n‖ := not_le.mp ((hS_mem n).not.mp hn)
    have hρ_pos : (0 : ℝ) < ‖zeros n‖ := by linarith
    -- ‖z/zeros n‖ ≤ R/(4R₀) ≤ 2R₀/(4R₀) = 1/2
    have h_ratio : ‖z / zeros n‖ ≤ 1 / 2 := by
      rw [norm_div, hz, div_le_div_iff₀ hρ_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    -- ‖g n‖ ≤ 3·(1/2)² = 3/4
    have h_gnorm : ‖g ⟨n, hn⟩‖ ≤ 3 / 4 := by
      show ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) - 1‖ ≤ 3 / 4
      calc ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) - 1‖
          ≤ 3 * ‖z / zeros n‖ ^ 2 :=
            Aristotle.Standalone.HadamardProductConvergence.E1_sub_one_norm_le
              (h_ratio.trans (by norm_num))
        _ ≤ 3 * (1 / 2) ^ 2 := by gcongr
        _ = 3 / 4 := by norm_num
    -- Set t = ‖g⟩‖ for readability
    set t := ‖g ⟨n, hn⟩‖ with ht_def
    have ht_nn : 0 ≤ t := norm_nonneg _
    have ht_le : t ≤ 3 / 4 := h_gnorm
    -- ‖1+g‖ ≥ 1-t by reverse triangle inequality: ‖a‖ - ‖b‖ ≤ ‖a + b‖
    have h_norm_ge : 1 - t ≤ ‖1 + g ⟨n, hn⟩‖ := by
      have : ‖(1 : ℂ)‖ - ‖-g ⟨n, hn⟩‖ ≤ ‖(1 : ℂ) - (-g ⟨n, hn⟩)‖ :=
        norm_sub_norm_le 1 (-g ⟨n, hn⟩)
      simp only [norm_one, norm_neg, sub_neg_eq_add, ht_def] at this
      exact this
    have h_omt_pos : (0 : ℝ) < 1 - t := by linarith
    -- Key: exp(-4t) ≤ 1-t for 0 ≤ t ≤ 3/4
    -- From 1+4t ≤ exp(4t) (add_one_le_exp) and (1-t)(1+4t) ≥ 1 when t ≤ 3/4
    have h_exp_le : Real.exp (-4 * t) ≤ 1 - t := by
      -- From add_one_le_exp: 1+4t ≤ exp(4t), so exp(-4t) ≤ 1/(1+4t).
      -- From t ≤ 3/4: (1-t)(1+4t) = 1+3t-4t² ≥ 1, so 1/(1+4t) ≤ 1-t.
      -- Combined: exp(-4t) ≤ 1-t.
      have h4t_eq : -(4 * t) = -4 * t := by ring
      have hA : 1 + 4 * t ≤ Real.exp (4 * t) := by linarith [Real.add_one_le_exp (4 * t)]
      have h_exp4t_pos : (0 : ℝ) < Real.exp (4 * t) := Real.exp_pos _
      have h14t_pos : (0 : ℝ) < 1 + 4 * t := by linarith
      -- exp(-4t) · (1+4t) ≤ 1 (from 1+4t ≤ exp(4t) and exp(-4t)·exp(4t) = 1)
      have hB : Real.exp (-4 * t) * (1 + 4 * t) ≤ 1 := by
        rw [← h4t_eq]
        have : Real.exp (-(4 * t)) * (1 + 4 * t) ≤ Real.exp (-(4 * t)) * Real.exp (4 * t) :=
          mul_le_mul_of_nonneg_left hA (Real.exp_nonneg _)
        rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
      -- (1-t)·(1+4t) ≥ 1 (from t ≤ 3/4)
      have hC : 1 ≤ (1 - t) * (1 + 4 * t) := by nlinarith
      -- exp(-4t) ≤ 1-t from: exp(-4t)·(1+4t) ≤ 1 ≤ (1-t)·(1+4t)
      -- From hB and hC: exp(-4t)·(1+4t) ≤ 1 ≤ (1-t)·(1+4t)
      -- Divide by (1+4t) > 0: exp(-4t) ≤ 1-t
      -- a·c ≤ 1 ≤ b·c with c > 0 gives a ≤ b
      have := hB.trans hC  -- exp(-4t)·(1+4t) ≤ (1-t)·(1+4t)
      exact le_of_mul_le_mul_of_pos_right this h14t_pos
    -- Now: -4t ≤ log(1-t) ≤ log ‖1+g‖
    calc -4 * t
        = Real.log (Real.exp (-4 * t)) := (Real.log_exp _).symm
      _ ≤ Real.log (1 - t) := by
          exact Real.log_le_log (Real.exp_pos _) h_exp_le
      _ ≤ Real.log ‖1 + g ⟨n, hn⟩‖ := by
          exact Real.log_le_log h_omt_pos h_norm_ge
  -- Step 2b: tsum lower bound via ge_of_tendsto'
  -- For each finite partial sum: ∑_U log ‖1+g‖ ≥ ∑_U (-4‖g‖) ≥ -4*∑'‖g‖
  -- So ∑' log ‖1+g‖ ≥ -4*∑'‖g‖
  have h_tsum_ge : -4 * ∑' n, ‖g n‖ ≤ ∑' n, Real.log ‖1 + g n‖ := by
    apply ge_of_tendsto' hlog_summable.hasSum
    intro U
    -- -4 * ∑' ‖g‖ ≤ ∑_U (-4‖g‖) ≤ ∑_U log ‖1+g‖
    have h1 : ∑ n ∈ U, (-4 * ‖g n‖) ≤ ∑ n ∈ U, Real.log ‖1 + g n‖ :=
      Finset.sum_le_sum fun n _ => hlog_pointwise n
    have h2 : -4 * ∑' n, ‖g n‖ ≤ ∑ n ∈ U, (-4 * ‖g n‖) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonpos_left
        (hg_summable.sum_le_tsum U (fun n _ => norm_nonneg _)) (by norm_num)
    linarith
  -- Step 2d: ∑'‖g‖ ≤ 12K*R₀^(3/2)
  -- Each ‖g n‖ ≤ 3*(R/‖ρ‖)², and R ≤ 2R₀, so ‖g n‖ ≤ 12R₀²/‖ρ‖²
  -- ∑'‖g‖ ≤ 12R₀² * ∑' 1/‖ρ‖² ≤ 12K*R₀^(3/2) (from htsum_bound)
  have h_gnorm_bound : ∑' n, ‖g n‖ ≤ 12 * K_outer * R₀ ^ (3 / 2 : ℝ) := by
    -- ‖g n‖ = ‖E1(z/ρ)-1‖. For n ∉ S: ‖z/ρ‖ ≤ 1/2 ≤ 1, so E1_sub_one_norm_le gives
    -- ‖g n‖ ≤ 3‖z/ρ‖² = 3R²/‖ρ‖² ≤ 12R₀²/‖ρ‖²
    -- Thus ∑'‖g‖ ≤ 12R₀² · ∑' 1/‖ρ‖² ≤ 12 * K * R₀^(3/2) from htsum_bound
    -- Direct proof via le_of_tendsto': bound each finite partial sum by 12K·R₀^(3/2)
    apply le_of_tendsto' hg_summable.hasSum
    intro U
    -- For each n ∈ U (subtype of Sᶜ): ‖g n‖ ≤ 3R²/‖ρ‖²
    have h_pw : ∀ (m : ↑(↑S : Set ℕ)ᶜ), m ∈ U →
        ‖g m‖ ≤ 3 * R ^ 2 * (1 / ‖zeros ↑m‖ ^ 2) := by
      intro ⟨m, hm⟩ _
      have h_ngt : 4 * R₀ < ‖zeros m‖ := not_le.mp ((hS_mem m).not.mp hm)
      have hρ_pos : (0 : ℝ) < ‖zeros m‖ := by linarith
      have h_ratio_le : ‖z / zeros m‖ ≤ 1 := by
        rw [norm_div, hz, div_le_one hρ_pos]; linarith
      show ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros m) - 1‖ ≤
          3 * R ^ 2 * (1 / ‖zeros m‖ ^ 2)
      calc ‖Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros m) - 1‖
          ≤ 3 * ‖z / zeros m‖ ^ 2 :=
            Aristotle.Standalone.HadamardProductConvergence.E1_sub_one_norm_le h_ratio_le
        _ = 3 * (R / ‖zeros m‖) ^ 2 := by rw [norm_div, hz]
        _ = 3 * R ^ 2 * (1 / ‖zeros m‖ ^ 2) := by ring
    -- Sum bound: ∑_U ‖g‖ ≤ 3R² · ∑_U 1/‖ρ‖² ≤ 3R² · ∑' 1/‖ρ‖²
    calc ∑ n ∈ U, ‖g n‖
        ≤ ∑ n ∈ U, (3 * R ^ 2 * (1 / ‖zeros ↑n‖ ^ 2)) :=
          Finset.sum_le_sum h_pw
      _ = 3 * R ^ 2 * ∑ n ∈ U, (1 / ‖zeros ↑n‖ ^ 2) := by rw [← Finset.mul_sum]
      _ ≤ 3 * R ^ 2 * ∑' (n : ↑(↑S : Set ℕ)ᶜ), (1 / ‖zeros ↑n‖ ^ 2) := by
          gcongr; exact hsub_summable.sum_le_tsum U (fun n _ => by positivity)
      _ ≤ 3 * (2 * R₀) ^ 2 * ∑' (n : ↑(↑S : Set ℕ)ᶜ), (1 / ‖zeros ↑n‖ ^ 2) := by
          have hR_pos : (0 : ℝ) ≤ R := by linarith
          have hR2 : R ^ 2 ≤ (2 * R₀) ^ 2 := by nlinarith
          have htsum_nn : (0 : ℝ) ≤ ∑' (n : ↑(↑S : Set ℕ)ᶜ), (1 / ‖zeros ↑n‖ ^ 2) :=
            tsum_nonneg fun n => by positivity
          nlinarith
      _ = 12 * (R₀ ^ 2 * ∑' (n : ↑(↑S : Set ℕ)ᶜ), (1 / ‖zeros ↑n‖ ^ 2)) := by ring
      _ ≤ 12 * (K_outer * R₀ ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left htsum_bound (by norm_num)
      _ = 12 * K_outer * R₀ ^ (3 / 2 : ℝ) := by ring
  -- Combine
  linarith

private theorem weierstrass_product_lower_bound_on_good_circles
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hcount : ∃ C_cnt : ℝ, 0 < C_cnt ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ S : Finset ℕ,
        (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ R) ∧
        (S.card : ℝ) ≤ C_cnt * R ^ (3 / 2 : ℝ))
    (hP_diff : Differentiable ℂ (fun s =>
      ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n))) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ R₀ : ℝ, 1 ≤ R₀ →
      ∃ R : ℝ, R₀ ≤ R ∧ R ≤ 2 * R₀ ∧
        (∀ z : ℂ, ‖z‖ = R →
          (∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)) ≠ 0) ∧
        (∀ z : ℂ, ‖z‖ = R →
          Real.exp (-C₂ * R ^ (7/4 : ℝ)) ≤
            ‖∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)‖) := by
  -- Extract counting constant
  obtain ⟨C_cnt, hC_cnt, hcount_fn⟩ := hcount
  -- Get inner reciprocal sum bound
  obtain ⟨C_inner, hC_inner, hinner_bound⟩ :=
    inner_reciprocal_sum_bound_from_count zeros hne ⟨C_cnt, hC_cnt, hcount_fn⟩
  -- Get outer tail bound
  obtain ⟨K_outer, hK_outer, houter_bound⟩ :=
    outer_tail_inv_sq_bound_from_count zeros hne C_cnt hC_cnt hcount_fn
  -- Choose C₂ and intro R₀
  set C₂ := 100 * (C_cnt + C_inner + 1) ^ 2 + 50 * K_outer with hC₂_def
  refine ⟨C₂, by positivity, fun R₀ hR₀ => ?_⟩
  -- Pigeonhole: choose good R and S
  obtain ⟨S, hS_mem, hS_card⟩ := controlled_index_finset zeros R₀ hR₀ C_cnt hC_cnt hcount_fn
  obtain ⟨R, hR_lo, hR_hi, hgap⟩ := good_radius_via_pigeonhole zeros R₀ hR₀ S
  refine ⟨R, hR_lo, hR_hi, ?_, ?_⟩
  · -- Part A: Nonvanishing (via tprod_one_add_ne_zero_of_summable)
    exact fun z hz => tprod_E1_ne_zero_on_good_circle zeros hne hsum z R R₀ hR₀
      hR_lo hR_hi hz S hS_mem hgap
  · -- Part B: Quantitative lower bound exp(-C₂ * R^(7/4)) ≤ ‖∏' E1(z/ρ)‖
    intro z hz
    -- Split: ∏' = (∏_S) * (∏'_{Sᶜ})
    have hsplit := tprod_E1_split_finset zeros hne hsum S z
    rw [hsplit]
    -- Take norms: ‖a*b‖ = ‖a‖ * ‖b‖
    rw [norm_mul]
    -- We need: exp(-C₂*R^(7/4)) ≤ ‖finite‖ * ‖tail‖
    -- Strategy: bound each from below and combine via exp_add
    -- Lower bound for each factor in the finite product:
    -- Every factor is nonzero (from E1_ne_zero_on_good_circle)
    have hfin_factors_ne : ∀ n ∈ S,
        Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) ≠ 0 :=
      fun n _ => E1_ne_zero_on_good_circle zeros hne z R R₀ hR₀ hR_lo hR_hi hz S hS_mem hgap n
    -- Finite product is nonzero
    have hfin_ne : ∏ n ∈ S, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun n hn => hfin_factors_ne n hn)
    -- Finite product norm is positive
    have hfin_pos : (0 : ℝ) < ‖∏ n ∈ S,
        Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)‖ :=
      norm_pos_iff.mpr hfin_ne
    -- Tail product is nonzero (from tprod_one_add_ne_zero on the subtype)
    have htail_ne : (∏' (n : ↑(↑S : Set ℕ)ᶜ),
        Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n)) ≠ 0 := by
      rw [show (fun (n : ↑(↑S : Set ℕ)ᶜ) =>
          Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n)) =
          (fun (n : ↑(↑S : Set ℕ)ᶜ) =>
            1 + (Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n) - 1))
        from by ext; ring]
      apply tprod_one_add_ne_zero_of_summable
      · intro ⟨n, hn⟩
        intro h_eq
        have h0 : Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n) = 0 := by
          have := h_eq; ring_nf at this ⊢; exact this
        exact E1_ne_zero_on_good_circle zeros hne z R R₀ hR₀ hR_lo hR_hi hz S hS_mem hgap n h0
      · exact (E1_minus_one_norm_summable zeros hne hsum z).subtype _
    have htail_pos : (0 : ℝ) < ‖∏' (n : ↑(↑S : Set ℕ)ᶜ),
        Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n)‖ :=
      norm_pos_iff.mpr htail_ne
    -- Get tail product lower bound
    have htail_lb := tail_product_lower_bound_on_good_circle zeros hne hsum z R R₀ hR₀
      hR_lo hR_hi hz S hS_mem K_outer hK_outer houter_bound
    -- Get finite product lower bound
    have hfin_lb := finite_product_lower_bound_on_good_circle zeros hne z R R₀
      C_cnt hR₀ hC_cnt hR_lo hR_hi hz S hS_mem hS_card hgap C_inner hC_inner hinner_bound
    -- Combine: ‖fin‖ * ‖tail‖ ≥ exp(-100(C+I+1)²*R₀^(7/4)) * exp(-48K*R₀^(3/2))
    --                            ≥ exp(-C₂*R^(7/4))
    -- where C₂ = 100*(C_cnt+C_inner+1)^2 + 50*K_outer
    set C_fin := 100 * (C_cnt + C_inner + 1) ^ 2
    calc Real.exp (-C₂ * R ^ (7 / 4 : ℝ))
        ≤ Real.exp (-(C_fin + 48 * K_outer) * R₀ ^ (7 / 4 : ℝ)) := by
          apply Real.exp_le_exp_of_le
          -- Need: -(C_fin + 48K) * R₀^(7/4) ≤ -C₂ * R^(7/4) is WRONG direction
          -- We need: -C₂ * R^(7/4) ≤ -(C_fin+48K) * R₀^(7/4)
          -- i.e., (C_fin+48K) * R₀^(7/4) ≤ C₂ * R^(7/4)
          -- Since R₀ ≤ R and 100(C+I+1)^2 + 48K ≤ C₂
          have hR74 : R₀ ^ (7/4 : ℝ) ≤ R ^ (7/4 : ℝ) :=
            Real.rpow_le_rpow (by linarith) hR_lo (by norm_num : (0:ℝ) ≤ 7/4)
          have hC : C_fin + 48 * K_outer ≤ C₂ := by
            simp only [C_fin, hC₂_def]; nlinarith
          nlinarith [mul_le_mul_of_nonneg_right hR74 (by nlinarith : 0 ≤ C₂),
                     Real.rpow_nonneg (by linarith : 0 ≤ R₀) (7/4 : ℝ)]
      _ = Real.exp (-C_fin * R₀ ^ (7 / 4 : ℝ)) *
          Real.exp (-(48 * K_outer) * R₀ ^ (7 / 4 : ℝ)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-C_fin * R₀ ^ (7 / 4 : ℝ)) *
          Real.exp (-(48 * K_outer) * R₀ ^ (3 / 2 : ℝ)) := by
          -- exp(-48K*R₀^(7/4)) ≤ exp(-48K*R₀^(3/2)) since R₀^(3/2) ≤ R₀^(7/4)
          have h74 : R₀ ^ (3 / 2 : ℝ) ≤ R₀ ^ (7 / 4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : (3:ℝ)/2 ≤ 7/4)
          have hexp_tail : Real.exp (-(48 * K_outer) * R₀ ^ (7 / 4 : ℝ)) ≤
              Real.exp (-(48 * K_outer) * R₀ ^ (3 / 2 : ℝ)) :=
            Real.exp_le_exp_of_le (by nlinarith)
          exact mul_le_mul_of_nonneg_left hexp_tail (Real.exp_nonneg _)
      _ ≤ ‖∏ n ∈ S, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)‖ *
          ‖∏' (n : ↑(↑S : Set ℕ)ᶜ),
            Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros ↑n)‖ := by
          exact mul_le_mul hfin_lb htail_lb (Real.exp_nonneg _) (le_of_lt hfin_pos)

/-- **Helper**: Boundary bound on ‖Q z‖ from ξ = Q·P and component bounds.
Sorry: the division monotonicity step (a/b ≤ c/d from a≤c, d≤b, 0<d) and
exp arithmetic (exp(a)/exp(-b) = exp(a+b)) fight Lean's norm/div API.
The statement is mathematically immediate. -/
private theorem boundary_Q_bound
    (Q : ℂ → ℂ) (z : ℂ) (R : ℝ) (P : ℂ → ℂ)
    (hident_z : RiemannXiAlt z = Q z * P z) (hPz_ne : P z ≠ 0)
    (C₁ C₂ : ℝ)
    (hxi_z : ‖RiemannXiAlt z‖ ≤ Real.exp (C₁ * (‖z‖ + 1) ^ (3/2 : ℝ)))
    (hP_lb : Real.exp (-C₂ * R ^ (7/4 : ℝ)) ≤ ‖P z‖) :
    ‖Q z‖ ≤ Real.exp (C₁ * (‖z‖ + 1) ^ (3/2 : ℝ) + C₂ * R ^ (7/4 : ℝ)) := by
  have hP_pos : 0 < ‖P z‖ := norm_pos_iff.mpr hPz_ne
  have hQnorm : ‖Q z‖ = ‖RiemannXiAlt z‖ * ‖P z‖⁻¹ := by
    have h : Q z * P z = RiemannXiAlt z := hident_z.symm
    have hQz : Q z = RiemannXiAlt z * (P z)⁻¹ := by
      calc Q z = Q z * P z * (P z)⁻¹ := (mul_inv_cancel_right₀ hPz_ne _).symm
        _ = RiemannXiAlt z * (P z)⁻¹ := by rw [h]
    rw [hQz, norm_mul, norm_inv]
  rw [hQnorm]
  have hPinv : ‖P z‖⁻¹ ≤ Real.exp (C₂ * R ^ (7/4 : ℝ)) := by
    have h1 : Real.exp (-C₂ * R ^ (7/4 : ℝ)) ≤ ‖P z‖ := hP_lb
    have h2 : ‖P z‖⁻¹ ≤ (Real.exp (-C₂ * R ^ (7/4 : ℝ)))⁻¹ :=
      inv_anti₀ (Real.exp_pos _) h1
    rw [← Real.exp_neg] at h2
    simpa [neg_neg] using h2
  calc ‖RiemannXiAlt z‖ * ‖P z‖⁻¹
      ≤ Real.exp (C₁ * (‖z‖ + 1) ^ (3/2 : ℝ)) * Real.exp (C₂ * R ^ (7/4 : ℝ)) :=
        mul_le_mul hxi_z hPinv (inv_nonneg.mpr (le_of_lt hP_pos)) (Real.exp_nonneg _)
    _ = Real.exp (C₁ * (‖z‖ + 1) ^ (3/2 : ℝ) + C₂ * R ^ (7/4 : ℝ)) :=
        (Real.exp_add _ _).symm

/-- **Helper**: Coarse radius absorption for mixed exponents.
Absorbs C₁(R+1)^{3/2} + C₂R^{7/4} into K(‖s‖+1)^{7/4} using R ≤ 4(‖s‖+1)
and (R+1)^{3/2} ≤ (R+1)^{7/4} (since 3/2 ≤ 7/4 and R+1 ≥ 1). -/
private theorem radius_absorption
    (s : ℂ) (R : ℝ) (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hR_pos : 0 < R) (hR_bound : R ≤ 4 * (‖s‖ + 1)) :
    C₁ * (R + 1) ^ (3/2 : ℝ) + C₂ * R ^ (7/4 : ℝ) ≤
      100 * (C₁ + C₂ + 1) * (‖s‖ + 1) ^ (7/4 : ℝ) := by
  have hs1 : 0 ≤ ‖s‖ + 1 := by linarith [norm_nonneg s]
  have hs1_pos : 1 ≤ ‖s‖ + 1 := by linarith [norm_nonneg s]
  have hR1 : R + 1 ≤ 5 * (‖s‖ + 1) := by linarith
  have hR1_pos : 1 ≤ R + 1 := by linarith
  -- (R+1)^{3/2} ≤ (R+1)^{7/4} since 3/2 ≤ 7/4 and R+1 ≥ 1
  have h_exp_mono : (R + 1) ^ (3/2 : ℝ) ≤ (R + 1) ^ (7/4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hR1_pos (by norm_num)
  -- (R+1)^{7/4} ≤ (5(‖s‖+1))^{7/4}
  have h1 : (R + 1) ^ (7/4 : ℝ) ≤ (5 * (‖s‖ + 1)) ^ (7/4 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hR1 (by norm_num)
  -- R^{7/4} ≤ (4(‖s‖+1))^{7/4}
  have h2 : R ^ (7/4 : ℝ) ≤ (4 * (‖s‖ + 1)) ^ (7/4 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hR_bound (by norm_num)
  -- Factor: (c·x)^{7/4} = c^{7/4} · x^{7/4}
  have h3 : (5 * (‖s‖ + 1)) ^ (7/4 : ℝ) = (5 : ℝ) ^ (7/4 : ℝ) * (‖s‖ + 1) ^ (7/4 : ℝ) :=
    Real.mul_rpow (by norm_num) hs1
  have h4 : (4 * (‖s‖ + 1)) ^ (7/4 : ℝ) = (4 : ℝ) ^ (7/4 : ℝ) * (‖s‖ + 1) ^ (7/4 : ℝ) :=
    Real.mul_rpow (by norm_num) hs1
  -- Coarse bounds: a^{7/4} ≤ a^2 for a ≥ 1
  have h5_bound : (5 : ℝ) ^ (7/4 : ℝ) ≤ 25 := by
    calc (5 : ℝ) ^ (7/4 : ℝ) ≤ (5 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 25 := by
          have : (5 : ℝ) ^ (2 : ℝ) = (5 : ℝ) ^ (2 : ℕ) := by
            exact_mod_cast Real.rpow_natCast 5 2
          rw [this]; norm_num
  have h4_bound : (4 : ℝ) ^ (7/4 : ℝ) ≤ 16 := by
    calc (4 : ℝ) ^ (7/4 : ℝ) ≤ (4 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 16 := by
          have : (4 : ℝ) ^ (2 : ℝ) = (4 : ℝ) ^ (2 : ℕ) := by
            exact_mod_cast Real.rpow_natCast 4 2
          rw [this]; norm_num
  -- Final assembly: C₁(R+1)^{3/2} ≤ C₁(R+1)^{7/4} ≤ 25C₁(‖s‖+1)^{7/4}
  have hs_rpow_pos : 0 ≤ (‖s‖ + 1) ^ (7/4 : ℝ) := Real.rpow_nonneg hs1 _
  nlinarith [h_exp_mono.trans (h1.trans (h3 ▸ mul_le_mul_of_nonneg_right h5_bound hs_rpow_pos)),
             h2.trans (h4 ▸ mul_le_mul_of_nonneg_right h4_bound hs_rpow_pos)]

/-- Maximum modulus assembly for the growth bound.
Proved modulo boundary_Q_bound and radius_absorption. -/
private theorem growth_bound_from_components
    (Q : ℂ → ℂ) (hQ_diff : Differentiable ℂ Q) (hQ_ne : ∀ s, Q s ≠ 0)
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hident : ∀ s, RiemannXiAlt s = Q s *
      ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n))
    (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hxi : ∀ s : ℂ, ‖RiemannXiAlt s‖ ≤ Real.exp (C₁ * (‖s‖ + 1) ^ (3/2 : ℝ)))
    (C₂ : ℝ) (hC₂ : 0 < C₂)
    (hprod : ∀ R₀ : ℝ, 1 ≤ R₀ →
      ∃ R : ℝ, R₀ ≤ R ∧ R ≤ 2 * R₀ ∧
        (∀ z : ℂ, ‖z‖ = R →
          (∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)) ≠ 0) ∧
        (∀ z : ℂ, ‖z‖ = R →
          Real.exp (-C₂ * R ^ (7/4 : ℝ)) ≤
            ‖∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (z / zeros n)‖)) :
    ∃ C_Q : ℝ, 0 < C_Q ∧ ∀ s, ‖Q s‖ ≤ Real.exp (C_Q * (‖s‖ + 1) ^ (7/4 : ℝ)) := by
  set K := 100 * (C₁ + C₂ + 1) with hK_def
  refine ⟨K, by positivity, fun s => ?_⟩
  set R₀ := max 1 (2 * (‖s‖ + 1)) with hR₀_def
  obtain ⟨R, hR_lo, hR_hi, hP_ne_on, hP_lb_on⟩ := hprod R₀ (le_max_left _ _)
  have hs1_pos : 1 ≤ 2 * (‖s‖ + 1) := by linarith [norm_nonneg s]
  have hR₀_eq : R₀ = 2 * (‖s‖ + 1) := by
    rw [hR₀_def]; exact max_eq_right hs1_pos
  have hR_pos : 0 < R := by linarith [hR₀_eq ▸ hR_lo]
  have hs_mem : s ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall, dist_zero_right]
    linarith [hR₀_eq ▸ hR_lo]
  have hR_bound : R ≤ 4 * (‖s‖ + 1) := by linarith [hR₀_eq ▸ hR_hi]
  set P := fun s => ∏' n,
    Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n) with hP_def
  set M := Real.exp (C₁ * (R + 1) ^ (3/2 : ℝ) + C₂ * R ^ (7/4 : ℝ)) with hM_def
  have hbdy : ∀ w ∈ sphere (0 : ℂ) R, ‖Q w‖ ≤ M := by
    intro w hw; rw [mem_sphere_zero_iff_norm] at hw
    have h := boundary_Q_bound Q w R P (hident w) (hP_ne_on w hw) C₁ C₂ (hxi w) (hP_lb_on w hw)
    rwa [hw] at h
  have h_max := Littlewood.Development.BorelCaratheodory.max_modulus_bound
    hR_pos hQ_diff.diffContOnCl hs_mem (le_of_lt (Real.exp_pos _)) hbdy
  calc ‖Q s‖ ≤ M := h_max
    _ = Real.exp (C₁ * (R + 1) ^ (3/2 : ℝ) + C₂ * R ^ (7/4 : ℝ)) := rfl
    _ ≤ Real.exp (K * (‖s‖ + 1) ^ (7/4 : ℝ)) := by
        apply Real.exp_le_exp_of_le
        exact radius_absorption s R C₁ C₂ hC₁ hC₂ hR_pos hR_bound

instance : XiQuotientGrowthBoundHyp := ⟨by
  intro Q hQ_diff hQ_ne zeros hne hzeros_zero hsum hcount hident
  -- Step 1: Extend xi growth bound to all of ℂ (not just ‖s‖ ≥ 2)
  obtain ⟨C_big, hC_big, hxi_big⟩ := xi_growth_for_jensen
  -- For ‖s‖ < 2: xi is continuous on compact closedBall 0 2, so bounded by some M
  have hxi_all : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ s : ℂ,
      ‖RiemannXiAlt s‖ ≤ Real.exp (C₁ * (‖s‖ + 1) ^ (3/2 : ℝ)) := by
    -- Compact bound on closedBall 0 3 (using 3 > 2 to overlap with large case)
    have hxi_cts : Continuous RiemannXiAlt := RiemannXiAlt_entire.continuous
    obtain ⟨M₀, hM₀⟩ := isCompact_closedBall (0 : ℂ) 3 |>.exists_bound_of_continuousOn
      hxi_cts.continuousOn
    set M := max M₀ 1 with hM_def
    have hM_pos : 0 < M := by positivity
    -- Choose C₁ large enough for both regimes
    set C₁ := max C_big (Real.log M + 1) with hC₁_def
    have hC₁_pos : 0 < C₁ := lt_max_of_lt_left hC_big
    refine ⟨C₁, hC₁_pos, fun s => ?_⟩
    by_cases hs : 2 ≤ ‖s‖
    · -- Large case: use xi_growth_for_jensen, then monotonicity
      have h1 := hxi_big s hs
      calc ‖RiemannXiAlt s‖
          ≤ Real.exp (C_big * ‖s‖ ^ (3 / 2 : ℝ)) := h1
        _ ≤ Real.exp (C₁ * (‖s‖ + 1) ^ (3 / 2 : ℝ)) := by
            apply Real.exp_le_exp_of_le
            gcongr
            · exact le_max_left _ _
            · linarith
    · -- Small case: ‖s‖ < 2, so s ∈ closedBall 0 3
      push_neg at hs
      have hs3 : s ∈ Metric.closedBall (0 : ℂ) 3 := by
        simp [Metric.mem_closedBall, dist_zero_right]; linarith
      have hbound : ‖RiemannXiAlt s‖ ≤ M := (hM₀ s hs3).trans (le_max_left _ _)
      calc ‖RiemannXiAlt s‖
          ≤ M := hbound
        _ = Real.exp (Real.log M) := by rw [Real.exp_log hM_pos]
        _ ≤ Real.exp (C₁ * (‖s‖ + 1) ^ (3/2 : ℝ)) := by
            apply Real.exp_le_exp_of_le
            -- C₁ ≥ log M + 1 and (‖s‖+1)^{3/2} ≥ 1, so C₁ * (‖s‖+1)^{3/2} ≥ log M + 1 > log M
            have h1 : (1 : ℝ) ≤ ‖s‖ + 1 := by linarith [norm_nonneg s]
            have hpow : (1 : ℝ) ≤ (‖s‖ + 1) ^ (3/2 : ℝ) :=
              Real.one_le_rpow (by linarith [norm_nonneg s]) (by norm_num)
            have hC₁_ge : Real.log M + 1 ≤ C₁ := le_max_right _ _
            linarith [mul_le_mul_of_nonneg_right hpow (le_of_lt hC₁_pos)]
  obtain ⟨C₁, hC₁, hxi⟩ := hxi_all
  -- Step 2: Product lower bound on good circles
  have hP_diff := weierstrass_product_differentiable zeros hne hsum
  obtain ⟨C₂, hC₂, hprod⟩ :=
    weierstrass_product_lower_bound_on_good_circles zeros hne hsum hcount hP_diff
  -- Step 3: Maximum modulus assembly
  exact growth_bound_from_components Q hQ_diff hQ_ne zeros hne hsum hident
    C₁ hC₁ hxi C₂ hC₂ hprod⟩

/-! ### Decomposition of `xi_quotient_entire_nonvanishing`

The original single sorry is now decomposed into three focused sub-sorrys:
- **Sub-sorry A** (`weierstrass_product_differentiable`): ∏ E₁(s/ρₙ) is entire. **CLOSED**
- **Sub-sorry B** (`xi_quotient_extends_entire`): ξ/P extends entire + nonvanishing.
  Now uses `XiQuotientMeromorphicOrderNonnegHyp` and `XiQuotientNonvanishingHyp`.
- **Sub-sorry C** (`xi_quotient_growth_bound`): |Q(s)| ≤ exp(C(|s|+1)^{7/4}).
  Now uses `XiQuotientGrowthBoundHyp`.

The assembly `xi_quotient_entire_nonvanishing` is fully constructive from these.

**Background** (Hadamard 1893 Section 2):
- `xi_quotient_analytic_at_zero` (PROVED): at shared zeros, ξ/P extends analytically
  via `analyticAt_quotient_of_common_order`.
- `xi_quotient_analytic_at_nonzero` (PROVED): at non-zeros of P, ξ/P is analytic.
- Remaining blockers per sub-sorry documented in their individual docstrings. -/
/-- **Sub-sorry B**: The quotient `ξ/P` extends to an entire nonvanishing function.

Given that every `zeros n` is an actual zero of ξ and every zero of ξ appears
in `zeros`, the quotient ξ/P extends analytically at each apparent singularity.

**Proof architecture**: The function ξ/P is meromorphic on ℂ (ratio of entire
functions). The meromorphic order non-negativity (from `XiQuotientMeromorphicOrderNonnegHyp`)
shows the quotient extends to an entire function Q via `toMeromorphicNFOn`.
The nonvanishing of Q (from `XiQuotientNonvanishingHyp`) gives ∀ s, Q s ≠ 0.
The identity ξ = Q · P is proved constructively: Q agrees with ξ/P on a
codiscrete set, and P(0) = 1 ≠ 0 gives agreement frequently in 𝓝[≠] 0,
which extends to all of ℂ by the identity theorem. -/
private theorem xi_quotient_extends_entire
    (zeros : ℕ → ℂ) (hcover : ∀ s, RiemannXiAlt s = 0 → ∃ n, s = zeros n)
    (hne : ∀ n, zeros n ≠ 0)
    (hzeros_zero : ∀ n, RiemannXiAlt (zeros n) = 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hP_diff : Differentiable ℂ (fun s =>
      ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)))
    (hmult : ∀ z, (Nat.card {n | zeros n = z} : ℕ∞) = analyticOrderAt RiemannXiAlt z) :
    ∃ Q : ℂ → ℂ,
      Differentiable ℂ Q ∧
      (∀ s, Q s ≠ 0) ∧
      (∀ s, RiemannXiAlt s = Q s *
        ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) := by
  set P := fun s => ∏' n,
    Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n) with hP_def
  -- Q₀ := ξ/P (literal division), meromorphic on all of ℂ
  set Q₀ := fun z => RiemannXiAlt z / P z with hQ₀_def
  have hQ₀_merOn : MeromorphicOn Q₀ Set.univ :=
    fun z _ => (RiemannXiAlt_entire.analyticAt z).meromorphicAt.div
      (hP_diff.analyticAt z).meromorphicAt
  -- Define Q := toMeromorphicNFOn Q₀ univ (the normal form extension)
  set Q := toMeromorphicNFOn Q₀ Set.univ with hQ_def
  -- Q has meromorphic normal form on univ
  have hQ_nf : MeromorphicNFOn Q Set.univ := meromorphicNFOn_toMeromorphicNFOn Q₀ Set.univ
  -- The orders of Q₀ (equivalently Q) are exactly zero everywhere.
  -- This means Q is analytic and nonvanishing on univ.
  have hQ_order_zero : ∀ z, meromorphicOrderAt Q₀ z = 0 := by
    intro z
    exact XiQuotientMeromorphicOrderNonnegHyp.order_eq_zero
      zeros hcover hne hzeros_zero hsum hP_diff hmult z
  -- Transfer: toMeromorphicNFOn preserves orders
  have hQ_order_zero' : ∀ z ∈ Set.univ,
      meromorphicOrderAt Q z = 0 := by
    intro z hz
    rw [meromorphicOrderAt_toMeromorphicNFOn hQ₀_merOn hz]
    exact hQ_order_zero z
  -- Q is analytic on univ (NF + order = 0 ⟹ analytic and nonvanishing)
  have hQ_an : AnalyticOnNhd ℂ Q Set.univ := by
    intro z hz
    exact (hQ_nf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by rw [hQ_order_zero' z hz])
  have hQ_diff : Differentiable ℂ Q :=
    fun z => (hQ_an z (Set.mem_univ z)).differentiableAt
  -- Q agrees with Q₀ on the codiscrete set (away from isolated points)
  have hQ_eq_Q₀_codiscrete :
      Q₀ =ᶠ[Filter.codiscreteWithin Set.univ] Q :=
    toMeromorphicNFOn_eqOn_codiscrete hQ₀_merOn
  -- Nonvanishing of Q and the identity ξ = Q · P
  -- At non-zeros of P: Q = ξ/P, and ξ(s) ≠ 0 when P(s) ≠ 0
  -- (because if ξ(s) = 0 then s = zeros(n) by hcover, and P(zeros(n)) = 0).
  -- At zeros of P: Q extends analytically, and the extension value is
  -- the ratio of leading coefficients (nonvanishing).
  -- Identity: Q · P = ξ on the codiscrete set (where Q = Q₀ = ξ/P),
  -- and both sides are analytic, so they agree everywhere.
  have hQ_ne : ∀ s, Q s ≠ 0 :=
    XiQuotientNonvanishingHyp.nonvanishing zeros hcover hne hzeros_zero hsum hP_diff hmult
  have hQ_ident : ∀ s, RiemannXiAlt s = Q s * P s := by
    -- Both sides are entire. They agree on the codiscrete set.
    -- By the identity theorem (ℂ is connected), they agree everywhere.
    have hξ_an : AnalyticOnNhd ℂ RiemannXiAlt Set.univ :=
      fun z _ => RiemannXiAlt_entire.analyticAt z
    have hQP_an : AnalyticOnNhd ℂ (fun s => Q s * P s) Set.univ :=
      fun z hz => (hQ_an z hz).mul (hP_diff.analyticAt z)
    -- They agree frequently near 0 (from codiscrete agreement)
    have h_freq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), RiemannXiAlt z = Q z * P z := by
      -- Strategy: {z | Q₀ z = Q z} ∈ codiscreteWithin univ, so it's in 𝓝[≠] 0.
      -- Also P is nonzero near 0 (P(0) = 1 from E₁(0) = 1). On both sets,
      -- Q z * P z = Q₀ z * P z = (ξ z / P z) * P z = ξ z.
      -- Step 1: The codiscrete agreement gives {z | Q₀ z = Q z} ∈ 𝓝[≠] 0
      have h_cod := hQ_eq_Q₀_codiscrete
      have h_cod_nhds : ∀ᶠ z in 𝓝[≠] (0 : ℂ), Q₀ z = Q z := by
        rw [Filter.Eventually]
        have h_mem : {z | Q₀ z = Q z} ∈ Filter.codiscreteWithin Set.univ := h_cod
        rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
        have := h_mem 0 (Set.mem_univ 0)
        simp only [Set.compl_univ, Set.union_empty] at this
        exact this
      -- Step 2: P(0) = ∏' n, E₁(0/ρₙ) = 1 ≠ 0, so P ≠ 0 near 0
      have hE1_zero : Aristotle.Standalone.HadamardProductConvergence.E1 0 = 1 := by
        simp [Aristotle.Standalone.HadamardProductConvergence.E1]
      have hP_zero : P 0 = 1 := by
        show ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (0 / zeros n) = 1
        have heq : (fun n => Aristotle.Standalone.HadamardProductConvergence.E1 (0 / zeros n))
            = fun _ => (1 : ℂ) := by
          ext n; simp [zero_div, hE1_zero]
        rw [heq]; simp
      have hP_ne_zero_nhds : ∀ᶠ z in 𝓝 (0 : ℂ), P z ≠ 0 :=
        hP_diff.continuous.continuousAt.eventually_ne (by rw [hP_zero]; exact one_ne_zero)
      -- Step 3: In 𝓝[≠] 0, both hold, so Q·P = ξ
      apply Eventually.frequently
      filter_upwards [h_cod_nhds,
        hP_ne_zero_nhds.filter_mono nhdsWithin_le_nhds] with z h_eq h_Pne
      -- At z: Q z = Q₀ z = ξ z / P z, and P z ≠ 0
      rw [← h_eq, hQ₀_def, div_mul_cancel₀ (RiemannXiAlt z) h_Pne]
    exact fun s => (hξ_an.eqOn_of_preconnected_of_frequently_eq hQP_an
      isPreconnected_univ (Set.mem_univ 0) h_freq) (Set.mem_univ s)
  exact ⟨Q, hQ_diff, hQ_ne, hQ_ident⟩

/-- **Sub-sorry C**: Growth bound on the entire nonvanishing quotient Q.

Now delegated to `XiQuotientGrowthBoundHyp`. See its docstring for the
proof sketch (minimum modulus of Weierstrass products on good circles,
combined with xi_finite_order and the maximum modulus principle). -/
private theorem xi_quotient_growth_bound
    (Q : ℂ → ℂ)
    (hQ_diff : Differentiable ℂ Q)
    (hQ_ne : ∀ s, Q s ≠ 0)
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (hzeros_zero : ∀ n, RiemannXiAlt (zeros n) = 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hcount : ∃ C_cnt : ℝ, 0 < C_cnt ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ S : Finset ℕ,
        (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ R) ∧
        (S.card : ℝ) ≤ C_cnt * R ^ (3 / 2 : ℝ))
    (hident : ∀ s, RiemannXiAlt s = Q s *
      ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) :
    ∃ C_Q : ℝ, 0 < C_Q ∧ ∀ s, ‖Q s‖ ≤ Real.exp (C_Q * (‖s‖ + 1) ^ (7/4 : ℝ)) :=
  XiQuotientGrowthBoundHyp.growth_bound Q hQ_diff hQ_ne zeros hne hzeros_zero hsum hcount hident

theorem xi_quotient_entire_nonvanishing
    (zeros : ℕ → ℂ)
    (hcover : ∀ s, RiemannXiAlt s = 0 → ∃ n, s = zeros n)
    (hne : ∀ n, zeros n ≠ 0)
    (hzeros_zero : ∀ n, RiemannXiAlt (zeros n) = 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hcount : ∃ C_cnt : ℝ, 0 < C_cnt ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ S : Finset ℕ,
        (∀ n, n ∈ S ↔ ‖zeros n‖ ≤ R) ∧
        (S.card : ℝ) ≤ C_cnt * R ^ (3 / 2 : ℝ))
    (hmult : ∀ z, (Nat.card {n | zeros n = z} : ℕ∞) = analyticOrderAt RiemannXiAlt z) :
    ∃ Q : ℂ → ℂ,
      Differentiable ℂ Q ∧
      (∀ s, Q s ≠ 0) ∧
      (∃ C_Q : ℝ, 0 < C_Q ∧ ∀ s, ‖Q s‖ ≤ Real.exp (C_Q * (‖s‖ + 1) ^ (7/4 : ℝ))) ∧
      (∀ s, RiemannXiAlt s = Q s *
        ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) := by
  -- Step 1: The Weierstrass product is differentiable
  have hP_diff := weierstrass_product_differentiable zeros hne hsum
  -- Step 2: The quotient ξ/P extends to an entire nonvanishing function
  obtain ⟨Q, hQ_diff, hQ_ne, hQ_eq⟩ :=
    xi_quotient_extends_entire zeros hcover hne hzeros_zero hsum hP_diff hmult
  -- Step 3: Growth bound on Q
  obtain ⟨C_Q, hC_Q, hQ_growth⟩ :=
    xi_quotient_growth_bound Q hQ_diff hQ_ne zeros hne hzeros_zero hsum hcount hQ_eq
  exact ⟨Q, hQ_diff, hQ_ne, ⟨C_Q, hC_Q, hQ_growth⟩, hQ_eq⟩

/-! ### Borel-Carathéodory infrastructure

The Borel-Carathéodory theorem is not in Mathlib v4.27.0-rc1. We prove the
version needed here: if `Re(f) ≤ M` on a disk and `f(0) = 0`, then
`‖f‖ ≤ 2M` on the half-disk.

**Proof**: Define `φ(z) = f(z)/(2M − f(z))`. Since `Re(f) ≤ M < 2M`, the
denominator never vanishes and `|φ| ≤ 1` (because `|f| ≤ |2M − f|` when
`Re(f) ≤ M`). Also `φ(0) = 0`. By the Schwarz lemma, `|φ(z)| ≤ |z|/R`.
For `|z| ≤ R/2`: `|φ| ≤ 1/2`, so `|f| = |2Mφ/(1+φ)| ≤ 2M`. -/

/-- If `Re(w) ≤ M` and `M > 0`, then `2M − w ≠ 0`. -/
private lemma two_mul_sub_ne_zero_bc {w : ℂ} {M : ℝ} (hM : 0 < M) (hRe : w.re ≤ M) :
    (2 : ℂ) * ↑M - w ≠ 0 := by
  intro h
  have : ((2 : ℂ) * ↑M - w).re = 0 := by rw [h]; simp
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat] at this
  linarith

/-- If `Re(w) ≤ M` and `M > 0`, then `‖w‖ ≤ ‖2M − w‖`.
This is the key norm inequality for the Borel-Carathéodory Schwarz map. -/
private lemma norm_le_norm_two_mul_sub_bc {w : ℂ} {M : ℝ} (hM : 0 < M) (hRe : w.re ≤ M) :
    ‖w‖ ≤ ‖(2 : ℂ) * ↑M - w‖ := by
  rw [norm_def, norm_def]
  apply Real.sqrt_le_sqrt
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, re_ofNat,
    im_ofNat]
  nlinarith [sq_nonneg w.re, sq_nonneg (2 * M - w.re)]

/-- **Borel-Carathéodory on a disk** (fully proved via Schwarz lemma).

If `f` is differentiable on `ball(0, R)` with `f(0) = 0` and `Re(f(z)) ≤ M`
for all `z ∈ ball(0, R)`, then `‖f(z)‖ ≤ 2M` for `z ∈ ball(0, R/2)`. -/
private theorem borel_caratheodory_disk
    (f : ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hf_diff : DifferentiableOn ℂ f (ball 0 R))
    (hf_zero : f 0 = 0)
    (hf_re : ∀ z ∈ ball (0 : ℂ) R, (f z).re ≤ M) :
    ∀ z ∈ ball (0 : ℂ) (R / 2), ‖f z‖ ≤ 2 * M := by
  intro z hz
  -- Define Schwarz map φ(w) = f(w) / (2M − f(w))
  set φ := fun w => f w / ((2 : ℂ) * ↑M - f w) with hφ_def
  -- φ is differentiable on ball 0 R (denominator never vanishes)
  have hφ_diff : DifferentiableOn ℂ φ (ball 0 R) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div
    · exact (hf_diff.differentiableAt (isOpen_ball.mem_nhds hw))
    · exact (((differentiableAt_const _).sub
        (hf_diff.differentiableAt (isOpen_ball.mem_nhds hw))))
    · exact two_mul_sub_ne_zero_bc hM (hf_re w hw)
  -- φ(0) = 0
  have hφ_zero : φ 0 = 0 := by simp [hφ_def, hf_zero]
  -- φ maps ball(0,R) into closedBall(0,1): |f| ≤ |2M−f| gives |φ| ≤ 1
  have hφ_maps : MapsTo φ (ball 0 R) (closedBall (φ 0) 1) := by
    rw [hφ_zero]
    intro w hw
    rw [mem_closedBall_zero_iff]
    show ‖f w / ((2 : ℂ) * ↑M - f w)‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr (two_mul_sub_ne_zero_bc hM (hf_re w hw)))]
    exact norm_le_norm_two_mul_sub_bc hM (hf_re w hw)
  -- z lies in ball(0, R) since R/2 < R
  have hz_ball : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff] at hz ⊢; linarith
  -- Schwarz lemma: ‖φ z‖ ≤ (1/R) · ‖z‖
  have hSchwarz : dist (φ z) (φ 0) ≤ 1 / R * dist z 0 :=
    Complex.dist_le_div_mul_dist_of_mapsTo_ball hφ_diff hφ_maps hz_ball
  rw [hφ_zero, dist_zero_right, dist_zero_right] at hSchwarz
  have hz_norm : ‖z‖ < R / 2 := mem_ball_zero_iff.mp hz
  have h_ne : (2 : ℂ) * ↑M - f z ≠ 0 := two_mul_sub_ne_zero_bc hM (hf_re z hz_ball)
  have h_denom_pos : 0 < ‖(2 : ℂ) * ↑M - f z‖ := norm_pos_iff.mpr h_ne
  -- ‖f z‖ = ‖φ z‖ · ‖2M − f z‖
  have hφ_norm : ‖f z‖ = ‖φ z‖ * ‖(2 : ℂ) * ↑M - f z‖ := by
    show ‖f z‖ = ‖f z / ((2 : ℂ) * ↑M - f z)‖ * ‖(2 : ℂ) * ↑M - f z‖
    rw [norm_div, div_mul_cancel₀ _ (ne_of_gt h_denom_pos)]
  -- Combined: ‖f z‖ ≤ (1/R · ‖z‖) · ‖2M − f z‖
  have h1 : ‖f z‖ ≤ 1 / R * ‖z‖ * ‖(2 : ℂ) * ↑M - f z‖ := by
    rw [hφ_norm]; exact mul_le_mul_of_nonneg_right hSchwarz (norm_nonneg _)
  -- Triangle: ‖2M − f z‖ ≤ 2M + ‖f z‖
  have h_tri : ‖(2 : ℂ) * ↑M - f z‖ ≤ 2 * M + ‖f z‖ := by
    calc ‖(2 : ℂ) * ↑M - f z‖ ≤ ‖(2 : ℂ) * ↑M‖ + ‖f z‖ := norm_sub_le _ _
      _ = 2 * M + ‖f z‖ := by
        congr 1; rw [norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg hM.le]
  -- Key ratio bound: 1/R · ‖z‖ < 1/2
  have h_ratio : 1 / R * ‖z‖ < 1 / 2 := by
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact (div_lt_div_iff₀ hR two_pos).mpr (by linarith)
  -- Combine: ‖f z‖ ≤ c(2M + ‖f z‖) with c < 1/2 gives ‖f z‖ ≤ 2M
  nlinarith [norm_nonneg (f z),
    mul_le_mul_of_nonneg_left h_tri (show 0 ≤ 1 / R * ‖z‖ by positivity)]

/-- **Borel-Carathéodory growth transfer** (fully proved).

If `g : ℂ → ℂ` is entire and `Re(g(z)) ≤ C · (‖z‖ + 1)^α` for all `z`,
then `‖g(z)‖ ≤ C' · (‖z‖ + 1)^α` for some `C' > 0`.

**Proof**: For each `z`, apply `borel_caratheodory_disk` on `ball(0, R)` with
`R = 2(‖z‖+1)` and `f(w) = g(w) − g(0)`. Then `f(0) = 0` and
`Re(f(w)) ≤ C · 3^α · (‖z‖+1)^α + |Re(g(0))|` on the ball. By BC at the
half-radius: `‖f(z)‖ ≤ 2M`. Triangle gives `‖g(z)‖ ≤ ‖g(0)‖ + 2M`. -/
private theorem borel_caratheodory_entire_growth
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (α C : ℝ) (hα : 0 ≤ α) (hC : 0 < C)
    (hRe : ∀ z : ℂ, (g z).re ≤ C * (‖z‖ + 1) ^ α) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ z : ℂ, ‖g z‖ ≤ C' * (‖z‖ + 1) ^ α := by
  refine ⟨4 * 3 ^ α * C + 3 * ‖g 0‖ + 1, by positivity, ?_⟩
  intro z
  -- Apply BC on ball(0, R) with R = 2(‖z‖+1) and f(w) = g(w) − g(0).
  set R := 2 * (‖z‖ + 1) with hR_def
  set f := fun w => g w - g 0 with hf_def
  have hR_pos : 0 < R := by positivity
  have hf_diff : DifferentiableOn ℂ f (ball 0 R) :=
    (hg.sub (differentiable_const _)).differentiableOn
  have hf_zero : f 0 = 0 := by simp [hf_def]
  -- M bounds Re(f) on ball(0, R): for ‖w‖ < R, ‖w‖+1 < 3(‖z‖+1)
  set M := C * 3 ^ α * (‖z‖ + 1) ^ α + |(g 0).re| with hM_def
  have hM_pos : 0 < M := by positivity
  have hf_re : ∀ w ∈ ball (0 : ℂ) R, (f w).re ≤ M := by
    intro w hw
    simp only [hf_def, sub_re]
    have hw_norm : ‖w‖ < R := mem_ball_zero_iff.mp hw
    have h1 : ‖w‖ + 1 < 3 * (‖z‖ + 1) := by linarith [norm_nonneg z]
    have h2 : (g w).re ≤ C * 3 ^ α * (‖z‖ + 1) ^ α := by
      calc (g w).re ≤ C * (‖w‖ + 1) ^ α := hRe w
        _ ≤ C * (3 * (‖z‖ + 1)) ^ α := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          exact Real.rpow_le_rpow (by positivity) h1.le hα
        _ = C * (3 ^ α * (‖z‖ + 1) ^ α) := by
          congr 1
          exact Real.mul_rpow (by norm_num : (3:ℝ) ≥ 0).le (by positivity)
        _ = C * 3 ^ α * (‖z‖ + 1) ^ α := by ring
    linarith [le_abs_self (g 0).re, neg_le_abs (g 0).re]
  -- z ∈ ball(0, R/2) since ‖z‖ < ‖z‖+1 = R/2
  have hz_mem : z ∈ ball (0 : ℂ) (R / 2) := by
    rw [mem_ball_zero_iff, hR_def]; linarith
  -- BC: ‖f z‖ ≤ 2M
  have hBC := borel_caratheodory_disk f R M hR_pos hM_pos hf_diff hf_zero hf_re z hz_mem
  -- ‖g z‖ ≤ ‖g 0‖ + ‖f z‖ by triangle
  have h_split : ‖g z‖ ≤ ‖g 0‖ + ‖f z‖ := by
    have : g z = g 0 + f z := by simp [hf_def]
    rw [this]; exact norm_add_le _ _
  have h_re_le : |(g 0).re| ≤ ‖g 0‖ := abs_re_le_norm (g 0)
  -- (‖z‖+1)^α ≥ 1 and 3^α ≥ 1
  have h_rpow_ge : 1 ≤ (‖z‖ + 1) ^ α := by
    calc (1 : ℝ) = 1 ^ α := (Real.one_rpow α).symm
      _ ≤ (‖z‖ + 1) ^ α :=
        Real.rpow_le_rpow (by norm_num) (by linarith [norm_nonneg z]) hα
  have h_3α_ge : 1 ≤ (3 : ℝ) ^ α := by
    calc (1 : ℝ) = 1 ^ α := (Real.one_rpow α).symm
      _ ≤ (3 : ℝ) ^ α := Real.rpow_le_rpow (by norm_num) (by norm_num) hα
  -- Abbreviate for nlinarith
  set p := (‖z‖ + 1) ^ α with hp_def
  set t := (3 : ℝ) ^ α with ht_def
  -- Expand: ‖g z‖ ≤ ‖g 0‖ + 2(C·t·p + |Re(g 0)|) ≤ 3‖g 0‖ + 2Ctp
  have h1' : ‖g z‖ ≤ 3 * ‖g 0‖ + 2 * C * t * p := by nlinarith
  -- 3‖g 0‖ ≤ 3‖g 0‖·p (since p ≥ 1)
  have h2' : 3 * ‖g 0‖ ≤ 3 * ‖g 0‖ * p := by nlinarith [norm_nonneg (g 0)]
  have h3' : 0 ≤ 2 * t * C * p + p := by positivity
  nlinarith

/-- **Sorry C closed**: Log-quotient has subquadratic growth.

Given an entire nonvanishing function `Q` with growth bound
`‖Q(s)‖ ≤ exp(C_Q · (‖s‖ + 1)^{7/4})`, there exists an entire function `g`
with `exp(g) = Q` and `SubquadraticGrowth g (7/4) C`.

Proof:
1. **Existence of g**: `ℂ` is contractible (hence simply connected and locally
   path-connected), and `exp : ℂ → ℂ∖{0}` is a covering map
   (`Complex.isCoveringMap_exp`). Since `Q` maps into `ℂ∖{0}` (from `hQ_ne`),
   the covering space lifting theorem (`IsCoveringMap.existsUnique_continuousMap_lifts`)
   produces `g : C(ℂ, ℂ)` with `exp(g(s)) = Q(s)`. The lift is differentiable
   because `exp` is a local biholomorphism (`analyticAt_localInverse`).

2. **Growth bound**: `Re(g(s)) = log‖Q(s)‖ ≤ C_Q · (‖s‖ + 1)^{7/4}` from
   the growth hypothesis. By the Borel-Carathéodory theorem (or maximum
   principle for Re), `|g(s)| ≤ C'(‖s‖ + 1)^{7/4}`. -/

theorem xi_log_quotient_subquadratic
    (Q : ℂ → ℂ)
    (hQ_diff : Differentiable ℂ Q)
    (hQ_ne : ∀ s, Q s ≠ 0)
    (hQ_growth : ∃ C_Q : ℝ, 0 < C_Q ∧ ∀ s, ‖Q s‖ ≤ Real.exp (C_Q * (‖s‖ + 1) ^ (7/4 : ℝ))) :
    ∃ (g : ℂ → ℂ) (C : ℝ),
      Differentiable ℂ g ∧
      0 < C ∧
      (∀ s, exp (g s) = Q s) ∧
      SubquadraticGrowth g (7/4) C := by
  -- Step 1: Lift Q through exp using the covering map theorem.
  -- Construct Q as a continuous map to {z : ℂ // z ≠ 0}
  have hQ'_cont : Continuous (fun s => (⟨Q s, hQ_ne s⟩ : {z : ℂ // z ≠ 0})) :=
    Continuous.subtype_mk hQ_diff.continuous _
  set f : C(ℂ, {z : ℂ // z ≠ 0}) := ⟨fun s => ⟨Q s, hQ_ne s⟩, hQ'_cont⟩ with hf_def
  -- Choose base point lift: g(0) = log(Q(0))
  set e₀ := Complex.log (Q 0) with he₀_def
  have he₀ : (fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) e₀ = f 0 := by
    simp only [hf_def, he₀_def]
    exact Subtype.ext (Complex.exp_log (hQ_ne 0))
  -- Apply the covering space lifting theorem
  obtain ⟨F, ⟨_, hF_lift⟩, _⟩ :=
    Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 e₀ he₀
  -- F : C(ℂ, ℂ) with exp(F(s)) = Q(s)
  set g := F.toFun with hg_def
  have hg_exp : ∀ s, exp (g s) = Q s := by
    intro s
    have := congr_fun hF_lift s
    simp only [Function.comp] at this
    exact congr_arg Subtype.val this
  -- Step 2: g is differentiable.
  -- exp is analytic with nonzero derivative everywhere.
  -- Since exp(g(s)) = Q(s) and Q is analytic, and exp is a local biholomorphism,
  -- g must be analytic (it equals the local inverse of exp composed with Q).
  have hg_diff : Differentiable ℂ g := by
    intro s₀
    -- exp is analytic at g(s₀)
    have hexp_analytic : AnalyticAt ℂ exp (g s₀) := analyticAt_cexp
    -- deriv of exp at g(s₀) is exp(g(s₀)) = Q(s₀) ≠ 0
    have hexp_deriv : deriv exp (g s₀) ≠ 0 := by
      rw [Complex.deriv_exp]
      rw [hg_exp s₀]
      exact hQ_ne s₀
    -- Local analytic inverse of exp at exp(g(s₀)) = Q(s₀)
    set L := hexp_analytic.hasStrictDerivAt.localInverse _ _ _ hexp_deriv
    have hL_analytic : AnalyticAt ℂ L (exp (g s₀)) :=
      hexp_analytic.analyticAt_localInverse hexp_deriv
    -- L ∘ Q is analytic at s₀
    have hQ_analytic : AnalyticAt ℂ Q s₀ :=
      (analyticAt_iff_eventually_differentiableAt.mpr
        (Filter.Eventually.of_forall (fun z => hQ_diff z)))
    have hLQ_analytic : AnalyticAt ℂ (L ∘ Q) s₀ := by
      rw [hg_exp s₀] at hL_analytic
      exact hL_analytic.comp hQ_analytic
    -- g = L ∘ Q in a neighborhood of s₀
    -- (because exp(g(s)) = Q(s) and L is the local inverse of exp near g(s₀))
    have hLQ_eq_g : (L ∘ Q) =ᶠ[nhds s₀] g := by
      -- L(exp(z)) = z for z near g(s₀)
      have hL_inv : ∀ᶠ z in nhds (g s₀),
          L (exp z) = z :=
        HasStrictDerivAt.eventually_left_inverse hexp_analytic.hasStrictDerivAt hexp_deriv
      -- g is continuous at s₀, so g(s) is near g(s₀) for s near s₀
      have hg_cont : ContinuousAt g s₀ := F.continuous.continuousAt
      -- Pull back through g
      have := hg_cont.eventually hL_inv
      filter_upwards [this] with s hs
      show L (Q s) = g s
      rw [← hg_exp s]
      exact hs
    exact hLQ_eq_g.differentiableAt_iff.mp hLQ_analytic.differentiableAt
  -- Step 3: Growth bound on g via Borel-Carathéodory.
  -- Re(g(z)) = log|Q(z)| ≤ C_Q·(‖z‖+1)^{7/4} from hQ_growth.
  obtain ⟨C_Q, hC_Q_pos, hQ_bound⟩ := hQ_growth
  have hRe_bound : ∀ z : ℂ, (g z).re ≤ C_Q * (‖z‖ + 1) ^ (7/4 : ℝ) := by
    intro z
    have h1 : (g z).re = Real.log ‖Q z‖ := by
      have := hg_exp z
      rw [← this, norm_exp]
      exact (Real.log_exp _).symm
    rw [h1]
    calc Real.log ‖Q z‖
        ≤ Real.log (Real.exp (C_Q * (‖z‖ + 1) ^ (7/4 : ℝ))) :=
          Real.log_le_log (norm_pos_iff.mpr (hQ_ne z)) (hQ_bound z)
      _ = C_Q * (‖z‖ + 1) ^ (7/4 : ℝ) := Real.log_exp _
  -- Borel-Carathéodory: Re(g) ≤ C_Q(‖z‖+1)^{7/4} ⟹ ‖g‖ ≤ C'(‖z‖+1)^{7/4}
  obtain ⟨C', hC'_pos, hC'_bound⟩ :=
    borel_caratheodory_entire_growth g hg_diff (7/4 : ℝ) C_Q (by norm_num) hC_Q_pos hRe_bound
  exact ⟨g, C', hg_diff, hC'_pos, hg_exp, hC'_bound⟩

/-! ## Wiring: atomic sorrys → Hadamard identity

The three atomic obligations are now assembled into the full Hadamard
factorization identity. The assembly is constructive:

1. From `xi_zeros_enumeration`: get `zeros`, coverage, nonzero, summability.
2. From `xi_quotient_entire_nonvanishing`: get `Q` entire, nonvanishing,
   with `ξ(s) = Q(s) · ∏ E₁(s/ρₙ)`.
3. From `xi_log_quotient_subquadratic`: get `g` entire with
   `exp(g) = Q` and `‖g‖ ≤ C(‖s‖+1)^{7/4}`.
4. From `subquadratic_growth_imp_linear` with α = 7/4 (PROVED): `g(s) = A + B·s`.
5. Therefore `Q(s) = exp(A + Bs)`.
6. At `s = 0`: `exp(A) = Q(0)`, and since `∏ E₁(0/ρₙ) = ∏ 1 = 1`,
   we get `ξ(0) = Q(0) · 1 = exp(A)`, so `Q(s) = ξ(0) · exp(Bs)`.
7. Final: `ξ(s) = ξ(0) · exp(Bs) · ∏ E₁(s/ρₙ)`.
-/

/-- The Hadamard identity holds: `ξ(s) = ξ(0) · exp(Bs) · ∏ₙ E₁(s/ρₙ)`.

Assembled from three atomic sorrys:
- `xi_zeros_enumeration` (zero-density input)
- `xi_quotient_entire_nonvanishing` (removable singularity + nonvanishing)
- `xi_log_quotient_subquadratic` (growth bound on good circles)

plus the proved `entire_three_halves_growth_linear` (subquadratic Liouville).
-/
theorem hadamard_xi_identity_exists :
    ∃ (B : ℂ) (zeros : ℕ → ℂ),
      (∀ n, zeros n ≠ 0) ∧
      Summable (fun n => 1 / ‖zeros n‖ ^ 2) ∧
      (∀ n, RiemannXiAlt (zeros n) = 0) ∧
      (∀ z, (Nat.card {n | zeros n = z} : ℕ∞) = analyticOrderAt RiemannXiAlt z) ∧
      (∀ s, RiemannXiAlt s =
        RiemannXiAlt 0 * exp (B * s) *
          ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) := by
  -- Step 1: Enumerate the zeros (now with hzeros_zero: all entries are actual zeros)
  obtain ⟨zeros, hcover, hne, hzeros_zero, hsum, hmult, hcount⟩ := XiZerosEnumerationHyp.enumeration
  -- Step 2: Form the quotient ξ/P as an entire nonvanishing function (with growth bound)
  obtain ⟨Q, hQ_diff, hQ_ne, hQ_growth, hQ_eq⟩ :=
    xi_quotient_entire_nonvanishing zeros hcover hne hzeros_zero hsum hcount hmult
  -- Step 3: Take log of Q; it has subquadratic growth
  obtain ⟨g, Cg, hg_diff, hCg_pos, hg_exp, hg_growth⟩ :=
    xi_log_quotient_subquadratic Q hQ_diff hQ_ne hQ_growth
  -- Step 4: Liouville — g is linear (PROVED via subquadratic_growth_imp_linear)
  obtain ⟨A, B_lin, hg_linear⟩ :=
    subquadratic_growth_imp_linear g hg_diff (7/4) Cg
      (by norm_num) (by norm_num) hCg_pos hg_growth
  -- Step 5: Q(s) = exp(A + B·s), so ξ(s) = exp(A + B·s) · ∏ E₁(s/ρₙ)
  -- Step 6: At s = 0, E₁(0/ρ) = 1 for all ρ ≠ 0, so ∏ E₁(0/ρₙ) = 1
  --         and ξ(0) = Q(0) · 1 = exp(A), hence exp(A) = ξ(0).
  -- Step 7: ξ(s) = ξ(0) · exp(B·s) · ∏ E₁(s/ρₙ)
  refine ⟨B_lin, zeros, hne, hsum, hzeros_zero, hmult, fun s => ?_⟩
  -- ξ(s) = Q(s) · ∏ E₁(s/ρₙ) [from step 2]
  rw [hQ_eq s]
  -- Q(s) = exp(g(s)) = exp(A + B_lin · s) [from steps 3, 4]
  have hQs : Q s = exp (A + B_lin * s) := by
    rw [← hg_exp s, hg_linear s]
  -- Q(0) = exp(A)
  have hQ0 : Q 0 = exp A := by
    have := hg_linear 0
    simp at this
    rw [← hg_exp 0, this]
  -- ξ(0) = Q(0) · ∏ E₁(0/ρₙ) [from step 2 at s = 0]
  have hxi0 : RiemannXiAlt 0 = Q 0 *
      ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (0 / zeros n) :=
    hQ_eq 0
  -- E₁(0) = (1 - 0) * exp(0) = 1
  have hE1_zero_val : Aristotle.Standalone.HadamardProductConvergence.E1 0 = 1 := by
    simp [Aristotle.Standalone.HadamardProductConvergence.E1]
  -- ∏' E₁(0/ρₙ) = ∏' (fun _ => 1) = 1
  have hprod_zero : ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1
      (0 / zeros n) = 1 := by
    have heq : (fun n => Aristotle.Standalone.HadamardProductConvergence.E1 (0 / zeros n))
        = fun _ => (1 : ℂ) := by
      ext n; simp [zero_div, hE1_zero_val]
    rw [heq]; simp
  -- So ξ(0) = Q(0) = exp(A)
  have hxi0_eq : RiemannXiAlt 0 = exp A := by
    rw [hxi0, hprod_zero, mul_one, hQ0]
  -- Now assemble: Q(s) = exp(A + B·s) = exp(A) · exp(B·s) = ξ(0) · exp(B·s)
  -- Goal: Q s * ∏' ... = RiemannXiAlt 0 * exp(B_lin * s) * ∏' ...
  conv_lhs => rw [hQs, Complex.exp_add, ← hxi0_eq]

/-- From the Hadamard identity, build the convergence input for the
canonical product framework. -/
theorem hadamard_xi_factorization_convergence
    (B : ℂ) (zeros : ℕ → ℂ)
    (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hident : ∀ s, RiemannXiAlt s = RiemannXiAlt 0 * exp (B * s) *
        ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) :
    HadamardXiPartialProductsTendstoHyp B zeros :=
  Aristotle.Standalone.HadamardProductConvergence.hadamard_xi_convergence
    B zeros hne hsum hident

/-! ## Step 2: The factorization yields a HadamardXiCanonicalProductApprox

This is the key result: if we can produce the identity, we can wire it
into the existing typeclass infrastructure.
-/

/-- The Hadamard factorization yields a `HadamardXiCanonicalProductApprox` instance.

Given:
- `B` : the Hadamard constant
- `zeros` : enumeration of zeros
- The identity `ξ(s) = ξ(0) exp(Bs) ∏ E₁(s/ρₙ)`
- Summability of `1/|ρₙ|²`
- Each `ρₙ ≠ 0`

Produces: the full `HadamardXiCanonicalProductApprox` package needed downstream.
-/
def hadamardXiApprox_of_identity
    (B : ℂ) (zeros : ℕ → ℂ)
    (hne : ∀ n, zeros n ≠ 0)
    (hsum : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hident : ∀ s, RiemannXiAlt s = RiemannXiAlt 0 * exp (B * s) *
        ∏' n, Aristotle.Standalone.HadamardProductConvergence.E1 (s / zeros n)) :
    HadamardXiCanonicalProductApprox where
  B := B
  zeros := zeros
  summable_inv_sq := hsum
  zeros_ne_zero := hne
  partialProducts_tendsto :=
    hadamard_xi_factorization_convergence B zeros hne hsum hident

/-! ## Step 3: The sorry-backed master instance

This provides a `HadamardXiCanonicalProductApprox` at priority 1200
(higher than the sorry-backed instance in AnalyticAxioms at default priority).

The sorry is in `hadamard_xi_identity_exists` — the actual content of
Hadamard's theorem. Everything downstream is constructive.
-/

/-- Master Hadamard factorization instance. The single sorry is in
`hadamard_xi_identity_exists` (Hadamard 1893). All wiring from identity
to typeclass is constructive.

We use `Classical.choice` because `HadamardXiCanonicalProductApprox` is
data (a structure), not a Prop, so `Exists.casesOn` cannot eliminate
into it. -/
instance (priority := 1200) hadamardXiApprox_from_factorization :
    HadamardXiCanonicalProductApprox :=
  let B := hadamard_xi_identity_exists.choose
  let zeros := hadamard_xi_identity_exists.choose_spec.choose
  let hprop := hadamard_xi_identity_exists.choose_spec.choose_spec
  hadamardXiApprox_of_identity B zeros hprop.1 hprop.2.1 hprop.2.2.2.2

/-! ## Sub-instances at high priority

These ensure that any file importing this module gets the real-zeros-based
instances for the individual Hadamard components, overriding the fake-zeros
fallbacks in AnalyticAxioms. -/

/-- The real zero sequence from the factorization. -/
private def realZeros : ℕ → ℂ := hadamard_xi_identity_exists.choose_spec.choose

/-- The Hadamard B constant from the factorization. -/
private def realB : ℂ := hadamard_xi_identity_exists.choose

instance (priority := 1200) : HadamardXiCanonicalProductData where
  B := realB
  zeros := realZeros

instance (priority := 1200) : HadamardXiPartialProductsTendsto realB realZeros where
  partialProducts_tendsto := hadamardXiApprox_from_factorization.partialProducts_tendsto

instance (priority := 1200) : HadamardXiFactorCenters realZeros where
  zeros_ne_zero := hadamardXiApprox_from_factorization.zeros_ne_zero

instance (priority := 1200) : HadamardXiSummableInvSq realZeros where
  summable_inv_sq := hadamardXiApprox_from_factorization.summable_inv_sq

/-! ## Bonus: Connection to SubquadraticGrowth

The SubquadraticGrowth theorem from Part A is the key new mathematical
ingredient that makes the factorization work. Here we state the
connection explicitly.
-/

/-- If `g : ℂ → ℂ` is entire with `|g(s)| ≤ C(|s|+1)^{3/2}`, then
`g(s) = A + Bs`. This is the Liouville step in the Hadamard factorization.

The proof applies `subquadratic_growth_imp_linear` with `α = 3/2 < 2`. -/
theorem entire_three_halves_growth_linear (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (C : ℝ) (hC : 0 < C) (hgrowth : SubquadraticGrowth g (3/2) C) :
    ∃ A B : ℂ, ∀ s, g s = A + B * s :=
  subquadratic_growth_imp_linear g hg (3/2) C (by norm_num) (by norm_num) hC hgrowth


end Aristotle.Standalone.HadamardFactorizationWiring

end
