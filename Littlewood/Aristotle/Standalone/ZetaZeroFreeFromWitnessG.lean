/-
Proof that witnessG analytic on {Re > α'} implies zrf has no zeros there.

This is the Landau zero-free argument. The proof has three parts:
1. Algebraic identity: φ·zrf = σ·zrf' on {Re > 1} (from witnessG_eq_formula + corrected_logDeriv_eq)
2. Identity theorem: extend to {Re > α'}
3. Order contradiction: if zrf(s₀) = 0, analyticOrderAt gives impossible equation

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ZetaPoleCancellation
import Littlewood.Aristotle.Standalone.SigmaLtOneFromPringsheimExtension
import Littlewood.Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.ZetaZeroFreeFromWitnessG

open Complex Filter Topology Set
open Aristotle.ZetaPoleCancellation
open Aristotle.PringsheimPsiAtom

private abbrev U (α' : ℝ) := {s : ℂ | α' < s.re}

/-- The corrected function φ(s) = witnessG(s) - s·C'/(s-α') - σ. -/
private abbrev φ (C' α' σ_sign : ℝ) (s : ℂ) : ℂ :=
  witnessG C' α' σ_sign s - s * (↑C' : ℂ) / (s - (↑α' : ℂ)) - (↑σ_sign : ℂ)

/-- The key function k(s) = φ(s)·zrf(s) - σ·zrf'(s). -/
private abbrev k (C' α' σ_sign : ℝ) (s : ℂ) : ℂ :=
  φ C' α' σ_sign s * zrf s - (↑σ_sign : ℂ) * deriv zrf s

/-- Helper: s - α' ≠ 0 when α' < s.re. -/
private lemma sub_ofReal_ne_zero {α' : ℝ} {s : ℂ} (hs : α' < s.re) :
    s - (↑α' : ℂ) ≠ 0 := by
  intro h
  have := congr_arg re h
  simp only [sub_re, ofReal_re, zero_re] at this
  linarith

/-- k is analytic on U. -/
private lemma k_analyticOnNhd (α' : ℝ) (C' : ℝ) (σ_sign : ℝ)
    (h_anal : AnalyticOnNhd ℂ (witnessG C' α' σ_sign) (U α')) :
    AnalyticOnNhd ℂ (k C' α' σ_sign) (U α') := by
  intro s hs
  have hsα := sub_ofReal_ne_zero hs
  exact ((((h_anal s hs).sub
    ((analyticAt_id.mul analyticAt_const).div
      (analyticAt_id.sub analyticAt_const) hsα)).sub analyticAt_const).mul
    (zrf_analyticAt s)).sub (analyticAt_const.mul (zrf_analyticAt s).deriv)

/-- σ_sign ≠ 0 as a complex number. -/
private lemma σ_ne_zero (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1) :
    (↑σ_sign : ℂ) ≠ 0 := by
  rcases hσ with rfl | rfl <;> simp

/-- k = 0 on {Re > 1}. The key algebraic identity. -/
private lemma k_eq_zero_of_one_lt_re
    (α' : ℝ) (hα' : 1 / 2 < α') (hα'1 : α' < 1)
    (C' : ℝ) (hC' : 0 < C')
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C' * x ^ α')
    (s : ℂ) (hs : 1 < s.re) :
    k C' α' σ_sign s = 0 := by
  have hs1 : s ≠ 1 := by
    intro h; subst h; simp only [one_re] at hs; linarith
  have hα's : α' < s.re := by linarith
  have h_zrf_ne : zrf s ≠ 0 := by
    rw [zrf_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1)
      (riemannZeta_ne_zero_of_one_le_re (by linarith))
  -- Get the two key identities
  have h_wG := witnessG_eq_formula C' hC' α' hα' σ_sign hσ hbound s hs hα's
  have h_corr := corrected_logDeriv_eq hs1 h_zrf_ne
  -- Step 1: Show φ(s) = σ · (zrf'/zrf)
  have h_φ : φ C' α' σ_sign s = ↑σ_sign * (deriv zrf s / zrf s) := by
    simp only [φ]
    rw [h_wG]
    -- Cancel s*C'/(s-α') terms (a + b + c - a - d = b + c - d)
    have cancel : s * ↑C' / (s - ↑α') + ↑σ_sign * (s / (s - 1)) +
        ↑σ_sign * (deriv riemannZeta s / riemannZeta s) - s * ↑C' / (s - ↑α') - ↑σ_sign =
        ↑σ_sign * (s / (s - 1)) + ↑σ_sign * (deriv riemannZeta s / riemannZeta s) - ↑σ_sign := by
      abel
    rw [cancel]
    -- Factor out σ_sign: σ*A + σ*B = σ*(A+B)
    rw [show ↑σ_sign * (s / (s - 1)) + ↑σ_sign * (deriv riemannZeta s / riemannZeta s) =
        ↑σ_sign * (s / (s - 1) + deriv riemannZeta s / riemannZeta s) from by ring]
    -- Use corrected_logDeriv_eq: 1 + zrf'/zrf = s/(s-1) + ζ'/ζ
    rw [← h_corr]
    -- Goal: σ * (1 + zrf'/zrf) - σ = σ * (zrf'/zrf)
    rw [mul_add, mul_one]
    -- Goal: σ + σ * (zrf'/zrf) - σ = σ * (zrf'/zrf)
    abel
  -- Step 2: k = φ*zrf - σ*zrf' = (σ*zrf'/zrf)*zrf - σ*zrf' = σ*zrf' - σ*zrf' = 0
  simp only [k]
  rw [h_φ, mul_assoc, div_mul_cancel₀ (deriv zrf s) h_zrf_ne, sub_self]

/-- k = 0 on all of U (by identity theorem). -/
private lemma k_eqOn_zero
    (α' : ℝ) (hα' : 1 / 2 < α') (hα'1 : α' < 1)
    (C' : ℝ) (hC' : 0 < C')
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C' * x ^ α')
    (h_anal : AnalyticOnNhd ℂ (witnessG C' α' σ_sign) {s : ℂ | α' < s.re}) :
    EqOn (k C' α' σ_sign) 0 (U α') := by
  have h2_in_U : (2 : ℂ) ∈ U α' := by
    show α' < (2 : ℂ).re; norm_num; linarith
  have hk_eventuallyZero : k C' α' σ_sign =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have h_open_half : IsOpen {s : ℂ | 1 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h2_in_half : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
      show 1 < (2 : ℂ).re; norm_num
    filter_upwards [h_open_half.mem_nhds h2_in_half] with s hs
    exact k_eq_zero_of_one_lt_re α' hα' hα'1 C' hC' σ_sign hσ hbound s hs
  exact (k_analyticOnNhd α' C' σ_sign h_anal).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt α').isPreconnected h2_in_U hk_eventuallyZero

/-- φ is analytic at any point of U. -/
private lemma φ_analyticAt {α' : ℝ} {C' σ_sign : ℝ} {s : ℂ}
    (h_anal : AnalyticOnNhd ℂ (witnessG C' α' σ_sign) (U α')) (hs : α' < s.re) :
    AnalyticAt ℂ (φ C' α' σ_sign) s := by
  have hsα := sub_ofReal_ne_zero hs
  show AnalyticAt ℂ (fun z =>
    witnessG C' α' σ_sign z - z * ↑C' / (z - ↑α') - ↑σ_sign) s
  exact ((h_anal s hs).sub
    ((analyticAt_id.mul analyticAt_const).div
      (analyticAt_id.sub analyticAt_const) hsα)).sub analyticAt_const

/-- Main theorem: zrf has no zeros on {Re > α'}. -/
theorem zrf_ne_zero_of_witnessG_analytic'
    (α' : ℝ) (hα' : 1 / 2 < α') (hα'1 : α' < 1)
    (C' : ℝ) (hC' : 0 < C')
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C' * x ^ α')
    (h_anal : AnalyticOnNhd ℂ (witnessG C' α' σ_sign) {s : ℂ | α' < s.re}) :
    ∀ s : ℂ, α' < s.re → zrf s ≠ 0 := by
  intro s hs h_zrf_zero
  -- k(s) = 0 (from identity theorem)
  have hk_zero := k_eqOn_zero α' hα' hα'1 C' hC' σ_sign hσ hbound h_anal hs
  simp only [k, Pi.zero_apply] at hk_zero
  -- From k(s) = 0 and zrf(s) = 0: σ·deriv(zrf)(s) = 0
  rw [h_zrf_zero, mul_zero, zero_sub, neg_eq_zero] at hk_zero
  -- σ ≠ 0, so deriv(zrf)(s) = 0
  have h_deriv_zero : deriv zrf s = 0 := by
    rcases mul_eq_zero.mp hk_zero with h | h
    · exact absurd h (σ_ne_zero σ_sign hσ)
    · exact h
  -- Case analysis: zrf ≡ 0 near s, or isolated zero
  have h_zrf_anal := zrf_analyticAt s
  rcases h_zrf_anal.eventually_eq_zero_or_eventually_ne_zero with h_zero | h_ne_zero
  · -- Case: zrf ≡ 0 near s → zrf ≡ 0 on U → zrf(1) = 1, contradiction
    have h_zrf_analU : AnalyticOnNhd ℂ zrf (U α') := fun z _ => zrf_analyticAt z
    have h_zrfU := h_zrf_analU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt α').isPreconnected hs h_zero
    have h1_in_U : (1 : ℂ) ∈ U α' := by
      show α' < (1 : ℂ).re; simp only [one_re]; exact hα'1
    have h_zrf1 := h_zrfU h1_in_U
    -- h_zrf1 : zrf 1 = (0 : ℂ → ℂ) 1
    rw [Pi.zero_apply, zrf_one] at h_zrf1
    exact one_ne_zero h_zrf1
  · -- Case: zrf has isolated zero at s
    -- h_ne_zero : ∀ᶠ z in 𝓝[≠] s, zrf z ≠ 0
    -- analyticOrderAt zrf s ≠ ⊤ (zrf is not identically 0 near s)
    have h_ord_ne_top : analyticOrderAt zrf s ≠ ⊤ := by
      intro h_eq_top
      rw [analyticOrderAt_eq_top] at h_eq_top
      have h1 : ∀ᶠ z in 𝓝[≠] s, zrf z = 0 := h_eq_top.filter_mono nhdsWithin_le_nhds
      have h2 : ∀ᶠ z in 𝓝[≠] s, False := h1.and h_ne_zero |>.mono fun z ⟨h, h'⟩ => h' h
      exact absurd (Filter.eventually_false_iff_eq_bot.mp h2) (Filter.NeBot.ne inferInstance)
    -- analyticOrderAt zrf s ≠ 0 (since zrf s = 0)
    have h_ord_ne_zero : analyticOrderAt zrf s ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨h_zrf_anal, h_zrf_zero⟩
    -- φ is analytic at s
    have h_φ_anal : AnalyticAt ℂ (φ C' α' σ_sign) s := φ_analyticAt h_anal hs
    -- From k ≡ 0 on U: φ * zrf =ᶠ[𝓝 s] σ * deriv(zrf)
    have h_eq_near : (fun z => φ C' α' σ_sign z * zrf z) =ᶠ[𝓝 s]
        (fun z => (↑σ_sign : ℂ) * deriv zrf z) := by
      have hU_nhd : U α' ∈ 𝓝 s :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
      filter_upwards [hU_nhd] with z hz
      have h := k_eqOn_zero α' hα' hα'1 C' hC' σ_sign hσ hbound h_anal hz
      simp only [k, Pi.zero_apply] at h
      exact sub_eq_zero.mp h
    -- Orders of both sides agree
    have h_ord_eq := analyticOrderAt_congr h_eq_near
    -- LHS order: ord(φ) + ord(zrf) by analyticOrderAt_mul
    have h_lhs := analyticOrderAt_mul h_φ_anal h_zrf_anal
    -- RHS order: ord(const σ * deriv zrf) = ord(const σ) + ord(deriv zrf)
    have h_rhs : analyticOrderAt (fun z => (↑σ_sign : ℂ) * deriv zrf z) s =
        analyticOrderAt (fun (_ : ℂ) => (↑σ_sign : ℂ)) s + analyticOrderAt (deriv zrf) s :=
      analyticOrderAt_mul analyticAt_const h_zrf_anal.deriv
    -- ord(const σ) = 0 since σ ≠ 0
    have h_const_ord : analyticOrderAt (fun (_ : ℂ) => (↑σ_sign : ℂ)) s = 0 :=
      analyticAt_const.analyticOrderAt_eq_zero.mpr (σ_ne_zero σ_sign hσ)
    -- Derivative order: ord(deriv zrf, s) + 1 = ord(zrf, s) (using zrf(s) = 0)
    have h_deriv_ord : analyticOrderAt (deriv zrf) s + 1 = analyticOrderAt zrf s := by
      have h := h_zrf_anal.analyticOrderAt_deriv_add_one
      -- h : analyticOrderAt (deriv zrf) s + 1 = analyticOrderAt (zrf · - zrf s) s
      -- Since zrf s = 0: zrf · - zrf s = zrf
      rw [h_zrf_zero] at h
      simpa using h
    -- Combine: ord(φ) + ord(zrf) + 1 = ord(zrf), which is impossible
    have h_am_eq_d : analyticOrderAt (φ C' α' σ_sign) s + analyticOrderAt zrf s =
        analyticOrderAt (deriv zrf) s := by
      have := h_ord_eq.trans h_rhs
      rw [h_const_ord, zero_add] at this
      exact h_lhs.symm.trans this
    have h_key : analyticOrderAt (φ C' α' σ_sign) s + analyticOrderAt zrf s + 1 =
        analyticOrderAt zrf s := by rw [h_am_eq_d, h_deriv_ord]
    -- Contradiction via ℕ∞ arithmetic
    rcases eq_or_ne (analyticOrderAt (φ C' α' σ_sign) s) ⊤ with ha_top | ha_ne_top
    · -- ord(φ) = ⊤: ⊤ + m + 1 = ⊤ ≠ m
      simp only [ha_top, top_add] at h_key
      exact h_ord_ne_top h_key.symm
    · -- Both finite: extract ℕ witnesses and use omega
      have hn : analyticOrderAt zrf s = ↑(analyticOrderAt zrf s).toNat :=
        (ENat.coe_toNat h_ord_ne_top).symm
      have hp : analyticOrderAt (φ C' α' σ_sign) s =
          ↑(analyticOrderAt (φ C' α' σ_sign) s).toNat :=
        (ENat.coe_toNat ha_ne_top).symm
      rw [hn, hp] at h_key
      norm_cast at h_key
      omega

end Aristotle.Standalone.ZetaZeroFreeFromWitnessG
