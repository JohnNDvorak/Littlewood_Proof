/-
Landau-Schmidt: identity principle infrastructure for half-planes.

## Main Results

* `zeta_logDeriv_analyticAt_re_gt_one` : ζ'/ζ analytic for Re > 1
* `halfPlane_diff_one_isPreconnected` : {Re > α} \ {1} is preconnected
* `eqOn_of_agree_on_re_gt_one` : Identity principle on half-planes —
    if F, G are analytic on {Re > α} and F = G on {Re > 1}, then F = G on {Re > α}

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ZetaLogDerivPole
import Littlewood.Aristotle.HalfPlaneConnected
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Analytic.Uniqueness

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Aristotle.LandauDirichletIntegral

open Complex Set Filter Topology Bornology

/-! ## Analyticity of ζ'/ζ on {Re > 1} -/

/-- ζ'/ζ is analytic at any s with Re(s) > 1. -/
theorem zeta_logDeriv_analyticAt_re_gt_one (s : ℂ) (hs : 1 < s.re) :
    AnalyticAt ℂ (fun z => deriv riemannZeta z / riemannZeta z) s := by
  have hs_ne : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hs_nz : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by linarith : 1 ≤ s.re)
  exact (ZetaLogDerivPole.zeta_analyticAt s hs_ne).deriv.div
    (ZetaLogDerivPole.zeta_analyticAt s hs_ne) hs_nz

/-- ζ'/ζ is AnalyticOnNhd on {Re > 1}. -/
theorem zeta_logDeriv_analyticOnNhd_re_gt_one :
    AnalyticOnNhd ℂ (fun z => deriv riemannZeta z / riemannZeta z)
      {s : ℂ | 1 < s.re} :=
  fun s hs => zeta_logDeriv_analyticAt_re_gt_one s hs

/-! ## Preconnectedness -/

/-- {s : ℂ | α < s.re} \ {1} is preconnected. This is the key geometric
fact for the identity principle in the Landau argument. -/
theorem halfPlane_diff_one_isPreconnected (α : ℝ) :
    IsPreconnected ({s : ℂ | α < s.re} \ {(1 : ℂ)}) :=
  HalfPlaneConnected.halfPlane_diff_singleton_isPreconnected α 1

/-! ## Identity principle on half-planes -/

/-- **Identity principle for half-planes**: If F and G are both analytic on
{Re > α} (α < 1) and agree on {Re > 1}, then they agree on all of {Re > α}.

This uses the Mathlib identity principle `eqOn_of_preconnected_of_eventuallyEq`
applied to the convex (hence preconnected) set {Re > α}. -/
theorem eqOn_of_agree_on_re_gt_one
    (α : ℝ) (hα : α < 1)
    (F G : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {s : ℂ | α < s.re})
    (hG : AnalyticOnNhd ℂ G {s : ℂ | α < s.re})
    (h_eq : ∀ s : ℂ, 1 < s.re → F s = G s) :
    EqOn F G {s : ℂ | α < s.re} := by
  -- Pick z₀ with Re > 1 as the base point for identity principle
  set z₀ : ℂ := ⟨2, 0⟩
  have hz₀ : z₀ ∈ {s : ℂ | α < s.re} := by
    simp only [mem_setOf_eq]; show α < (2 : ℝ); linarith
  -- F = G in a neighborhood of z₀ (since {Re > 1} is open and z₀ ∈ it)
  have hfg_ev : F =ᶠ[𝓝 z₀] G := by
    have h_open : IsOpen {s : ℂ | (1 : ℝ) < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hz₀_mem : z₀ ∈ {s : ℂ | (1 : ℝ) < s.re} := by
      simp only [mem_setOf_eq]; norm_num
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{s : ℂ | 1 < s.re}, h_open.mem_nhds hz₀_mem, fun s hs => h_eq s hs⟩
  -- {Re > α} is preconnected (convex)
  have h_preconn : IsPreconnected {s : ℂ | α < s.re} := by
    have hconv : Convex ℝ {s : ℂ | α < s.re} := by
      have : {s : ℂ | α < s.re} = Complex.reCLM ⁻¹' Ioi α := by
        ext s; simp [Complex.reCLM_apply]
      rw [this]
      exact (convex_Ioi α).linear_preimage Complex.reCLM.toLinearMap
    exact hconv.isPreconnected
  -- Apply identity principle
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG h_preconn hz₀ hfg_ev

end Aristotle.LandauDirichletIntegral
