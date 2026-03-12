import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGrowthCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTReciprocalLogCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeHolomorphicCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeRectangleBoundCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTZetaRectangleBoundCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivSeriesCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTAnalyticRefactorBundle

open Complex
open Filter
open scoped Real
open Aristotle.Standalone.ExternalPort.StrongPNTGrowthCompat
open Aristotle.Standalone.ExternalPort.StrongPNTReciprocalLogCompat
open Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat
open Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeHolomorphicCompat
open Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeRectangleBoundCompat
open Aristotle.Standalone.ExternalPort.StrongPNTZetaRectangleBoundCompat
open Aristotle.Standalone.ExternalPort.StrongPNTLogDerivSeriesCompat
open Aristotle.Standalone.ExternalPort.StrongPNTLogDerivCompat

/-- Lean-4.27 refactor surface for the remaining StrongPNT analytic helper lane.
This payload aggregates growth, reciprocal-log, holomorphic/rectangle bounds,
Dirichlet-series line identities, and local meromorphic log-derivative facts. -/
structure StrongPNTAnalyticRefactorPayload : Type where
  logPowNatLeConstMul :
    ∀ (X₀ : ℝ), 0 < X₀ → ∀ k : ℕ,
      ∃ C ≥ (1 : ℝ), ∀ X : ℝ, X ≥ X₀ → Real.log X ^ k ≤ C * X
  logPowNatEventuallyLinear :
    ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ X in atTop, Real.log X ^ k ≤ C * X
  normReciprocalInequalityPos :
    ∀ (x x₁ : ℝ), x₁ ≥ 1 →
      ‖x ^ 2 + x₁ ^ 2‖₊⁻¹ ≤ (‖x₁‖₊ ^ 2)⁻¹
  normReciprocalInequalityNeg :
    ∀ (x x₁ : ℝ), x₁ ≤ -1 →
      ‖x ^ 2 + x₁ ^ 2‖₊⁻¹ ≤ (‖x₁‖₊ ^ 2)⁻¹
  oneAddInvLog :
    ∀ {X : ℝ}, 3 ≤ X → (1 + (Real.log X)⁻¹) < 2
  logPos :
    ∀ (T : ℝ), 3 < T → Real.log T > 1
  bddAboveNormImageRectangleOfHolomorphicOn :
    ∀ {g : ℂ → ℂ} {z w : ℂ},
      DifferentiableOn ℂ g (z.Rectangle w) →
      BddAbove (norm ∘ g '' (z.Rectangle w))
  differentiableOnLogDeriv :
    ∀ {U : Set ℂ}, IsOpen U → ∀ {f : ℂ → ℂ},
      DifferentiableOn ℂ f U →
      (∀ z ∈ U, f z ≠ 0) →
      DifferentiableOn ℂ
        (Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeHolomorphicCompat.logDeriv f)
        U
  differentiableOnNegLogDerivRiemannZetaReGtOne :
    DifferentiableOn ℂ (fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
      {s : ℂ | 1 < s.re}
  existsNormNegLogDerivBoundOnRectangleOfReGtOne :
    ∀ {z w : ℂ}, z.Rectangle w ⊆ {s : ℂ | 1 < s.re} →
      ∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖-deriv riemannZeta s / riemannZeta s‖ ≤ B
  existsNormRiemannZetaBoundOnRectangleOfReGtOne :
    ∀ {z w : ℂ}, z.Rectangle w ⊆ {s : ℂ | 1 < s.re} →
      ∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖riemannZeta s‖ ≤ B
  existsNormInvRiemannZetaBoundOnRectangleOfReGtOne :
    ∀ {z w : ℂ}, z.Rectangle w ⊆ {s : ℂ | 1 < s.re} →
      ∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖(riemannZeta s)⁻¹‖ ≤ B
  negLogDerivRiemannZetaReEqTsumReOnLine :
    ∀ {σ t : ℝ}, 1 < σ →
      (-deriv riemannZeta (σ + t * Complex.I) /
          riemannZeta (σ + t * Complex.I)).re =
        ∑' n : ℕ,
          (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (σ + t * Complex.I) n).re
  absReNegLogDerivRiemannZetaOnLineLeNorm :
    ∀ (σ t : ℝ),
      |(-deriv riemannZeta (σ + t * Complex.I) /
          riemannZeta (σ + t * Complex.I)).re| ≤
        ‖-deriv riemannZeta (σ + t * Complex.I) /
          riemannZeta (σ + t * Complex.I)‖
  zetaLogDerivMeromorphicAt :
    ∀ (ρ₀ : ℂ), ρ₀ ≠ 1 →
      MeromorphicAt (fun s => deriv riemannZeta s / riemannZeta s) ρ₀
  zetaLogDerivMeromorphicOrderNeg :
    ∀ (ρ₀ : ℂ), ρ₀ ≠ 1 → riemannZeta ρ₀ = 0 →
      meromorphicOrderAt (fun s => deriv riemannZeta s / riemannZeta s) ρ₀ < 0
  zetaLogDerivTendstoCobounded :
    ∀ (ρ₀ : ℂ), ρ₀ ≠ 1 → riemannZeta ρ₀ = 0 →
      Tendsto (fun s => deriv riemannZeta s / riemannZeta s)
        (nhdsWithin ρ₀ (({ρ₀} : Set ℂ)ᶜ))
        (Bornology.cobounded ℂ)

/-- Canonical payload assembled from the current compat theorem family. -/
def fromCompat : StrongPNTAnalyticRefactorPayload where
  logPowNatLeConstMul := by
    intro X₀ hX₀ k
    exact log_pow_nat_le_const_mul_port X₀ hX₀ k
  logPowNatEventuallyLinear := by
    intro k
    exact log_pow_nat_eventually_linear_port k
  normReciprocalInequalityPos := by
    intro x x₁ hx₁
    exact norm_reciprocal_inequality_1 x x₁ hx₁
  normReciprocalInequalityNeg := by
    intro x x₁ hx₁
    exact norm_reciprocal_inequality x x₁ hx₁
  oneAddInvLog := by
    intro X hX
    exact one_add_inv_log hX
  logPos := by
    intro T hT
    exact StrongPNTReciprocalLogCompat.log_pos T hT
  bddAboveNormImageRectangleOfHolomorphicOn := by
    intro g z w hDiff
    exact bddAbove_norm_image_rectangle_of_holomorphicOn hDiff
  differentiableOnLogDeriv := by
    intro U hU_open f hf hf_ne
    exact differentiableOn_logDeriv hU_open hf hf_ne
  differentiableOnNegLogDerivRiemannZetaReGtOne :=
    differentiableOn_neg_logDeriv_riemannZeta_re_gt_one
  existsNormNegLogDerivBoundOnRectangleOfReGtOne := by
    intro z w hRect
    exact exists_norm_neg_logDeriv_bound_on_rectangle_of_re_gt_one hRect
  existsNormRiemannZetaBoundOnRectangleOfReGtOne := by
    intro z w hRect
    exact exists_norm_riemannZeta_bound_on_rectangle_of_re_gt_one hRect
  existsNormInvRiemannZetaBoundOnRectangleOfReGtOne := by
    intro z w hRect
    exact exists_norm_inv_riemannZeta_bound_on_rectangle_of_re_gt_one hRect
  negLogDerivRiemannZetaReEqTsumReOnLine := by
    intro σ t hσ
    exact neg_logDeriv_riemannZeta_re_eq_tsum_re_on_line hσ
  absReNegLogDerivRiemannZetaOnLineLeNorm := by
    intro σ t
    exact abs_re_neg_logDeriv_riemannZeta_on_line_le_norm σ t
  zetaLogDerivMeromorphicAt := by
    intro ρ₀ hne
    exact zeta_logDeriv_meromorphicAt_port ρ₀ hne
  zetaLogDerivMeromorphicOrderNeg := by
    intro ρ₀ hne hz
    exact zeta_logDeriv_meromorphicOrder_neg_port ρ₀ hne hz
  zetaLogDerivTendstoCobounded := by
    intro ρ₀ hne hz
    exact zeta_logDeriv_tendsto_cobounded_port ρ₀ hne hz

/-- Rectangle-bound endpoint for `ζ` and `1/ζ` from one refactored analytic
payload. -/
theorem zeta_and_inv_bounds_on_rectangle_of_re_gt_one_of_refactored_payload
    (hPayload : StrongPNTAnalyticRefactorPayload)
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    (∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖riemannZeta s‖ ≤ B) ∧
      (∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖(riemannZeta s)⁻¹‖ ≤ B) := by
  exact
    ⟨hPayload.existsNormRiemannZetaBoundOnRectangleOfReGtOne hRect,
      hPayload.existsNormInvRiemannZetaBoundOnRectangleOfReGtOne hRect⟩

/-- Line-series endpoint for the real part of `-ζ'/ζ` from one refactored
analytic payload. -/
theorem neg_logDeriv_riemannZeta_re_series_on_line_of_refactored_payload
    (hPayload : StrongPNTAnalyticRefactorPayload)
    {σ t : ℝ}
    (hσ : 1 < σ) :
    (-deriv riemannZeta (σ + t * Complex.I) /
        riemannZeta (σ + t * Complex.I)).re =
      ∑' n : ℕ,
        (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ + t * Complex.I) n).re := by
  exact hPayload.negLogDerivRiemannZetaReEqTsumReOnLine hσ

/-- Local meromorphic-growth endpoint for `ζ'/ζ` at a nontrivial zeta zero from
one refactored analytic payload. -/
theorem zeta_logDeriv_tendsto_cobounded_of_refactored_payload
    (hPayload : StrongPNTAnalyticRefactorPayload)
    (ρ₀ : ℂ) (hne : ρ₀ ≠ 1) (hz : riemannZeta ρ₀ = 0) :
    Tendsto (fun s => deriv riemannZeta s / riemannZeta s)
      (nhdsWithin ρ₀ (({ρ₀} : Set ℂ)ᶜ))
      (Bornology.cobounded ℂ) := by
  exact hPayload.zetaLogDerivTendstoCobounded ρ₀ hne hz

end Aristotle.Standalone.ExternalPort.StrongPNTAnalyticRefactorBundle
