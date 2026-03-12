import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aPerron
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogFromComponents

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourCompat

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aPerron
open Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds
open Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogFromComponents
open Aristotle.DirichletPhaseAlignment (ZerosBelow)

/-- External-port adapter endpoint for Perron transfer (`contourPull`/`residuePull`
style step). -/
theorem perron_truncation_error_port
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerron :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * (Real.log x) ^ 2)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T) :
    ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T - contourRemainderRe x T| ≤
        Cₚ * (Real.log x) ^ 2 := by
  exact perron_truncation_error perronIntegralRe contourRemainderRe hPerron hResidue

/-- External-port adapter endpoint for contour-box evaluation combination
(`ZetaBoxEval`/`I_kBound` style aggregation). -/
theorem contour_remainder_bound_port
    (contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerron :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |shiftedRemainderRe x T - contourRemainderRe x T| ≤
          Cₚ * (Real.log x) ^ 2)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact contour_remainder_bound contourRemainderRe hPerron hContour

/-- External-port adapter endpoint for the full B5a component combiner
(`SmoothedChebyshevPull` style endpoint). -/
theorem shifted_contours_bound_of_components_port
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerronRaw :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * (Real.log x) ^ 2)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_contours_bound_of_components
    perronIntegralRe contourRemainderRe hPerronRaw hResidue hContour

/-- External-port adapter endpoint in the legacy linear-log witness shape. -/
theorem legacy_linear_log_bound_of_components_exact_port
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerron :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * Real.log x)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * Real.log T / Real.sqrt T)) :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
  exact
    legacy_linear_log_bound_of_components_exact
      perronIntegralRe contourRemainderRe hPerron hResidue hContour

end Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourCompat

