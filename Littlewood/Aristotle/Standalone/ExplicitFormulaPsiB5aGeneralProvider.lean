import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aGeneralProvider

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton

variable [Littlewood.Development.ShiftedRemainderInterface.ShiftedRemainderSegmentBoundLargeTHyp]
variable [Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp]

/-- B5a-only provider endpoint for the truncated explicit formula bound used by
`ExplicitFormulaPsiSkeleton`.

This module intentionally avoids the full Perron/RH-pi provider lane so the
`LittlewoodPsi` path can depend on a localized B5a endpoint only. The intended
constructive implementation is the same shifted-remainder theorem previously
re-exported through `PerronExplicitFormulaProvider.general_explicit_formula_from_perron`. -/
private theorem general_explicit_formula_from_perron_proof :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact ContourRemainderBoundHyp.bound

/-- B5a-only provider endpoint matching the theorem surface used by
`ExplicitFormulaPsiSkeleton`. -/
theorem general_explicit_formula_from_perron :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) :=
  general_explicit_formula_from_perron_proof

end Aristotle.Standalone.ExplicitFormulaPsiB5aGeneralProvider
