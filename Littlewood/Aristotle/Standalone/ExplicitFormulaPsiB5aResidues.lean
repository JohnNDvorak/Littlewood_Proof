import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aResidues

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton

/-- Residue-extraction normal form for the shifted remainder.

From a decomposition
`perronIntegralRe = x - zeroSumRe + contourRemainderRe`, we obtain
`shiftedRemainderRe = (chebyshevPsi - perronIntegralRe) + contourRemainderRe`.
-/
theorem residue_extraction
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T) :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      shiftedRemainderRe x T =
        (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T) +
          contourRemainderRe x T := by
  intro x T hx hT
  have hres := hResidue x T hx hT
  unfold shiftedRemainderRe
  rw [hres]
  ring

end Aristotle.Standalone.ExplicitFormulaPsiB5aResidues
