import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aPerron

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton

/-- Algebraic Perron-remainder transfer.

If a Perron model `perronIntegralRe` approximates `chebyshevPsi` with `(log x)^2`
error and decomposes as `x - zeroSumRe + contourRemainderRe`, then
`shiftedRemainderRe - contourRemainderRe` has the same `(log x)^2` bound.
-/
theorem perron_truncation_error
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
  rcases hPerron with ⟨Cₚ, hCₚ_pos, hCₚ⟩
  refine ⟨Cₚ, hCₚ_pos, ?_⟩
  intro x T hx hT
  have hres := hResidue x T hx hT
  have hrewrite :
      shiftedRemainderRe x T - contourRemainderRe x T =
        Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T := by
    unfold shiftedRemainderRe
    rw [hres]
    ring
  rw [hrewrite]
  exact hCₚ x T hx hT

end Aristotle.Standalone.ExplicitFormulaPsiB5aPerron
