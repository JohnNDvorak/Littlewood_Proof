/-
Bridge for the Hardy Z first moment bound: |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2}.

This isolates the O(T^{1/2}) first moment bound for the Hardy Z function
to a single sorry, replacing the previous sorry in `mainTerm_first_moment_ibp`
(RSExpansionProof.lean).

The mathematical content is Titchmarsh 1951 §4.15: integration by parts on
Z(t) = Re(e^{iθ(t)} ζ(½+it)) using the monotone phase θ(t), with:
  - Boundary terms O(|ζ(½+iT)|/θ'(T)) = O(T^{1/6}/log T) = O(T^{1/2})
  - Correction integral involving d/dt[ζ/(iθ')] controlled by convexity

The sub-lemmas (boundary bound, correction integrand bound, mode sum estimates)
are proved in HardyZFirstMomentIBP.lean. The assembly into the final O(T^{1/2})
bound requires the actual IBP computation on ∫ Z, which is blocked by
the import cycle (HardyZFirstMomentIBP imports RSExpansionProof).

Breaking the import cycle and completing the assembly will close this sorry.

Reference: Titchmarsh 1951 §4.15; Ingham 1932 §5.2.
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace Aristotle.Standalone.HardyZFirstMomentBridge

/-- **Hardy Z first moment O(√T) bridge**.

    |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2} for all T ≥ 2.

    This is the classical result of Titchmarsh (1951, §4.15).
    The proof requires integration by parts on the oscillatory integral
    ∫ Re(e^{iθ(t)} ζ(½+it)) dt with the monotone phase θ(t).

    SORRY: Assembly of IBP sub-lemmas into final bound.
    All ingredients are proved in HardyZFirstMomentIBP.lean:
    - ibp_boundary_both_endpoints_le_sqrt (boundary terms O(√T))
    - ibp_correction_integrand_bound (correction O(t^{3/4}/log t))
    - per-mode VdC infrastructure (OffResonanceSmoothVdC)
    - mode sum estimates (AbelSummationPsiPi)
    Closing requires: breaking the HardyZFirstMomentIBP ↔ RSExpansionProof
    import cycle, then assembling the IBP computation. -/
theorem hardyZ_first_moment_sqrt :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, HardyEstimatesPartial.hardyZ t| ≤ C * T ^ ((1 : ℝ) / 2) := by
  sorry

end Aristotle.Standalone.HardyZFirstMomentBridge
