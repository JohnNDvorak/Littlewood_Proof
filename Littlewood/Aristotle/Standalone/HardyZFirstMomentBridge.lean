/-
Bridge for the Hardy Z first moment bound: |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2}.

This isolates the O(T^{1/2}) first moment bound for the Hardy Z function
to a single sorry. The import cycle (IBP ↔ RSExpansionProof) has been broken:
IBP now imports this bridge directly.

## Mathematical content (Titchmarsh 1951 §4.15)

Z(t) = MainTerm(t) + ErrorTerm(t) where
  MainTerm = 2·∑_{n ≤ N(t)} (n+1)^{-1/2} · cos(θ(t) - t·log(n+1))
  ErrorTerm = Z - MainTerm  (Riemann-Siegel remainder)

|∫₁ᵀ Z| ≤ |∫₁ᵀ MainTerm| + |∫₁ᵀ ErrorTerm|

(A) ErrorTerm: O(√T) by alternating block cancellation.
    Requires: Siegel saddle-point expansion (SiegelSaddleExpansionHyp sorry)
              + Gabcke phase coupling (GabckePhaseCouplingHyp sorry).
    Infrastructure: signed_block_integral_nonneg, error_term_first_moment_assembly.
    STATUS: Proved in RSExpansionProof.errorTerm_first_moment_sqrt, but that
    file imports THIS bridge, so we cannot use it here.

(B) MainTerm: O(√T) by per-mode VdC on the Dirichlet polynomial.
    Each mode n has oscillatory integral bounded by C_vdc/log((k+1)/(n+1))
    per block. Sum over modes + blocks gives O(√T).
    Infrastructure: off_resonance_integral_bound_smooth (OffResonanceSmoothVdC),
    block_sum_assembly (IBP Part 7), Abel summation.
    STATUS: Sub-lemmas proved, final assembly not done.

## Closing strategy

Extract ErrorTerm first moment infrastructure from RSExpansionProof into
a standalone file (no bridge dependency), then import here. Then assemble
the MainTerm bound from the per-mode VdC infrastructure.

## Dependency note (2026-03-16)

This sorry is NOT irreducible: it follows from the two Siegel/Gabcke sorrys
(SiegelSaddleExpansionHyp, GabckePhaseCouplingHyp) plus the per-mode VdC
infrastructure. The sorry exists because the proof assembly requires code
currently in RSExpansionProof (which imports this file, creating a cycle).

Reference: Titchmarsh 1951 §4.15; Ingham 1932 §5.2.
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace Aristotle.Standalone.HardyZFirstMomentBridge

open HardyEstimatesPartial

/-- **Hardy Z first moment O(√T) bridge**.

    |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2} for all T ≥ 2.

    This is the classical result of Titchmarsh (1951, §4.15).

    SORRY STATUS: Derived from SiegelSaddleExpansionHyp + GabckePhaseCouplingHyp
    sorrys + per-mode VdC assembly. Not independently irreducible.
    See module docstring for closing strategy. -/
theorem hardyZ_first_moment_sqrt :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, hardyZ t| ≤ C * T ^ ((1 : ℝ) / 2) := by
  sorry

end Aristotle.Standalone.HardyZFirstMomentBridge
