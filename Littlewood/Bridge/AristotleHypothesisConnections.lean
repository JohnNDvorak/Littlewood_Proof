/-
# Aristotle Hypothesis Connections Analysis

This file documents the connections between Aristotle proofs and hypothesis classes.

See also: `Littlewood/Bridge/AristotleBridges.lean` for proven bridge lemmas.

## STATUS SUMMARY

### ALREADY CONNECTED (4 instances with proofs)

| Hypothesis Class | Instance Location | Proof Source |
|------------------|-------------------|--------------|
| FunctionalEquationHyp | FunctionalEquationHyp.lean:70 | riemannZeta_eq_chiFE_mul |
| LambdaSymmetryHyp | FunctionalEquationHyp.lean:80 | completedRiemannZeta_one_sub |
| ZeroConjZeroHyp | ZeroCountingFunction.lean:1618 | riemannZeta_conj |
| ZeroOneSubZeroHyp | ZeroCountingFunction.lean:1640 | riemannZeta_one_sub |

### BRIDGE LEMMAS PROVED (AristotleBridges.lean)

| Bridge | Theorem | Status |
|--------|---------|--------|
| chebyshevPsiV3 = Chebyshev.psi | chebyshevPsiV3_eq_psi | ✓ PROVED |
| chebyshevPsiV3 = chebyshevPsi | chebyshevPsiV3_eq_chebyshevPsi | ✓ PROVED |
| zeroCountingFunction = N (sets) | zeroCountingFunction_set_eq | ✓ PROVED |
| zeroCountingFunction T = N T | zeroCountingFunction_eq_NAsymptotic_N | ✓ PROVED |

### IN MATHLIB (no hypothesis needed)

| Property | Mathlib Theorem |
|----------|-----------------|
| ζ(s) ≠ 0 for Re(s) ≥ 1 | riemannZeta_ne_zero_of_one_le_re |
| ζ(s̄) = ζ(s)̄ | riemannZeta_conj |
| Λ(1-s) = Λ(s) | completedRiemannZeta_one_sub |

### BRIDGED (needs more work to fully connect)

1. **ZeroCountingAsymptoticHyp** (ZeroCountingFunction.lean:565)
   - Aristotle has: N_asymptotic (NAsymptotic.lean), zero_counting_main_term (ZeroCountingNew.lean)
   - Bridge: zeroCountingFunction_eq_NAsymptotic_N proves (zeroCountingFunction T : ℝ) = N T ✓
   - Remaining gap: N_asymptotic requires hypotheses (h_S, h_RVM, h_Stirling)
   - ZeroCountingNew provides S_isBigO_log; need h_RVM and h_Stirling

2. **ExplicitFormulaPsiHyp** (ExplicitFormulaPsi.lean)
   - Aristotle has: explicit_formula_psi_v3 (ExplicitFormulaV3.lean)
   - Bridge: chebyshevPsiV3_eq_chebyshevPsi proves chebyshevPsiV3 = chebyshevPsi ✓
   - Can now directly use Aristotle's explicit formula results

### NOT DIRECTLY CONNECTABLE (blocked)

1. **SchmidtPsiOscillationHyp** (SchmidtTheorem.lean)
   - Aristotle has: trigPoly_zero_iff_coeffs_zero, schmidt_oscillation
   - Gap: These prove trig polynomial properties, not chebyshevPsi oscillation
   - Need: Explicit formula connecting ψ(x) to sum over zeros (multi-step chain)

### KEY ARISTOTLE THEOREMS AVAILABLE

From ThreeFourOneV2.lean:
- three_four_one_v2: |ζ(σ)|³|ζ(σ+it)|⁴|ζ(σ+2it)| ≥ 1
- zeta_ne_zero_re_one_v2: ζ(1+it) ≠ 0 (uses Mathlib)

From SchmidtNew.lean:
- trigPoly_zero_iff_coeffs_zero: Trig poly = 0 iff all coeffs = 0
- schmidt_oscillation: Non-zero trig poly oscillates

From XiDifferentiability.lean:
- xi_LiteralCorrected_entire: Corrected xi is entire
- xi_Literal_not_differentiable: Naive xi is NOT differentiable

From RiemannXiEntire.lean:
- RiemannXiAlt_entire: Alternative xi definition is entire

## RECOMMENDATIONS FOR FUTURE WORK

1. ~~**Create ZeroDef Equivalence Lemmas**~~ ✓ DONE
   See: zeroCountingFunction_eq_NAsymptotic_N in AristotleBridges.lean

2. ~~**Wire ExplicitFormulaV3**~~ ✓ DONE
   See: chebyshevPsiV3_eq_chebyshevPsi in AristotleBridges.lean

3. **Supply h_RVM and h_Stirling for N_asymptotic**
   These hypotheses are needed to use NAsymptotic.N_asymptotic
   - h_RVM: Riemann-von Mangoldt connection (argument principle)
   - h_Stirling: Stirling approximation for Gamma argument

4. **Complete Schmidt Chain**
   Connect trig poly results → explicit formula → ψ oscillation

-/

import Mathlib

-- Verify Mathlib's zeta non-vanishing on Re(s) ≥ 1 is available
#check @riemannZeta_ne_zero_of_one_le_re

-- Verify completed zeta symmetry
#check @completedRiemannZeta_one_sub

-- Note: riemannZeta_conj is proved in Aristotle/HardyZReal.lean, not Mathlib
-- #check @riemannZeta_conj  -- (in Aristotle/HardyZReal.lean)
