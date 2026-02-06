/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Littlewood.Main.Littlewood
import Littlewood.CriticalAssumptions

/-!
# Critical Path Status Test

This file tracks which components of the Littlewood proof are complete
and which remain sorry-backed. Run:

```
lake build Littlewood.Tests.CriticalPathTest
```

If this compiles, the entire critical path type-checks.

## Current Status (2026-02-04)

- Main target: 11 sorry warnings (8 project + 3 external dependency)
- Critical assumptions: 5 (in CriticalAssumptions.lean)
- Bridge sorries: 2 (ExplicitFormulaOscillation + ThetaExplicitFormulaOscillation)
- Aristotle sorries: 1 (approx_functional_eq)
- External (PrimeNumberTheoremAnd): 3 (NOT on critical path)
-/

open Chebyshev LogarithmicIntegral ZetaZeros Schmidt ExplicitFormula Conversion

namespace Littlewood.Tests.CriticalPath

/-! ## Main Theorems (should typecheck with sorry-backed instances) -/

-- The two headline results
#check Littlewood.littlewood_psi
#check LittlewoodPi.littlewood_pi_li

-- Key corollaries
#check LittlewoodPi.pi_gt_li_infinitely_often
#check LittlewoodPi.pi_lt_li_infinitely_often
#check LittlewoodPi.pi_minus_li_sign_changes

/-! ## Critical Assumptions (5 sorry-backed instances)

These are the mathematical gaps. When Aristotle closes them,
the corresponding sorry in CriticalAssumptions.lean can be removed. -/

-- 1. Explicit formula for psi (blocked on Perron's formula / Mathlib contour integration)
#check (inferInstance : ExplicitFormulaPsiHyp)

-- 2. Explicit formula for theta (same zero sum as psi, O(√x) error)
#check (inferInstance : ExplicitFormulaThetaHyp)

-- 3. Phragmen-Lindelof convexity bound (Aristotle PhragmenLindelof.lean, 3 sorries)
--    NOTE: Aristotle currently proves exponent 1/2, but hypothesis requires 1/4+eps
#check (inferInstance : ZetaCriticalLineBoundHyp)

-- 4. First moment of Hardy's Z-function (needs van der Corput bounds)
#check (inferInstance : HardyFirstMomentUpperHyp)

-- 5. Theta-to-pi-li oscillation transfer (needs quantitative PNT)
#check (inferInstance : OmegaThetaToPiLiHyp)

/-! ## Auto-Wired Instances (resolve via bridge chain, 0 additional sorries in wiring) -/

-- Hardy critical line zeros: from ZetaCriticalLineBoundHyp + HardyFirstMomentUpperHyp
#check (inferInstance : HardyCriticalLineZerosHyp)

-- Psi oscillation from critical zeros: from HardyCriticalLineZerosHyp + ExplicitFormulaPsiHyp
--   (1 sorry in Bridge/ExplicitFormulaOscillation.lean)
#check (inferInstance : PsiOscillationFromCriticalZerosHyp)

-- Psi oscillation at sqrt scale: from PsiOscillationFromCriticalZerosHyp (0 sorry)
#check (inferInstance : PsiOscillationSqrtHyp)

-- Theta oscillation at sqrt scale: from HardyCriticalLineZerosHyp + ExplicitFormulaThetaHyp
--   (1 sorry in Bridge/ThetaExplicitFormulaOscillation.lean)
#check (inferInstance : ThetaOscillationSqrtHyp)

-- Pi-li oscillation at sqrt/log scale: from ThetaOscillationSqrtHyp + OmegaThetaToPiLiHyp (0 sorry)
#check (inferInstance : PiLiOscillationSqrtHyp)

/-! ## Proved Instances (no sorries, not on critical path)

The following are fully proved with no sorries but live in files not
imported by the main theorems (they feed into infrastructure, not the
critical path):
- ZeroConjZeroHyp (ZetaZeros/)
- ZeroOneSubZeroHyp (ZetaZeros/)
- FunctionalEquationHyp (Aristotle/FunctionalEquationHyp.lean)
- LambdaSymmetryHyp (Aristotle/FunctionalEquationHyp.lean)
- ZetaLogDerivPoleHyp (CoreLemmas/LandauLemma.lean)
-/

/-! ## Progress Tracking

When a sorry is closed, change the corresponding line below from
`sorry` to the actual proof term, and verify this file still compiles.

### Scoreboard (sorry count for main target)
-- 2026-02-04: 11 sorries (down from 69, architecture improved)
--   Architecture change: PsiToThetaOscillation (dubious ψ→θ transfer)
--   replaced by ExplicitFormulaThetaHyp + ThetaExplicitFormulaOscillation
--   (direct θ oscillation from explicit formula, same argument as ψ).
-/

end Littlewood.Tests.CriticalPath
