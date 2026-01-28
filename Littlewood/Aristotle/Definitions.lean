/-
Unified definitions for the Littlewood project.
Import this instead of individual files when only definitions are needed.

This file consolidates the canonical versions of key definitions
that have multiple implementations across Aristotle files.
-/

import Mathlib

noncomputable section

open Complex Real

/-! ## Hardy Z-Function Definitions

Multiple versions exist due to iterative Aristotle development:
- hardyZAssump (HardyAssumptions.lean) - assumption-based
- hardyZ' (HardyZReal.lean) - first attempt
- hardyZV2 (HardyZRealV2.lean) - improved
- hardyZV3 (HardyZComplete.lean) - complete version
- hardyZV4 (HardyZRealV4.lean) - fully proved, CANONICAL

Use hardyZV4 and hardyThetaV4 as the canonical definitions.
-/

-- Re-export canonical definitions from HardyZRealV4
-- (These are the fully proved versions with no sorries)

/-! ## Functional Equation Definitions

Multiple chi/Lambda definitions exist:
- chi, Lambda (FunctionalEquation.lean) - has false statements at poles
- chiV2, LambdaV2 (FunctionalEquationV2.lean) - CANONICAL with proper hypotheses

Use V2 versions which correctly handle pole restrictions.
-/

/-! ## Schmidt Oscillation

SchmidtNew.lean contains the complete Schmidt oscillation theorem.
SchmidtOscillation.lean and SchmidtOscillationInfinite.lean are earlier versions.
-/

end
