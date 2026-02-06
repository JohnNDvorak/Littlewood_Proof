/-
Bridge: Wire Aristotle's hardyZ_first_moment_bound_conditional
         → HardyFirstMomentUpperHyp.

STATUS: PLACEHOLDER — NOT imported by the main build.

PREREQUISITES (all currently unproved):
  1. Integrability of MainTerm (from approximate functional equation)
  2. Integrability of ErrorTerm
  3. |∫ MainTerm| ≤ C₁·T^{1/2+ε} (needs van der Corput bounds)
  4. |∫ ErrorTerm| ≤ C₂·T^{1/2+ε}

EXISTING PROGRESS:
  - hardyZ_first_moment_bound_conditional (HardyZFirstMoment.lean): PROVED (0 sorry)
    but requires the 4 prerequisites above
  - OscillatorySumBound.oscillatory_sum_integral_bound: PROVED (0 sorry)
    provides partial progress toward prerequisite 3

BLOCKERS:
  - approx_functional_eq (Aristotle, 1 sorry) — must close first to even
    define MainTerm/ErrorTerm with the right signatures
  - van der Corput exponential sum bounds — not in Mathlib
  - Definition mismatch: HardyZFirstMoment.MainTerm vs HardyApproxFunctionalEq.hardySum

PLAN:
  When approx_functional_eq closes:
  1. Verify MainTerm/ErrorTerm definitions align
  2. Prove integrability (prerequisites 1-2)
  3. Prove integral bounds (prerequisites 3-4) via van der Corput
  4. Apply hardyZ_first_moment_bound_conditional
  5. Wire result to HardyFirstMomentUpperHyp

CONSUMED BY: CriticalAssumptions.lean (replaces the sorry on HardyFirstMomentUpperHyp).
-/

-- This file is a PLACEHOLDER. It does not import project files or provide
-- any instances. It serves as documentation for the wiring plan.
--
-- When ready to activate:
--   1. Add imports:
--      import Littlewood.Aristotle.HardyZFirstMoment
--      import Littlewood.Aristotle.HardyApproxFunctionalEq
--      import Littlewood.Bridge.HardyChainHyp
--   2. Prove the 4 prerequisites
--   3. Wire to HardyFirstMomentUpperHyp instance
--   4. Import from CriticalAssumptions.lean
--   5. Remove the sorry instance for HardyFirstMomentUpperHyp
