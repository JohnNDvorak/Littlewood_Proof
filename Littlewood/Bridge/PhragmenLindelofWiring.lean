/-
Bridge: Wire Aristotle's Phragmén-Lindelöf convexity bound to ZetaCriticalLineBoundHyp.

WIRING TARGET: Aristotle/zeta_convexity_bound at σ = 1/2.

IMPORTANT: Do NOT wire through zeta_critical_line_bound — that theorem proves
exponent 1/2, but ZetaCriticalLineBoundHyp requires exponent 1/4 + ε. The correct
source is zeta_convexity_bound, which at σ = 1/2 gives:
  |ζ(1/2 + it)| ≤ C|t|^{convexity_exponent(1/2) + ε} = C|t|^{1/4 + ε}

SIGNATURE DIFFERENCES:
  Hypothesis: ‖ζ(1/2 + I * t)‖ ≤ C * |t| ^ (1/4 + ε), threshold |t| ≥ 2
  Aristotle:  ‖ζ(σ + t * I)‖ ≤ C * |t| ^ (convexity_exponent σ + ε), threshold 1 ≤ |t|
  Both use σ = 1/2; I*t = t*I by commutativity; Aristotle's threshold is weaker (good).

STATUS: Ready to activate when Aristotle closes zeta_convexity_bound's sorry.
Currently propagates Aristotle's 3 sorry warnings (gamma_growth, zeta_critical_line_bound,
zeta_convexity_bound). The wiring itself has 0 sorries.

ACTIVATION: When Aristotle closes zeta_convexity_bound:
1. Import this file from CriticalAssumptions.lean
2. Remove the sorry-backed `instance : ZetaCriticalLineBoundHyp` from CriticalAssumptions.lean
3. The bridge auto-discharges the hypothesis

WARNING: Do NOT import this file while CriticalAssumptions.lean also provides
ZetaCriticalLineBoundHyp — it would create a duplicate instance.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Littlewood.Aristotle.PhragmenLindelof
import Littlewood.Bridge.HardyChainHyp

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Real Set Filter MeasureTheory

namespace PhragmenLindelofWiring

/-- Wire zeta_convexity_bound at σ = 1/2 to ZetaCriticalLineBoundHyp.

    When Aristotle closes the sorry in `zeta_convexity_bound`,
    this instance auto-discharges ZetaCriticalLineBoundHyp with 0 additional work,
    replacing the sorry in CriticalAssumptions.lean. -/
instance : ZetaCriticalLineBoundHyp where
  bound := by
    intro ε hε
    -- Use zeta_convexity_bound at σ = 1/2
    obtain ⟨C, hC, hbound⟩ := zeta_convexity_bound (1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1) ε hε
    refine ⟨C, hC, fun t ht => ?_⟩
    -- Threshold: |t| ≥ 2 → 1 ≤ |t|
    have h1 : 1 ≤ |t| := by linarith
    -- Apply the bound
    have hbd := hbound t h1
    -- convexity_exponent(1/2) = 1/4
    rw [convexity_exponent_half] at hbd
    -- Cast + commutativity: ↑(1/2 : ℝ) + ↑t * I = 1/2 + I * ↑t
    convert hbd using 2
    push_cast; ring_nf

end PhragmenLindelofWiring
