/-
# Littlewood Formalization: Critical Path Assumptions

This file provides ONLY the sorry-backed instances that are on the critical
path to the two main theorems:
  - littlewood_psi  : ψ(x) - x = Ω±(√x)
  - littlewood_pi_li : π(x) - li(x) = Ω±(√x / log x)

## Critical Path for littlewood_psi (0 sorry instances here):
  HardyCriticalLineZerosHyp (extracted from DeepSorries.deep_mathematical_results.1)
    → (via LandauOscillation, 0 sorry, priority 2000) PsiOscillationFromCriticalZerosHyp
    → (via PsiOscillationWiring) PsiOscillationSqrtHyp
    → littlewood_psi
  LandauOscillation delegates to Aristotle/LandauLittlewood → LandauContradiction
    → SmoothedExplicitFormula (extracted from DeepSorries.deep_mathematical_results.2.1).

## Critical Path for littlewood_pi_li (0 sorry instances here):
  HardyCriticalLineZerosHyp (same source as above)
    → (via LandauOscillation, 0 sorry, priority 2000) PiLiOscillationSqrtHyp
    → littlewood_pi_li

## Total sorries in this file: 0
## Total critical path sorries: 1
##   DeepSorries:69 (deep_mathematical_results — bundles Hardy's theorem,
##     ψ Landau contradiction, and π-li Landau contradiction)

For non-critical infrastructure hypotheses (zero counting, weighted average,
Landau lemma, etc.), see Assumptions.lean which imports this file and adds
the remaining ~52 sorry instances.
-/

-- Class definition files (minimal set for critical path)
import Littlewood.ExplicitFormulas.ConversionFormulas
import Littlewood.Bridge.HardyChainHyp

-- Bridge files (provide auto-wired instances)
import Littlewood.Bridge.HardyCriticalLineZerosDirect
-- import Littlewood.Bridge.HardyCriticalLineWiring  -- MERGED: bypassed by HardyCriticalLineZerosDirect
import Littlewood.Bridge.ExplicitFormulaOscillation
import Littlewood.Bridge.PsiOscillationWiring
import Littlewood.Bridge.ThetaExplicitFormulaOscillation
import Littlewood.Bridge.PsiToPiLiOscillation
import Littlewood.Bridge.OmegaThetaToPiLiWiring
import Littlewood.Bridge.PhragmenLindelofWiring
import Littlewood.Bridge.PiLiDirectOscillation
import Littlewood.Bridge.LandauOscillation

-- Aristotle files (provide proved instances)
-- import Littlewood.Aristotle.HardyFirstMomentDirect  -- MERGED into DeepSorries

namespace Littlewood.CriticalAssumptions

open Conversion ZetaZeros

-- ============================================================
-- Critical Path Sorry Instances (0 in this file)
-- ============================================================

-- ALL critical path sorries are now in Aristotle/DeepSorries.lean:
--   deep_mathematical_results bundles:
--     (1) Hardy's theorem: ζ has ∞ zeros on Re(s) = 1/2
--     (2) Landau ψ-contradiction: σ·(ψ-x) = o₊(√x) + ∞ critical zeros → False
--     (3) Landau π-li contradiction: σ·(π-li) = o₊(√x/log x) + ∞ critical zeros → False
--
-- Extraction chain:
--   DeepSorries.deep_mathematical_results.1
--     → HardyCriticalLineZerosDirect (instance, 0 sorry)
--   DeepSorries.deep_mathematical_results.2.1
--     → SmoothedExplicitFormula.psi_signed_contradiction (theorem, 0 sorry)
--   DeepSorries.deep_mathematical_results.2.2
--     → SmoothedExplicitFormula.pi_li_signed_contradiction (theorem, 0 sorry)

-- ExplicitFormulaPsiHyp: REMOVED from critical path.
--   The tsum formulation ∑' ρ : zetaNontrivialZeros, x^ρ/ρ is FALSE
--   (not absolutely convergent → tsum = 0 in Lean/Mathlib).
--   The truncated explicit formula content is now folded into the
--   ExplicitFormulaOscillation bridge sorry.
--   See docs/FALSE_THEOREMS.md for the tsum architectural issue.

-- OmegaThetaToPiLiHyp: PROVIDED by Bridge/OmegaThetaToPiLiWiring.lean
-- (isolated bridge sorry; consumed by Bridge/PsiToPiLiOscillation.lean)

-- ExplicitFormulaThetaHyp: REMOVED from critical path.
--   Same tsum issue as ExplicitFormulaPsiHyp. The truncated explicit
--   formula content is folded into the ThetaExplicitFormulaOscillation
--   bridge sorry.

end Littlewood.CriticalAssumptions
