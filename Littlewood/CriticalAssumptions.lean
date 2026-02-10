/-
# Littlewood Formalization: Critical Path Assumptions

This file provides ONLY the sorry-backed instances that are on the critical
path to the two main theorems:
  - littlewood_psi  : ψ(x) - x = Ω±(√x)
  - littlewood_pi_li : π(x) - li(x) = Ω±(√x / log x)

## Critical Path for littlewood_psi (0 sorry instances here):
  ZetaCriticalLineBoundHyp (AUTO) + HardyFirstMomentUpperHyp
    → (via Hardy chain) HardyCriticalLineZerosHyp
    → (via LandauOscillation, 1 sorry, priority 2000) PsiOscillationFromCriticalZerosHyp
    → (via PsiOscillationWiring) PsiOscillationSqrtHyp
    → littlewood_psi
  NOTE: ExplicitFormulaOscillation also provides PsiOscillationFromCriticalZerosHyp
  but via the FALSE TruncatedExplicitFormulaPsiHyp (psi_approx with S=∅ contradicts
  Littlewood). LandauOscillation supersedes it with a TRUE sorry.

## Critical Path for littlewood_pi_li (0 sorry instances here):
  HardyCriticalLineZerosHyp (auto-wired above)
    → (via LandauOscillation, 1 sorry, priority 2000) PiLiOscillationSqrtHyp
    → littlewood_pi_li
  NOTE: PiLiDirectOscillation also provides PiLiOscillationSqrtHyp but requires
  TruncatedExplicitFormulaPiHyp (no instance; pi_approx is FALSE with S=∅).
  LandauOscillation supersedes it with a TRUE sorry for the direct Landau argument.

## Total sorries in this file: 0 (was 4)
##   REMOVED: ExplicitFormulaPsiHyp (tsum is FALSE; folded into bridge sorry)
##   REMOVED: ExplicitFormulaThetaHyp (tsum is FALSE; folded into bridge sorry)
##   MOVED: ErrorTermFirstMomentBoundHyp → Aristotle/RiemannSiegelFirstMoment.lean
## Total critical path sorries (including bridges + Aristotle): 4
##   LandauOscillation:72 (ψ Landau), LandauOscillation:101 (π-li Landau),
##   StationaryPhaseDecomposition:74 (stationary phase), RiemannSiegelFirstMoment:75 (RS)

For non-critical infrastructure hypotheses (zero counting, weighted average,
Landau lemma, etc.), see Assumptions.lean which imports this file and adds
the remaining ~52 sorry instances.
-/

-- Class definition files (minimal set for critical path)
import Littlewood.ExplicitFormulas.ConversionFormulas
import Littlewood.Bridge.HardyChainHyp

-- Bridge files (provide auto-wired instances)
import Littlewood.Bridge.HardyCriticalLineWiring
import Littlewood.Bridge.ExplicitFormulaOscillation
import Littlewood.Bridge.PsiOscillationWiring
import Littlewood.Bridge.ThetaExplicitFormulaOscillation
import Littlewood.Bridge.PsiToPiLiOscillation
import Littlewood.Bridge.OmegaThetaToPiLiWiring
import Littlewood.Bridge.PhragmenLindelofWiring
import Littlewood.Bridge.PiLiDirectOscillation
import Littlewood.Bridge.LandauOscillation

-- Aristotle files (provide proved instances)
import Littlewood.Aristotle.StationaryPhaseDecomposition
import Littlewood.Aristotle.RiemannSiegelFirstMoment

namespace Littlewood.CriticalAssumptions

open Conversion ZetaZeros

-- ============================================================
-- Critical Path Sorry Instances (0 in this file)
-- ============================================================

-- ExplicitFormulaPsiHyp: REMOVED from critical path.
--   The tsum formulation ∑' ρ : zetaNontrivialZeros, x^ρ/ρ is FALSE
--   (not absolutely convergent → tsum = 0 in Lean/Mathlib).
--   The truncated explicit formula content is now folded into the
--   ExplicitFormulaOscillation bridge sorry.
--   See docs/FALSE_THEOREMS.md for the tsum architectural issue.

-- ZetaCriticalLineBoundHyp: PROVIDED by Bridge/PhragmenLindelofWiring.lean
-- (auto-derived from Aristotle/PhragmenLindelof.lean, 0 sorries)

-- MainTermFirstMomentBoundHyp: AUTO-WIRED
--   Aristotle/StationaryPhaseDecomposition.lean provides
--   HardyCosIntegralAlternatingSqrtDecompositionHyp (1 atomic sorry),
--   which auto-wires to MainTermFirstMomentBoundHyp via
--   Bridge/HardyFirstMomentWiring.lean (0 sorries).

-- ErrorTermFirstMomentBoundHyp: PROVIDED by Aristotle/RiemannSiegelFirstMoment.lean
--   Atomic sorry: rs_remainder_first_moment_quarter gives |∫ ErrorTerm| ≤ C·T^{1/4}
--   Auto-wired: T^{1/4} ≤ T^{1/2+ε} for ε > 0 → ErrorTermFirstMomentBoundHyp

/-- First moment upper bound for Hardy's Z-function.

    AUTO-WIRED from MainTermFirstMomentBoundHyp + ErrorTermFirstMomentBoundHyp.

    The auto-wiring chain:
    1. StationaryPhaseDecomposition → HardyCosIntegralAlternatingSqrtDecompositionHyp
       (1 atomic sorry for oscillatory integral bound)
    2. HardyCosIntegralAlternatingSqrtDecompositionHyp → MainTermFirstMomentBoundHyp
       (0 sorries, via HardyFirstMomentWiring)
    3. RiemannSiegelFirstMoment → ErrorTermFirstMomentBoundHyp
       (1 atomic sorry for RS alternating cancellation)
    4. MainTermFirstMomentBoundHyp + ErrorTermFirstMomentBoundHyp
       → HardyFirstMomentUpperHyp (0 sorries, via HardyFirstMomentWiring)

    CONSUMED BY: Bridge/HardyCriticalLineWiring.lean (combined with
    ZetaCriticalLineBoundHyp to produce HardyCriticalLineZerosHyp). -/
instance : HardyFirstMomentUpperHyp :=
  HardyFirstMomentWiring.hardyFirstMomentUpper_from_two_bounds

-- OmegaThetaToPiLiHyp: PROVIDED by Bridge/OmegaThetaToPiLiWiring.lean
-- (isolated bridge sorry; consumed by Bridge/PsiToPiLiOscillation.lean)

-- ExplicitFormulaThetaHyp: REMOVED from critical path.
--   Same tsum issue as ExplicitFormulaPsiHyp. The truncated explicit
--   formula content is folded into the ThetaExplicitFormulaOscillation
--   bridge sorry.

end Littlewood.CriticalAssumptions
