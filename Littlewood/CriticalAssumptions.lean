/-
# Littlewood Formalization: Critical Path Assumptions

This file provides ONLY the sorry-backed instances that are on the critical
path to the two main theorems:
  - littlewood_psi  : ψ(x) - x = Ω±(√x)
  - littlewood_pi_li : π(x) - li(x) = Ω±(√x / log x)

## Critical Path for littlewood_psi (1 sorry instance here + 1 bridge auto-wired + 1 bridge sorry):
  ZetaCriticalLineBoundHyp (AUTO) + HardyFirstMomentUpperHyp
    → (via Hardy chain) HardyCriticalLineZerosHyp
    → (via ExplicitFormulaOscillation, 1 sorry) PsiOscillationFromCriticalZerosHyp
    → (via PsiOscillationWiring) PsiOscillationSqrtHyp
    → littlewood_psi

## Critical Path for littlewood_pi_li (0 sorry instances here + 2 bridge sorries):
  HardyCriticalLineZerosHyp (auto-wired above)
    → (via ThetaExplicitFormulaOscillation, 1 sorry) ThetaOscillationSqrtHyp
  OmegaThetaToPiLiHyp (via OmegaThetaToPiLiWiring, 1 sorry) + ThetaOscillationSqrtHyp
    → (via PsiToPiLiOscillation) PiLiOscillationSqrtHyp
    → littlewood_pi_li

## Total sorries in this file: 1 (was 4)
##   REMOVED: ExplicitFormulaPsiHyp (tsum is FALSE; folded into bridge sorry)
##   REMOVED: ExplicitFormulaThetaHyp (tsum is FALSE; folded into bridge sorry)
## Total critical path sorries (including bridges + Aristotle): ~7

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

namespace Littlewood.CriticalAssumptions

open Conversion ZetaZeros

-- ============================================================
-- Critical Path Sorry Instances (1 total, was 4)
-- ============================================================

-- ExplicitFormulaPsiHyp: REMOVED from critical path.
--   The tsum formulation ∑' ρ : zetaNontrivialZeros, x^ρ/ρ is FALSE
--   (not absolutely convergent → tsum = 0 in Lean/Mathlib).
--   The truncated explicit formula content is now folded into the
--   ExplicitFormulaOscillation bridge sorry.
--   See docs/FALSE_THEOREMS.md for the tsum architectural issue.

-- ZetaCriticalLineBoundHyp: PROVIDED by Bridge/PhragmenLindelofWiring.lean
-- (auto-derived from Aristotle/PhragmenLindelof.lean, 0 sorries)

/-- First moment upper bound for Hardy's Z-function.

    STATEMENT: ∀ ε > 0, ∃ C > 0, ∃ T₀ ≥ 2, ∀ T ≥ T₀,
      |∫ t in Ioc 1 T, Z(t)| ≤ C · T^{1/2+ε}

    STATUS: Aristotle/HardyZFirstMoment.lean has a PROVED conditional theorem
    `hardyZ_first_moment_bound_conditional` (0 sorries), plus wiring lemmas
    that discharge prerequisites (1) and (2):
      - `MainTerm_eq_hardySum`, `mainTerm_integrable`
      - `ErrorTerm_eq_hardyRemainder`, `errorTerm_integrable`
    via Aristotle/HardyZMeasurability.lean.
    Remaining missing prerequisites are:
      3. |∫ MainTerm| ≤ C₁·T^{1/2+ε}
      4. |∫ ErrorTerm| ≤ C₂·T^{1/2+ε}
    In `Bridge/HardyFirstMomentWiring.lean`, (3) is further reduced to
    oscillatory-integral control classes:
      - `HardyExpPhaseIntegralUniformBoundHyp`
      - `HardyExpPhaseIntervalIntegralUniformBoundOnSupportHyp`
      - `HardyExpPhaseVdcOnSupportHyp` (endpoint + correction + decomposition)
      - `HardyExpPhaseVdcEndpointBoundOnSupportHyp`
      - `HardyExpPhaseVdcCorrectionBoundOnSupportHyp`
      - `HardyExpPhaseVdcCalculusOnSupportHyp` (van der Corput calculus layer)
    while (4) remains `ErrorTermFirstMomentBoundHyp`.

    CONSUMED BY: Bridge/HardyCriticalLineWiring.lean (combined with
    ZetaCriticalLineBoundHyp to produce HardyCriticalLineZerosHyp).

    REFERENCES:
    - Titchmarsh, "Theory of the Riemann Zeta Function", Section 7.6 -/
instance : HardyFirstMomentUpperHyp := by
  refine ⟨?_⟩
  sorry

-- OmegaThetaToPiLiHyp: PROVIDED by Bridge/OmegaThetaToPiLiWiring.lean
-- (isolated bridge sorry; consumed by Bridge/PsiToPiLiOscillation.lean)

-- ExplicitFormulaThetaHyp: REMOVED from critical path.
--   Same tsum issue as ExplicitFormulaPsiHyp. The truncated explicit
--   formula content is folded into the ThetaExplicitFormulaOscillation
--   bridge sorry.

end Littlewood.CriticalAssumptions
