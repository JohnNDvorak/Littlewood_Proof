import Littlewood.Bridge.PhragmenLindelofWiring
import Littlewood.Bridge.HardyDirichletPhaseAlignmentWiring
import Littlewood.Bridge.HardyMeanSquareAsymptoticWiring
import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.Aristotle.RiemannSiegelFirstMoment
import Littlewood.Aristotle.Standalone.CombinedAtomsFromDeepBlockers
import Littlewood.Aristotle.Standalone.RSCompleteBlockAsymptotic

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyCriticalLineZerosFromStandalone

open Schmidt
open Aristotle.Standalone.AtkinsonFormula
open Aristotle.Standalone.SiegelSaddleExpansionHyp
open Aristotle.Standalone.GabckePhaseCouplingHyp

variable [AtkinsonShiftedInversePhaseCellPrefixBoundHyp]
variable [SiegelSaddleExpansionHyp]
variable [GabckePhaseCouplingHyp]

private theorem rs_per_block_signed_bound :
    Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp := by
  letI : AtkinsonShiftedCorrectionPrefixBoundHyp :=
    atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix
  exact
    Aristotle.Standalone.RSCompleteBlockAsymptotic.perBlockSignedBoundHyp_of_blockAsymptotic
      Aristotle.Standalone.RSCompleteBlockAsymptotic.rsCompleteBlockWithResidual_sorry

private theorem mainTermFirstMomentBoundHyp_from_inversePhaseCell :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  refine ⟨?_⟩
  intro ε hε
  obtain ⟨C_M, hC_M, hmain⟩ := mainTerm_first_moment_sqrt_of_inversePhaseCellPrefix
  refine ⟨C_M, hC_M, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hpow :
      T ^ ((1 : ℝ) / 2) ≤ T ^ ((1 : ℝ) / 2 + ε) := by
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  exact le_trans (hmain T hT) (mul_le_mul_of_nonneg_left hpow (le_of_lt hC_M))

/-- Expose the tracked B2 endpoint as the standard first-main-term class. -/
instance (priority := 100) :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp :=
  mainTermFirstMomentBoundHyp_from_inversePhaseCell

/-- The RS per-block sign structure yields the standard error-term first-moment
bound needed by the Hardy chain. -/
instance (priority := 100) :
    HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp :=
  RiemannSiegelFirstMoment.errorTermFirstMomentBound_from_quarter rs_per_block_signed_bound

/-- Non-circular Hardy critical-line infinitude, routed through the tracked
standalone B1/B2/B3 theorem endpoints instead of `DeepSorries`. -/
instance (priority := 100) :
    Schmidt.HardyCriticalLineZerosHyp where
  infinite :=
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.hardy_critical_line_infinitely_many_zeros_from_blockers
      rs_per_block_signed_bound

end HardyCriticalLineZerosFromStandalone
