import Littlewood.Aristotle.HardyMeanSquareAsymptoticLeaf
import Littlewood.Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyMeanSquareAsymptoticWiring

open Aristotle.Standalone.AtkinsonFormula
open Aristotle.Standalone.SiegelSaddleExpansionHyp
open Aristotle.Standalone.GabckePhaseCouplingHyp

/-- Non-circular bridge from the tracked B1 theorem package to the standard
`HardyMeanSquareAsymptoticHyp` class. Unlike the instance in
`DeepBlockersResolved`, this does not depend on the public 15-class surface. -/
instance (priority := 100)
    [AtkinsonShiftedInversePhaseCellPrefixBoundHyp]
    [SiegelSaddleExpansionHyp]
    [GabckePhaseCouplingHyp] :
    Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp := by
  letI : AtkinsonShiftedCorrectionPrefixBoundHyp :=
    atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix
  exact
    Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment.hardyMeanSquareAsymptoticHyp_proved

end HardyMeanSquareAsymptoticWiring
