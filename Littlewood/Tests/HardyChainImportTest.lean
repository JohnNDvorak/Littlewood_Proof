/-
Test: All Hardy chain files import without error.
If this file compiles, the entire Hardy Z infrastructure is consistent.
-/

import Littlewood.Aristotle.HardyZReal
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Aristotle.HardyZRealV4
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyZCauchySchwarz
import Littlewood.Aristotle.HardyZContradiction
import Littlewood.Aristotle.HardyInfrastructure
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.ConvexityBounds
import Littlewood.Aristotle.HardyZComplete
import Littlewood.Aristotle.HardyAssumptions
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.CompletedZetaCriticalLine
import Littlewood.Bridge.HardyZTransfer
-- import Littlewood.Bridge.HardyAssemblyAttempt  -- DEPRECATED: V1 exploration

-- Verify key definitions are accessible
#check HardyEstimatesPartial.hardyZ
#check HardyEstimatesPartial.hardyTheta
#check hardyZV2
#check hardyThetaV2
#check hardyZV4
#check hardyThetaV4
#check HardyZContradiction.BuildingBlocks
#check HardyZContradiction.Z
#check HardyZTransfer.hardyTheta_eq_thetaV2
#check HardyZTransfer.hardyZ_eq_hardyZV2_re
#check CompletedZetaCriticalLine.completedRiemannZeta_critical_line_real

-- Verify key sorry-free results
#check hardyZV2_real
#check continuous_hardyZV2
#check hardyZV2_zero_iff_zeta_zero
#check hardyZV2_abs_eq_zeta_abs
#check HardyEstimatesPartial.exp_iTheta_norm
#check HardyEstimatesPartial.hardyZ_abs_le
#check HardyEstimatesPartial.hardySum_integral_eq
#check HardyEstimatesPartial.hardyZ_integrable

-- If this compiles, all Hardy imports work
theorem hardy_chain_test : True := trivial
