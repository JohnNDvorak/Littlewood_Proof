/-
Wiring Simulation Test: Validates the entire chain works when hypotheses are provided.

This file tests that when all sorry-backed hypotheses in CriticalAssumptions are assumed,
the main theorems follow with 0 additional sorries from the wiring layer.

PURPOSE: If any #check fails, it reveals a broken link in the dependency chain.

EXPECTED RESULT: All #check commands succeed, meaning the wiring layer is complete
and only needs the mathematical content from Aristotle to close.

SORRY COUNT: 0 (this file contains no proofs, only #check commands)
-/

import Littlewood.Main.Littlewood
import Littlewood.Main.LittlewoodPi
import Littlewood.Assumptions
import Littlewood.CriticalAssumptions
import Littlewood.ExplicitFormulas.ConversionFormulas
import Littlewood.Oscillation.SchmidtTheorem

open Schmidt Conversion ExplicitFormula ZetaZeros

/-! ## Step 1: Critical Hypothesis Instances

These are the 5 sorry-backed hypotheses in CriticalAssumptions.lean.
All should resolve via inferInstance. -/

section CriticalHypotheses

#check (inferInstance : ExplicitFormulaPsiHyp)
#check (inferInstance : ExplicitFormulaThetaHyp)
#check (inferInstance : ZetaCriticalLineBoundHyp)
#check (inferInstance : HardyFirstMomentUpperHyp)
#check (inferInstance : OmegaThetaToPiLiHyp)

end CriticalHypotheses

/-! ## Step 2: Bridge-Derived Instances

These instances are derived by the bridge files from the critical hypotheses. -/

section BridgeDerived

-- From ExplicitFormulaOscillation.lean
#check (inferInstance : PsiOscillationFromCriticalZerosHyp)

-- From ThetaExplicitFormulaOscillation.lean
#check (inferInstance : ThetaOscillationSqrtHyp)

-- From OmegaPsiToTheta.lean (OmegaPsiToThetaHyp is FALSE for f=√x, so not used)
-- #check (inferInstance : OmegaPsiToThetaHyp)  -- Intentionally omitted

-- From PsiToPiLiOscillation.lean
#check (inferInstance : PiLiOscillationSqrtHyp)

-- From SchmidtPsi.lean / SchmidtTheorem.lean
#check (inferInstance : PsiOscillationSqrtHyp)

end BridgeDerived

/-! ## Step 3: Main Theorems

These are the ultimate goals of the formalization. -/

section MainTheorems

-- Littlewood's theorem for ψ (Main/Littlewood.lean)
#check @Littlewood.littlewood_psi

-- Littlewood's theorem for π (Main/LittlewoodPi.lean)
#check @LittlewoodPi.littlewood_pi_li
#check @LittlewoodPi.pi_gt_li_infinitely_often
#check @LittlewoodPi.pi_lt_li_infinitely_often

end MainTheorems

/-! ## Step 4: Intermediate Key Theorems

These are important intermediate results on the critical path. -/

section IntermediateTheorems

-- Schmidt oscillation theorem
#check @Schmidt.psi_oscillation_sqrt

-- Chebyshev ψ asymptotic from Gauss (Bridge/FromGauss.lean)
-- Note: Requires import Littlewood.Bridge.FromGauss if needed
-- #check @chebyshevPsi_asymptotic_from_gauss

end IntermediateTheorems

/-! ## Step 5: Conversion Chain Validation

Verify the ψ → θ → π-li conversion chain types correctly. -/

section ConversionChain

-- omega_theta_to_pi_li requires OmegaThetaToPiLiHyp
variable [OmegaThetaToPiLiHyp] in
#check @omega_theta_to_pi_li

-- omega_psi_to_pi_li requires both OmegaPsiToThetaHyp and OmegaThetaToPiLiHyp
-- Note: OmegaPsiToThetaHyp is FALSE for f = √x, so this path is NOT used
-- variable [OmegaPsiToThetaHyp] [OmegaThetaToPiLiHyp] in
-- #check @omega_psi_to_pi_li

end ConversionChain

/-! ## Summary

If all #check commands above succeed:
✓ All hypothesis instances resolve
✓ All bridge files wire correctly
✓ Main theorems typecheck
✓ Only the 11 sorry warnings (8 project + 3 external) remain

The wiring is COMPLETE. Remaining work is pure mathematical content. -/
