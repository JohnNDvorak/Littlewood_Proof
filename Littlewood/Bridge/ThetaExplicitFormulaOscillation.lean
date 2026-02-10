/-
Bridge: HardyCriticalLineZerosHyp → ThetaOscillationSqrtHyp.

STATUS: SORRY REMOVED — instance replaced by PiLiDirectOscillation.lean.

The old architecture required this bridge to prove θ(x) - x = Ω±(√x),
which was then transferred to π(x) - li(x) = Ω±(√x / log x) via
OmegaThetaToPiLiHyp. But the transfer required PsiRemainderMeanSquareHyp
(∫|ψ-t|²/t² = O(log x)), which is RH-strength.

The new PiLiDirectOscillation bridge proves π-li oscillation DIRECTLY
from critical-line zeros, bypassing both this bridge and OmegaThetaToPiLiHyp.
This merges 2 sorries into 1, reducing the total sorry count.

ThetaOscillationSqrtHyp is no longer on the critical path for either
main theorem:
  - littlewood_psi: uses PsiOscillationFromCriticalZerosHyp (separate sorry)
  - littlewood_pi_li: uses PiLiOscillationSqrtHyp (now from PiLiDirectOscillation)

If ThetaOscillationSqrtHyp is needed independently in the future, the instance
can be restored here once the truncated explicit formula for θ is available.
The mathematical content is identical to ExplicitFormulaOscillation (for ψ)
with a different error term (O(√x) vs O(log x)).

SORRY COUNT: 0 (was 1)
-/

import Littlewood.Oscillation.SchmidtTheorem

noncomputable section

open Schmidt

-- Instance REMOVED: was
--   instance [HardyCriticalLineZerosHyp] : ThetaOscillationSqrtHyp where
--     oscillation := by sorry
--
-- Replaced by PiLiDirectOscillation.lean which provides PiLiOscillationSqrtHyp
-- directly, bypassing the need for θ oscillation as an intermediate step.
