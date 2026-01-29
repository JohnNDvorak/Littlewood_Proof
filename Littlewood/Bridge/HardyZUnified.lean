/-
Unified exports from Hardy Z files.

Multiple Aristotle files prove variants of Hardy Z being real:
- HardyZRealV4: hardyZV4_real
- HardyZRealV2: hardyZV2_real
- HardyZReal: completedRiemannZeta_real_on_critical_line
- HardyZComplete: hardyZV3_real
- HardyZConjugation: completedRiemannZeta_critical_line_real

This file provides unified access to these results.
-/

import Littlewood.Aristotle.HardyZRealV4
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Aristotle.HardyZReal
import Littlewood.Aristotle.HardyZComplete
import Littlewood.Aristotle.HardyZConjugation
import Littlewood.Aristotle.HardyAssumptions

namespace HardyZUnified

/-
Key theorems available:

From HardyZRealV4:
- hardyThetaV4, hardyZV4: definitions
- hardyZV4_real: (hardyZV4 t).im = 0

From HardyZReal:
- riemannZeta_conj: ζ(s̄) = ζ(s)̄
- gamma_conj: Γ(s̄) = Γ(s)̄
- completedRiemannZeta_conj: Λ(s̄) = Λ(s)̄
- completedRiemannZeta_real_on_critical_line: Im(Λ(1/2+it)) = 0

From HardyZConjugation:
- completedRiemannZeta_critical_line_real: same as above via Hurwitz
-/

-- Summary theorem: The completed Riemann zeta function is real on the critical line
-- This is the key property for Hardy's theorem
-- Available from HardyZReal.completedRiemannZeta_real_on_critical_line
-- and from HardyZConjugation.completedRiemannZeta_critical_line_real
theorem completedRiemannZeta_is_real_on_critical_line (t : ℝ) :
    (completedRiemannZeta (1 / 2 + Complex.I * t)).im = 0 :=
  completedRiemannZeta_real_on_critical_line t

-- Hardy Z is real (from HardyZRealV4)
theorem hardyZ_is_real (t : ℝ) : (hardyZV4 t).im = 0 := hardyZV4_real t

-- Zeta conjugation (from HardyZReal)
theorem zeta_conjugation (s : ℂ) : riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) :=
  riemannZeta_conj s

end HardyZUnified
