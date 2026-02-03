/-
Bridge: Wire PsiOscillationFromCriticalZerosHyp → PsiOscillationSqrtHyp.

These two classes assert the identical proposition:
  (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x]

PsiOscillationFromCriticalZerosHyp is intended as the *output* of the
Hardy + explicit formula chain.  PsiOscillationSqrtHyp is the *input*
consumed by littlewood_psi (the main theorem).  This file bridges them
so that discharging PsiOscillationFromCriticalZerosHyp automatically
discharges PsiOscillationSqrtHyp.

Together with HardyCriticalLineWiring (which gives
  [ZetaCriticalLineBoundHyp] [HardyFirstMomentUpperHyp] → HardyCriticalLineZerosHyp),
the remaining gap to the main theorem is:
  HardyCriticalLineZerosHyp + [explicit formula hypotheses]
    → PsiOscillationFromCriticalZerosHyp

STATUS: 0 sorries.
-/

import Littlewood.Oscillation.SchmidtTheorem

noncomputable section

open Schmidt

/-- PsiOscillationFromCriticalZerosHyp directly provides PsiOscillationSqrtHyp,
    since they assert the same proposition. -/
instance [PsiOscillationFromCriticalZerosHyp] : PsiOscillationSqrtHyp where
  oscillation := PsiOscillationFromCriticalZerosHyp.oscillation
