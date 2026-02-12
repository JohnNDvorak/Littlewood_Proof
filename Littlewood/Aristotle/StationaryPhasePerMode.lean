/-
Per-mode tail wrapper for Hardy cosine oscillatory integrals.

This is a direct specialization of the existing first-derivative Van der Corput
bound to Hardy cosine modes.
-/

import Mathlib
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.VdcFirstDerivTest

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.StationaryPhasePerMode

open Set intervalIntegral HardyEstimatesPartial

/--
Van der Corput tail bound for a Hardy cosine mode, under explicit phase
regularity and monotonic-derivative hypotheses.
-/
theorem per_mode_tail_bound
    (n : ℕ) (a b m : ℝ)
    (hab : a ≤ b) (hm : 0 < m)
    (hphi : Differentiable ℝ (fun t => hardyTheta t - t * Real.log (↑n + 1)))
    (hphi' : Differentiable ℝ (deriv (fun t => hardyTheta t - t * Real.log (↑n + 1))))
    (hphi'' : Continuous (deriv (deriv (fun t => hardyTheta t - t * Real.log (↑n + 1)))))
    (hphi'_lower : ∀ t ∈ Icc a b,
      m ≤ deriv (fun t => hardyTheta t - t * Real.log (↑n + 1)) t)
    (hphi''_nonneg : ∀ t ∈ Icc a b,
      0 ≤ deriv (deriv (fun t => hardyTheta t - t * Real.log (↑n + 1))) t) :
    |∫ t in a..b, hardyCos n t| ≤ 3 / m := by
  simpa [hardyCos] using
    (VdcFirstDerivTest.vdc_cos_bound
      (phi := fun t => hardyTheta t - t * Real.log (↑n + 1))
      (a := a) (b := b) (m := m)
      hab hm hphi hphi' hphi'' hphi'_lower hphi''_nonneg)

end Aristotle.StationaryPhasePerMode
