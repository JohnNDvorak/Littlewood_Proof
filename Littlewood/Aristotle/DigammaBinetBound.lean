/- 
Atomic Binet-style digamma bound used by `DigammaAsymptotic`.

This file isolates the deep analytic step:
  ‖Γ'(s)/Γ(s) - log(s)‖ ≤ C / ‖s‖
on the half-strip `Re(s) ≥ 1/4`, `|Im(s)| ≥ 1`.
-/

import Mathlib

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.DigammaBinetBound

open Complex

/-- **Atomic sorry**: Binet/digamma bound on a right half-strip away from the real axis. -/
theorem digamma_log_bound_atomic :
    ∃ C > 0, ∀ s : ℂ, s.re ≥ 1/4 → |s.im| ≥ 1 →
      Gamma s ≠ 0 →
      ‖deriv Gamma s / Gamma s - Complex.log s‖ ≤ C / ‖s‖ := by
  sorry

end Aristotle.DigammaBinetBound

