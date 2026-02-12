/- 
Atomic second-mean-value existence theorem.

This file isolates the deep measure-theoretic step used in
`Littlewood.Aristotle.SecondMVT`.
-/

import Mathlib

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.SecondMVTAtomic

open MeasureTheory intervalIntegral Set

/-- **Atomic sorry**: du Bois-Reymond second MVT existence form on `[a,b]`. -/
theorem second_mvt_exists_c_atomic {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf_mono : MonotoneOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume a b) :
    ∃ c ∈ Icc a b, ∫ t in a..b, f t * g t =
      f a * (∫ t in a..c, g t) + f b * (∫ t in c..b, g t) := by
  sorry

end Aristotle.SecondMVTAtomic

