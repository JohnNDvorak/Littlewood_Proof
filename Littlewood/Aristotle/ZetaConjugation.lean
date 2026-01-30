/-
Conjugation symmetry properties of the Riemann zeta function and Hurwitz zeta FE pair.

Non-redundant results from Aristotle (d407b50e):
- completedRiemannZeta_one_conj: the value at s=1 is real
- hurwitzEvenFEPair_zero_*: real-valuedness of FE pair components for a=0

Redundant results (already in project, NOT included here):
- riemannZeta_conj: already in HardyZReal.lean, ZeroCountingFunction.lean
- mellin_conj_of_real_valued: already in CompletedZetaCriticalLine.lean
- completedRiemannZeta_conj: already in HardyZConjugation.lean

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
The value of the completed Riemann zeta function at s=1 is real (invariant under conjugation).
-/
theorem completedRiemannZeta_one_conj :
    starRingEnd ℂ (completedRiemannZeta 1) = completedRiemannZeta 1 := by
      have h_zeta1 : completedRiemannZeta 1 = (Complex.ofReal (Real.eulerMascheroniConstant - Real.log (4 * Real.pi))) / 2 := by
        field_simp;
        convert congr_arg ( · * 2 ) completedRiemannZeta_one using 1 ; ring;
        norm_num [ Complex.ofReal_sub, Complex.ofReal_log ( show 0 ≤ Real.pi * 4 by positivity ) ];
      norm_num [ h_zeta1, Complex.ext_iff ];
      erw [ Complex.conj_ofReal ] ; norm_num

/-
The function f in the functional equation pair for the Riemann zeta function is real-valued.
-/
theorem hurwitzEvenFEPair_zero_f_real (x : ℝ) :
    ((HurwitzZeta.hurwitzEvenFEPair 0).f x).im = 0 := by
      unfold HurwitzZeta.hurwitzEvenFEPair;
      norm_num [ Function.comp, HurwitzZeta.evenKernel ]

/-
The function g in the functional equation pair for the Riemann zeta function is real-valued.
-/
theorem hurwitzEvenFEPair_zero_g_real (x : ℝ) :
    ((HurwitzZeta.hurwitzEvenFEPair 0).g x).im = 0 := by
      convert hurwitzEvenFEPair_zero_f_real x using 1

/-
The constants in the functional equation pair for the Riemann zeta function are real-valued.
-/
theorem hurwitzEvenFEPair_zero_constants_real :
    ((HurwitzZeta.hurwitzEvenFEPair 0).f₀).im = 0 ∧
    ((HurwitzZeta.hurwitzEvenFEPair 0).g₀).im = 0 ∧
    ((HurwitzZeta.hurwitzEvenFEPair 0).ε).im = 0 ∧
    ((HurwitzZeta.hurwitzEvenFEPair 0).k : ℂ).im = 0 := by
      norm_num [ HurwitzZeta.hurwitzEvenFEPair ]

end
