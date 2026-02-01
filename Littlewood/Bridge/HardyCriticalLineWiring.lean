/-
Pre-wire HardyCriticalLineZerosHyp for when Hardy's theorem completes.

Schmidt.HardyCriticalLineZerosHyp requires:
  infinite : Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1/2 }

STATUS: Conversion lemma proved. Instance depends on HardySetupV2Instance (3 sorry fields).
When those sorries close, this file gives Hardy → HardyCriticalLineZerosHyp automatically.

NOTE: Migrated from V1 (HardyInfiniteZeros) to V2 (HardyInfiniteZerosV2).
V1 had unsatisfiable field signatures; its proof was vacuously true.
-/

import Mathlib
import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.Aristotle.HardyInfiniteZerosV2
import Littlewood.Bridge.HardySetupV2Instance

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyCriticalLineWiring

open Complex Set ZetaZeros

/-! ## Conversion: real zeros → nontrivial zeros on critical line -/

/-- The map t ↦ 1/2 + it is injective. -/
lemma critical_line_injective :
    Function.Injective (fun t : ℝ => (1/2 : ℂ) + Complex.I * (t : ℂ)) := by
  intro a b hab
  have := congr_arg Complex.im hab
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im] at this
  exact this

/-- If {t : ℝ | ζ(1/2+it) = 0} is infinite, so is {ρ ∈ zetaNontrivialZeros | ρ.re = 1/2}. -/
theorem hardy_zeros_to_nontrivial_zeros
    (h : Set.Infinite {t : ℝ | riemannZeta (1/2 + Complex.I * t) = 0}) :
    Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1/2 } := by
  apply Set.Infinite.mono _
    (h.image (fun (a : ℝ) _ (b : ℝ) _ hab => critical_line_injective hab))
  intro ρ ⟨t, ht, hρ⟩
  subst hρ
  refine ⟨⟨ht, ?_, ?_⟩, ?_⟩ <;> simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im] <;> norm_num

/-! ## The instance (depends on HardySetupInstance having 0 sorries) -/

/-- Hardy's theorem: infinitely many zeros of ζ on the critical line.
    This instance closes when HardySetupV2Instance's 3 sorry fields are proved. -/
instance : Schmidt.HardyCriticalLineZerosHyp where
  infinite := hardy_zeros_to_nontrivial_zeros HardyInfiniteZerosV2.hardy_infinitely_many_zeros_v2

end HardyCriticalLineWiring
