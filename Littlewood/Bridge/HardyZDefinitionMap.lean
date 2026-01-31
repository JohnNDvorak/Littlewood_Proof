/-
Map all Hardy Z definition variants across the project.

There are multiple Hardy Z definitions due to iterative Aristotle generation:
- HardyEstimatesPartial.hardyZ     (ℝ → ℝ, uses Complex.log.im for theta)
- HardyZRealV2.hardyZV2            (ℝ → ℂ, uses Complex.arg for theta)
- HardyZRealV4.hardyZV4            (ℝ → ℂ, uses Complex.arg for theta)
- HardyZContradiction.Z theta      (parameterized by theta)

This file collects the equivalence proofs.

KEY RESULTS:
- hardyTheta ≡ hardyThetaV2 (via Complex.log_im = Complex.arg)
- hardyZ t = (hardyZV2 t).re
- hardyZV2 = hardyZV4 (identical definitions)

All results sorry-free (0 sorries).
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Aristotle.HardyZRealV4
import Littlewood.Aristotle.HardyZContradiction
import Littlewood.Bridge.HardyZTransfer

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyZDefinitionMap

/-! ## Definition Inventory

| Name | Type | Theta | File |
|------|------|-------|------|
| HardyEstimatesPartial.hardyTheta | ℝ → ℝ | Im(log(Γ(...))) | HardyEstimatesPartial |
| hardyThetaV2 | ℝ → ℝ | arg(Γ(...)) | HardyZRealV2 |
| hardyThetaV4 | ℝ → ℝ | arg(Γ(...)) | HardyZRealV4 |
| HardyEstimatesPartial.hardyZ | ℝ → ℝ | Re(exp(iθ)·ζ) | HardyEstimatesPartial |
| hardyZV2 | ℝ → ℂ | exp(iθ)·ζ | HardyZRealV2 |
| hardyZV4 | ℝ → ℂ | exp(iθ)·ζ | HardyZRealV4 |
| HardyZContradiction.Z θ | ℝ → ℝ | Re(exp(iθ)·ζ) | HardyZContradiction |
-/

/-! ## Equivalences from HardyZTransfer -/

-- theta definitions agree (Im(log z) = arg z for z ≠ 0)
example : ∀ t, HardyEstimatesPartial.hardyTheta t = hardyThetaV2 t :=
  HardyZTransfer.hardyTheta_eq_thetaV2

-- hardyZ (real) = Re(hardyZV2)
example : ∀ t, HardyEstimatesPartial.hardyZ t = (hardyZV2 t).re :=
  HardyZTransfer.hardyZ_eq_hardyZV2_re

/-! ## V2 = V4 (identical definitions) -/

-- hardyThetaV2 and hardyThetaV4 are literally the same definition
lemma thetaV2_eq_thetaV4 (t : ℝ) : hardyThetaV2 t = hardyThetaV4 t := by
  rfl

-- hardyZV2 and hardyZV4 are literally the same definition
lemma hardyZV2_eq_hardyZV4 (t : ℝ) : hardyZV2 t = hardyZV4 t := by
  rfl

/-! ## Connection to HardyZContradiction.Z -/

-- HardyZContradiction.Z θ t = Re(exp(iθ(t)) · ζ(1/2+it))
-- When θ = hardyThetaV2, this equals hardyZ t

lemma contradiction_Z_eq_hardyZ (t : ℝ) :
    HardyZContradiction.Z hardyThetaV2 t = HardyEstimatesPartial.hardyZ t := by
  simp only [HardyZContradiction.Z, HardyEstimatesPartial.hardyZ,
    HardyZTransfer.hardyTheta_eq_thetaV2]

/-! ## Summary of Available Properties (all sorry-free) -/

-- From HardyZRealV2:
example : ∀ t, (hardyZV2 t).im = 0 := hardyZV2_real
example : Continuous hardyZV2 := continuous_hardyZV2
example : ∀ t, hardyZV2 t = 0 ↔ riemannZeta (1/2 + Complex.I * t) = 0 :=
  hardyZV2_zero_iff_zeta_zero
example : ∀ t, ‖hardyZV2 t‖ = ‖riemannZeta (1/2 + Complex.I * t)‖ :=
  hardyZV2_abs_eq_zeta_abs

-- From HardyEstimatesPartial:
example (t : ℝ) : ‖Complex.exp (Complex.I * HardyEstimatesPartial.hardyTheta t)‖ = 1 :=
  HardyEstimatesPartial.exp_iTheta_norm t

-- From HardyZTransfer:
example (t : ℝ) : |(hardyZV2 t).re| ≤ ‖riemannZeta (1/2 + Complex.I * t)‖ :=
  HardyZTransfer.hardyZ_abs_le_zeta_V2 t

end HardyZDefinitionMap
