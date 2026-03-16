/-
OVERNIGHT TASK: Attempt to assemble Hardy's theorem from existing pieces.

Goal: Prove Set.Infinite {t : ℝ | riemannZeta (1/2 + I*t) = 0}

## Available Building Blocks (all sorry-free)

### Hardy Z properties:
- HardyZRealV2.hardyZV2_real: Z(t) is real-valued
- HardyZRealV2.continuous_hardyZV2: Z is continuous
- HardyZRealV2.hardyZV2_zero_iff_zeta_zero: Z(t)=0 ↔ ζ(1/2+it)=0
- HardyZRealV2.hardyZV2_abs_eq_zeta_abs: |Z(t)| = |ζ(1/2+it)|
- HardyEstimatesPartial.exp_iTheta_norm: |e^{iθ(t)}| = 1
- HardyZFirstMoment.hardyZ_abs_le: |Z(t)| ≤ |ζ(1/2+it)|
- HardyZCauchySchwarz.integral_cauchy_schwarz: Cauchy-Schwarz for integrals
- HardyZCauchySchwarz.hardyZ_eq_alt: alternative Z formula

### Contradiction:
- HardyZContradiction.BuildingBlocks: structure with 6 fields
- HardyZContradiction.contradiction_final_step: T log T vs T^{3/4+ε} → False
- HardyZContradiction.Z_continuous: Z continuous from BuildingBlocks
- HardyZContradiction.Z_constant_sign_implies_integral_eq_abs

### Convexity:
- ConvexityBounds.*: PL interpolation, Gamma/sin/cos bounds

### Critical line reality:
- CompletedZetaCriticalLine.completedRiemannZeta_critical_line_real

## GAP ANALYSIS

To populate BuildingBlocks, we need:
1. ✅ completedRiemannZeta_critical_line_real — in CompletedZetaCriticalLine
2. ✅ hardyZ_is_real — follows from HardyZRealV2.hardyZV2_real (+ transfer)
3. ⚠️ hardyZ_eq_norm_zeta — need |Z(t)| = |ζ(1/2+it)|, have it for V2 def
4. ❌ zeta_mean_square_lower_bound — MeanSquare.lean has 3 sorries
5. ❌ hardyZ_integral_bound — HardyEstimatesPartial.HardyEstimates.first_moment_upper
6. ⚠️ hardyZ_continuous — have continuous_hardyZV2, need for real-valued Z

Items 4-5 are the true gaps: the mean square lower bound and the first moment
upper bound. These are deep analytic results that require:
- Mean square: ∫|ζ(1/2+it)|² dt = T log T + O(T) (partially in MeanSquare.lean)
- First moment: |∫ Z(t) dt| ≤ C T^{1/2+ε} (conditional in HardyZFirstMoment)

The mean square lower bound is the critical missing piece.
-/

import Mathlib
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Aristotle.HardyZRealV4
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyZCauchySchwarz
import Littlewood.Aristotle.HardyZContradiction
import Littlewood.Aristotle.HardyInfrastructure
import Littlewood.Aristotle.ConvexityBounds
import Littlewood.Aristotle.CompletedZetaCriticalLine
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

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace HardyAssemblyAttempt

/-! ## Step 1: Available pieces inventory

These are the key sorry-free pieces we have:
-/

-- Z is real-valued
example (t : ℝ) : (hardyZV2 t).im = 0 := hardyZV2_real t

-- Z is continuous
example : Continuous hardyZV2 := continuous_hardyZV2

-- Z zeros ↔ zeta zeros
example (t : ℝ) : hardyZV2 t = 0 ↔ riemannZeta (1/2 + I * t) = 0 :=
  hardyZV2_zero_iff_zeta_zero t

-- |Z(t)| = |ζ(1/2+it)|
example (t : ℝ) : ‖hardyZV2 t‖ = ‖riemannZeta (1/2 + I * t)‖ :=
  hardyZV2_abs_eq_zeta_abs t

-- Completed zeta is real on critical line
example (t : ℝ) : (completedRiemannZeta (1/2 + I * t)).im = 0 :=
  CompletedZetaCriticalLine.completedRiemannZeta_critical_line_real t

-- Definition bridge
example (t : ℝ) : HardyEstimatesPartial.hardyZ t = (hardyZV2 t).re :=
  HardyZTransfer.hardyZ_eq_hardyZV2_re t

-- Contradiction framework exists
example := @HardyZContradiction.contradiction_final_step

/-! ## Step 2: What BuildingBlocks needs

The HardyZContradiction.BuildingBlocks structure requires:
1. completedRiemannZeta_critical_line_real — ✅ HAVE
2. hardyZ_is_real — ✅ HAVE (hardyZV2_real)
3. hardyZ_eq_norm_zeta — ✅ HAVE (hardyZV2_abs_eq_zeta_abs, after transfer)
4. zeta_mean_square_lower_bound — ❌ MISSING (3 sorries in MeanSquare.lean)
5. hardyZ_integral_bound — ❌ MISSING (conditional in HardyZFirstMoment)
6. hardyZ_continuous — ✅ HAVE (continuous_hardyZV2)

## GAP: Items 4 and 5 are deep analytic results.

Item 4 (mean square lower bound) requires:
  ∃ c > 0, ∃ T₀, ∀ T ≥ T₀, ∫₀ᵀ Z(t)² dt ≥ c T log T

This comes from ∫|ζ(1/2+it)|² = T log T + O(T), which is
partially proved in MeanSquare.lean but 3 sorries remain.

Item 5 (first moment upper bound) requires:
  ∀ ε > 0, ∃ C, ∀ T ≥ 1, |∫₀ᵀ Z(t) dt| ≤ C T^{1/2+ε}

This is the deep analytic estimate from the approximate functional equation.
HardyZFirstMoment has it conditionally, but the hypothesis isn't proved.

## CONCLUSION: Cannot complete Hardy assembly without closing MeanSquare
## sorries OR getting a new Aristotle file for the mean square lower bound.
-/

/-! ## Step 3: Partial assembly — what we CAN prove

Even without the mean square, we can prove some useful intermediate results
connecting the various Hardy Z definitions.
-/

/-- If Z has finitely many zeros, then ζ has finitely many critical line zeros. -/
theorem finitely_many_Z_zeros_implies_finitely_many_zeta_zeros
    (h : Set.Finite {t : ℝ | hardyZV2 t = 0}) :
    Set.Finite {t : ℝ | riemannZeta (1/2 + I * t) = 0} := by
  convert h using 1
  ext t
  exact (hardyZV2_zero_iff_zeta_zero t).symm

/-- Contrapositive: infinitely many ζ zeros on critical line →
    infinitely many Z zeros. -/
theorem infinitely_many_zeta_zeros_implies_Z_zeros
    (h : Set.Infinite {t : ℝ | riemannZeta (1/2 + I * t) = 0}) :
    Set.Infinite {t : ℝ | hardyZV2 t = 0} := by
  intro h_fin
  exact h (finitely_many_Z_zeros_implies_finitely_many_zeta_zeros h_fin)

/-- Z changes sign between consecutive zeros (sorry-free, from V2). -/
example := @hardyZV2_constant_sign_between_zeros

/-- Assuming the HardyEstimates structure is populated plus convexity bound,
    we get Hardy's theorem.
    This shows the deduction is complete — only the estimates are missing.
    Proved by constructing HardySetupV2 and applying hardy_infinitely_many_zeros_v2. -/
theorem hardy_from_estimates
    (est : HardyEstimatesPartial.HardyEstimates)
    (h_convex : ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∀ t : ℝ, |t| ≥ 2 →
      |HardyEstimatesPartial.hardyZ t| ≤ C * |t|^(1/4 + ε)) :
    ∀ T₀ : ℝ, ∃ t > T₀, HardyEstimatesPartial.hardyZ t = 0 := by
  -- Construct HardySetupV2 from the estimates
  have inst : HardyInfiniteZerosV2.HardySetupV2 := {
    Z := HardyEstimatesPartial.hardyZ
    Z_continuous := est.hardyZ_continuous
    Z_zero_iff := HardySetupInstance.hardyZ_zero_iff
    mean_square_lower := by
      obtain ⟨c, hc, T₀, hT₀, h⟩ := est.mean_square_lower
      exact ⟨c, hc, max T₀ 2, le_max_right _ _, fun T hT =>
        h T (le_trans (le_max_left _ _) hT)⟩
    first_moment_upper := by
      intro ε hε
      obtain ⟨C, hC, T₀, hT₀, h⟩ := est.first_moment_upper ε hε
      exact ⟨C, hC, max T₀ 2, le_max_right _ _, fun T hT =>
        h T (le_trans (le_max_left _ _) hT)⟩
    Z_convexity_bound := h_convex
  }
  -- Apply Hardy's theorem (V2)
  have h_inf := @HardyInfiniteZerosV2.hardy_infinitely_many_zeros_v2 inst
  -- Transfer from "Set.Infinite {t | ζ(1/2+it)=0}" to "∀ T₀, ∃ t > T₀, Z(t) = 0"
  intro T₀
  -- From infinite zeros of ζ, we get infinite zeros of Z
  have h_Z_inf : Set.Infinite {t : ℝ | HardyEstimatesPartial.hardyZ t = 0} := by
    apply Set.Infinite.mono h_inf
    intro t ht
    exact (HardySetupInstance.hardyZ_zero_iff t).mpr ht
  -- An infinite subset of ℝ is unbounded above
  by_contra h_no
  push_neg at h_no
  -- h_no : ∀ t > T₀, Z(t) ≠ 0
  -- So {t | Z(t) = 0} ⊆ Iic T₀ ∪ {stuff ≤ T₀}
  apply h_Z_inf.not_bddAbove
  exact ⟨T₀, fun t ht => by
    by_contra h_gt; push_neg at h_gt
    exact h_no t h_gt ht⟩

end HardyAssemblyAttempt
