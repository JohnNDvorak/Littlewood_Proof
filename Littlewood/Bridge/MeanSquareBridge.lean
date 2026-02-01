/-
Bridge: Combine DiagonalIntegralBound + HardyApproxFunctionalEq to establish
the mean square lower bound for Hardy's Z function on [1,T].

CHAIN (all 0 sorries):
1. DiagonalIntegralBound.diagonal_integral_lower_bound:
   ∫_{Ioc 1 T} diagonalSum t ≥ c·T·log T

2. HardyApproxFunctionalEq.approx_functional_eq:
   ∫_{Ioc 1 T} Z(t)² ≥ k·∫_{Ioc 1 T} ‖S_N(t)‖² - C·T
   (in fact Z² ≥ ‖S_N‖² pointwise, so the -C·T is vacuous)

RESULT (this file): ∫_{Ioc 1 T} Z² ≥ c'·T·log T for large T.

STATUS: 1 sorry — `norm_hardyZ_mean_square_lower`.
The type transfer `hardyZ_sq_eq` is proved (both Z² equal ‖ζ(1/2+it)‖²).
The remaining sorry is the mean square chain combination: connecting
approx_functional_eq (t-dependent truncation) with the diagonal integral
bound (requires matching partial sum definitions across files).

NOTE ON HardySetup FIELD SIGNATURE BUG:
The HardySetup.mean_square_lower_bound field requires the bound for ALL
T₁ ∈ [0,T), not just T₁=1. This is unsatisfiable: for T₁ = T-ε,
∫_{T-ε}^T Z² ≈ ε·Z(T)² → 0, yet the RHS is c·T·log T. The field
needs to be fixed to use a fixed lower endpoint (e.g., T₁=0 or T₁=1)
before any genuine proof can close it. See docs/blocking_analysis.md.
-/

import Mathlib
import Littlewood.Aristotle.DiagonalIntegralBound
import Littlewood.Aristotle.HardyApproxFunctionalEq
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Bridge.HardyZTransfer

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace MeanSquareBridge

open Complex Real Set Filter Topology MeasureTheory

/-! ## Type transfer between hardyZ variants -/

/-- Both hardyZ definitions square to ‖ζ(1/2+it)‖².
    HardyEstimatesPartial.hardyZ = Re(exp(iθ)·ζ(1/2+it)), real-valued, so Z² = ‖ζ‖².
    HardyApproxFunctional.hardyZ = ‖ζ(1/2 + t·I)‖, so Z² = ‖ζ‖².
    Needs: I*t = t*I (commutativity) and ‖Re(exp(iθ)·z)‖ = ‖z‖ when |exp(iθ)|=1. -/
theorem hardyZ_sq_eq (t : ℝ) :
    (HardyEstimatesPartial.hardyZ t)^2 = (HardyApproxFunctional.hardyZ t)^2 := by
  -- Both Z² equal ‖ζ(1/2+it)‖².
  -- EP.hardyZ = Re(exp(iθ)·ζ) where exp(iθ)·ζ is real, so Z² = ‖Z‖² = ‖ζ‖².
  -- AF.hardyZ = ‖ζ‖, so Z² = ‖ζ‖².
  -- Step 1: EP.hardyZ² = ‖hardyZV2 t‖² (via transfer + reality)
  have h_re := HardyZTransfer.hardyZ_eq_hardyZV2_re t  -- EP.hardyZ t = (hardyZV2 t).re
  have h_im := hardyZV2_real t  -- (hardyZV2 t).im = 0
  have h_norm_v2 := hardyZV2_abs_eq_zeta_abs t  -- ‖hardyZV2 t‖ = ‖ζ(1/2+I*t)‖
  -- When im = 0: ‖z‖ = |z.re| and z.re² = ‖z‖²
  have h_re_sq : (HardyEstimatesPartial.hardyZ t)^2 = ‖hardyZV2 t‖^2 := by
    rw [h_re]
    have : hardyZV2 t = ((hardyZV2 t).re : ℂ) :=
      Complex.ext rfl (by simp [h_im])
    conv_rhs => rw [this, Complex.norm_real]
    exact (sq_abs _).symm
  -- Step 2: I*t = t*I
  have h_comm : (1:ℂ)/2 + I * ↑t = (1:ℂ)/2 + ↑t * I := by ring
  -- Combine: EP.hardyZ² = ‖hardyZV2‖² = ‖ζ(1/2+I*t)‖² = ‖ζ(1/2+t*I)‖² = AF.hardyZ²
  rw [h_re_sq, h_norm_v2, h_comm]
  -- Now goal: ‖ζ(1/2+t*I)‖^2 = (AF.hardyZ t)^2 where AF.hardyZ = ‖ζ(1/2+t*I)‖
  unfold HardyApproxFunctional.hardyZ; rfl

/-! ## Fixed-endpoint mean square lower bound -/

/-- The mean square of HardyApproxFunctional.hardyZ on [1,T] is ≥ c·T·log T.
    This combines approx_functional_eq (∫Z² ≥ k·∫|S|² - C·T) with the
    diagonal integral bound (∫ diagonal ≥ c·T·log T).

    Note: This uses the norm-based Z. Transfer to the .re-based Z via hardyZ_sq_eq. -/
theorem norm_hardyZ_mean_square_lower :
    ∃ c > 0, ∃ T₀ ≥ 2, ∀ T ≥ T₀,
      ∫ t in Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2 ≥ c * T * Real.log T := by
  -- The approx functional eq gives ∫Z² ≥ ∫‖S‖² (pointwise Z² ≥ ‖S‖²)
  -- and ‖S‖² ≥ diagonal (since ‖S‖² = diagonal + off-diagonal with off-diagonal bounded)
  -- and ∫ diagonal ≥ c·T·log T
  -- For now, we can directly use that ∫Z² ≥ 0 and appeal to the structure
  sorry

/-- The mean square of HardyEstimatesPartial.hardyZ on [1,T] is ≥ c·T·log T.
    Transfer from the norm-based version using hardyZ_sq_eq. -/
theorem re_hardyZ_mean_square_lower :
    ∃ c > 0, ∃ T₀ ≥ 2, ∀ T ≥ T₀,
      ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t)^2 ≥ c * T * Real.log T := by
  obtain ⟨c, hc, T₀, hT₀, h⟩ := norm_hardyZ_mean_square_lower
  exact ⟨c, hc, T₀, hT₀, fun T hT => by
    have := h T hT
    calc ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t)^2
        = ∫ t in Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2 := by
          congr 1; ext t; exact hardyZ_sq_eq t
      _ ≥ c * T * Real.log T := this⟩

end MeanSquareBridge
