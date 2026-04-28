 /-
Siegel contour integral infrastructure for the Riemann-Siegel expansion.

This file formalizes the actual contour object that the upstream steepest-descent
argument acts on. The missing proof in the repo is no longer "what contour
integral are we deforming?" but the narrower analytic step of proving the
contour-to-saddle estimate on that object.

What is provided here:

1. Gabcke's normalized block parameters `τ`, `z`, and `q`.
2. The phase-normalizing unit factor `U(t)` from the Siegel/Gabcke formula.
3. The diagonal contour through the saddle point `a = √(t / (2π))`.
4. The critical-line contour integrand and its truncated contour integral.
5. Exact algebraic identities relating these objects to the existing block
   parametrization infrastructure.

This file does **not** yet prove the full Riemann-Siegel contour representation
or the steepest-descent deformation estimate. Those remain the genuine analytic
leaf.

References:
- Siegel 1932, §3
- Gabcke 1979, Chapter 1 §1.2 and Chapter 2
- Gabcke 1979, equation (1.7), (1.9), and Lehmersche normalization
-/

import Littlewood.Aristotle.ContourIntegrationV2
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.Standalone.SteepestDescentContour

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.SiegelContourIntegral

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam
open Aristotle.ContourIntegrationV2
open Aristotle.Standalone.SteepestDescentContour

/-! ## Gabcke's normalized parameters -/

/-- Gabcke's `a = √(t / (2π))`, identical to the saddle point location. -/
def siegelA (t : ℝ) : ℝ := saddlePoint t

/-- Gabcke's small parameter `τ = 1 / (2 * √(2t))`. -/
def siegelTau (t : ℝ) : ℝ := 1 / (2 * Real.sqrt (2 * t))

/-- Lehmer/Gabcke's normalized block coordinate `z = 1 - 2p`. -/
def gabckeZ (p : ℝ) : ℝ := 1 - 2 * p

/-- Gabcke's `q = √π * z = √π * (1 - 2p)`. -/
def gabckeQ (p : ℝ) : ℝ := Real.sqrt Real.pi * gabckeZ p

/-- The unit phase factor `U(t)` in Gabcke's equation (1.9). -/
def siegelUPhase (t : ℝ) : ℝ :=
  t / 2 * Real.log (t / (2 * Real.pi)) - t / 2 - Real.pi / 8 - hardyTheta t

/-- The complex unit `U(t) = exp(i * phase)` from the saddle-point expansion. -/
def siegelU (t : ℝ) : ℂ := Complex.exp (Complex.I * (siegelUPhase t : ℂ))

theorem siegelA_eq_saddlePoint (t : ℝ) : siegelA t = saddlePoint t := rfl

theorem siegelA_eq_block (k : ℕ) (t : ℝ) :
    siegelA t = (k : ℝ) + 1 + blockParam k t := by
  simpa [siegelA] using saddlePoint_eq_block k t

theorem gabckeQ_eq_sqrt_pi_mul_gabckeZ (p : ℝ) :
    gabckeQ p = Real.sqrt Real.pi * gabckeZ p := rfl

theorem gabckeZ_mem_Icc (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    gabckeZ p ∈ Icc (-1 : ℝ) 1 := by
  rcases hp with ⟨hp0, hp1⟩
  constructor <;> unfold gabckeZ <;> nlinarith

theorem abs_gabckeZ_le_one (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    |gabckeZ p| ≤ 1 := by
  rcases gabckeZ_mem_Icc p hp with ⟨hlo, hhi⟩
  exact abs_le.2 ⟨hlo, hhi⟩

theorem abs_gabckeQ_le_sqrt_pi (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    |gabckeQ p| ≤ Real.sqrt Real.pi := by
  have hpi : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  unfold gabckeQ
  rw [abs_mul, abs_of_nonneg hpi]
  simpa [mul_comm] using mul_le_of_le_one_left hpi (abs_gabckeZ_le_one p hp)

theorem siegelTau_pos (t : ℝ) (ht : 0 < t) : 0 < siegelTau t := by
  unfold siegelTau
  positivity

theorem norm_siegelU_eq_one (t : ℝ) : ‖siegelU t‖ = 1 := by
  unfold siegelU
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

theorem siegelTau_blockCoord (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    siegelTau (blockCoord k p) =
      1 / (4 * Real.sqrt Real.pi * ((k : ℝ) + 1 + p)) := by
  let u : ℝ := (k : ℝ) + 1 + p
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    positivity
  have hu_pos : 0 < u := by
    dsimp [u]
    positivity
  have hsqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hsqrt :
      Real.sqrt (2 * blockCoord k p) = 2 * Real.sqrt Real.pi * u := by
    have h4pi :
        Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) Real.pi]
      norm_num
    unfold blockCoord
    rw [show 2 * (2 * Real.pi * u ^ 2) = (4 * Real.pi) * u ^ 2 by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi) (u ^ 2), h4pi, Real.sqrt_sq hu_nonneg]
  unfold siegelTau
  rw [hsqrt]
  field_simp [hu_pos.ne', hsqrt_pi_ne]
  ring

theorem siegelTau_blockCoord' (k : ℕ) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    siegelTau (blockCoord k p) =
      1 / (4 * Real.sqrt Real.pi * ((k : ℝ) + 1 + p)) :=
  siegelTau_blockCoord k p hp.1

/-! ## Diagonal contour through the saddle -/

/-- The direction of Siegel's diagonal contour: slope `-1`, oriented from left
upper to right lower. -/
def siegelDiagonalDir : ℂ := 1 - Complex.I

/-- The point on the diagonal contour through the saddle `a`, parameterized by
real `u`, so that `u = 0` is exactly the saddle point. -/
def siegelDiagonalPoint (a u : ℝ) : ℂ := (a : ℂ) + u * siegelDiagonalDir

theorem siegelDiagonalDir_ne_zero : siegelDiagonalDir ≠ 0 := by
  norm_num [siegelDiagonalDir, Complex.ext_iff]

theorem siegelDiagonalPoint_zero (a : ℝ) :
    siegelDiagonalPoint a 0 = a := by
  simp [siegelDiagonalPoint]

theorem siegelDiagonalPoint_re (a u : ℝ) :
    (siegelDiagonalPoint a u).re = a + u := by
  simp [siegelDiagonalPoint, siegelDiagonalDir]

theorem siegelDiagonalPoint_im (a u : ℝ) :
    (siegelDiagonalPoint a u).im = -u := by
  simp [siegelDiagonalPoint, siegelDiagonalDir]

theorem siegelDiagonalPoint_sub_saddle (a u : ℝ) :
    siegelDiagonalPoint a u - a = u * siegelDiagonalDir := by
  simp [siegelDiagonalPoint]

theorem siegelDiagonalPoint_through_saddle (t u : ℝ) :
    siegelDiagonalPoint (siegelA t) u = (siegelA t : ℂ) + u * siegelDiagonalDir := rfl

/-! ## Critical-line contour integrand -/

/-- The numerator in Siegel's contour integral after specializing to
`s = 1/2 + it`. -/
def siegelCriticalNumerator (t : ℝ) (x : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (Real.pi : ℂ) * x ^ 2) *
    x ^ ((-(1 / 2 : ℂ)) + Complex.I * (t : ℂ))

/-- The denominator `e^{iπx} - e^{-iπx} = 2i sin(πx)` in Siegel's integral. -/
def siegelCriticalDenominator (x : ℂ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi : ℂ) * x) -
    Complex.exp (-Complex.I * (Real.pi : ℂ) * x)

/-- The critical-line contour integrand from Gabcke's equation (1.7). -/
def siegelCriticalIntegrand (t : ℝ) (x : ℂ) : ℂ :=
  2 * siegelCriticalNumerator t x / siegelCriticalDenominator x

/-- Truncation of Siegel's diagonal contour integral through the saddle `a`. -/
def siegelDiagonalTruncIntegral (t a R : ℝ) : ℂ :=
  ∫ u in -R..R, siegelDiagonalDir * siegelCriticalIntegrand t (siegelDiagonalPoint a u)

/-- The prefactor extracted at the saddle point before the Gaussian correction. -/
def siegelSaddlePrefactor (t a : ℝ) : ℂ :=
  Complex.exp
    ((((-(1 / 2 : ℂ)) + Complex.I * (t : ℂ)) * Complex.log a) -
      Complex.I * (Real.pi : ℂ) * (a : ℂ) ^ 2)

/-- The shifted correction factor after removing the saddle prefactor and the
Gaussian kernel. This is the analytic object that still needs to be estimated by
steepest descent. -/
def siegelShiftedFactor (t a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi : ℂ) * z ^ 2) *
    siegelCriticalNumerator t ((a : ℂ) + z) *
      (siegelSaddlePrefactor t a)⁻¹

theorem siegelCriticalIntegrand_eq (t : ℝ) (x : ℂ) :
    siegelCriticalIntegrand t x =
      2 * siegelCriticalNumerator t x / siegelCriticalDenominator x := rfl

theorem siegelSaddlePrefactor_ne_zero (t a : ℝ) :
    siegelSaddlePrefactor t a ≠ 0 := by
  unfold siegelSaddlePrefactor
  exact Complex.exp_ne_zero _

theorem siegelCriticalNumerator_eq_saddlePrefactor_mul_gaussian_mul_shifted
    (t a : ℝ) (z : ℂ) :
    siegelCriticalNumerator t ((a : ℂ) + z) =
      siegelSaddlePrefactor t a *
        Complex.exp (-Complex.I * (2 * Real.pi : ℂ) * z ^ 2) *
        siegelShiftedFactor t a z := by
  have hpref : siegelSaddlePrefactor t a ≠ 0 := siegelSaddlePrefactor_ne_zero t a
  have hgauss :
      Complex.exp (-Complex.I * (2 * Real.pi : ℂ) * z ^ 2) *
          Complex.exp (Complex.I * (2 * Real.pi : ℂ) * z ^ 2) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  unfold siegelShiftedFactor
  symm
  calc
    siegelSaddlePrefactor t a *
        Complex.exp (-Complex.I * (2 * Real.pi : ℂ) * z ^ 2) *
        (Complex.exp (Complex.I * (2 * Real.pi : ℂ) * z ^ 2) *
          siegelCriticalNumerator t ((a : ℂ) + z) *
          (siegelSaddlePrefactor t a)⁻¹)
      =
        siegelCriticalNumerator t ((a : ℂ) + z) *
          (siegelSaddlePrefactor t a * (siegelSaddlePrefactor t a)⁻¹) *
          (Complex.exp (-Complex.I * (2 * Real.pi : ℂ) * z ^ 2) *
            Complex.exp (Complex.I * (2 * Real.pi : ℂ) * z ^ 2)) := by
            ring
    _ = siegelCriticalNumerator t ((a : ℂ) + z) * (1 * 1) := by
          rw [mul_inv_cancel₀ hpref, hgauss]
          simp
    _ = siegelCriticalNumerator t ((a : ℂ) + z) := by simp

/-! ## Block coordinates and Gabcke normalization -/

theorem gabckeZ_blockParam_blockCoord (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    gabckeZ (blockParam k (blockCoord k p)) = 1 - 2 * p := by
  rw [blockParam_blockCoord k p hp]
  rfl

theorem gabckeQ_blockParam_blockCoord (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    gabckeQ (blockParam k (blockCoord k p)) = Real.sqrt Real.pi * (1 - 2 * p) := by
  rw [gabckeQ_eq_sqrt_pi_mul_gabckeZ, gabckeZ_blockParam_blockCoord k p hp]

theorem gabckeZ_blockCoord_mem_Icc (k : ℕ) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    gabckeZ (blockParam k (blockCoord k p)) ∈ Icc (-1 : ℝ) 1 := by
  rw [blockParam_blockCoord k p hp.1]
  exact gabckeZ_mem_Icc p hp

theorem abs_gabckeQ_blockCoord_le_sqrt_pi (k : ℕ) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    |gabckeQ (blockParam k (blockCoord k p))| ≤ Real.sqrt Real.pi := by
  rw [blockParam_blockCoord k p hp.1]
  exact abs_gabckeQ_le_sqrt_pi p hp

end Aristotle.Standalone.SiegelContourIntegral
