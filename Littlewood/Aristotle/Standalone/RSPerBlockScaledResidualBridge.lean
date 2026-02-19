import Mathlib
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.RSRemainderAlternating
import Littlewood.Aristotle.RiemannSiegelFirstMoment
import Littlewood.Aristotle.Standalone.RSPerBlockSignedBoundChain
import Littlewood.Bridge.HardyFirstMomentWiring

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RSPerBlockScaledResidualBridge

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.Standalone.RSPerBlockSignedBoundChain

/-- A concrete per-block residual hypothesis: each centered block error is bounded
by `R / hardyN T`. Summing over `hardyN T` blocks then yields a uniform centered
residual bound. -/
def ScaledPerBlockResidualInput (A R : ℝ) : Prop :=
  ∀ T : ℝ, T ≥ 2 →
    ∀ k : ℕ, k < hardyN T →
      |(∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
        - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ R / (hardyN T : ℝ)

/-- The scaled per-block residual hypothesis implies the local signed block clause
with constant error bound `R`. -/
theorem localPerBlockSignedInput_of_scaledResidual
    {A R : ℝ} (hR : 0 ≤ R)
    (hscaled : ScaledPerBlockResidualInput A R) :
    LocalPerBlockSignedInput A R := by
  intro T hT k hk
  refine ⟨(-1 : ℝ) ^ k, rfl, ?_⟩
  have hscaled_k :
      |(∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
        - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤
      R / (hardyN T : ℝ) := hscaled T hT k hk
  have hNpos_nat : 0 < hardyN T := by
    exact lt_of_lt_of_le (Nat.zero_lt_succ k) (Nat.succ_le_of_lt hk)
  have hNpos : 0 < (hardyN T : ℝ) := Nat.cast_pos.mpr hNpos_nat
  have hRmul : R ≤ R * (hardyN T : ℝ) := by
    have hN_ge_one : (1 : ℝ) ≤ (hardyN T : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hNpos_nat)
    calc
      R = R * 1 := by ring
      _ ≤ R * (hardyN T : ℝ) := by
            exact mul_le_mul_of_nonneg_left hN_ge_one hR
  have hdiv_le : R / (hardyN T : ℝ) ≤ R := by
    exact (div_le_iff₀ hNpos).2 hRmul
  exact le_trans hscaled_k hdiv_le

/-- Nontrivial bridge inequality: from per-block `R / hardyN T` control to the
uniform centered residual bound required by `CenteredResidualInput`. -/
theorem centeredResidualInput_of_scaledResidual
    {A R : ℝ} (hscaled : ScaledPerBlockResidualInput A R) :
    CenteredResidualInput A R := by
  intro T hT
  have hT_two : T ≥ 2 := by
    have htwo_pi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    exact le_trans htwo_pi hT
  have hT_nonneg : 0 ≤ T := by linarith
  have hNpos_nat : 0 < hardyN T := by
    have hstart0 : hardyStart 0 ≤ T := by
      rw [Aristotle.HardyNProperties.hardyStart_formula]
      simpa using hT
    exact (hardyN_lt_iff 0 T hT_nonneg).2 hstart0
  have hNpos : 0 < (hardyN T : ℝ) := Nat.cast_pos.mpr hNpos_nat

  let resid : ℕ → ℝ := fun k =>
    (∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
      - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))

  have hterm :
      ∀ k ∈ Finset.range (hardyN T), |resid k| ≤ R / (hardyN T : ℝ) := by
    intro k hk
    exact hscaled T hT_two k (Finset.mem_range.mp hk)

  have hsumabs :
      |∑ k ∈ Finset.range (hardyN T), resid k|
        ≤ ∑ k ∈ Finset.range (hardyN T), |resid k| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (fun k => resid k) (Finset.range (hardyN T)))

  have hsumle :
      (∑ k ∈ Finset.range (hardyN T), |resid k|)
        ≤ ∑ _k ∈ Finset.range (hardyN T), R / (hardyN T : ℝ) := by
    exact Finset.sum_le_sum hterm

  have hconst :
      (∑ _k ∈ Finset.range (hardyN T), R / (hardyN T : ℝ))
        = (hardyN T : ℝ) * (R / (hardyN T : ℝ)) := by
    simp

  have hcancel : (hardyN T : ℝ) * (R / (hardyN T : ℝ)) = R := by
    field_simp [ne_of_gt hNpos]

  calc
    |∑ k ∈ Finset.range (hardyN T), resid k|
        ≤ ∑ k ∈ Finset.range (hardyN T), |resid k| := hsumabs
    _ ≤ ∑ _k ∈ Finset.range (hardyN T), R / (hardyN T : ℝ) := hsumle
    _ = (hardyN T : ℝ) * (R / (hardyN T : ℝ)) := hconst
    _ = R := hcancel

/-- Direct global alternating-`sqrt` decomposition from the scaled per-block
residual hypothesis. -/
theorem globalAlternating_fixedA_of_scaledResidual
    {A R : ℝ} (hA : 0 < A)
    (hscaled : ScaledPerBlockResidualInput A R) :
    ∃ B : ℝ, B ≥ 0 ∧
      ∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)|
                + B := by
  have hcenter : CenteredResidualInput A R :=
    centeredResidualInput_of_scaledResidual hscaled
  exact globalAlternating_fixedA_of_centeredResidual hA hcenter

/-- Build `PerBlockSignedBoundHyp` from a single scaled per-block residual input.
This removes the separate centered-residual hypothesis. -/
theorem perBlockSignedBoundHyp_of_scaledResidual
    {A R : ℝ} (hA : 0 < A) (hR : 0 ≤ R)
    (hscaled : ScaledPerBlockResidualInput A R) :
    Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp := by
  have hlocal : LocalPerBlockSignedInput A R :=
    localPerBlockSignedInput_of_scaledResidual hR hscaled
  have hcenter : CenteredResidualInput A R :=
    centeredResidualInput_of_scaledResidual hscaled
  exact perBlockSignedBoundHyp_of_local_and_centered hA hlocal hcenter

/-- Ready-to-wire decomposition theorem in the same shape used by
`RiemannSiegelSignCancellation`. -/
theorem errorTerm_alternatingSqrt_decomposition_of_scaledResidual
    {A R : ℝ} (hA : 0 < A) (hR : 0 ≤ R)
    (hscaled : ScaledPerBlockResidualInput A R) :
    ∃ A' B : ℝ, A' > 0 ∧ B ≥ 0 ∧
      ∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A' * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B := by
  exact Aristotle.RSRemainderAlternating.errorTerm_alternatingSqrt_decomposition
    (perBlockSignedBoundHyp_of_scaledResidual hA hR hscaled)

/-- Direct wiring from scaled per-block residual control to the Hardy-chain
error-term first-moment hypothesis. -/
theorem errorTermFirstMomentBoundHyp_of_scaledResidual
    {A R : ℝ} (hA : 0 < A) (hR : 0 ≤ R)
    (hscaled : ScaledPerBlockResidualInput A R) :
    HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp :=
  RiemannSiegelFirstMoment.errorTermFirstMomentBound_from_quarter
    (perBlockSignedBoundHyp_of_scaledResidual hA hR hscaled)

end Aristotle.Standalone.RSPerBlockScaledResidualBridge
