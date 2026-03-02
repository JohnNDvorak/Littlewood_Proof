import Mathlib
import Littlewood.Aristotle.RSBlockDecomposition
import Littlewood.Aristotle.RSRemainderAlternating
import Littlewood.Aristotle.RiemannSiegelFirstMoment
import Littlewood.Aristotle.Standalone.RSPerBlockSignedBoundConstructive
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

namespace Aristotle.Standalone.RSPerBlockSignedBoundChain

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-- Local signed block control with fixed `A` and block-uniform error `B`. -/
def LocalPerBlockSignedInput (A B : ℝ) : Prop :=
  ∀ T : ℝ, T ≥ 2 →
    ∀ k : ℕ, k < hardyN T →
      ∃ s : ℝ, s = (-1 : ℝ) ^ k ∧
        |(∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
            ErrorTerm t) - s * A * Real.sqrt ((k : ℝ) + 1)| ≤ B

/-- Long-range centered residual control on breakpoint blocks (`T ≥ 2π`). -/
def CenteredResidualInput (A R : ℝ) : Prop :=
  ∀ T : ℝ, T ≥ 2 * Real.pi →
    |∑ k ∈ Finset.range (hardyN T),
      ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
          ErrorTerm t)
        - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R

/-- Promote centered residual control to a global alternating-`sqrt` bound on
`T ≥ 2` while keeping the same leading constant `A`. -/
theorem globalAlternating_fixedA_of_centeredResidual
    {A R : ℝ} (hA : 0 < A)
    (hcenter : CenteredResidualInput A R) :
    ∃ B : ℝ, B ≥ 0 ∧
      ∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)|
                + B := by
  let Bsmall : ℝ := ∫ t in Ioc (1 : ℝ) (2 * Real.pi), ‖ErrorTerm t‖
  let Blong : ℝ := |∫ t in Ioc (1 : ℝ) (hardyStart 0), ErrorTerm t| + R
  let B : ℝ := max Bsmall Blong

  have hA_nonneg : 0 ≤ A := le_of_lt hA
  have hB_nonneg : 0 ≤ B := by
    have hBsmall_nonneg : 0 ≤ Bsmall := by
      refine integral_nonneg ?_
      intro t
      exact norm_nonneg (ErrorTerm t)
    exact le_trans hBsmall_nonneg (le_max_left Bsmall Blong)

  refine ⟨B, hB_nonneg, ?_⟩
  intro T hT
  by_cases hT_long : 2 * Real.pi ≤ T
  · rcases
      _root_.Aristotle.Standalone.RSPerBlockSignedBoundConstructive.centered_blocks_to_global_alternating_of_centered_blocks
        (A := A) (R := R) hA_nonneg hcenter T hT_long with
      ⟨N, hN, hbound⟩
    refine ⟨N, hN, ?_⟩
    have hB_ge_Blong : Blong ≤ B := le_max_right Bsmall Blong
    exact le_trans hbound (by
      have :
          A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + Blong
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B := by
        linarith
      exact this)
  · have hT_short : T < 2 * Real.pi := lt_of_not_ge hT_long
    refine ⟨0, ?_, ?_⟩
    · have hT_one : (1 : ℝ) ≤ T := by linarith
      simpa using (Real.one_le_rpow hT_one (by norm_num : (0 : ℝ) ≤ 1 / 2))
    · have hsubset : Ioc (1 : ℝ) T ⊆ Ioc (1 : ℝ) (2 * Real.pi) := by
        intro t ht
        exact ⟨ht.1, le_trans ht.2 (le_of_lt hT_short)⟩
      have h_int_full : IntegrableOn (fun t : ℝ => ‖ErrorTerm t‖) (Ioc (1 : ℝ) (2 * Real.pi)) := by
        exact (errorTerm_integrable (2 * Real.pi)).norm
      have h_abs_le_norm :
          |∫ t in Ioc (1 : ℝ) T, ErrorTerm t|
            ≤ ∫ t in Ioc (1 : ℝ) T, ‖ErrorTerm t‖ := by
        simpa [Real.norm_eq_abs] using
          (MeasureTheory.norm_integral_le_integral_norm (f := fun t : ℝ => ErrorTerm t)
            (μ := volume.restrict (Ioc (1 : ℝ) T)))
      have h_norm_le_Bsmall :
          ∫ t in Ioc (1 : ℝ) T, ‖ErrorTerm t‖ ≤ Bsmall := by
        exact le_trans
          (setIntegral_mono_set h_int_full
            (ae_of_all _ (fun _ => norm_nonneg _))
            (Eventually.of_forall (fun t ht => hsubset ht)))
          (le_refl Bsmall)
      have h_abs_le_B : |∫ t in Ioc (1 : ℝ) T, ErrorTerm t| ≤ B := by
        exact le_trans (le_trans h_abs_le_norm h_norm_le_Bsmall) (le_max_left Bsmall Blong)
      have hmain_nonneg :
          0 ≤ A * |∑ k ∈ Finset.range (0 + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| := by
        exact mul_nonneg hA_nonneg (abs_nonneg _)
      linarith

/-- Build the full `PerBlockSignedBoundHyp` payload from:
1) local signed per-block control (retained for downstream compatibility), and
2) long-range centered residual control.

NOTE: After the 2026-03 simplification of `PerBlockSignedBoundHyp` (removal of
the false local clause), only the centered residual input is needed. The local
input parameter is retained for API stability but is unused. -/
theorem perBlockSignedBoundHyp_of_local_and_centered
    {A Blocal R : ℝ} (hA : 0 < A)
    (_hlocal : LocalPerBlockSignedInput A Blocal)
    (hcenter : CenteredResidualInput A R) :
    Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp := by
  rcases globalAlternating_fixedA_of_centeredResidual (A := A) (R := R) hA hcenter with
    ⟨Bglobal, hBglobal_nonneg, hglobal⟩
  exact ⟨A, Bglobal, hA, hBglobal_nonneg, hglobal⟩

/-- Ready-to-wire decomposition theorem in the remainder namespace shape,
constructed from local+centered block inputs. -/
theorem remainder_alternatingSqrt_of_local_and_centered
    {A Blocal R : ℝ} (hA : 0 < A)
    (hlocal : LocalPerBlockSignedInput A Blocal)
    (hcenter : CenteredResidualInput A R) :
    ∃ A' B : ℝ, A' > 0 ∧ B ≥ 0 ∧
      ∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A' * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B := by
  exact Aristotle.RSRemainderAlternating.errorTerm_alternatingSqrt_decomposition
    (perBlockSignedBoundHyp_of_local_and_centered hA hlocal hcenter)

/-- Ready-to-wire `ErrorTermFirstMomentBoundHyp` payload from local+centered
block inputs through the existing Riemann-Siegel first-moment chain. -/
theorem errorTermFirstMomentBoundHyp_of_local_and_centered
    {A Blocal R : ℝ} (hA : 0 < A)
    (hlocal : LocalPerBlockSignedInput A Blocal)
    (hcenter : CenteredResidualInput A R) :
    HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp :=
  RiemannSiegelFirstMoment.errorTermFirstMomentBound_from_quarter
    (perBlockSignedBoundHyp_of_local_and_centered hA hlocal hcenter)

end Aristotle.Standalone.RSPerBlockSignedBoundChain
