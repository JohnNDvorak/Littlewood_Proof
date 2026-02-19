import Mathlib
import Littlewood.Aristotle.Standalone.RSPerBlockSignedBoundConstructive
import Littlewood.Aristotle.RiemannSiegelSignCancellation
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

namespace Aristotle.Standalone.RSFirstMomentQuarterFromCenteredBlocks

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-- Promote centered block control on `T ≥ 2π` to a full alternating-sqrt
decomposition on `T ≥ 2` by absorbing the compact interval `[2, 2π]` into a
single constant. -/
theorem errorTerm_alternatingSqrt_decomposition_from_centered_blocks
    {A R : ℝ} (hA : 0 < A)
    (hcenter :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R) :
    ∃ A' B : ℝ, A' > 0 ∧ B ≥ 0 ∧
      ∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A' * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B := by
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

  refine ⟨A, B, hA, hB_nonneg, ?_⟩
  intro T hT
  by_cases hT_long : 2 * Real.pi ≤ T
  · rcases Aristotle.Standalone.RSPerBlockSignedBoundConstructive.centered_blocks_to_global_alternating_of_centered_blocks
        (A := A) (R := R) hA_nonneg hcenter T hT_long with ⟨N, hN, hbound⟩
    refine ⟨N, hN, ?_⟩
    have hB_ge_Blong : Blong ≤ B := le_max_right Bsmall Blong
    exact le_trans hbound (by
      have : A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + Blong
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

/-- Centered-block route to the RS first-moment `T^(1/4)` bound. -/
theorem errorTerm_firstMoment_quarter_of_centered_blocks
    {A R : ℝ} (hA : 0 < A)
    (hcenter :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R) :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, ErrorTerm t| ≤ C * T ^ (1 / 4 : ℝ) := by
  refine RiemannSiegelSignCancellation.errorTerm_firstMoment_quarter_of_alternatingSqrt ?_
  exact errorTerm_alternatingSqrt_decomposition_from_centered_blocks hA hcenter

/-- Wiring form for Hardy's first-moment chain: centered-block control implies
the `ErrorTermFirstMomentBoundHyp` typeclass payload. -/
theorem errorTermFirstMomentBoundHyp_from_centered_blocks
    {A R : ℝ} (hA : 0 < A)
    (hcenter :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R) :
    HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp := by
  obtain ⟨C, hC, hquarter⟩ := errorTerm_firstMoment_quarter_of_centered_blocks hA hcenter
  refine ⟨?_⟩
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro T hT
  calc
    |∫ t in Ioc 1 T, ErrorTerm t| ≤ C * T ^ (1 / 4 : ℝ) := hquarter T hT
    _ ≤ C * T ^ (1 / 2 + ε) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
      exact Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ T) (by linarith)

/-- Combined Hardy first-moment wiring:
main-term hypothesis + centered-block RS control yields `HardyFirstMomentUpperHyp`. -/
theorem hardyFirstMomentUpperHyp_from_mainTerm_and_centered_blocks
    [HardyFirstMomentWiring.MainTermFirstMomentBoundHyp]
    {A R : ℝ} (hA : 0 < A)
    (hcenter :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R) :
    HardyFirstMomentUpperHyp := by
  letI : HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp :=
    errorTermFirstMomentBoundHyp_from_centered_blocks hA hcenter
  exact HardyFirstMomentWiring.hardyFirstMomentUpper_from_two_bounds

end Aristotle.Standalone.RSFirstMomentQuarterFromCenteredBlocks
