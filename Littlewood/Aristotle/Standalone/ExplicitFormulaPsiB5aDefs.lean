import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
import Littlewood.Development.HadamardProductZeta

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiSkeleton

open Aristotle.DirichletPhaseAlignment (ZerosBelow)

/-- The real part of the zero sum Σ_{|γ|≤T} x^ρ/ρ, abstracted behind a def
to prevent `ring` failures on Finset.sum expressions. -/
def zeroSumRe (x T : ℝ) : ℝ :=
  (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re

/-- The explicit formula error: ψ(x) - x + Σ Re(x^ρ/ρ).
Defined concretely so all B5a mathematical content concentrates
into `shifted_contours_bound`. -/
def shiftedRemainderRe (x T : ℝ) : ℝ :=
  Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + zeroSumRe x T

/-- Pointwise bound on ζ'/ζ on the critical line — the Hadamard product hypothesis.

    **Mathematical content** (Titchmarsh §9.6.1, Davenport Ch. 12):
    The Hadamard product for ζ gives:
      -ζ'/ζ(s) = -B - 1/(s-1) + Σ_ρ (1/(s-ρ) + 1/ρ)
    Decomposing the zero sum into nearby (|γ-t| ≤ 1) and distant (|γ-t| > 1)
    parts, with N(T+1)-N(T) ≤ C·logT and choosing δ = 1/logT:
      |ζ'/ζ(1/2+it)| ≤ A·(logT)²  for 1 ≤ |t| ≤ T, T ≥ 2.

    Since ζ'/ζ is not yet formalized in Mathlib, we state this as:
    the Perron contour integral of ζ'/ζ · x^s/s over the standard rectangle
    decomposes into vertical + horizontal segment contributions, each governed
    by the O((logT)²) pointwise bound:
      - Vertical: ≤ A · √x · (logT)³ / T  (from ∫₁ᵀ |ζ'/ζ|·√x/t dt)
      - Horizontal: ≤ A · √x · (logT)² / T  (from |ζ'/ζ|·√x/T · segment length)

    The contour integration step (converting pointwise to integral) requires
    complex analysis not in Mathlib. The algebraic reduction from this
    pre-standard form to the standard O(√x·(logT)²/√T) form is sorry-free
    in PerronAssumptionsBridge.lean (`large_T_assembly`).

    **SORRY STATUS** (2026-03-16): Delegated to HadamardProductZeta.hadamard_contour_bound.
    All downstream reductions (this -> LargeTContourBoundHyp -> large-T case of
    ContourRemainderBoundHyp) are sorry-free once this is provided.
    See PerronAssumptionsBridge.lean Part 17-23 for full gap specification. -/
class ZetaLogDerivPointwiseBoundHyp : Prop where
  bound : ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
    |shiftedRemainderRe x T| ≤
      A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
      2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T)

/-- Definitional equality between this file's shiftedRemainderRe and the
    HadamardProductZeta version (both expand to the same expression). -/
private theorem shiftedRemainderRe_eq (x T : ℝ) :
    shiftedRemainderRe x T =
      Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T := by
  rfl

instance : ZetaLogDerivPointwiseBoundHyp where
  bound := by
    obtain ⟨A, hA, h⟩ := Littlewood.Development.HadamardProductZeta.hadamard_contour_bound
    exact ⟨A, hA, fun x T hx hT => by rw [shiftedRemainderRe_eq]; exact h x T hx hT⟩

/-! ### Algebraic reduction: segment form -> standard form

The following inline lemmas reduce the pre-standard segment bound
(vertical + horizontal) to the standard O(√x·(logT)²/√T) form.
These duplicate the bridge's `large_T_assembly` to avoid an import cycle. -/

/-- For T ≥ 16, logT ≤ √T.
    Proof: √16 = 4, exp(u) ≥ u² for u ≥ 4, so T = (√T)² ≤ exp(√T). -/
private theorem logT_le_sqrtT_local {T : ℝ} (hT : 16 ≤ T) :
    Real.log T ≤ Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  rw [← Real.exp_le_exp]
  calc Real.exp (Real.log T) = T := Real.exp_log hT_pos
    _ = (Real.sqrt T) ^ 2 := (Real.sq_sqrt hT_pos.le).symm
    _ ≤ Real.exp (Real.sqrt T) := by
        have h4 : (4 : ℝ) ≤ Real.sqrt T := by
          calc (4 : ℝ) = Real.sqrt 16 := by
                rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
                    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
            _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
        have hu0 : 0 ≤ Real.sqrt T := by linarith
        have h_taylor := Real.sum_le_exp_of_nonneg hu0 4
        simp [Finset.sum_range_succ, Nat.factorial] at h_taylor
        nlinarith [sq_nonneg (Real.sqrt T - 4)]

/-- Segment form -> standard form: for T ≥ 16,
    A·√x·(logT)³/T + 2A·√x·(logT)²/T ≤ 3A·(√x·(logT)²/√T). -/
private theorem segment_to_standard_form {A x T : ℝ} (hA : 0 < A)
    (_hx : x ≥ 2) (hT : 16 ≤ T) :
    A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
    2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T) ≤
    3 * A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  have hT_pos : 0 < T := by linarith
  have h_sqrtT : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  have h_sqrt_le_T : Real.sqrt T ≤ T := by
    calc Real.sqrt T ≤ Real.sqrt T * Real.sqrt T :=
          le_mul_of_one_le_right h_sqrtT.le (by rw [Real.one_le_sqrt]; linarith)
      _ = T := Real.mul_self_sqrt hT_pos.le
  have hlogT_nn : 0 ≤ Real.log T := (Real.log_pos (by linarith : (1 : ℝ) < T)).le
  have h_log_sqrt := logT_le_sqrtT_local hT
  have h_vert : A * (Real.sqrt x * (Real.log T) ^ 3 / T) ≤
      A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    rw [div_le_div_iff₀ hT_pos h_sqrtT]
    have h_sq_T : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT_pos.le
    calc Real.sqrt x * (Real.log T) ^ 3 * Real.sqrt T
        = Real.sqrt x * ((Real.log T) ^ 2 * Real.log T * Real.sqrt T) := by ring
      _ ≤ Real.sqrt x * ((Real.log T) ^ 2 * Real.sqrt T * Real.sqrt T) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg x)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_log_sqrt (sq_nonneg _)) h_sqrtT.le
      _ = Real.sqrt x * ((Real.log T) ^ 2 * (Real.sqrt T * Real.sqrt T)) := by ring
      _ = Real.sqrt x * ((Real.log T) ^ 2 * T) := by rw [h_sq_T]
      _ = Real.sqrt x * (Real.log T) ^ 2 * T := by ring
  have h_horiz : 2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T) ≤
      2 * A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_div_iff₀ hT_pos h_sqrtT]
    exact mul_le_mul_of_nonneg_left h_sqrt_le_T
      (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _))
  linarith

/-- Large-T contour bound -- derived from `ZetaLogDerivPointwiseBoundHyp`.
    **SORRY FLOW**: Transits 1 sorry from `ZetaLogDerivPointwiseBoundHyp`. -/
class LargeTContourBoundHyp : Prop where
  bound : ∃ C₁ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
    |shiftedRemainderRe x T| ≤ C₁ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)

instance : LargeTContourBoundHyp where
  bound := by
    obtain ⟨A, hA, h_seg⟩ := ZetaLogDerivPointwiseBoundHyp.bound
    exact ⟨3 * A, by positivity, fun x T hx hT => by
      calc |shiftedRemainderRe x T|
          ≤ A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
            2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T) := h_seg x T hx hT
        _ ≤ 3 * A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
            segment_to_standard_form hA hx hT⟩

theorem large_T_from_zeta_logderiv :
    ∃ C₁ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤ C₁ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
  LargeTContourBoundHyp.bound

/-- Contour remainder bound -- Davenport Ch. 17, Montgomery-Vaughan §12.5.
    |ψ(x) - x + Σ Re(x^ρ/ρ)| ≤ C·(√x·(logT)²/√T).

    **SORRY STATUS** (2026-03-16):
    - Large-T case (T ≥ 16): transits `ZetaLogDerivPointwiseBoundHyp` (sorry #1)
    - Small-T case (T ∈ [2,16]): transits `SmallTPerronBoundHyp` (sorry #2)
    Both sub-sorrys are INDEPENDENT and IRREDUCIBLE within this file.

    **CIRCULARITY NOTE**: PerronExplicit's `general_explicit_formula_from_perron`
    uses `ContourRemainderBoundHyp.bound` (via `contour_integral_remainder_bound`),
    so the bridge's `small_T_contour_bound` is NOT an independent proof -- it
    transits the small-T sorry circularly. -/
class ContourRemainderBoundHyp : Prop where
  bound : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
    |shiftedRemainderRe x T| ≤ Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)

/-! ### Hadamard product sub-decomposition -- algebraic infrastructure -/

theorem segment_form_from_separate_bounds {A_v A_h x T : ℝ}
    (_hAv : 0 < A_v) (_hAh : 0 < A_h) (_hx : x ≥ 2) (_hT : 16 ≤ T)
    (h_vert : |shiftedRemainderRe x T| ≤
      A_v * (Real.sqrt x * (Real.log T) ^ 3 / T))
    (h_horiz_bound : A_h * (Real.sqrt x * (Real.log T) ^ 2 / T) ≥ 0) :
    |shiftedRemainderRe x T| ≤
      A_v * (Real.sqrt x * (Real.log T) ^ 3 / T) +
      2 * A_h * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  linarith

theorem vertical_error_nonneg (x T : ℝ) (_hx : x ≥ 2) (hT : T ≥ 2) :
    0 ≤ Real.sqrt x * (Real.log T) ^ 3 / T := by
  apply div_nonneg _ (by linarith)
  apply mul_nonneg (Real.sqrt_nonneg _)
  exact pow_nonneg (Real.log_nonneg (by linarith)) 3

theorem horizontal_error_nonneg (x T : ℝ) (_hx : x ≥ 2) (hT : T ≥ 2) :
    0 ≤ Real.sqrt x * (Real.log T) ^ 2 / T := by
  apply div_nonneg _ (by linarith)
  exact mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)

theorem horizontal_le_vertical_error {x T : ℝ} (_hx : x ≥ 2) (hT : 16 ≤ T) :
    Real.sqrt x * (Real.log T) ^ 2 / T ≤
    Real.sqrt x * (Real.log T) ^ 3 / T := by
  have hT_pos : 0 < T := by linarith
  apply div_le_div_of_nonneg_right _ hT_pos.le
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg x)
  have hlogT : 1 ≤ Real.log T := by
    have : Real.log (Real.exp 1) ≤ Real.log T := by
      apply Real.log_le_log (Real.exp_pos 1)
      calc Real.exp 1 ≤ 3 := by
            have := Real.exp_one_lt_d9; linarith
        _ ≤ T := by linarith
    rwa [Real.log_exp] at this
  calc (Real.log T) ^ 2 = (Real.log T) ^ 2 * 1 := by ring
    _ ≤ (Real.log T) ^ 2 * Real.log T :=
        mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)
    _ = (Real.log T) ^ 3 := by ring

theorem segment_equal_constants_bound {A x T : ℝ} (hA : 0 < A) (hx : x ≥ 2) (hT : 16 ≤ T) :
    A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
    2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T) ≤
    3 * A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
  segment_to_standard_form hA hx hT

theorem zeta_logderiv_suffices_for_large_T
    (A : ℝ) (hA : 0 < A)
    (h_seg : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
        2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T)) :
    ∃ C₁ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        C₁ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
  ⟨3 * A, by positivity, fun x T hx hT =>
    (h_seg x T hx hT).trans (segment_to_standard_form hA hx hT)⟩

theorem pointwise_to_segment_algebra
    (P x T : ℝ) (_hP : 0 < P) (_hx : x ≥ 2) (_hT : 16 ≤ T) :
    2 * P * (Real.sqrt x * (Real.log T) ^ 3 / T) +
    2 * (2 * P) * (Real.sqrt x * (Real.log T) ^ 2 / T) =
    2 * P * Real.sqrt x * ((Real.log T) ^ 3 + 2 * (Real.log T) ^ 2) / T := by
  ring

theorem pointwise_to_standard_constant (P : ℝ) (hP : 0 < P) :
    0 < 6 * P := by positivity

theorem log_combined_le_standard {T : ℝ} (hT : 16 ≤ T) :
    (Real.log T) ^ 3 + 2 * (Real.log T) ^ 2 ≤
    3 * (Real.log T) ^ 2 * Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  have h_sqrtT : 1 ≤ Real.sqrt T := by
    rw [Real.one_le_sqrt]; linarith
  have hlogT : 0 ≤ Real.log T := (Real.log_pos (by linarith : (1 : ℝ) < T)).le
  have h_log_sqrt := logT_le_sqrtT_local hT
  calc (Real.log T) ^ 3 + 2 * (Real.log T) ^ 2
      = (Real.log T) ^ 2 * Real.log T + 2 * (Real.log T) ^ 2 * 1 := by ring
    _ ≤ (Real.log T) ^ 2 * Real.sqrt T + 2 * (Real.log T) ^ 2 * Real.sqrt T := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_log_sqrt (sq_nonneg _)
        · exact mul_le_mul_of_nonneg_left h_sqrtT (by positivity)
    _ = 3 * (Real.log T) ^ 2 * Real.sqrt T := by ring

/-! ### Case-split infrastructure for ContourRemainderBoundHyp -/

theorem contour_case_split
    (C_s C_l : ℝ) (hCs : 0 < C_s) (_hCl : 0 < C_l)
    (h_small : ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |shiftedRemainderRe x T| ≤
        C_s * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T))
    (h_large : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        C_l * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  refine ⟨max C_s C_l, lt_max_of_lt_left hCs, ?_⟩
  intro x T hx hT
  have h_err_nn : 0 ≤ Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by
    apply div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (Real.sqrt_nonneg _)
  by_cases hT16 : T ≤ 16
  · calc |shiftedRemainderRe x T|
        ≤ C_s * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
          h_small x T hx hT hT16
      _ ≤ max C_s C_l * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h_err_nn
  · push_neg at hT16
    calc |shiftedRemainderRe x T|
        ≤ C_l * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
          h_large x T hx (by linarith)
      _ ≤ max C_s C_l * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) h_err_nn

theorem contour_large_T_available :
    ∃ C₁ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        C₁ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
  LargeTContourBoundHyp.bound

theorem contour_from_small_T
    (h_small : ∃ C₀ > (0:ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |shiftedRemainderRe x T| ≤
        C₀ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  obtain ⟨C₀, hC₀, h₀⟩ := h_small
  obtain ⟨C₁, hC₁, h₁⟩ := contour_large_T_available
  exact contour_case_split C₀ C₁ hC₀ hC₁ h₀ h₁

/-! ### Log² absorption -- key algebraic step for small-T closure -/

theorem log_sq_le_mul_sqrt (x : ℝ) (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  have hx0 : 0 ≤ x := by linarith
  have h1 : Real.log x ≤ 4 * x ^ ((1:ℝ)/4) := by
    have := Real.log_le_rpow_div hx0 (show (0:ℝ) < 1/4 by positivity); linarith
  calc (Real.log x) ^ 2
      ≤ (4 * x ^ ((1:ℝ)/4)) ^ 2 := pow_le_pow_left₀ (Real.log_nonneg hx) h1 2
    _ = 16 * (x ^ ((1:ℝ)/4)) ^ (2:ℕ) := by ring
    _ = 16 * x ^ ((1:ℝ)/2) := by
        rw [← Real.rpow_natCast (x ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hx0]; norm_num

theorem log_sq_absorbed_by_error (x T : ℝ) (hx : 1 ≤ x) (hT_lo : 2 ≤ T) (hT_hi : T ≤ 16) :
    (Real.log x) ^ 2 ≤ (64 / (Real.log 2) ^ 2) *
      (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  have hT_pos : 0 < T := by linarith
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  have hlog2_sq : 0 < (Real.log 2) ^ 2 := sq_pos_of_pos (Real.log_pos (by norm_num))
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
  have hsqrtT_le : Real.sqrt T ≤ 4 := by
    calc Real.sqrt T ≤ Real.sqrt 16 := Real.sqrt_le_sqrt (by linarith)
      _ = 4 := by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
  have hlog2_nn : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have h_sq_mono : (Real.log 2) ^ 2 ≤ (Real.log T) ^ 2 :=
    pow_le_pow_left₀ hlog2_nn hlogT 2
  have h_key : (Real.log 2) ^ 2 * Real.sqrt T ≤ 4 * (Real.log T) ^ 2 := by
    calc (Real.log 2) ^ 2 * Real.sqrt T
        ≤ (Real.log T) ^ 2 * Real.sqrt T :=
          mul_le_mul_of_nonneg_right h_sq_mono hsqrtT_pos.le
      _ ≤ (Real.log T) ^ 2 * 4 :=
          mul_le_mul_of_nonneg_left hsqrtT_le (sq_nonneg _)
      _ = 4 * (Real.log T) ^ 2 := by ring
  have h_16 : 16 ≤ 64 / (Real.log 2) ^ 2 * ((Real.log T) ^ 2 / Real.sqrt T) := by
    rw [div_mul_div_comm, le_div_iff₀ (mul_pos hlog2_sq hsqrtT_pos)]
    have := mul_le_mul_of_nonneg_left h_key (show (0:ℝ) ≤ 16 by norm_num)
    linarith
  calc (Real.log x) ^ 2
      ≤ 16 * Real.sqrt x := log_sq_le_mul_sqrt x hx
    _ ≤ (64 / (Real.log 2) ^ 2 * ((Real.log T) ^ 2 / Real.sqrt T)) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right h_16 (Real.sqrt_nonneg x)
    _ = (64 / (Real.log 2) ^ 2) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by ring

theorem small_T_from_general_formula
    (C₂ : ℝ) (hC₂ : 0 < C₂)
    (h_gen : ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) :
    ∃ C₀ > (0:ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |shiftedRemainderRe x T| ≤
        C₀ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  refine ⟨C₂ * (1 + 64 / (Real.log 2) ^ 2), by positivity, ?_⟩
  intro x T hx hT_lo hT_hi
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h_abs := h_gen x T hx hT_lo hT_hi
  have h_la := log_sq_absorbed_by_error x T hx1 hT_lo hT_hi
  calc |shiftedRemainderRe x T|
      ≤ C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := h_abs
    _ ≤ C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
        (64 / (Real.log 2) ^ 2) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) := by
        apply mul_le_mul_of_nonneg_left _ hC₂.le
        exact add_le_add_right h_la _
    _ = C₂ * (1 + 64 / (Real.log 2) ^ 2) *
        (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by ring

/-- Small-T general formula hypothesis -- the Perron explicit formula for T ∈ [2,16].
    Delegated to HadamardProductZeta.perron_small_T_bound. -/
class SmallTPerronBoundHyp : Prop where
  bound : ∃ C₂ > (0:ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
    |shiftedRemainderRe x T| ≤
      C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)

instance : SmallTPerronBoundHyp where
  bound := by
    obtain ⟨C₂, hC₂, h⟩ := Littlewood.Development.HadamardProductZeta.perron_small_T_bound
    exact ⟨C₂, hC₂, fun x T hx hT_lo hT_hi => by
      rw [shiftedRemainderRe_eq]; exact h x T hx hT_lo hT_hi⟩

/-- Instance combining sorry #1 (large-T) and sorry #2 (small-T).
    SORRY FLOW: 2 upstream sorrys (both INDEPENDENT and IRREDUCIBLE). -/
instance : ContourRemainderBoundHyp where
  bound := by
    apply contour_from_small_T
    obtain ⟨C₂, hC₂, hg⟩ := SmallTPerronBoundHyp.bound
    exact small_T_from_general_formula C₂ hC₂ hg

/-! ### Perron error shape toolbox -/

theorem perron_error_shape_nonneg (x T : ℝ) :
    0 ≤ Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T :=
  div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (Real.sqrt_nonneg _)

theorem perron_error_scaled_nonneg (C x T : ℝ) (hC : 0 ≤ C) :
    0 ≤ C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
  mul_nonneg hC (perron_error_shape_nonneg x T)

theorem perron_error_mono_in_x {x₁ x₂ T : ℝ} (hle : x₁ ≤ x₂) (_hT : 0 < T) :
    Real.sqrt x₁ * (Real.log T) ^ 2 / Real.sqrt T ≤
    Real.sqrt x₂ * (Real.log T) ^ 2 / Real.sqrt T := by
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (sq_nonneg _)

theorem perron_error_lower_bound {x T : ℝ} (_hx : 0 ≤ x) (hT : 2 ≤ T) :
    (Real.log 2) ^ 2 / 4 * (Real.sqrt x / Real.sqrt T) ≤
    Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
  have hlog_sq : (Real.log 2) ^ 2 ≤ (Real.log T) ^ 2 :=
    pow_le_pow_left₀ hlog2.le hlogT 2
  rw [show (Real.log 2) ^ 2 / 4 * (Real.sqrt x / Real.sqrt T) =
      Real.sqrt x * ((Real.log 2) ^ 2 / 4) / Real.sqrt T from by ring]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc Real.sqrt x * ((Real.log 2) ^ 2 / 4)
      ≤ Real.sqrt x * ((Real.log T) ^ 2 / 1) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        rw [div_one]
        calc (Real.log 2) ^ 2 / 4 ≤ (Real.log 2) ^ 2 := by linarith [sq_pos_of_pos hlog2]
          _ ≤ (Real.log T) ^ 2 := hlog_sq
    _ = Real.sqrt x * (Real.log T) ^ 2 := by ring

/-! ### Full sorry decomposition chain

This file has TWO independent sorrys (delegated to HadamardProductZeta.lean):
  Sorry #1: hadamard_contour_bound (T ≥ 16, Hadamard product)
  Sorry #2: perron_small_T_bound (T ∈ [2,16], general Perron formula)
Neither implies the other. -/

theorem hadamard_algebraic_complete (C_pw : ℝ) (_hCpw : 0 < C_pw)
    (T : ℝ) (_hT : 2 ≤ T) :
    C_pw * (Real.log T) ^ 2 ≥ 0 := by positivity

theorem contour_integration_algebraic (C_pw x T : ℝ) :
    C_pw * Real.sqrt x * (Real.log T) ^ 3 =
    C_pw * (Real.log T) ^ 2 * (Real.sqrt x * Real.log T) := by ring

theorem residue_captured_in_shifted_remainder :
    ∀ x T : ℝ, shiftedRemainderRe x T =
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + zeroSumRe x T := by
  intro x T; rfl

/-- Closing both sorrys requires providing:
    1. Hadamard segment bound for T ≥ 16 (sorry #1)
    2. General Perron formula for T ∈ [2,16] (sorry #2, `SmallTPerronBoundHyp`) -/
theorem full_closure_witness
    (A : ℝ) (hA : 0 < A)
    (h_bound : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
        2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T)) :
    (∃ A' > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        A' * (Real.sqrt x * (Real.log T) ^ 3 / T) +
        2 * A' * (Real.sqrt x * (Real.log T) ^ 2 / T))
    ∧ (∃ C₁ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        C₁ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :=
  ⟨⟨A, hA, h_bound⟩,
   ⟨3 * A, by positivity, fun x T hx hT =>
      (h_bound x T hx hT).trans (segment_to_standard_form hA hx hT)⟩⟩

end Aristotle.Standalone.ExplicitFormulaPsiSkeleton
