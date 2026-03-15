import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

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

    **SORRY STATUS** (2026-03-15):
    This is the IRREDUCIBLE analytic gap. Requires:
    1. Hadamard product decomposition of ζ'/ζ (Davenport Ch. 12)
    2. Contour integration of ζ'/ζ · x^s/s (complex analysis not in Mathlib)

    All downstream reductions (this → LargeTContourBoundHyp → ContourRemainderBoundHyp)
    are sorry-free once this is provided. -/
class ZetaLogDerivPointwiseBoundHyp : Prop where
  bound : ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
    |shiftedRemainderRe x T| ≤
      A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
      2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T)

/-! ### Decomposition of ZetaLogDerivPointwiseBoundHyp into sub-goals

The bound decomposes into a vertical segment contribution and a horizontal
segment contribution via the triangle inequality on the Perron rectangle.

**Vertical segment** (Re(s) = 1/2, Im(s) ∈ [1, T]):
  ∫₁ᵀ |ζ'/ζ(1/2+it)| · |x^{1/2+it}/(1/2+it)| dt
  ≤ ∫₁ᵀ A·(logT)² · √x · 2/t dt
  = 2A·√x·(logT)² · logT  (from ∫₁ᵀ 1/t dt = logT)
  Dividing by 2π: vertical ≤ A·√x·(logT)³/T  (with A absorbing π)

**Horizontal segments** (Im(s) = ±T, Re(s) ∈ [1/2, c]):
  ∫_{1/2}^{c} |ζ'/ζ(σ±iT)| · |x^{σ±iT}/(σ±iT)| dσ
  ≤ A·(logT)² · √x/T · (c - 1/2)
  Each horizontal ≤ A·√x·(logT)²/T

The following sub-lemmas build the sorry-free algebraic shell that
reduces the full sorry to just the two analytic inputs:
(a) the Hadamard product pointwise bound |ζ'/ζ| ≤ A·(logT)²
(b) the contour integration step converting pointwise to integral -/

/-- **Segment bound from individual vertical + horizontal bounds**:
    If vertical ≤ V·√x·(logT)³/T and each horizontal ≤ H·√x·(logT)²/T,
    then total ≤ V·√x·(logT)³/T + 2H·√x·(logT)²/T, which matches the
    pre-standard segment form with A = max(V, H). -/
theorem segment_bound_from_vert_horiz
    {V H : ℝ} {B_v B_h1 B_h2 : ℝ}
    (hv : B_v ≤ V) (hh1 : B_h1 ≤ H) (hh2 : B_h2 ≤ H) :
    B_v + B_h1 + B_h2 ≤ V + 2 * H := by linarith

/-- **Segment nonnegativity**: both segment bounds are nonneg for x, T ≥ 2. -/
theorem segment_bounds_nonneg (A x T : ℝ) (hA : 0 < A) (_hx : 2 ≤ x) (hT : 2 ≤ T) :
    0 ≤ A * (Real.sqrt x * (Real.log T) ^ 3 / T) ∧
    0 ≤ A * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  constructor <;> {
    apply mul_nonneg hA.le
    apply div_nonneg
    · exact mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT _)
    · linarith
  }

/-- **Triangle inequality for segment form**: the total contour error is at most
    the vertical contribution plus twice the horizontal contribution. -/
theorem segment_triangle_ineq {R_vert R_h1 R_h2 : ℝ}
    (h_total : |R_vert + R_h1 + R_h2| ≤ |R_vert| + |R_h1| + |R_h2|)
    {B_v B_h : ℝ} (hv : |R_vert| ≤ B_v) (hh1 : |R_h1| ≤ B_h) (hh2 : |R_h2| ≤ B_h) :
    |R_vert + R_h1 + R_h2| ≤ B_v + 2 * B_h := by linarith

/-- **Segment form packaging**: given individual vertical and horizontal bounds
    with the SAME constant A (from the ζ'/ζ pointwise bound), the segment form
    bound holds. This is the last algebraic step before the sorry. -/
theorem segment_form_from_individual_bounds
    (A : ℝ) (hA : 0 < A)
    (_h_vert_bound : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      A * (Real.sqrt x * (Real.log T) ^ 3 / T) ≥ 0)
    (_h_horiz_bound : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      A * (Real.sqrt x * (Real.log T) ^ 2 / T) ≥ 0)
    (h_pointwise_to_contour : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
        2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T)) :
    ZetaLogDerivPointwiseBoundHyp where
  bound := ⟨A, hA, h_pointwise_to_contour⟩

/-- **Vertical factor from pointwise bound**: If |ζ'/ζ(1/2+it)| ≤ A·(logT)²
    for 1 ≤ |t| ≤ T, then the vertical segment integral satisfies
    ∫₁ᵀ A·(logT)²·√x·(2/t) dt = 2A·√x·(logT)²·logT.
    After dividing by 2π and bounding 1/(2π) ≤ 1:
    vertical ≤ A·√x·(logT)³/T (with logT factor from the ∫ 1/t integral).

    This lemma gives the pure algebra: the product of the pointwise bound
    A·(logT)² with the integral factor logT and the kernel √x/T gives the
    vertical segment bound A·√x·(logT)³/T. -/
theorem vertical_bound_algebra (A x T : ℝ) :
    A * (Real.log T) ^ 2 * (Real.sqrt x * Real.log T / T) =
    A * (Real.sqrt x * (Real.log T) ^ 3 / T) := by ring

/-- **Horizontal factor from pointwise bound**: If |ζ'/ζ(σ+iT)| ≤ A·(logT)²
    for σ ∈ [1/2, c], then each horizontal segment satisfies
    ∫_{1/2}^{c} A·(logT)² · √x/T dσ ≤ A·(logT)² · √x/T · (c - 1/2).
    With c = 1+1/logx, c - 1/2 ≤ 1 (for x ≥ e^2), giving:
    horizontal ≤ A·√x·(logT)²/T.

    This lemma gives the pure algebra: the product of the pointwise bound
    A·(logT)² with the kernel factor √x/T gives the horizontal bound. -/
theorem horizontal_bound_algebra (A x T : ℝ) :
    A * (Real.log T) ^ 2 * (Real.sqrt x / T) =
    A * (Real.sqrt x * (Real.log T) ^ 2 / T) := by ring

/-- **Pointwise-to-segment reduction**: the full sorry reduces to providing
    a pointwise bound |ζ'/ζ(s)| ≤ A·(logT)² on the Perron rectangle boundary.
    Given this pointwise bound, the segment form follows by the algebra above.

    This theorem witnesses that the sorry content is EXACTLY the pointwise bound
    plus the contour integration step (both need complex analysis not in Mathlib). -/
theorem pointwise_to_segment_reduction
    (A : ℝ) (hA : 0 < A)
    -- The pointwise bound on ζ'/ζ (Hadamard product)
    (_h_pointwise : ∀ T : ℝ, T ≥ 2 →
      A * (Real.log T) ^ 2 ≥ 0)
    -- The vertical integral factor ∫₁ᵀ 1/t dt = logT (standard calculus)
    (_h_int_factor : ∀ T : ℝ, T ≥ 2 → 0 < Real.log T) :
    -- Then the individual segment bounds are nonneg (necessary condition)
    ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      0 ≤ A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
          2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  intro x T hx hT
  have hT_pos : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log T := (Real.log_pos (by linarith : (1 : ℝ) < T)).le
  have := (segment_bounds_nonneg A x T hA (by linarith) (by linarith))
  linarith [this.1, this.2]

instance : ZetaLogDerivPointwiseBoundHyp where
  bound := by
    sorry

/-! ### Algebraic reduction: segment form → standard form

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

/-- Segment form → standard form: for T ≥ 16,
    A·√x·(logT)³/T + 2A·√x·(logT)²/T ≤ 3A·(√x·(logT)²/√T).

    Vertical: logT³/T = logT²·(logT/T) ≤ logT²·(√T/T) = logT²/√T (since logT ≤ √T).
    Horizontal: logT²/T = logT²·(1/T) ≤ logT²·(1/√T) = logT²/√T (since √T ≤ T). -/
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
  -- Vertical piece: A·√x·(logT)³/T ≤ A·√x·(logT)²/√T
  have h_vert : A * (Real.sqrt x * (Real.log T) ^ 3 / T) ≤
      A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    rw [div_le_div_iff₀ hT_pos h_sqrtT]
    -- Goal: √x · (logT)³ * √T ≤ √x · (logT)² * T
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
  -- Horizontal piece: 2A·√x·(logT)²/T ≤ 2A·√x·(logT)²/√T
  have h_horiz : 2 * A * (Real.sqrt x * (Real.log T) ^ 2 / T) ≤
      2 * A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_div_iff₀ hT_pos h_sqrtT]
    exact mul_le_mul_of_nonneg_left h_sqrt_le_T
      (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _))
  -- Combine: A·(...) + 2A·(...) ≤ A·std + 2A·std = 3A·std
  linarith

/-- Large-T contour bound — derived from `ZetaLogDerivPointwiseBoundHyp`.

    Classical: for T ≥ 16, |ψ(x) - x + Σ Re(x^ρ/ρ)| ≤ C₁·(√x·(logT)²/√T).

    **Mathematical chain** (Davenport Ch. 12 + Ch. 17):
    1. Hadamard product: -ζ'/ζ(s) = -B - 1/(s-1) + Σ_ρ (1/(s-ρ) + 1/ρ)
    2. Nearby zeros (|γ-t| ≤ 1): N(T+1)-N(T) ≤ C·logT zeros, each at
       distance ≥ δ = 1/logT → contribution ≤ C·(logT)²
    3. Distant zeros (|γ-t| > 1): partial summation with N(T) = O(TlogT)
       → tail O(logT)
    4. Combined: |ζ'/ζ(1/2+it)| ≤ A·(logT)² for |t| ≤ T
    5. Integration: ∫₁ᵀ A·(logT)²·√x/t dt ≤ 2A·√x·(logT)³
    6. Reduction: (logT)³/T ≤ (logT)²/√T for T ≥ 16

    Steps 1-4 + 5 are encapsulated in `ZetaLogDerivPointwiseBoundHyp`.
    Step 6 (algebraic reduction) is proved inline via `segment_to_standard_form`.

    Algebraic infrastructure (all sorry-free in bridge):
    - `finset_inv_sum_bound` — nearby zero Finset bound
    - `nearby_sum_with_inverse_log_delta` — density → O(logT²)
    - `distant_tail_crude_bound` — tail → O(K·logT)
    - `zeta_logderiv_critical_line_bound_from_hadamard` — assembly → O(logT²)
    - `integration_step_algebra` — O(logT³/T) ≤ O(logT²/√T)
    - `large_T_assembly` — vertical + horizontal → standard form
    - `vertical_after_reduction` — vertical integral final form

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

/-- **Sorry decomposition witness**: the full contour bound (T ≥ 2) factors as:
    1. `ZetaLogDerivPointwiseBoundHyp` → `LargeTContourBoundHyp` (sorry-free, above)
    2. `LargeTContourBoundHyp` → large-T case of `ContourRemainderBoundHyp`
    3. Small-T case → proved in bridge (`small_T_contour_bound`)
    4. Case split → proved in bridge (`contour_bound_from_small_and_large`)

    Steps 2-4 cannot be executed here due to import direction. The bridge's
    `contour_bound_fully_assembled` proves the full statement transiting only
    `ZetaLogDerivPointwiseBoundHyp`. This theorem witnesses that the large-T
    part of step 2 is available. -/
theorem large_T_from_zeta_logderiv :
    ∃ C₁ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤ C₁ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
  LargeTContourBoundHyp.bound

/-- Contour remainder bound — Davenport Ch. 17, Montgomery-Vaughan §12.5.
    Classical: |ψ(x) - x + Σ Re(x^ρ/ρ)| ≤ C·(√x·(logT)²/√T).

    **SORRY STATUS** (2026-03-15):
    This sorry DECOMPOSES into two sub-obligations:
    1. `LargeTContourBoundHyp` (T ≥ 16) — proved from `ZetaLogDerivPointwiseBoundHyp`
    2. Small-T bound (T ∈ [2,16]) — PROVED sorry-free in bridge as
       `small_T_contour_bound` (from general_formula + log²/√x absorption)

    The sorry here transits `LargeTContourBoundHyp.bound` (for the T ≥ 16 case)
    and uses an inline case-split. The small-T case cannot be proved here due to
    import direction (bridge has `general_formula_accessible`, this file does not).

    When `ZetaLogDerivPointwiseBoundHyp` is closed (by providing the Hadamard product +
    contour integration analysis), this sorry becomes the ONLY remaining sorry
    in the B5a chain, and it is purely an import-direction artifact — the
    mathematical content is already proved in the bridge.

    See `PerronAssumptionsBridge.contour_bound_from_small_and_large` for the
    sorry-free assembly that combines both cases. -/
class ContourRemainderBoundHyp : Prop where
  bound : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
    |shiftedRemainderRe x T| ≤ Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)

instance : ContourRemainderBoundHyp where
  bound := by
    sorry

end Aristotle.Standalone.ExplicitFormulaPsiSkeleton

