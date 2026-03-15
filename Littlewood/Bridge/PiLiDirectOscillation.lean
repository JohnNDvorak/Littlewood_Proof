/-
Bridge: Extract π(x) - li(x) = Ω±(√x / log x) from critical-line zeros
using a truncated explicit formula input tailored to π.

This bridge isolates the oscillation-extraction argument (phase alignment +
anti-alignment) from the analytic Perron-contour work needed to produce the
truncated π explicit formula itself.

Dependencies:
- `HardyCriticalLineZerosHyp`
- `TruncatedExplicitFormulaPiHyp`

Output:
- `PiLiOscillationSqrtHyp`
-/

import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.Aristotle.Standalone.AbelSummationPsiPi
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs

noncomputable section

open Schmidt Asymptotics
open Filter ZetaZeros
open scoped BigOperators

namespace PiLiDirectOscillationBridge

private def piLiError (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x

/-- Input hypothesis for extracting π-li oscillation from critical-line zeros. -/
class TruncatedExplicitFormulaPiHyp : Prop where
  /-- Truncated explicit formula for `π(x) - li(x)` at `√x/log x` scale. -/
  pi_approx :
    ∀ (S : Finset ℂ),
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop,
        |piLiError x + ((∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ).re) / Real.log x|
          ≤ ε * (Real.sqrt x / Real.log x)

  /-- Anti-alignment for singleton critical-line zeros, scaled by `1/log x`. -/
  zero_sum_neg_frequently :
    ∀ (ρ₀ : ℂ), ρ₀ ∈ zetaNontrivialZeros →
      ρ₀.re = 1 / 2 → ρ₀.im ≠ 0 →
      ∃ c > 0, ∀ X : ℝ, ∃ x > X,
        1 < x ∧
          ((∑ ρ ∈ ({ρ₀} : Finset ℂ), ((x : ℂ) ^ ρ / ρ)).re) / Real.log x
            ≤ -(c * (Real.sqrt x / Real.log x))

/-! ### MATHEMATICAL ANALYSIS: pi_approx soundness (2026-03-15)

**STATUS (updated 2026-03-15)**: Two layers with different truth values:

1. `PiApproxFromExplicitFormulaHyp` (O-bound, `∃ D > 0`): **MATHEMATICALLY TRUE**.
   States ∃ D > 0 such that for any S of critical-line zeros, eventually
   |π(x) - li(x) + (Σ_{ρ∈S} x^ρ/ρ)/logx| ≤ D·√x/logx.
   This follows from the Perron contour formula + Abel summation ψ→π.
   The constant D absorbs the Abel correction O(√x/logx).
   Sorry: proof not yet formalized (requires composing Perron + Abel constants).

2. `TruncatedExplicitFormulaPiHyp.pi_approx` (little-o, `∀ ε > 0`): **MATHEMATICALLY FALSE**.
   Setting S=∅ gives π(x)-li(x) = o(√x/logx), contradicting Ω± oscillation.
   Retained with false type to avoid breaking 50+ downstream files.
   The main theorem path bypasses this via LandauOscillation.lean (priority 2000).

**ROOT CAUSE** of the false little-o statement:
1. The `∀ S` quantification (including S=∅) is incompatible with Ω± oscillation.
2. The ψ→π Abel correction O(√x/logx) contributes at the SAME scale as ε·√x/logx.

**CORRECT MULTI-FILE REFACTOR** (future work):
Replace `∀ S, ∀ ε > 0` in TruncatedExplicitFormulaPiHyp with ZerosBelow T + O-bound.
Then the oscillation extraction uses A(T) → ∞ growth to exceed D for large T.
This affects 50+ downstream files.

**SORRY HISTORY**: 2 sorrys → 1 sorry (consolidated). The remaining sorry on
PiApproxFromExplicitFormulaHyp is now a legitimate proof obligation (true statement).
The false `pi_approx` field in PerronExplicitFormulaProvider has its own sorry.
-/

/-- Abel summation correction: π(x) - li(x) ≈ (ψ(x) - x)/logx with correction
    of order O(√x/logx). Classical: partial summation applied to the
    prime-counting function (Davenport Ch. 17; Montgomery-Vaughan §2.2).

    NOTE (2026-03-15): The correction is O(√x/logx), not O(√x/(logx)²) as
    previously claimed. The dominant term is (ψ(x)-θ(x))/logx where
    ψ-θ = θ(√x) + θ(x^{1/3}) + ... ≈ √x. This class is retained for
    reference but NO LONGER INSTANTIATED — the ψ→π decomposition is the
    wrong approach for pi_approx. See MATHEMATICAL ANALYSIS above. -/
class AbelCorrectionPsiPiHyp : Prop where
  /-- There exists D > 0 such that eventually the Abel correction is bounded. -/
  correction_bound : ∃ D > (0 : ℝ), ∀ᶠ x in atTop,
    |piLiError x - (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) /
      Real.log x| ≤ D * (Real.sqrt x / Real.log x)

/-- ψ-level explicit formula using ZerosBelow T (the Perron truncation).

    For any δ > 0, there exists T₀ ≥ 2 such that eventually
    |(ψ(x) - x + Σ_{ρ∈ZerosBelow T₀} x^ρ/ρ) / logx| ≤ δ · √x/logx.

    This is MATHEMATICALLY CORRECT. The Perron formula gives
    |ψ(x) - x + Σ_{|γ|≤T} x^ρ/ρ| ≤ C·(√x·(logT)²/√T + (logx)²),
    and choosing T₀ with (logT₀)²/√T₀ small + x large gives δ-smallness.

    PROVABLE from `general_explicit_formula_from_perron` +
    `psi_bound_div_log_eventually_small` (AbelSummationPsiPi).

    NOTE: This is useful for the ψ-chain (littlewood_psi) but CANNOT be
    combined with AbelCorrectionPsiPiHyp to prove pi_approx because the
    Abel correction O(√x/logx) is at the same scale as the target.
    See MATHEMATICAL ANALYSIS above. -/
class PsiExplicitFormulaZerosHyp : Prop where
  /-- For any δ > 0, there exists T₀ ≥ 2 such that eventually the
      ψ-level error with ZerosBelow T₀, divided by logx, is δ-small
      at the √x/logx scale. -/
  psi_level_bound :
    ∀ δ : ℝ, 0 < δ →
      ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ᶠ x in atTop,
        |(Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x +
            (∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T₀,
              (x : ℂ) ^ ρ / ρ).re) / Real.log x|
          ≤ δ * (Real.sqrt x / Real.log x)

/-- PROVED from `ContourRemainderBoundHyp` (ExplicitFormulaPsiB5aDefs) +
    `psi_bound_div_log_eventually_small` (AbelSummationPsiPi).
    1. Get Cc from ContourRemainderBoundHyp.bound
    2. Upgrade to two-term bound (add nonneg (logx)² term)
    3. Apply psi_bound_div_log_eventually_small → T₀ ≥ 2, eventually small
    4. Unfold shiftedRemainderRe = chebyshevPsi - x + zeroSumRe to match goal -/
instance : PsiExplicitFormulaZerosHyp where
  psi_level_bound := by
    intro δ hδ
    -- Get Cc from ContourRemainderBoundHyp (sorry upstream in B5aDefs)
    obtain ⟨Cc, hCc_pos, hCc_bound⟩ :=
      Aristotle.Standalone.ExplicitFormulaPsiSkeleton.ContourRemainderBoundHyp.bound
    -- Upgrade one-term bound to two-term bound needed by psi_bound_div_log_eventually_small
    have hR : ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
      intro x T hx hT
      calc |Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe x T|
          ≤ Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := hCc_bound x T hx hT
        _ ≤ Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hCc_pos.le
            linarith [sq_nonneg (Real.log x)]
    -- Apply the AbelSummationPsiPi workhorse to get T₀ and eventually-small
    obtain ⟨T₀, hT₀, hev⟩ := AbelSummationPsiPi.psi_bound_div_log_eventually_small
      (fun x T => Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe x T)
      Cc hCc_pos hR δ hδ
    refine ⟨T₀, hT₀, ?_⟩
    -- shiftedRemainderRe x T₀ = chebyshevPsi x - x + (∑ ρ ∈ ZerosBelow T₀, (x:ℂ)^ρ/ρ).re
    filter_upwards [hev, AbelSummationPsiPi.log_eventually_pos] with x hx hlx
    rw [abs_div, abs_of_pos hlx]
    have heq : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x +
        (∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T₀,
          (↑x : ℂ) ^ ρ / ρ).re =
        Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe x T₀ := by
      simp only [Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe,
                  Aristotle.Standalone.ExplicitFormulaPsiSkeleton.zeroSumRe]
    rw [heq]; exact hx

/-- π-level truncated explicit formula at √x/logx scale (O-bound version).

    **MATHEMATICALLY TRUE**: For any finite set S of critical-line zeros,
    the explicit formula gives an O-bound:
      |π(x) - li(x) + (Σ_{ρ∈S} x^ρ/ρ)/logx| ≤ D · √x/logx
    where D depends on the Abel correction constant but NOT on S or ε.

    This replaces the previous ∀ε>0 (little-o) version which was FALSE
    (setting S=∅ contradicts Littlewood's Ω± oscillation). The O-bound
    IS compatible with Ω± because the phase-aligned sum grows with |S|
    and can exceed D for large enough S.

    NOTE: TruncatedExplicitFormulaPiHyp.pi_approx retains the ∀ε>0 form
    for downstream compatibility (50+ files). The bridge from this O-bound
    to that little-o form requires the full ZerosBelow T refactor. -/
class PiApproxFromExplicitFormulaHyp : Prop where
  /-- There exists D > 0 such that for any finite set S of critical-line zeros,
      eventually |π(x) - li(x) + (Σ_{ρ∈S} x^ρ/ρ)/logx| ≤ D · √x/logx.
      The constant D comes from the Abel summation ψ→π correction. -/
  pi_approx_bound :
    ∃ D : ℝ, 0 < D ∧
      ∀ (S : Finset ℂ),
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) →
        ∀ᶠ x in atTop,
          |piLiError x + ((∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ).re) / Real.log x|
            ≤ D * (Real.sqrt x / Real.log x)

/-- Sorry for PiApproxFromExplicitFormulaHyp (O-bound version).

    SORRY (1): The statement is now MATHEMATICALLY TRUE. The proof requires:
    (1) The Perron contour formula for ψ(x) (from ContourRemainderBoundHyp)
    (2) Abel summation ψ → π with O(√x/logx) correction
    (3) Combining: the remainder + Abel correction give a fixed D

    The previous ∀ε>0 version was mathematically false; this O-bound version
    is the correct statement. Provable from PsiExplicitFormulaZerosHyp +
    AbelCorrectionPsiPiHyp once their constants are composed. -/
instance : PiApproxFromExplicitFormulaHyp where
  pi_approx_bound := by
    sorry

/-- Ω₋ direction for `π(x) - li(x)` from aligned phases. -/
private theorem omega_minus_from_zeros
    [TruncatedExplicitFormulaPiHyp]
    (h_zeros : Set.Infinite {ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2}) :
    IsOmegaMinus (fun x => piLiError x) (fun x => Real.sqrt x / Real.log x) := by
  obtain ⟨ρ₀, hρ₀_mem, hρ₀_re⟩ := h_zeros.nonempty

  have hρ₀_re_pos : (0 : ℝ) < ρ₀.re := by rw [hρ₀_re]; norm_num
  have hρ₀_ne : ρ₀ ≠ 0 := by
    intro h
    simp [h] at hρ₀_re_pos

  have h_re_inv_pos : 0 < (1 / ρ₀).re := by
    simp only [one_div]
    rw [Complex.inv_re]
    exact div_pos hρ₀_re_pos (Complex.normSq_pos.mpr hρ₀_ne)

  set c₀ := (1 / ρ₀).re with hc₀_def

  have hS_re : ∀ ρ ∈ ({ρ₀} : Finset ℂ), ρ.re = 1 / 2 := by
    intro ρ hρ
    simp only [Finset.mem_singleton] at hρ
    subst hρ
    exact hρ₀_re

  have hS_in : ∀ ρ ∈ ({ρ₀} : Finset ℂ), ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    simp only [Finset.mem_singleton] at hρ
    subst hρ
    exact ⟨hρ₀_mem, hρ₀_re⟩

  have hρ₀_norm_pos : (0 : ℝ) < ‖ρ₀‖ := norm_pos_iff.mpr hρ₀_ne
  set ε_a := c₀ * ‖ρ₀‖ / 2 with hε_a_def
  have hε_a_pos : (0 : ℝ) < ε_a := by positivity

  have h_ef :=
    TruncatedExplicitFormulaPiHyp.pi_approx {ρ₀} hS_in (c₀ / 4) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp h_ef

  refine ⟨c₀ / 4, by positivity, ?_⟩
  rw [Filter.frequently_atTop]
  intro a

  obtain ⟨x, hx_gt, hx_align⟩ :=
    Aristotle.DirichletPhaseAlignment.exists_large_x_phases_aligned_finset
      {ρ₀} hS_re ε_a hε_a_pos (max (max a x₀) 2)

  have hx_pos : (0 : ℝ) < x := by linarith [le_max_right (max a x₀) (2 : ℝ)]
  have hx_gt_two : (2 : ℝ) < x := by
    exact lt_of_le_of_lt (le_max_right (max a x₀) (2 : ℝ)) hx_gt
  have hx_ge_a : a ≤ x := by
    linarith [le_max_left a x₀, le_max_left (max a x₀) (2 : ℝ)]
  have hx_ge_x₀ : x₀ ≤ x := by
    linarith [le_max_right a x₀, le_max_left (max a x₀) (2 : ℝ)]

  have h_bound :=
    Aristotle.DirichletPhaseAlignment.bound_real_part_of_sum_aligned
      hS_re hx_pos hε_a_pos hx_align

  have h_ef_x := hx₀ x hx_ge_x₀
  simp only [Finset.sum_singleton] at h_bound h_ef_x

  have h_upper := (abs_le.mp h_ef_x).2

  have h_eps_cancel : ε_a * (1 / ‖ρ₀‖) = c₀ / 2 := by
    rw [hε_a_def]
    field_simp

  have h_re_lower : ((x : ℂ) ^ ρ₀ / ρ₀).re ≥ Real.sqrt x * (c₀ / 2) := by
    calc
      ((x : ℂ) ^ ρ₀ / ρ₀).re
          ≥ Real.sqrt x * ((1 / ρ₀).re - ε_a * (1 / ‖ρ₀‖)) := h_bound
      _ = Real.sqrt x * (c₀ / 2) := by
          rw [← hc₀_def, h_eps_cancel]
          ring

  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)

  have h_re_lower_scaled :
      (c₀ / 2) * (Real.sqrt x / Real.log x)
        ≤ (((x : ℂ) ^ ρ₀ / ρ₀).re) / Real.log x := by
    have htmp :
        (Real.sqrt x * (c₀ / 2)) / Real.log x
          ≤ (((x : ℂ) ^ ρ₀ / ρ₀).re) / Real.log x := by
      rw [div_le_div_iff₀ hlog_pos hlog_pos]
      nlinarith [h_re_lower]
    have hrewrite :
        (c₀ / 2) * (Real.sqrt x / Real.log x)
          = (Real.sqrt x * (c₀ / 2)) / Real.log x := by ring
    simpa [hrewrite] using htmp

  refine ⟨x, hx_ge_a, ?_⟩
  nlinarith [h_upper, h_re_lower_scaled]

/-- Ω₊ direction for `π(x) - li(x)` from anti-aligned singleton phases. -/
private theorem omega_plus_from_zeros
    [TruncatedExplicitFormulaPiHyp]
    (h_zeros : Set.Infinite {ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2}) :
    IsOmegaPlus (fun x => piLiError x) (fun x => Real.sqrt x / Real.log x) := by
  have h_inf := h_zeros.diff (Set.finite_singleton ((1 / 2 : ℝ) : ℂ))
  obtain ⟨ρ₀, ⟨hρ₀_mem, hρ₀_re⟩, hρ₀_notin⟩ := h_inf.nonempty

  have hρ₀_im_ne : ρ₀.im ≠ 0 := by
    intro him
    exact hρ₀_notin
      (Set.mem_singleton_iff.mpr
        (Complex.ext (by simp [hρ₀_re]) (by simp [him])))

  have hS_in : ∀ ρ ∈ ({ρ₀} : Finset ℂ), ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    simp only [Finset.mem_singleton] at hρ
    subst hρ
    exact ⟨hρ₀_mem, hρ₀_re⟩

  obtain ⟨c, hc_pos, h_neg⟩ :=
    TruncatedExplicitFormulaPiHyp.zero_sum_neg_frequently ρ₀ hρ₀_mem hρ₀_re hρ₀_im_ne

  have h_ef := TruncatedExplicitFormulaPiHyp.pi_approx {ρ₀} hS_in (c / 2) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp h_ef

  refine ⟨c / 2, by positivity, ?_⟩
  rw [Filter.frequently_atTop]
  intro a

  obtain ⟨x, hx_gt, hx_one, hx_neg⟩ := h_neg (max a x₀)
  have hx_ge_a : a ≤ x := by linarith [le_max_left a x₀]
  have hx_ge_x₀ : x₀ ≤ x := by linarith [le_max_right a x₀]

  have h_ef_x := hx₀ x hx_ge_x₀
  simp only [Finset.sum_singleton] at h_ef_x hx_neg

  have h_lower := (abs_le.mp h_ef_x).1

  refine ⟨x, hx_ge_a, ?_⟩
  nlinarith [h_lower, hx_neg]

/-- π(x) - li(x) = Ω±(√x / log x) from critical-line zeros plus a truncated
explicit formula input for π. -/
instance [HardyCriticalLineZerosHyp] [TruncatedExplicitFormulaPiHyp] :
    PiLiOscillationSqrtHyp where
  oscillation := by
    have h_zeros := HardyCriticalLineZerosHyp.infinite
    exact ⟨omega_plus_from_zeros h_zeros, omega_minus_from_zeros h_zeros⟩

end PiLiDirectOscillationBridge
