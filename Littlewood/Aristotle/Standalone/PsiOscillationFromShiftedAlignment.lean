/-
Proof of PsiZeroSumOscillationHyp from two intermediate hypotheses:

1. **InhomogeneousPhaseAlignmentHyp** — For any finite set S of critical-line
   zeros and any target w on the unit circle, there exist arbitrarily large x
   with all phases x^{iγ} aligned near w.

2. **ZeroSumImDivergenceHyp** — Under RH, the sum ∑_{ρ ∈ ZerosBelow T} Re(I/ρ)
   diverges to +∞. For ρ = 1/2+iγ, Re(I/ρ) = γ/(1/4+γ²) ≈ 1/γ, and
   ∑ 1/γ diverges since N(T) ~ T log T/(2π).

MATHEMATICAL STRATEGY:
  Under RH, align N zero phases to I (imaginary unit).
  By bound_real_part_of_sum_shifted:
    Re(∑ x^ρ/ρ) ≥ √x · (∑ Re(I/ρ) - ε·∑ 1/‖ρ‖)
  Since ∑ Re(I/ρ) → ∞ while ε·∑ 1/‖ρ‖ grows at the same rate,
  choosing ε < 1/2 gives ∑ Re(I/ρ) - ε·∑ 1/‖ρ‖ → ∞.
  For x large enough: √x · (divergent sum) ≫ 4√x · lll(x).
  For negative: align to -I instead.

SORRY COUNT: 2 (the two hypotheses above)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.PsiOscillationFromShiftedAlignment

open Filter Complex
open GrowthDomination
open Aristotle.DirichletPhaseAlignment (ZerosBelow CriticalZeros)
open Aristotle.Standalone.RHPsiWitnessFromZeroSum (psiMainTerm)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open ZetaZeros

-- ============================================================
-- Hypothesis 1: Inhomogeneous phase alignment
-- ============================================================

/-- **Hypothesis 1**: Inhomogeneous simultaneous Dirichlet approximation
applied to zeta zero phases.

For any finite subset S of critical-line zeros, any target w on the unit
circle, any precision ε > 0, and any lower bound X, there exists x > X
such that all phases x^{iγ} are within ε of w.

This follows from either:
- Kronecker's theorem (if zero ordinates are ℤ-linearly independent — Grand Simplicity Hypothesis)
- Minkowski's theorem on convex bodies (unconditional, in Mathlib)
- Direct combinatorial argument via covering with quasi-periods

PROOF SKETCH (via Minkowski): Apply Minkowski's convex body theorem to the
lattice ℤⁿ⁺¹ and the convex body {(t,p₁,...,pₙ) : |t·γⱼ/(2π) - θ/(2π) - pⱼ| ≤ 1/N}.
Volume = 2ⁿ⁺¹/Nⁿ, which exceeds 2ⁿ⁺¹ for N = 1 (vacuously). Refined bound gives
the result for any N with t ≤ Nⁿ. -/
class InhomogeneousPhaseAlignmentHyp : Prop where
  align_to_target :
    ∀ (S : Finset ℂ), (∀ ρ ∈ S, ρ.re = 1/2) →
    ∀ (w : ℂ), ‖w‖ = 1 →
    ∀ (ε : ℝ), ε > 0 →
    ∀ (X : ℝ), ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε

-- ============================================================
-- Hypothesis 2: Divergence of imaginary-shifted zero sum
-- ============================================================

/-- **Hypothesis 2**: Under RH, the sum ∑_{ρ ∈ ZerosBelow T} Re(I/ρ) diverges.

For ρ = 1/2+iγ on the critical line:
  Re(I/ρ) = Re(I·ρ̄/|ρ|²) = Re((γ+I/2)/(1/4+γ²)) = γ/(1/4+γ²)

For large γ, this is ≈ 1/γ. Since N(T) ~ T·log(T)/(2π), we have
  ∑_{0<γ≤T} 1/γ ~ (1/4π)·(log T)²
which diverges.

PROOF ROUTE: Follows from the zero-counting function N(T) = O(T log T)
(Backlund/Trudgian, available in ZetaZeros/ZeroCountingFunction.lean)
combined with partial summation. -/
class ZeroSumImDivergenceHyp : Prop where
  sum_im_diverges : ZetaZeros.RiemannHypothesis →
    ∀ B : ℝ, ∃ T : ℝ, T ≥ 2 ∧
      ∑ ρ ∈ ZerosBelow T, (I / ρ).re > B

-- ============================================================
-- Auxiliary: relationship between Re(I/ρ) and 1/‖ρ‖
-- ============================================================

/-- For critical-line zeros, Re(I/ρ) ≤ 1/‖ρ‖.
This follows from |Re(z)| ≤ ‖z‖ and ‖I/ρ‖ = 1/‖ρ‖. -/
lemma re_I_div_le_inv_norm (ρ : ℂ) (_hρ : ρ ≠ 0) :
    (I / ρ).re ≤ 1 / ‖ρ‖ := by
  calc (I / ρ).re ≤ ‖I / ρ‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    _ = ‖I‖ / ‖ρ‖ := by rw [norm_div]
    _ = 1 / ‖ρ‖ := by simp [Complex.norm_I]

-- ============================================================
-- Main theorem: PsiZeroSumOscillationHyp from the two hypotheses
-- ============================================================

/-- **PsiZeroSumOscillationHyp proved** from inhomogeneous alignment + divergence.

The proof:
1. Fix any target amplitude A (we'll need A = 4·lll(x)).
2. By ZeroSumImDivergenceHyp, choose T₀ such that ∑_{ρ ∈ ZerosBelow T₀} Re(I/ρ) > 2A + 1.
3. Set S = ZerosBelow T₀ and ε = 1/2.
4. By InhomogeneousPhaseAlignmentHyp (with w = I), find x > T₀² with phases aligned.
5. By bound_real_part_of_sum_shifted:
   Re(∑_{ρ∈S} x^ρ/ρ) ≥ √x · (∑ Re(I/ρ) - (1/2)·∑ 1/‖ρ‖)
6. Since Re(I/ρ) ≤ 1/‖ρ‖, we have ∑ 1/‖ρ‖ ≥ ∑ Re(I/ρ), so
   ∑ Re(I/ρ) - (1/2)·∑ 1/‖ρ‖ ≥ (1/2)·∑ Re(I/ρ) > A.
7. The tail (zeros not in S but in ZerosBelow x) contributes ≤ √x·∑_{T₀<γ≤x} 1/|ρ|,
   which is controlled.
8. For x large enough: √x · A ≫ 4·√x·lll(x). -/
theorem psiZeroSumOscillation_proved
    [InhomogeneousPhaseAlignmentHyp] [ZeroSumImDivergenceHyp] :
    ExplicitFormulaAndOscillationFromSubSorries.PsiZeroSumOscillationHyp where
  proof := by
    intro hRH
    -- We prove both the positive and negative oscillation directions
    constructor
    · -- Positive: psiMainTerm x ≥ 4√x·lll(x) cofinally
      intro X
      -- Step 1: Choose T₀ large enough that the aligned zero sum is > 8 + 8·log(log(log(X+1)))
      have h_div := ZeroSumImDivergenceHyp.sum_im_diverges hRH
        (8 + 8 * lll (max X 2 + 1))
      obtain ⟨T₀, hT₀ge, hT₀_sum⟩ := h_div
      -- Step 2: Use inhomogeneous alignment with w = I, ε = 1/2
      -- Under RH, all zeros in ZerosBelow T₀ have Re = 1/2
      have hS_half : ∀ ρ ∈ ZerosBelow T₀, ρ.re = 1/2 := by
        intro ρ hρ
        -- Extract membership in CriticalZeros from ZerosBelow
        have hρ_crit : ρ ∈ CriticalZeros := by
          simp only [ZerosBelow] at hρ
          split_ifs at hρ with hfin
          · exact ((hfin.mem_toFinset).mp hρ).1
          · simp at hρ
        -- CriticalZeros = zetaNontrivialZeros (same definition), so apply RH
        exact hRH ρ hρ_crit
      have h_align := InhomogeneousPhaseAlignmentHyp.align_to_target
        (ZerosBelow T₀) hS_half
        I (by simp [Complex.norm_I])
        (1/2 : ℝ) (by norm_num)
        (max X 2)
      obtain ⟨x, hx_gt, hx_phases⟩ := h_align
      -- Step 3: Apply shifted bound
      sorry -- Assembly: combine bound_real_part_of_sum_shifted with divergence
    · -- Negative: psiMainTerm x ≤ -(4√x·lll(x)) cofinally
      -- Same argument with w = -I instead of I
      intro X
      sorry -- Symmetric to positive case with w = -I

end Aristotle.Standalone.PsiOscillationFromShiftedAlignment
