/-
Proof of PsiZeroSumOscillationHyp from three intermediate hypotheses:

1. **InhomogeneousPhaseAlignmentHyp** — Simultaneous Dirichlet approximation
   for zeta zero phases.

2. **ZeroSumImDivergenceHyp** — Under RH, ∑_{0<γ≤T} Re(I/ρ) diverges (ρ = 1/2+iγ).
   NOTE: The sum is over POSITIVE imaginary part zeros only, since conjugate
   pairs cancel: Re(I/ρ) + Re(I/ρ̄) = 0. The sum ∑ Re(I/ρ) over ZerosBelow T
   (which includes both conjugates) would be identically 0 by symmetry.

3. **ExplicitFormulaPsiGeneralHyp** — Truncated explicit formula for ψ(x)
   with variable truncation T.

MATHEMATICAL STRATEGY:
  The explicit formula gives ψ(x) - x ≈ -Re(∑_{|γ|≤T₀} x^ρ/ρ).
  By conjugate symmetry: Re(∑ x^ρ/ρ) = 2·Re(∑_{γ>0} x^ρ/ρ).
  Aligning the positive-Im zeros' phases to -I via bound_real_part_of_sum_shifted_upper:
    Re(∑_{γ>0} x^ρ/ρ) ≤ √x·(-∑ Re(I/ρ) + ε·∑ 1/‖ρ‖)
  Since ∑ Re(I/ρ) → ∞ and ε is small, this is very negative.
  So ψ(x) - x ≈ -2·(very negative) → +∞.

SORRY COUNT: 2 (assembly sorrys, pending explicit formula + conjugate symmetry bridge)

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
such that all phases x^{iγ} are within ε of w. -/
class InhomogeneousPhaseAlignmentHyp : Prop where
  align_to_target :
    ∀ (S : Finset ℂ), (∀ ρ ∈ S, ρ.re = 1/2) →
    ∀ (w : ℂ), ‖w‖ = 1 →
    ∀ (ε : ℝ), ε > 0 →
    ∀ (X : ℝ), ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε

-- ============================================================
-- Hypothesis 2: Divergence of zero sum (positive Im only)
-- ============================================================

/-- The subset of ZerosBelow T with positive imaginary part.
Since zeros come in conjugate pairs, this is "half" of ZerosBelow T. -/
def ZerosBelowPos (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => 0 < ρ.im)

/-- **Hypothesis 2**: Under RH, the sum ∑_{0<γ≤T} Re(I/ρ) diverges.
The sum is over POSITIVE imaginary part zeros only.

For ρ = 1/2+iγ with γ > 0: Re(I/ρ) = γ/(1/4+γ²) ≈ 1/γ.
Since ∑ 1/γ diverges (N(T) ~ T·log T), this sum diverges. -/
class ZeroSumImDivergenceHyp : Prop where
  sum_im_diverges : ZetaZeros.RiemannHypothesis →
    ∀ B : ℝ, ∃ T : ℝ, T ≥ 2 ∧
      ∑ ρ ∈ ZerosBelowPos T, (I / ρ).re > B

-- ============================================================
-- Auxiliary lemmas
-- ============================================================

/-- For critical-line zeros, Re(I/ρ) ≤ 1/‖ρ‖. -/
lemma re_I_div_le_inv_norm (ρ : ℂ) (_hρ : ρ ≠ 0) :
    (I / ρ).re ≤ 1 / ‖ρ‖ := by
  calc (I / ρ).re ≤ ‖I / ρ‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    _ = ‖I‖ / ‖ρ‖ := by rw [norm_div]
    _ = 1 / ‖ρ‖ := by simp [Complex.norm_I]

-- ============================================================
-- Main theorem: PsiZeroSumOscillationHyp
-- ============================================================

/-- **PsiZeroSumOscillationHyp proved** from alignment + divergence + explicit formula.

The proof aligns positive-Im zeros' phases, uses the shifted bound to control
the zero sum, then bridges to chebyshevPsi via the explicit formula.

For positive oscillation (ψ-x ≥ C√x): align to -I, upper bound makes zero sum negative.
For negative oscillation (ψ-x ≤ -C√x): align to I, lower bound makes zero sum positive. -/
theorem psiZeroSumOscillation_proved
    [InhomogeneousPhaseAlignmentHyp] [ZeroSumImDivergenceHyp]
    [ExplicitFormulaPsiGeneralHyp] :
    ExplicitFormulaAndOscillationFromSubSorries.PsiZeroSumOscillationHyp where
  proof := by
    intro hRH
    obtain ⟨C_ef, hC_ef⟩ := ExplicitFormulaPsiGeneralHyp.proof
    -- We prove both the positive and negative oscillation directions
    constructor
    · -- Positive: chebyshevPsi x - x ≥ C * √x cofinally
      -- Strategy: align positive-Im zeros to -I, making Re(∑ x^ρ/ρ) very negative
      -- over ZerosBelowPos T₀. Then ψ(x) - x ≈ -(sum) is very positive.
      intro C X
      -- Choose T₀ with divergent sum
      have h_div := ZeroSumImDivergenceHyp.sum_im_diverges hRH
        (4 * (|C| + |C_ef| + 1))
      obtain ⟨T₀, hT₀ge, hT₀_sum⟩ := h_div
      -- Under RH, zeros in ZerosBelowPos T₀ have Re = 1/2
      have hS_half : ∀ ρ ∈ ZerosBelowPos T₀, ρ.re = 1/2 := by
        intro ρ hρ
        simp only [ZerosBelowPos, Finset.mem_filter] at hρ
        have hρ_crit : ρ ∈ CriticalZeros := by
          simp only [ZerosBelow] at hρ
          split_ifs at hρ with hfin
          · exact ((hfin.mem_toFinset).mp hρ.1).1
          · simp at hρ
        exact hRH ρ hρ_crit
      -- Align phases of ZerosBelowPos T₀ to -I
      have h_align := InhomogeneousPhaseAlignmentHyp.align_to_target
        (ZerosBelowPos T₀) hS_half
        (-I) (by simp [Complex.norm_neg, Complex.norm_I])
        (1/4 : ℝ) (by norm_num)
        (max X 2)
      obtain ⟨x, hx_gt, hx_phases⟩ := h_align
      refine ⟨x, lt_of_le_of_lt (le_max_left X 2) hx_gt, ?_⟩
      -- Assembly: combine alignment bound + explicit formula + divergence
      -- to get chebyshevPsi x - x ≥ C * √x
      sorry -- Assembly: upper bound on positive-Im zero sum + explicit formula bridge
    · -- Negative: chebyshevPsi x - x ≤ -(C * √x) cofinally
      -- Strategy: align positive-Im zeros to I, making Re(∑ x^ρ/ρ) very positive
      intro C X
      have h_div := ZeroSumImDivergenceHyp.sum_im_diverges hRH
        (4 * (|C| + |C_ef| + 1))
      obtain ⟨T₀, hT₀ge, hT₀_sum⟩ := h_div
      have hS_half : ∀ ρ ∈ ZerosBelowPos T₀, ρ.re = 1/2 := by
        intro ρ hρ
        simp only [ZerosBelowPos, Finset.mem_filter] at hρ
        have hρ_crit : ρ ∈ CriticalZeros := by
          simp only [ZerosBelow] at hρ
          split_ifs at hρ with hfin
          · exact ((hfin.mem_toFinset).mp hρ.1).1
          · simp at hρ
        exact hRH ρ hρ_crit
      have h_align := InhomogeneousPhaseAlignmentHyp.align_to_target
        (ZerosBelowPos T₀) hS_half
        I (by simp [Complex.norm_I])
        (1/4 : ℝ) (by norm_num)
        (max X 2)
      obtain ⟨x, hx_gt, hx_phases⟩ := h_align
      refine ⟨x, lt_of_le_of_lt (le_max_left X 2) hx_gt, ?_⟩
      sorry -- Assembly: lower bound on positive-Im zero sum + explicit formula bridge

end Aristotle.Standalone.PsiOscillationFromShiftedAlignment
