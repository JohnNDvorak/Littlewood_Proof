/-
Decomposition of ExplicitFormulaAndOscillationHyp (Blocker B5) into two
independent sorry-leaf hypotheses:

  1. ExplicitFormulaPsiAtTEqXHyp — truncated explicit formula at T=x (unconditional)
  2. PsiZeroSumOscillationHyp — cofinal oscillation of zero sum (conditional on RH)

These two assertions are mathematically independent:
  (1) is unconditional number theory (Riemann-von Mangoldt, Montgomery-Vaughan §12.5)
  (2) requires RH and uses Dirichlet approximation on zero phases (Littlewood 1914)

The assembly theorem `explicitFormulaAndOscillationHyp_proved` trivially pairs them
to instantiate the combined class `ExplicitFormulaAndOscillationHyp`.

NOTE: The name `TruncatedExplicitFormulaPsiHyp` is NOT used here because it already
exists in Bridge/ExplicitFormulaOscillation.lean and is documented as FALSE
(see README line 281, LandauOscillation.lean:8-12).

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.RHPsiWitnessFromZeroSum

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

open Filter Complex
open GrowthDomination
open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.RHPsiWitnessFromZeroSum (psiMainTerm)
open ZetaZeros

-- ============================================================
-- Sub-sorry 1a: General truncated explicit formula (variable T)
-- ============================================================

/-- **Strengthened sub-sorry for B5**: General truncated explicit formula for ψ
with variable truncation parameter T.

For all x ≥ 2, T ≥ 2:
  |ψ(x) - x + Σ_{|γ|≤T} Re(x^ρ/ρ)| ≤ C · (√x · (log T)² / √T + (log x)²)

The T=x specialization recovers ExplicitFormulaPsiAtTEqXHyp with error O((log x)²).
The variable-T form is needed for the Ingham oscillation argument (B5b).
Reference: Davenport Ch. 17, Montgomery-Vaughan §12.5. -/
class ExplicitFormulaPsiGeneralHyp : Prop where
  proof : ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
    |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
      (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
    C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)

-- ============================================================
-- Sub-sorry 1b: Truncated explicit formula at T=x (derived)
-- ============================================================

/-- **Sub-sorry leaf 1/2 for B5**: Truncated explicit formula for ψ at T=x.

For all x ≥ 2, |ψ(x) - x + Σ_{|γ|≤x} Re(x^ρ/ρ)| ≤ C · (log x)².

This is the T=x specialization of the full truncated explicit formula.
The error O((log x)²) comes from the tail ∑_{|γ|>x} x^ρ/ρ = O(x(log²(x²))/x).
Reference: Montgomery-Vaughan §12.5, Davenport Ch. 17. -/
class ExplicitFormulaPsiAtTEqXHyp : Prop where
  proof : ∃ C : ℝ, ∀ x : ℝ, x ≥ 2 →
    |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
      (-(∑ ρ ∈ ZerosBelow x, ((x : ℂ) ^ ρ) / ρ).re)| ≤ C * (Real.log x) ^ 2

/-- The general explicit formula implies the T=x specialization.
Setting T=x: error ≤ C·(√x·(log x)²/√x + (log x)²) = C·2·(log x)². -/
instance explicitFormulaPsiAtTEqX_of_general
    [h : ExplicitFormulaPsiGeneralHyp] : ExplicitFormulaPsiAtTEqXHyp where
  proof := by
    obtain ⟨C, hC⟩ := h.proof
    refine ⟨2 * |C|, fun x hx => ?_⟩
    have hEF := hC x x hx hx
    have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    -- At T=x: √x·(log x)²/√x = (log x)²
    have h_sqrt_pos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos_of_pos (by linarith)
    have h_sqrt_cancel : Real.sqrt x * (Real.log x) ^ 2 / Real.sqrt x = (Real.log x) ^ 2 := by
      rw [mul_div_cancel_left₀]
      exact ne_of_gt h_sqrt_pos
    -- error ≤ C·((log x)² + (log x)²) = C·2·(log x)² ≤ 2|C|·(log x)²
    calc |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow x, ((x : ℂ) ^ ρ) / ρ).re)|
        ≤ C * (Real.sqrt x * (Real.log x) ^ 2 / Real.sqrt x + (Real.log x) ^ 2) := hEF
      _ = C * (2 * (Real.log x) ^ 2) := by rw [h_sqrt_cancel]; ring
      _ ≤ |C| * (2 * (Real.log x) ^ 2) := by
          apply mul_le_mul_of_nonneg_right (le_abs_self C)
          positivity
      _ = 2 * |C| * (Real.log x) ^ 2 := by ring

-- ============================================================
-- Sub-sorry 2: Oscillation of zero sum under RH
-- ============================================================

/-- **Sub-sorry leaf 2/2 for B5**: Under RH, `ψ(x) - x` is unbounded in both
directions relative to √x.

The Landau indirect argument (Landau 1905, Ingham 1932) proves by contradiction:
if ψ(x) - x were bounded above (or below) by C√x for all large x, the Dirichlet
series for ψ would converge past Re(s) = 1/2, contradicting RH (critical-line zeros).

Quantifies over all C: the oscillation grows without bound. -/
class PsiZeroSumOscillationHyp : Prop where
  proof : ZetaZeros.RiemannHypothesis →
    (∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≥ C * Real.sqrt x) ∧
    (∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≤ -(C * Real.sqrt x))

-- ============================================================
-- Assembly: pair the two leaves into the combined class
-- ============================================================

/-- Assembly: `ExplicitFormulaAndOscillationHyp` follows trivially from the
two independent sub-sorry leaves by pairing their `.proof` fields. -/
theorem explicitFormulaAndOscillationHyp_proved
    [ExplicitFormulaPsiAtTEqXHyp] [PsiZeroSumOscillationHyp] :
    Aristotle.Standalone.RHPsiWitnessFromZeroSum.ExplicitFormulaAndOscillationHyp where
  proof := ⟨ExplicitFormulaPsiAtTEqXHyp.proof, PsiZeroSumOscillationHyp.proof⟩

end Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
