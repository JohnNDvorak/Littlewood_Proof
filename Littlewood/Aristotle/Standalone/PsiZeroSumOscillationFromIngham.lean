/-
Proof of PsiZeroSumOscillationHyp (B5b) from ExplicitFormulaPsiGeneralHyp (B5a)
via Ingham's contradiction argument.

## Mathematical Strategy (Ingham 1932)

Given the general truncated explicit formula (B5a) with variable truncation T:
  |ψ(x) - x + Σ_{|γ|≤T} Re(x^ρ/ρ)| ≤ C · (√x · (log T)²/√T + (log x)²)

To show: under RH, psiMainTerm(x) = Σ_{|γ|≤x} Re(x^ρ/ρ) oscillates cofinally ≥ 4√x·lll(x).

1. Choose T₀ large so that ∑_{Im(ρ)>0, ρ∈ZerosBelow(T₀)} Re(I/ρ) > M (arbitrarily large)
2. Align positive-Im zero phases to I via inhomogeneous Dirichlet approximation
3. Use the general EF at T=T₀ and T=x to relate psiMainTerm to the T₀-truncated sum
4. The T₀-truncated sum splits as 2·Σ_{Im(ρ)>0} Re(x^ρ/ρ) (conjugate pairs contribute equally)
5. Aligned contribution ≥ 2√x·(∑ Re(I/ρ) − ε·∑ 1/‖ρ‖) ≈ √x·(log T₀)²
6. Error from bridge ≤ C·(√x·(log T₀)²/√T₀ + (log x)²) — dominated by signal for T₀ large
7. Since lll(x) ≈ log(log T₀) ≪ (log T₀)², the oscillation ≥ 4√x·lll(x) follows

## Sub-results needed (sorry within main proof body)

1. **Inhomogeneous phase alignment** (Cassels 1957, Ch. III):
   For any finset S of critical-line zeros, target w on unit circle, ε > 0, X > 0,
   ∃ x > X with all phases x^{iγ} within ε of w.

2. **Divergence of ∑_{Im(ρ)>0} Re(I/ρ)** (Backlund 1918 + partial summation):
   Under RH, ∑_{Im(ρ)>0, ρ∈ZerosBelow(T)} Re(I/ρ) → +∞.
   For ρ = 1/2+iγ, γ > 0: Re(I/ρ) = γ/(1/4+γ²) ≈ 1/γ, and ∑ 1/γ ~ (log T)²/(4π).

3. **Conjugate pair Re equality**: Re(x^ρ/ρ) = Re(x^{ρ̄}/ρ̄) for real x > 0.
   Proof: conj(x^ρ/ρ) = x^{conj(ρ)}/conj(ρ) when x ∈ ℝ, and Re(conj(z)) = Re(z).

## References

- Ingham, A. E. (1932). The Distribution of Prime Numbers. Cambridge Tracts.
- Davenport, H. (2000). Multiplicative Number Theory, Ch. 17.
- Montgomery-Vaughan (2007). Multiplicative Number Theory I, §15.2.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
import Littlewood.Aristotle.DirichletPhaseAlignment

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.PsiZeroSumOscillationFromIngham

open Filter Complex
open GrowthDomination
open Aristotle.DirichletPhaseAlignment (ZerosBelow CriticalZeros)
open Aristotle.Standalone.RHPsiWitnessFromZeroSum (psiMainTerm)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open ZetaZeros

-- ============================================================
-- Infrastructure: positive-imaginary-part zeros (PROVED)
-- ============================================================

/-- The subset of ZerosBelow T with strictly positive imaginary part. -/
def PositiveImZerosBelow (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => 0 < ρ.im)

lemma positiveImZerosBelow_sub (T : ℝ) :
    PositiveImZerosBelow T ⊆ ZerosBelow T :=
  Finset.filter_subset _ _

lemma positiveImZerosBelow_re_half (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ ρ ∈ PositiveImZerosBelow T, ρ.re = 1 / 2 := by
  intro ρ hρ
  have hρ_mem : ρ ∈ ZerosBelow T := positiveImZerosBelow_sub T hρ
  have hρ_crit : ρ ∈ CriticalZeros := by
    simp only [ZerosBelow] at hρ_mem
    split_ifs at hρ_mem with hfin
    · exact ((hfin.mem_toFinset).mp hρ_mem).1
    · simp at hρ_mem
  exact hRH ρ hρ_crit

-- ============================================================
-- Proved: Re(I/ρ) ≤ 1/‖ρ‖ for nonzero ρ
-- ============================================================

/-- For any nonzero ρ, Re(I/ρ) ≤ 1/‖ρ‖.
Proof: |Re(z)| ≤ ‖z‖ and ‖I/ρ‖ = 1/‖ρ‖. -/
lemma re_I_div_le_inv_norm (ρ : ℂ) (_hρ : ρ ≠ 0) :
    (I / ρ).re ≤ 1 / ‖ρ‖ := by
  calc (I / ρ).re ≤ ‖I / ρ‖ := le_trans (le_abs_self _) (abs_re_le_norm _)
    _ = ‖I‖ / ‖ρ‖ := by rw [norm_div]
    _ = 1 / ‖ρ‖ := by rw [Complex.norm_I]

-- ============================================================
-- Main theorem: PsiZeroSumOscillationHyp from general explicit formula
-- ============================================================

/-- **B5b proved from B5a** via Ingham's argument (Ingham 1932):

Under RH, psiMainTerm oscillates cofinally with amplitude ±4√x·lll(x).

The proof uses ExplicitFormulaPsiGeneralHyp (the general truncated explicit formula
with variable T) combined with:
- Inhomogeneous Dirichlet approximation to align zero phases to I
- Divergence of ∑_{Im(ρ)>0} Re(I/ρ) ~ (log T)²/(4π) (from N(T) asymptotics)
- Conjugate pair symmetry: Re(x^ρ/ρ) = Re(x^{ρ̄}/ρ̄) for real x > 0
- bound_real_part_of_sum_shifted (PROVED in DirichletPhaseAlignment.lean)

The full inequality chain (Steps 3-8 below) requires ~100 lines of careful Lean
arithmetic and is deferred to a Codex pass.

Steps:
1. Choose T₀ with ∑_{γ>0} Re(I/ρ) > threshold (divergence)
2. Find x via inhomogeneous alignment of positive-Im zeros to I
3. General EF at T₀: ψ(x) - x ≈ -(∑_{T₀} x^ρ/ρ).re ± C·err₁
4. General EF at x:  ψ(x) - x ≈ -psiMainTerm(x) ± C·err₂
5. Bridge: psiMainTerm(x) ≈ (∑_{T₀} x^ρ/ρ).re ± C·(err₁+err₂)
6. Aligned bound: (∑_{T₀} x^ρ/ρ).re ≥ 2√x·(∑ Re(I/ρ) - ε·∑ 1/‖ρ‖)
7. For T₀ large: net contribution > √x·(log T₀)²/(16π)
8. Since lll(x) ≤ O(log(log T₀)) ≪ (log T₀)², psiMainTerm(x) ≥ 4√x·lll(x) -/
theorem psiZeroSumOscillation_proved
    [ExplicitFormulaPsiGeneralHyp] :
    PsiZeroSumOscillationHyp where
  proof := by
    intro hRH
    -- Extract the constant from the general explicit formula
    obtain ⟨C, hC⟩ := ExplicitFormulaPsiGeneralHyp.proof
    constructor
    · -- POSITIVE OSCILLATION: ∀ X, ∃ x > X, psiMainTerm(x) ≥ 4√x·lll(x)
      -- The argument uses the general EF at two different T values (T₀ and x),
      -- inhomogeneous Dirichlet alignment to I, and the divergence of
      -- ∑_{Im(ρ)>0} Re(I/ρ). See the docstring above for the full outline.
      -- The inequality chain assembly is deferred.
      intro X
      sorry
    · -- NEGATIVE OSCILLATION: ∀ X, ∃ x > X, psiMainTerm(x) ≤ -(4√x·lll(x))
      -- Symmetric: align positive-Im phases to -I instead of I.
      -- bound_real_part_of_sum_shifted_upper gives the upper bound.
      intro X
      sorry

end Aristotle.Standalone.PsiZeroSumOscillationFromIngham
