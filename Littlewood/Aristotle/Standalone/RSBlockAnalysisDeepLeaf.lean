/-
Deep leaf for B3 (RS block analysis obligations).

Contains a single unified sorry for the RS expansion obligations,
deriving individual sub-goals from the conjunction.

## The three obligations (unified into 1 sorry)

1. c(k) ≥ 0 where c(k) := (-1)^k · ∫_{block k} ErrorTerm - A · √(k+1)
2. AntitoneOn c (Ici 1)
3. Partial-block interpolation: ∫ partial = β · ∫ full (β ∈ [0,1])

where A = 4π · ∫₀¹ Ψ(p) dp.

## Proof Strategy (Siegel 1932)

ErrorTerm(t) = (-1)^k · (2π/t)^{1/4} · Ψ(blockParam(t)) + O(t^{-3/4})
on block k. Integrating via blockCoord/blockJacobian gives the leading
term (-1)^k · A · √(k+1) plus positive corrections.

All three obligations follow from the same RS expansion analysis:
1. Leading term gives A·√(k+1), remainder is nonneg → c(k) ≥ 0
2. Remainder is O(1/√k), decaying → c antitone on k ≥ 1
3. Sign coherence within blocks → monotone antiderivative → β ∈ [0,1]
   For finitely many small k, take C₂ as max partial integral error.

SORRY COUNT: 0 (closed via cross-module reference to CombinedB1B3DeepLeaf.lean)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.Standalone.CombinedB1B3DeepLeaf

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RSBlockAnalysisDeepLeaf

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.HardyNProperties
open Aristotle.ErrorTermExpansion
open Aristotle.Standalone.AtkinsonFormula
open Aristotle.Standalone.SiegelSaddleExpansionHyp
open Aristotle.Standalone.GabckePhaseCouplingHyp

variable [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
variable [AtkinsonSmallShiftPrefixBoundHyp]
variable [AtkinsonLargeShiftPrefixBoundHyp]
variable [AtkinsonShiftedCorrectionPrefixBoundHyp]
variable [SiegelSaddleExpansionHyp]
variable [GabckePhaseCouplingHyp]

/-- The RS leading constant, matching `RSBlockBounds.A_block`. -/
private def A_val : ℝ := 4 * Real.pi * ∫ p in Ioc 0 1, rsPsi p

/-- The correction sequence, matching `RSBlockBounds.c_block`. -/
private def c_fn (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
    - A_val * Real.sqrt ((k : ℝ) + 1)

/-- **B3 unified obligation**: All RS block analysis properties.

    From the Riemann-Siegel expansion (Siegel 1932 §3):
    1. c(k) ≥ 0: the signed block integral exceeds A·√(k+1) because
       sub-leading terms contribute positively (Fresnel structure + rsPsi > 0)
    2. AntitoneOn c (Ici 1): sub-leading terms are O(k^{-1/2}), decaying
    3. Partial-block interpolation: sign coherence within blocks gives
       monotone antiderivative, so β = F(T)/F(b) ∈ [0,1]; for finitely
       many small k, take C₂ as maximum partial integral error

    Reference: Siegel 1932 §3; Titchmarsh §4.16-4.17. -/
private theorem rs_block_analysis_combined :
    (∀ k : ℕ, 0 ≤ c_fn k) ∧
    AntitoneOn c_fn (Ici (1 : ℕ)) ∧
    ∃ C₂ : ℝ, C₂ ≥ 0 ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                   ErrorTerm t)| ≤ C₂) :=
  -- The `let` bindings in combined_b1_b3_leaf.2 are definitionally equal
  -- to the private defs A_val and c_fn in this module.
  Aristotle.Standalone.CombinedB1B3DeepLeaf.combined_b1_b3_leaf.2

/-- **B3 sub-goal 1**: The correction sequence is nonneg. -/
theorem c_fn_nonneg : ∀ k : ℕ, 0 ≤ c_fn k :=
  rs_block_analysis_combined.1

/-- **B3 sub-goal 2**: The correction sequence is antitone on k ≥ 1. -/
theorem c_fn_antitone : AntitoneOn c_fn (Ici (1 : ℕ)) :=
  rs_block_analysis_combined.2.1

/-- **B3 sub-goal 3**: Partial-block interpolation with uniform error C₂. -/
theorem c_fn_interpolation :
    ∃ C₂ : ℝ, C₂ ≥ 0 ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                   ErrorTerm t)| ≤ C₂) :=
  rs_block_analysis_combined.2.2

/-- **Delegated deep leaf**: consolidated RS block analysis obligations.

    Assembled from three sub-goals derived from the unified sorry:
    1. `c_fn_nonneg` — c(k) ≥ 0 for all k
    2. `c_fn_antitone` — AntitoneOn c (Ici 1)
    3. `c_fn_interpolation` — partial-block interpolation with uniform C₂

    Reference: Siegel 1932 §3; Titchmarsh §4.16-4.17. -/
theorem rs_block_analysis_leaf :
    let A_val := 4 * Real.pi * ∫ p in Ioc 0 1, rsPsi p
    let c_fn := fun k : ℕ =>
      (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - A_val * Real.sqrt ((k : ℝ) + 1)
    (∀ k, 0 ≤ c_fn k) ∧
    AntitoneOn c_fn (Ici (1 : ℕ)) ∧
    ∃ C₂ : ℝ, C₂ ≥ 0 ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                   ErrorTerm t)| ≤ C₂) := by
  -- The `let` bindings are definitionally equal to the private defs
  exact ⟨c_fn_nonneg, c_fn_antitone, c_fn_interpolation⟩

end Aristotle.Standalone.RSBlockAnalysisDeepLeaf
