/-
Hypothesis bridge for Gabcke's phase coupling (Satz 4): the signed block
correction c(k) is antitone for k ≥ 1.

This encapsulates the irreducible content of Gabcke 1979 Satz 4:
the signed remainder R(k) inherits phase coherence from the saddle-point
structure, making the block correction antitone. This is strictly harder
than the pointwise bound (Satz 1) because it requires the SIGNED remainder
structure, not just absolute value bounds.

## Mathematical content

The block correction is:
  c(k) = (-1)^k · ∫_{block k} ErrorTerm(t) dt - A · √(k+1)
where A = 4π · ∫₀¹ Ψ(p) dp.

The hypothesis asserts AntitoneOn c_fn (Ici 1) on ℕ, meaning
c(k+1) ≤ c(k) for all k ≥ 1.

This depends on:
(a) The saddle-point expansion giving precise phase information (not just bounds)
(b) The coupling of R(k) across consecutive blocks via phase coherence

SORRY COUNT: 0 (sorry delegated to GabckePhaseCouplingInfra.remainder_antitone_for_ge_one)

Reference: Gabcke 1979 Satz 4.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp
import Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

set_option linter.dupNamespace false

namespace Aristotle.Standalone.GabckePhaseCouplingHyp

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam Aristotle.ErrorTermExpansion

/-! ## Definitions: signed block correction -/

/-- The constant A = 4π · ∫₀¹ Ψ(p) dp appearing in the block correction. -/
def blockCorrectionA : ℝ := 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)

/-- The signed block correction c(k):
    c(k) = (-1)^k · ∫_{block k} ErrorTerm(t) dt - A · √(k+1)

    This measures the departure of the block integral from its expected
    asymptotic value. Gabcke showed this is antitone for k ≥ 1. -/
def signedBlockCorrection (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
    - blockCorrectionA * Real.sqrt ((k : ℝ) + 1)

/-! ## Hypothesis class -/

/-- **Gabcke phase coupling hypothesis** (Gabcke 1979 Satz 4).

    The signed block correction c(k) is antitone on {k : ℕ | k ≥ 1}.
    This captures the phase coherence between consecutive blocks: the
    signed remainder R(k) decreases as k grows, not just its absolute value.

    Closing this sorry requires:
    (a) Full steepest-descent expansion with phase (not just amplitude bounds)
    (b) Explicit evaluation of the Fresnel integrals on consecutive blocks
    (c) Monotone error bounds from the coupling structure

    This is strictly harder than SiegelSaddleExpansionHyp (Satz 1). -/
class GabckePhaseCouplingHyp : Prop where
  block_correction_antitone :
    AntitoneOn signedBlockCorrection (Ici (1 : ℕ))

/-! ## Decomposition: reducing to block estimates -/

open Aristotle.Standalone.GabckePhaseCouplingInfra in
/-- **Decomposition**: the signed block correction has the form
    c(k) = (-1)^k · I(k) - A · √(k+1), so antitone_from_block_estimate applies. -/
theorem signedBlockCorrection_form :
    ∀ k, signedBlockCorrection k =
      (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
      - blockCorrectionA * Real.sqrt ((k : ℝ) + 1) :=
  fun _ => rfl

/-- **Reduced sorry**: it suffices to show the block estimate condition.
    Specifically, for each k ≥ 1:
      blockCorrectionA · (√(k+1) - √(k+2))
      ≤ (-1)^k · (I_k + I_{k+1})
    where I_k = ∫_{block k} ErrorTerm(t) dt.

    This reduces the antitonicity of the signed block correction to a
    per-block signed integral estimate that requires the saddle-point
    expansion with phase information (Gabcke Satz 4). -/
theorem block_estimate_suffices
    (h_est : ∀ k : ℕ, 1 ≤ k →
      blockCorrectionA * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2))
      ≤ (-1 : ℝ) ^ k *
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t) +
         (∫ t in Ioc (hardyStart (k + 1)) (hardyStart (k + 2)), ErrorTerm t))) :
    GabckePhaseCouplingHyp := by
  constructor
  exact GabckePhaseCouplingInfra.antitone_from_block_estimate
    blockCorrectionA
    (fun k => ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
    signedBlockCorrection
    signedBlockCorrection_form
    h_est

/-! ## Instance from remainder antitonicity -/

/-- **Instance**: Gabcke's phase coupling from signed remainder antitonicity.

    The proof chain:
    1. `block_estimate_iff_remainder_antitone`: the block estimate condition
       follows from blockRemainder(k) ≥ blockRemainder(k+1)
    2. `remainder_antitone_for_ge_one`: the signed remainder IS antitone (sorry)

    The sorry is now isolated to the minimal irreducible content:
    R(k) = (-1)^k · ∫_{block k} ErrorTerm - leadingBlockIntegral(k) is antitone.
    This is Gabcke 1979 Satz 4 (signed steepest-descent phase coherence).

    Reference: Gabcke 1979 Satz 4. -/
instance : GabckePhaseCouplingHyp := by
  apply block_estimate_suffices
  intro k hk
  exact GabckePhaseCouplingInfra.block_estimate_iff_remainder_antitone k
    (GabckePhaseCouplingInfra.remainder_antitone_for_ge_one k hk)

/-! ## Bridge theorem -/

/-- **Bridge theorem**: derives the exact statement of
    `block_correction_antitone_from_saddle` from `GabckePhaseCouplingHyp`.

    The key observation is that `signedBlockCorrection` equals the `c_fn`
    defined locally in `block_correction_antitone_from_saddle`, so the
    hypothesis directly yields the goal after unfolding. -/
theorem antitone_from_hyp [GabckePhaseCouplingHyp] :
    let A_val := 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)
    let c_fn := fun k : ℕ =>
      (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - A_val * Real.sqrt ((k : ℝ) + 1)
    AntitoneOn c_fn (Ici (1 : ℕ)) := by
  -- c_fn = signedBlockCorrection
  show AntitoneOn (fun k : ℕ =>
    (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
      - (4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)) *
        Real.sqrt ((k : ℝ) + 1)) (Ici (1 : ℕ))
  convert GabckePhaseCouplingHyp.block_correction_antitone using 1

end Aristotle.Standalone.GabckePhaseCouplingHyp
