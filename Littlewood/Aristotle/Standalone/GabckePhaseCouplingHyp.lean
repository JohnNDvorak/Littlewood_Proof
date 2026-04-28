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
import Littlewood.Aristotle.Standalone.GabckeSignedProfileInstance

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

set_option linter.dupNamespace false

namespace Aristotle.Standalone.GabckePhaseCouplingHyp

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam Aristotle.ErrorTermExpansion
open Aristotle.Standalone.SiegelSaddleExpansionHyp

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

/-! ## Instance from atomic Gabcke leaves -/

/-- Direct theorem-first packaging of Gabcke's phase coupling from the two
no-axiom atomic Gabcke leaves.

    The proof chain:
    1. `GabckeBlockIndependence` + `GabckeSignPositivity` give the direct
       adjacent theorem surface via
       `GabckeSignedProfileInstance.remainder_antitone_for_ge_one_of_atoms`
    2. `block_estimate_iff_remainder_antitone` turns that into the block
       estimate condition
    3. `block_estimate_suffices` packages the result as
       `GabckePhaseCouplingHyp`

    Reference: Gabcke 1979 Satz 4. -/
theorem gabckePhaseCouplingHyp_of_atoms
    [GabckeSignedProfileInstance.GabckeBlockIndependence]
    [GabckeSignedProfileInstance.GabckeSignPositivity] :
    GabckePhaseCouplingHyp := by
  apply block_estimate_suffices
  intro k hk
  exact GabckePhaseCouplingInfra.block_estimate_iff_remainder_antitone k
    (Aristotle.Standalone.GabckeSignedProfileInstance.remainder_antitone_for_ge_one_of_atoms k hk)

/-- Direct theorem-first packaging of Gabcke's phase coupling from the exact
atomic boundary proposition. -/
theorem gabckePhaseCouplingHyp_of_atomicHyp
    (h : GabckeSignedProfileInstance.GabckeAtomicHyp) :
    GabckePhaseCouplingHyp := by
  let _ : GabckeSignedProfileInstance.GabckeBlockIndependence :=
    GabckeSignedProfileInstance.gabckeBlockIndependence_of_atomicHyp h
  let _ : GabckeSignedProfileInstance.GabckeSignPositivity :=
    GabckeSignedProfileInstance.gabckeSignPositivity_of_atomicHyp h
  exact gabckePhaseCouplingHyp_of_atoms

/-- Direct theorem-first block-correction antitonicity from the two no-axiom
atomic Gabcke leaves. This exposes the true current frontier without requiring
callers to go through the wrapper class explicitly. -/
theorem block_correction_antitone_of_atoms
    [GabckeSignedProfileInstance.GabckeBlockIndependence]
    [GabckeSignedProfileInstance.GabckeSignPositivity] :
    AntitoneOn signedBlockCorrection (Ici (1 : ℕ)) :=
  (gabckePhaseCouplingHyp_of_atoms).block_correction_antitone

/-- Direct theorem-first block-correction antitonicity from the exact atomic
boundary proposition. -/
theorem block_correction_antitone_of_atomicHyp
    (h : GabckeSignedProfileInstance.GabckeAtomicHyp) :
    AntitoneOn signedBlockCorrection (Ici (1 : ℕ)) :=
  (gabckePhaseCouplingHyp_of_atomicHyp h).block_correction_antitone

/-- Compatibility instance: the wrapper class is now secondary to the direct
theorem-first atomic route above. -/
instance
    [GabckeSignedProfileInstance.GabckeBlockIndependence]
    [GabckeSignedProfileInstance.GabckeSignPositivity] :
    GabckePhaseCouplingHyp :=
  gabckePhaseCouplingHyp_of_atoms

/-! ## Route from GabckeSignedAdjacentHyp (bypasses false GabckeBlockIndependence)

GabckeBlockIndependence is mathematically false (exact k-independence doesn't hold).
The weaker GabckeSignedAdjacentProp (adjacent monotonicity) IS true and suffices.
The route: GabckeSignedAdjacentHyp → remainder_antitone_for_ge_one_of_adjacent
→ block_estimate_iff_remainder_antitone → block_estimate_suffices → GabckePhaseCouplingHyp -/

theorem gabckePhaseCouplingHyp_of_adjacent
    [GabckePhaseCouplingInfra.GabckeSignedAdjacentHyp] :
    GabckePhaseCouplingHyp := by
  apply block_estimate_suffices
  intro k hk
  exact GabckePhaseCouplingInfra.block_estimate_iff_remainder_antitone k
    (GabckePhaseCouplingInfra.remainder_antitone_for_ge_one_of_adjacent k hk)

instance [GabckePhaseCouplingInfra.GabckeSignedAdjacentHyp] :
    GabckePhaseCouplingHyp :=
  gabckePhaseCouplingHyp_of_adjacent

/-- Conditional reduction for the public Hardy bridge: the current
`SiegelSaddleExpansionHyp` fields include the two adjacent Gabcke Satz 4 atoms
needed by `GabckeSignedAdjacentHyp`, hence they supply the legacy
`GabckePhaseCouplingHyp` wrapper without an additional public assumption. -/
theorem gabckePhaseCouplingHyp_of_siegelSaddleExpansionHyp
    [SiegelSaddleExpansionHyp] :
    GabckePhaseCouplingHyp :=
  gabckePhaseCouplingHyp_of_adjacent

/-- The theorem-shaped block-correction consequence of the Siegel/Gabcke
adjacent atoms. -/
theorem block_correction_antitone_of_siegelSaddleExpansionHyp
    [SiegelSaddleExpansionHyp] :
    AntitoneOn signedBlockCorrection (Ici (1 : ℕ)) :=
  gabckePhaseCouplingHyp_of_siegelSaddleExpansionHyp.block_correction_antitone

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

/-- Direct theorem-first bridge theorem from the two no-axiom atomic Gabcke
leaves, bypassing the wrapper class. -/
theorem antitone_from_atoms
    [GabckeSignedProfileInstance.GabckeBlockIndependence]
    [GabckeSignedProfileInstance.GabckeSignPositivity] :
    let A_val := 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)
    let c_fn := fun k : ℕ =>
      (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - A_val * Real.sqrt ((k : ℝ) + 1)
    AntitoneOn c_fn (Ici (1 : ℕ)) := by
  let _ : GabckePhaseCouplingHyp := gabckePhaseCouplingHyp_of_atoms
  exact antitone_from_hyp

/-- Direct theorem-first bridge theorem from the exact atomic boundary
proposition, bypassing all wrapper classes. -/
theorem antitone_from_atomicHyp
    (h : GabckeSignedProfileInstance.GabckeAtomicHyp) :
    let A_val := 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)
    let c_fn := fun k : ℕ =>
      (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - A_val * Real.sqrt ((k : ℝ) + 1)
    AntitoneOn c_fn (Ici (1 : ℕ)) := by
  let _ : GabckePhaseCouplingHyp := gabckePhaseCouplingHyp_of_atomicHyp h
  exact antitone_from_hyp

end Aristotle.Standalone.GabckePhaseCouplingHyp
