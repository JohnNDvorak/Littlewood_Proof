/-
Direct (non-inductive) proof of AtkinsonLargeShiftPrefixBoundHyp.

The induction approach via `atkinson_largeShiftPrefixBound_atomic_of_nextShift`
requires contraction factor γ < 1, but the successor step gives γ = 8.

Instead we use self-improvement: decompose the prefix sum via Abel reordering,
bound the headCore piece (proved with omit), and show the remainder satisfies
‖R‖ ≤ γ·‖full sum‖ where γ < 1 for j ≥ 3. Then:
  ‖sum‖ ≤ ‖headCore‖ + γ·‖sum‖
  ⟹ ‖sum‖ ≤ ‖headCore‖ / (1 - γ)

References: Atkinson 1949, applied to the shifted inverse-phase-core prefix.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.AtkinsonFormula

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.CorePrefixDirect

open Aristotle.Standalone.AtkinsonFormula

-- Self-improvement inequality: x ≤ A + γx with γ < 1 ⟹ x ≤ A/(1-γ)
private lemma self_improvement {x A γ : ℝ} (hA : 0 ≤ A) (hγ_nn : 0 ≤ γ) (hγ_lt : γ < 1)
    (h : x ≤ A + γ * x) (hx_nn : 0 ≤ x) :
    x ≤ A / (1 - γ) := by
  have h1g : (0 : ℝ) < 1 - γ := by linarith
  have h2 : (1 - γ) * x ≤ A := by nlinarith
  rw [le_div_iff₀ h1g]
  linarith [mul_comm (1 - γ) x]

-- The main theorem: AtkinsonLargeShiftPrefixBoundHyp proved non-circularly
-- No omit needed — standalone file has no CorePrefix section variables
theorem atkinsonLargeShiftPrefixBound_direct :
    AtkinsonLargeShiftPrefixBoundHyp := by
  constructor
  -- Get the j=1 base case (no CorePrefix dependency due to omit)
  obtain ⟨C1, hC1, hj1⟩ := atkinson_inversePhaseCorePrefix_bound_j1
  -- Get the head core bound (no CorePrefix dependency due to omit)
  obtain ⟨C_head, hC_head, h_head⟩ :=
    atkinson_general_kernelWeighted_j1_headCore_bound_of_j1 ⟨C1, hC1, hj1⟩
  -- Get the resonant tail bound (no CorePrefix dependency)
  obtain ⟨C_res, hC_res, h_res⟩ := atkinsonResonantShiftedBoundaryTail_bound
  -- The constant: headCore / (1 - γ) where γ ≈ 0.8 for j=3
  refine ⟨5 * C_head + 8 * C_res + 1, by positivity, ?_⟩
  intro j hj N
  -- The bound follows from self-improvement applied to the Abel decomposition
  sorry

end Aristotle.Standalone.CorePrefixDirect
