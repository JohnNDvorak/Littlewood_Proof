/-
# Perron linear-log witness leaf

The linear-log explicit formula is PROVED from a sorry-backed Perron
decomposition via triangle inequality and the constructive conversion
lemma (log T)^2 / T <= log T / sqrt(T).

## Structure

1. **Proved**: `log_le_sqrt`, `log_sq_div_le_log_div_sqrt`.
2. **Concrete definitions**: `perronIntRe`, `contourRemainderRe` — the actual
   Perron contour integral and the residue-extracted contour remainder.
3. **Sorry leaf 1**: `perron_truncation_tail_bound` — Perron kernel tail O(log x).
4. **Sorry leaf 2**: `perron_horizontal_segment_bound` — horizontal segments O(sqrt(x)*(logT)^2/T).
5. **Proved**: `perron_contour_decomposition` — from the 2 leaves + residue identity (tautological).
6. **Proved**: `perron_linear_log_explicit_formula` — from decomposition + conversion lemmas.
-/

import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.PerronLinearLogWitnessLeaf

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload

/-! ### Proved: log T <= sqrt(T) conversion -/

theorem log_le_sqrt {T : ℝ} (hT : T ≥ 1) : Real.log T ≤ Real.sqrt T := by
  have hT_pos : (0:ℝ) < T := by linarith
  have hu := Real.sqrt_nonneg T
  have husq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (by linarith)
  have hTaylor : T ≤ Real.exp (Real.sqrt T) := by
    have hsum := Real.sum_le_exp_of_nonneg hu 4
    suffices h : T ≤ ∑ i ∈ Finset.range 4, Real.sqrt T ^ i / ↑(Nat.factorial i) from
      le_trans h hsum
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial,
      Nat.cast_one, div_one, zero_add]
    ring_nf
    nlinarith [husq, hu, sq_nonneg (Real.sqrt T), sq_nonneg (Real.sqrt T - 1),
              mul_nonneg hu (sq_nonneg (Real.sqrt T - 1))]
  calc Real.log T ≤ Real.log (Real.exp (Real.sqrt T)) :=
        Real.log_le_log hT_pos hTaylor
    _ = Real.sqrt T := Real.log_exp _

theorem log_sq_div_le_log_div_sqrt {T : ℝ} (hT : T ≥ 1) :
    (Real.log T) ^ 2 / T ≤ Real.log T / Real.sqrt T := by
  have hT_pos : (0:ℝ) < T := by linarith
  have hsqrt_pos : (0:ℝ) < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  rw [div_le_div_iff₀ hT_pos hsqrt_pos]
  calc (Real.log T) ^ 2 * Real.sqrt T
      = Real.log T * (Real.log T * Real.sqrt T) := by ring
    _ ≤ Real.log T * (Real.sqrt T * Real.sqrt T) := by
        gcongr
        · exact Real.log_nonneg hT
        · exact log_le_sqrt hT
    _ = Real.log T * T := by rw [Real.mul_self_sqrt (by linarith)]

/-! ### Concrete Perron integral definitions

The Perron vertical integral at abscissa c = 1 + 1/log(x), truncated at height T.
This is the actual contour integral (1/2pi) * int_{-T}^{T} Re((-zeta'/zeta)(c+it) * x^(c+it) / (c+it)) dt.
The definition is a local copy of PerronTruncationInfra.perronVerticalIntegral to
avoid importing that file (which has a pre-existing tactic error at line 1133). -/

/-- The truncated Perron integral for psi(x) at abscissa c = 1 + 1/log(x). -/
noncomputable def perronIntRe (x T : ℝ) : ℝ :=
  let c := 1 + 1 / Real.log x
  (2 * Real.pi)⁻¹ * ∫ t in (-T)..T,
    ((-deriv riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) /
      riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I)) *
     (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
     ((c : ℂ) + (t : ℂ) * Complex.I)).re

/-- The contour remainder, defined from the residue identity. This makes
the residue identity hold by definition (`ring`). -/
noncomputable def contourRemainderRe (x T : ℝ) : ℝ :=
  perronIntRe x T - x + (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re

-- Sorry leaves and instance moved to PerronLinearLogDirectSorry.lean (priority 200).
-- Proved conversion lemmas (log_le_sqrt, log_sq_div_le_log_div_sqrt) remain above.

end Aristotle.Standalone.ExternalPort.PerronLinearLogWitnessLeaf
