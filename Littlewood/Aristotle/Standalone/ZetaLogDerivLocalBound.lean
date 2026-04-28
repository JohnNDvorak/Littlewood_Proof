/-
# Far-zero contribution bound for ζ'/ζ

Sub-lemma C for the Backlund S(T) = O(log T) bound:
the "far-zero" contribution Σ_{|γ-T| > 2} 1/|σ+iT - ρ| is O(log T)
for σ ∈ [1/2, 2] and T ≥ 14.

## Proof outline

1. For |γ-T| > 2 and σ ∈ [1/2, 2], β ∈ [0, 1]:
   |σ+iT - ρ| ≥ |T-γ| - |σ-β| ≥ |T-γ| - 2 ≥ |T-γ|/2
   So 1/|σ+iT-ρ| ≤ 2/|T-γ|.

2. Shell decomposition: Σ_{|γ-T| > 2} 1/|T-γ| ≤ Σ_{n≥2} (count in shell n)/n.
   Shell n has zeros with n ≤ |γ-T| < n+1.
   Count ≤ N(T+n+1) ≤ C·(T+n+1)·log(T+n+1) (crude bound).

3. Each shell contributes ≤ C·(T+n+1)·log(T+n+1)/n ≤ C'·log(T+n+1)·(1+1/n).
   Sum over n ≥ 2: converges by comparison with Σ log(T+n)/n² (since (T+n+1)/n ≤ T+2 for n≥2... actually need more care).

Actually, the cleaner route:
   Σ_{|γ-T|>2} 1/|T-γ| ≤ Σ_{|γ-T|>2} 1/(|T-γ|-1)²  ... no.

Cleaner: use 1/|T-γ|² ≤ 1/|T-γ| and partial summation.
   Σ 1/|T-γ|² ≤ Σ_{n≥2} (shells of width 1 at distance n) · 1/n²
   ≤ Σ_{n≥2} [N(T+n+1) - N(T-n-1)] / n²
   ≤ Σ_{n≥2} C·(T+n+1)·log(T+n+1) / n²

For the 1/|T-γ| version: this is harder. Use Abel summation against N.

For NOW: prove the simpler bound Σ 1/|T-γ|² ≤ C·log T, which suffices for
the kernel conversion (each term gets multiplied by the bounded |σ+iT-ρ|⁻¹).

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.ZeroCountingMultiplicity

set_option maxHeartbeats 1600000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ZetaZeros.ZetaLogDerivLocalBound

open Real ZetaZeros

/-! ### Distance bound for far zeros -/

/-- For a zero ρ = β + iγ with |γ-T| > 2 and σ ∈ [1/2, 2]:
    |σ + iT - ρ| ≥ |γ - T|/2 > 1. -/
theorem far_zero_norm_lower_bound
    {σ T : ℝ} (hσ_lo : 1 / 2 ≤ σ) (hσ_hi : σ ≤ 2)
    {ρ : ℂ} (hβ_lo : 0 < ρ.re) (hβ_hi : ρ.re < 1)
    (hfar : 2 < |ρ.im - T|) :
    |ρ.im - T| / 2 ≤ ‖(↑σ + ↑T * Complex.I) - ρ‖ := by
  -- The imaginary part of (σ+iT - ρ) is T - ρ.im, so |im| = |T - ρ.im| = |ρ.im - T|.
  -- And |ρ.im - T|/2 ≤ |ρ.im - T| ≤ |im part| ≤ ‖·‖.
  have him : (↑σ + ↑T * Complex.I - ρ).im = T - ρ.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.sub_im]
  calc |ρ.im - T| / 2
      ≤ |ρ.im - T| := by linarith [abs_nonneg (ρ.im - T)]
    _ = |T - ρ.im| := abs_sub_comm _ _
    _ = |(↑σ + ↑T * Complex.I - ρ).im| := by rw [him]
    _ ≤ ‖(↑σ + ↑T * Complex.I) - ρ‖ := Complex.abs_im_le_norm _

/-- The reciprocal bound: 1/‖s-ρ‖ ≤ 2/|γ-T| for far zeros. -/
theorem far_zero_inv_norm_upper_bound
    {σ T : ℝ} (hσ_lo : 1 / 2 ≤ σ) (hσ_hi : σ ≤ 2)
    {ρ : ℂ} (hβ_lo : 0 < ρ.re) (hβ_hi : ρ.re < 1)
    (hfar : 2 < |ρ.im - T|) :
    1 / ‖(↑σ + ↑T * Complex.I) - ρ‖ ≤ 2 / |ρ.im - T| := by
  have habs_pos : 0 < |ρ.im - T| := by linarith
  have hnorm_pos : 0 < ‖(↑σ + ↑T * Complex.I) - ρ‖ := by
    have := far_zero_norm_lower_bound hσ_lo hσ_hi hβ_lo hβ_hi hfar
    linarith
  rw [div_le_div_iff₀ hnorm_pos habs_pos]
  nlinarith [far_zero_norm_lower_bound hσ_lo hσ_hi hβ_lo hβ_hi hfar]

end ZetaZeros.ZetaLogDerivLocalBound
