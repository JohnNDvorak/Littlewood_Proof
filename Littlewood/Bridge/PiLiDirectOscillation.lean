/-
Bridge: Extract π(x) - li(x) = Ω±(√x / log x) from critical-line zeros
using a truncated explicit formula input tailored to π.

This bridge isolates the oscillation-extraction argument (phase alignment +
anti-alignment) from the analytic Perron-contour work needed to produce the
truncated π explicit formula itself.

Dependencies:
- `HardyCriticalLineZerosHyp`
- `TruncatedExplicitFormulaPiHyp`

Output:
- `PiLiOscillationSqrtHyp`
-/

import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.Aristotle.Standalone.AbelSummationPsiPi

noncomputable section

open Schmidt Asymptotics
open Filter ZetaZeros
open scoped BigOperators

namespace PiLiDirectOscillationBridge

private def piLiError (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x

/-- Input hypothesis for extracting π-li oscillation from critical-line zeros. -/
class TruncatedExplicitFormulaPiHyp : Prop where
  /-- Truncated explicit formula for `π(x) - li(x)` at `√x/log x` scale. -/
  pi_approx :
    ∀ (S : Finset ℂ),
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop,
        |piLiError x + ((∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ).re) / Real.log x|
          ≤ ε * (Real.sqrt x / Real.log x)

  /-- Anti-alignment for singleton critical-line zeros, scaled by `1/log x`. -/
  zero_sum_neg_frequently :
    ∀ (ρ₀ : ℂ), ρ₀ ∈ zetaNontrivialZeros →
      ρ₀.re = 1 / 2 → ρ₀.im ≠ 0 →
      ∃ c > 0, ∀ X : ℝ, ∃ x > X,
        1 < x ∧
          ((∑ ρ ∈ ({ρ₀} : Finset ℂ), ((x : ℂ) ^ ρ / ρ)).re) / Real.log x
            ≤ -(c * (Real.sqrt x / Real.log x))

/-! ### Decomposition of PiApproxFromExplicitFormulaHyp into Abel + ψ-level pieces

The `PiApproxFromExplicitFormulaHyp` sorry decomposes into two independent
mathematical obligations:

1. **Abel correction** (partial summation ψ → π):
   |π(x) - li(x) - (ψ(x) - x)/logx| ≤ D · √x/(logx)²
   Classical: Davenport Ch. 17, Montgomery-Vaughan §2.2.

2. **ψ-level explicit formula with ZerosBelow T** (Perron truncation):
   For any δ > 0, ∃ T₀ ≥ 2, ∀ᶠ x,
     |(ψ(x) - x + Σ_{ρ∈ZerosBelow T₀} x^ρ/ρ) / logx| ≤ δ · √x/logx
   Provable from `general_explicit_formula_from_perron` + choose T₀ with
   (logT₀)²/√T₀ small.

NOTE: The previous decomposition used arbitrary finite sets S of critical-line
zeros (`PsiExplicitFormulaFinsetHyp`), which is mathematically FALSE for S=∅
(would give ψ(x)-x = o(√x), contradicting Littlewood). The correct version
uses ZerosBelow T₀ (the actual Perron truncation set).

The bridge from ZerosBelow → arbitrary S needed by `PiApproxFromExplicitFormulaHyp`
is the remaining mathematical gap (sorry). The downstream fix is to change
`TruncatedExplicitFormulaPiHyp` to also use ZerosBelow T.
-/

/-- Abel summation correction: π(x) - li(x) ≈ (ψ(x) - x)/logx with correction
    of order O(√x/(logx)²). Classical: partial summation applied to the
    prime-counting function (Davenport Ch. 17; Montgomery-Vaughan §2.2).
    Not in Mathlib: requires von Mangoldt sum manipulation + integration. -/
class AbelCorrectionPsiPiHyp : Prop where
  /-- There exists D > 0 such that eventually the Abel correction is small. -/
  correction_bound : ∃ D > (0 : ℝ), ∀ᶠ x in atTop,
    |piLiError x - (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) /
      Real.log x| ≤ D * (Real.sqrt x / (Real.log x) ^ 2)

/-- ψ-level explicit formula using ZerosBelow T (the Perron truncation).

    For any δ > 0, there exists T₀ ≥ 2 such that eventually
    |(ψ(x) - x + Σ_{ρ∈ZerosBelow T₀} x^ρ/ρ) / logx| ≤ δ · √x/logx.

    This is the mathematically correct statement: the Perron formula gives
    |ψ(x) - x + Σ_{|γ|≤T} x^ρ/ρ| ≤ C·(√x·(logT)²/√T + (logx)²),
    and choosing T₀ with (logT₀)²/√T₀ small + x large gives δ-smallness.

    PROVABLE from `general_explicit_formula_from_perron` +
    `psi_bound_div_log_eventually_small` (AbelSummationPsiPi).

    NOTE: The previous `PsiExplicitFormulaFinsetHyp` used arbitrary finite sets S
    of zeros, which is mathematically FALSE for S=∅ (would give ψ(x)-x = o(√x),
    contradicting Littlewood). The ZerosBelow-based statement is correct. -/
class PsiExplicitFormulaZerosHyp : Prop where
  /-- For any δ > 0, there exists T₀ ≥ 2 such that eventually the
      ψ-level error with ZerosBelow T₀, divided by logx, is δ-small
      at the √x/logx scale. -/
  psi_level_bound :
    ∀ δ : ℝ, 0 < δ →
      ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ᶠ x in atTop,
        |(Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x +
            (∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T₀,
              (x : ℂ) ^ ρ / ρ).re) / Real.log x|
          ≤ δ * (Real.sqrt x / Real.log x)

instance : AbelCorrectionPsiPiHyp where
  correction_bound := by sorry

/-- PROVABLE from `general_explicit_formula_from_perron` +
    `psi_bound_div_log_eventually_small`. The proof path:
    1. Get C₂ from `general_explicit_formula_from_perron`
    2. Apply `psi_bound_div_log_eventually_small` with R(x,T) = shiftedRemainderRe x T
    3. This gives T₀ ≥ 2 and eventually |R(x,T₀)|/logx ≤ δ·√x/logx
    Not closed here because this file doesn't import PerronExplicitFormulaProvider. -/
instance : PsiExplicitFormulaZerosHyp where
  psi_level_bound := by sorry

/-- Abel summation ψ→π: the truncated explicit formula for π at √x/logx scale.
    Classical: Davenport Ch. 17 + partial summation (ψ→π).

    BRIDGED from `AbelCorrectionPsiPiHyp` + `PsiExplicitFormulaZerosHyp` via
    the Abel bridge. Sorry: ZerosBelow → arbitrary-S conversion. -/
class PiApproxFromExplicitFormulaHyp : Prop where
  pi_approx_bound :
    ∀ (S : Finset ℂ),
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop,
        |piLiError x + ((∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ).re) / Real.log x|
          ≤ ε * (Real.sqrt x / Real.log x)

/-- The Abel bridge: combine ψ-level ZerosBelow formula with Abel correction
    to get π-level for arbitrary finite sets S.

    MATHEMATICAL NOTE: The conversion from ZerosBelow T₀ to arbitrary S
    requires controlling the tail Σ_{ZerosBelow T₀ \ S} Re(x^ρ/ρ)/logx.
    Under RH, each |Re(x^ρ/ρ)| ≤ √x/|ρ|, so the tail is K·√x/logx
    where K = Σ_{ρ ∈ extra} 1/|ρ|.

    For singleton S = {ρ₀} (the downstream use case), this tail grows
    with T. The correct approach is to change the downstream
    TruncatedExplicitFormulaPiHyp interface to use ZerosBelow T directly.

    For now: sorry bridges the ZerosBelow → arbitrary-S gap.
    This sorry is honestly placed at the mathematically hard step,
    unlike the previous `PsiExplicitFormulaFinsetHyp` which was FALSE. -/
private theorem pi_approx_from_abel_and_psi
    [AbelCorrectionPsiPiHyp] [PsiExplicitFormulaZerosHyp]
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      |piLiError x + ((∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ).re) / Real.log x|
        ≤ ε * (Real.sqrt x / Real.log x) := by
  sorry

instance [AbelCorrectionPsiPiHyp] [PsiExplicitFormulaZerosHyp] :
    PiApproxFromExplicitFormulaHyp where
  pi_approx_bound := fun S hS ε hε => pi_approx_from_abel_and_psi S hS ε hε

/-- Ω₋ direction for `π(x) - li(x)` from aligned phases. -/
private theorem omega_minus_from_zeros
    [TruncatedExplicitFormulaPiHyp]
    (h_zeros : Set.Infinite {ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2}) :
    IsOmegaMinus (fun x => piLiError x) (fun x => Real.sqrt x / Real.log x) := by
  obtain ⟨ρ₀, hρ₀_mem, hρ₀_re⟩ := h_zeros.nonempty

  have hρ₀_re_pos : (0 : ℝ) < ρ₀.re := by rw [hρ₀_re]; norm_num
  have hρ₀_ne : ρ₀ ≠ 0 := by
    intro h
    simp [h] at hρ₀_re_pos

  have h_re_inv_pos : 0 < (1 / ρ₀).re := by
    simp only [one_div]
    rw [Complex.inv_re]
    exact div_pos hρ₀_re_pos (Complex.normSq_pos.mpr hρ₀_ne)

  set c₀ := (1 / ρ₀).re with hc₀_def

  have hS_re : ∀ ρ ∈ ({ρ₀} : Finset ℂ), ρ.re = 1 / 2 := by
    intro ρ hρ
    simp only [Finset.mem_singleton] at hρ
    subst hρ
    exact hρ₀_re

  have hS_in : ∀ ρ ∈ ({ρ₀} : Finset ℂ), ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    simp only [Finset.mem_singleton] at hρ
    subst hρ
    exact ⟨hρ₀_mem, hρ₀_re⟩

  have hρ₀_norm_pos : (0 : ℝ) < ‖ρ₀‖ := norm_pos_iff.mpr hρ₀_ne
  set ε_a := c₀ * ‖ρ₀‖ / 2 with hε_a_def
  have hε_a_pos : (0 : ℝ) < ε_a := by positivity

  have h_ef :=
    TruncatedExplicitFormulaPiHyp.pi_approx {ρ₀} hS_in (c₀ / 4) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp h_ef

  refine ⟨c₀ / 4, by positivity, ?_⟩
  rw [Filter.frequently_atTop]
  intro a

  obtain ⟨x, hx_gt, hx_align⟩ :=
    Aristotle.DirichletPhaseAlignment.exists_large_x_phases_aligned_finset
      {ρ₀} hS_re ε_a hε_a_pos (max (max a x₀) 2)

  have hx_pos : (0 : ℝ) < x := by linarith [le_max_right (max a x₀) (2 : ℝ)]
  have hx_gt_two : (2 : ℝ) < x := by
    exact lt_of_le_of_lt (le_max_right (max a x₀) (2 : ℝ)) hx_gt
  have hx_ge_a : a ≤ x := by
    linarith [le_max_left a x₀, le_max_left (max a x₀) (2 : ℝ)]
  have hx_ge_x₀ : x₀ ≤ x := by
    linarith [le_max_right a x₀, le_max_left (max a x₀) (2 : ℝ)]

  have h_bound :=
    Aristotle.DirichletPhaseAlignment.bound_real_part_of_sum_aligned
      hS_re hx_pos hε_a_pos hx_align

  have h_ef_x := hx₀ x hx_ge_x₀
  simp only [Finset.sum_singleton] at h_bound h_ef_x

  have h_upper := (abs_le.mp h_ef_x).2

  have h_eps_cancel : ε_a * (1 / ‖ρ₀‖) = c₀ / 2 := by
    rw [hε_a_def]
    field_simp

  have h_re_lower : ((x : ℂ) ^ ρ₀ / ρ₀).re ≥ Real.sqrt x * (c₀ / 2) := by
    calc
      ((x : ℂ) ^ ρ₀ / ρ₀).re
          ≥ Real.sqrt x * ((1 / ρ₀).re - ε_a * (1 / ‖ρ₀‖)) := h_bound
      _ = Real.sqrt x * (c₀ / 2) := by
          rw [← hc₀_def, h_eps_cancel]
          ring

  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)

  have h_re_lower_scaled :
      (c₀ / 2) * (Real.sqrt x / Real.log x)
        ≤ (((x : ℂ) ^ ρ₀ / ρ₀).re) / Real.log x := by
    have htmp :
        (Real.sqrt x * (c₀ / 2)) / Real.log x
          ≤ (((x : ℂ) ^ ρ₀ / ρ₀).re) / Real.log x := by
      rw [div_le_div_iff₀ hlog_pos hlog_pos]
      nlinarith [h_re_lower]
    have hrewrite :
        (c₀ / 2) * (Real.sqrt x / Real.log x)
          = (Real.sqrt x * (c₀ / 2)) / Real.log x := by ring
    simpa [hrewrite] using htmp

  refine ⟨x, hx_ge_a, ?_⟩
  nlinarith [h_upper, h_re_lower_scaled]

/-- Ω₊ direction for `π(x) - li(x)` from anti-aligned singleton phases. -/
private theorem omega_plus_from_zeros
    [TruncatedExplicitFormulaPiHyp]
    (h_zeros : Set.Infinite {ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2}) :
    IsOmegaPlus (fun x => piLiError x) (fun x => Real.sqrt x / Real.log x) := by
  have h_inf := h_zeros.diff (Set.finite_singleton ((1 / 2 : ℝ) : ℂ))
  obtain ⟨ρ₀, ⟨hρ₀_mem, hρ₀_re⟩, hρ₀_notin⟩ := h_inf.nonempty

  have hρ₀_im_ne : ρ₀.im ≠ 0 := by
    intro him
    exact hρ₀_notin
      (Set.mem_singleton_iff.mpr
        (Complex.ext (by simp [hρ₀_re]) (by simp [him])))

  have hS_in : ∀ ρ ∈ ({ρ₀} : Finset ℂ), ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    simp only [Finset.mem_singleton] at hρ
    subst hρ
    exact ⟨hρ₀_mem, hρ₀_re⟩

  obtain ⟨c, hc_pos, h_neg⟩ :=
    TruncatedExplicitFormulaPiHyp.zero_sum_neg_frequently ρ₀ hρ₀_mem hρ₀_re hρ₀_im_ne

  have h_ef := TruncatedExplicitFormulaPiHyp.pi_approx {ρ₀} hS_in (c / 2) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp h_ef

  refine ⟨c / 2, by positivity, ?_⟩
  rw [Filter.frequently_atTop]
  intro a

  obtain ⟨x, hx_gt, hx_one, hx_neg⟩ := h_neg (max a x₀)
  have hx_ge_a : a ≤ x := by linarith [le_max_left a x₀]
  have hx_ge_x₀ : x₀ ≤ x := by linarith [le_max_right a x₀]

  have h_ef_x := hx₀ x hx_ge_x₀
  simp only [Finset.sum_singleton] at h_ef_x hx_neg

  have h_lower := (abs_le.mp h_ef_x).1

  refine ⟨x, hx_ge_a, ?_⟩
  nlinarith [h_lower, hx_neg]

/-- π(x) - li(x) = Ω±(√x / log x) from critical-line zeros plus a truncated
explicit formula input for π. -/
instance [HardyCriticalLineZerosHyp] [TruncatedExplicitFormulaPiHyp] :
    PiLiOscillationSqrtHyp where
  oscillation := by
    have h_zeros := HardyCriticalLineZerosHyp.infinite
    exact ⟨omega_plus_from_zeros h_zeros, omega_minus_from_zeros h_zeros⟩

end PiLiDirectOscillationBridge
