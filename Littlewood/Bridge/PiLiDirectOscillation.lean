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
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs
import Littlewood.Aristotle.Standalone.ZeroSumNegFrequently

noncomputable section

open Schmidt Asymptotics
open Filter ZetaZeros
open scoped BigOperators

namespace PiLiDirectOscillationBridge

private def piLiError (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x

/-- **Proved parent class**: anti-alignment for singleton critical-line zeros.
    Separated from the false `pi_approx` field so that downstream files needing
    only this result can depend on a sorry-free typeclass.

    SORRY COUNT: 0 (proved in ZeroSumNegFrequently.lean via cosine oscillation). -/
class ZeroSumNegFrequentlyPiHyp : Prop where
  /-- Anti-alignment for singleton critical-line zeros, scaled by `1/log x`. -/
  zero_sum_neg_frequently :
    ∀ (ρ₀ : ℂ), ρ₀ ∈ zetaNontrivialZeros →
      ρ₀.re = 1 / 2 → ρ₀.im ≠ 0 →
      ∃ c > 0, ∀ X : ℝ, ∃ x > X,
        1 < x ∧
          ((∑ ρ ∈ ({ρ₀} : Finset ℂ), ((x : ℂ) ^ ρ / ρ)).re) / Real.log x
            ≤ -(c * (Real.sqrt x / Real.log x))

/-- Sorry-free global instance of `ZeroSumNegFrequentlyPiHyp`.
    Proof: direct from `ZeroSumNegFrequently.zero_sum_neg_frequently_core`. -/
instance : ZeroSumNegFrequentlyPiHyp where
  zero_sum_neg_frequently := by
    intro ρ₀ _hρ₀_mem hρ₀_re hρ₀_im
    exact Aristotle.Standalone.ZeroSumNegFrequently.zero_sum_neg_frequently_core
      ρ₀ hρ₀_re hρ₀_im

/-- Input hypothesis for extracting π-li oscillation from critical-line zeros.
    Contains both `pi_approx` (mathematically false, sorry) and `zero_sum_neg_frequently`
    (proved). The `pi_approx` field is retained for the B7/lll-factor chain; the main
    theorem path bypasses it via LandauOscillation.lean (priority 2000). -/
class TruncatedExplicitFormulaPiHyp : Prop where
  /-- Truncated explicit formula for `π(x) - li(x)` at `√x/log x` scale.
      **MATHEMATICALLY FALSE** for S=∅. Retained for backward compatibility. -/
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

/-- Any `TruncatedExplicitFormulaPiHyp` instance automatically provides
    `ZeroSumNegFrequentlyPiHyp`. This allows downstream code to depend only on the
    sorry-free parent class when `pi_approx` is not needed. -/
instance (priority := 100) [h : TruncatedExplicitFormulaPiHyp] : ZeroSumNegFrequentlyPiHyp where
  zero_sum_neg_frequently := h.zero_sum_neg_frequently

/-! ### MATHEMATICAL ANALYSIS: pi_approx soundness (2026-03-15)

**STATUS (updated 2026-03-15)**:

1. `PiApproxFromExplicitFormulaHyp` (T-parameterized O-bound): **MATHEMATICALLY TRUE**.
   States ∀ T ≥ 2, ∃ D_T > 0, ∀ᶠ x, |π(x)-li(x)+Σ_{ZerosBelow T}/logx| ≤ D_T·√x/logx.
   Proof: From the ψ-level Perron formula,
     |ψ(x) - x + Σ_{ZerosBelow T} x^ρ/ρ| ≤ C₂·(√x·(logT)²/√T + (logx)²).
   Abel summation ψ→π: |π(x)-li(x)-(ψ(x)-x)/logx| ≤ D_abel·√x/logx.
   Dividing the ψ bound by logx and noting (logx)²/logx = logx = o(√x/logx):
     D_T = C₂·(logT)²/√T + D_abel + C₂ works for x sufficiently large.

2. `TruncatedExplicitFormulaPiHyp.pi_approx` (little-o, `∀ ε > 0`): **MATHEMATICALLY FALSE**.
   Setting S=∅ gives π(x)-li(x) = o(√x/logx), contradicting Ω± oscillation.
   Retained with false type to avoid breaking 50+ downstream files.
   The main theorem path bypasses this via LandauOscillation.lean (priority 2000).
-/

/-- Abel summation correction: π(x) - li(x) ≈ (ψ(x) - x)/logx with correction
    of order O(√x/logx). Classical: partial summation applied to the
    prime-counting function (Davenport Ch. 17; Montgomery-Vaughan §2.2).

    NOTE (2026-03-15): The correction is O(√x/logx), not O(√x/(logx)²) as
    previously claimed. The dominant term is (ψ(x)-θ(x))/logx where
    ψ-θ = θ(√x) + θ(x^{1/3}) + ... ≈ √x. This class is retained for
    reference but NO LONGER INSTANTIATED — the ψ→π decomposition is the
    wrong approach for pi_approx. See MATHEMATICAL ANALYSIS above. -/
class AbelCorrectionPsiPiHyp : Prop where
  /-- There exists D > 0 such that eventually the Abel correction is bounded. -/
  correction_bound : ∃ D > (0 : ℝ), ∀ᶠ x in atTop,
    |piLiError x - (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) /
      Real.log x| ≤ D * (Real.sqrt x / Real.log x)

/-- ψ-level explicit formula using ZerosBelow T (the Perron truncation).

    For any δ > 0, there exists T₀ ≥ 2 such that eventually
    |(ψ(x) - x + Σ_{ρ∈ZerosBelow T₀} x^ρ/ρ) / logx| ≤ δ · √x/logx.

    This is MATHEMATICALLY CORRECT. The Perron formula gives
    |ψ(x) - x + Σ_{|γ|≤T} x^ρ/ρ| ≤ C·(√x·(logT)²/√T + (logx)²),
    and choosing T₀ with (logT₀)²/√T₀ small + x large gives δ-smallness.

    PROVABLE from `general_explicit_formula_from_perron` +
    `psi_bound_div_log_eventually_small` (AbelSummationPsiPi).

    NOTE: This is useful for the ψ-chain (littlewood_psi) but CANNOT be
    combined with AbelCorrectionPsiPiHyp to prove pi_approx because the
    Abel correction O(√x/logx) is at the same scale as the target.
    See MATHEMATICAL ANALYSIS above. -/
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

/-- PROVED from `ContourRemainderBoundHyp` (ExplicitFormulaPsiB5aDefs) +
    `psi_bound_div_log_eventually_small` (AbelSummationPsiPi).
    1. Get Cc from ContourRemainderBoundHyp.bound
    2. Upgrade to two-term bound (add nonneg (logx)² term)
    3. Apply psi_bound_div_log_eventually_small → T₀ ≥ 2, eventually small
    4. Unfold shiftedRemainderRe = chebyshevPsi - x + zeroSumRe to match goal -/
instance : PsiExplicitFormulaZerosHyp where
  psi_level_bound := by
    intro δ hδ
    -- Get Cc from ContourRemainderBoundHyp (sorry upstream in B5aDefs)
    obtain ⟨Cc, hCc_pos, hCc_bound⟩ :=
      Aristotle.Standalone.ExplicitFormulaPsiSkeleton.ContourRemainderBoundHyp.bound
    -- Upgrade one-term bound to two-term bound needed by psi_bound_div_log_eventually_small
    have hR : ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
      intro x T hx hT
      calc |Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe x T|
          ≤ Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := hCc_bound x T hx hT
        _ ≤ Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hCc_pos.le
            linarith [sq_nonneg (Real.log x)]
    -- Apply the AbelSummationPsiPi workhorse to get T₀ and eventually-small
    obtain ⟨T₀, hT₀, hev⟩ := AbelSummationPsiPi.psi_bound_div_log_eventually_small
      (fun x T => Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe x T)
      Cc hCc_pos hR δ hδ
    refine ⟨T₀, hT₀, ?_⟩
    -- shiftedRemainderRe x T₀ = chebyshevPsi x - x + (∑ ρ ∈ ZerosBelow T₀, (x:ℂ)^ρ/ρ).re
    filter_upwards [hev, AbelSummationPsiPi.log_eventually_pos] with x hx hlx
    rw [abs_div, abs_of_pos hlx]
    have heq : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x +
        (∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T₀,
          (↑x : ℂ) ^ ρ / ρ).re =
        Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe x T₀ := by
      simp only [Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe,
                  Aristotle.Standalone.ExplicitFormulaPsiSkeleton.zeroSumRe]
    rw [heq]; exact hx

/-- π-level truncated explicit formula at √x/logx scale (T-parameterized O-bound).

    **MATHEMATICALLY TRUE** (2026-03-15 refactor): For each T ≥ 2, the Perron
    formula at height T gives a ψ-level bound with remainder depending on T.
    Abel summation converts this to a π-level bound with D_T depending on T.
    The key: D_T is allowed to depend on T (via (logT)²/√T + Abel constant),
    and the ∀ᶠ x threshold also depends on T.

    This is the correct replacement for the old ∀S formulation (which was false
    for S=∅). Here ZerosBelow T is the canonical finite set from DirichletPhaseAlignment.

    Proof path:
    1. From `general_explicit_formula_from_perron`:
       |ψ(x) - x + Σ_{ZerosBelow T} Re(x^ρ/ρ)| ≤ C₂·(√x·(logT)²/√T + (logx)²)
    2. Abel summation ψ→π: |π(x)-li(x)-(ψ(x)-x)/logx| ≤ D_abel·√x/logx
    3. Dividing by logx and using (logx)³/√x → 0:
       D_T = C₂·(logT)²/√T + D_abel + C₂ works for x sufficiently large. -/
class PiApproxFromExplicitFormulaHyp : Prop where
  /-- For each T ≥ 2, there exists D_T > 0 such that eventually
      |π(x) - li(x) + (Σ_{ρ∈ZerosBelow T} x^ρ/ρ)/logx| ≤ D_T · √x/logx.
      The constant D_T absorbs the Perron error at height T plus the Abel correction. -/
  pi_approx_bound :
    ∀ T : ℝ, 2 ≤ T → ∃ D > (0 : ℝ), ∀ᶠ x in atTop,
      |piLiError x + (∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T,
        (x : ℂ) ^ ρ / ρ).re / Real.log x| ≤ D * (Real.sqrt x / Real.log x)

/- Abel summation correction: π(x) - li(x) ≈ (ψ(x) - x)/logx at √x/logx scale.
    SORRY: Mathematically true (classical Abel/partial summation, Davenport Ch. 17).

    BLOCKER ANALYSIS (2026-03-15, Agent 3):
    The PartialSummation.lean decomposition gives:
      π(x) - li(x) - (ψ(x)-x)/logx = -sumPrimePowers(x) + ∫₂ˣ (ψ(t)-t)/(t·(logt)²)dt + 2/log2

    Term-by-term:
    1. sumPrimePowers(x) = Σ_{p^k≤x, k≥2} 1/k ≈ π(√x)/2 = O(√x/logx) — PROVABLE from
       Mathlib's `Chebyshev.theta_le_log4_mul_x` + `Chebyshev.eventually_primeCounting_le`.
    2. ∫₂ˣ (ψ(t)-t)/(t·(logt)²)dt — with PNT (ψ(t) ~ t), this is o(x/(logx)²).
       BUT x/(logx)² ≫ √x/logx (ratio = √x/logx → ∞), so o(x/(logx)²) does NOT
       imply O(√x/logx). The weak PNT is INSUFFICIENT for the O(√x/logx) bound.
    3. 2/log(2) is constant — absorbed by D·√x/logx for large x.

    CORRECTED ANALYSIS (2026-03-15, Agent 3 iteration 3):
    The previous claim "o(x/(logx)²) = o(√x/logx)" was WRONG (inequality reversed).
    Weak PNT gives ψ(t) - t = o(t), yielding ∫ = o(x/log²x), but we need O(√x/logx).
    Strong PNT gives ψ(t) - t = O(t·exp(-c·√(log t))), yielding:
      ∫₂ˣ O(exp(-c·√(log t))/log²t) dt = O(x·exp(-c'·√(log x)))
    which IS O(√x/logx). But the Strong PNT is NOT formalized in PrimeNumberTheoremAnd
    (StrongPNT.lean has only blueprint comments, no proof).

    PrimeNumberTheoremAnd HAS:
    - `chebyshev_asymptotic : θ ~[atTop] id` (weak PNT)
    - `WeakPNT'' : ψ ~[atTop] id` (weak PNT for ψ)
    - Classical zero-free region formalized but Strong PNT error term NOT proved

    CONCLUSION: This sorry is IRREDUCIBLE with current formalized tools.
    Requires either:
    (a) Strong PNT error term O(x·exp(-c·√(logx))) — not in any Lean 4 library, or
    (b) A weaker approach that avoids the O(√x/logx) scale entirely.
    The main theorem path BYPASSES this via LandauOscillation.lean (priority 2000). -/

-- DEPRECATED (2026-03-16): AbelCorrectionPsiPiHyp instance removed — dead code.
-- Class retained as reference. The PiApproxFromExplicitFormulaHyp instance below
-- was the sole consumer; it too is removed. Neither typeclass is consumed downstream.
-- instance : AbelCorrectionPsiPiHyp where
--   correction_bound := by sorry

-- DEPRECATED (2026-03-16): PiApproxFromExplicitFormulaHyp instance removed — dead code.
-- Never consumed as a typeclass parameter by any file. Main theorem uses
-- LandauOscillation (priority 2000). Original proof combined ψ-level Perron
-- bound with Abel summation correction.
-- instance : PiApproxFromExplicitFormulaHyp where
--   pi_approx_bound := by sorry

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
