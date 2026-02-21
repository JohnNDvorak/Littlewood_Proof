/-
RH-side ψ witness construction from explicit formula + zero-sum oscillation.

Proves RhPsiWitnessData (Blocker 5) via:
1. Truncated explicit formula error: under RH, ψ(x) ≈ x - psiMainTerm(x)
   with error eventually ≤ (log x)² ≤ √x · lll(x)
2. psiMainTerm oscillation: psiMainTerm is cofinally ≥ 4√x·lll(x) AND ≤ -4√x·lll(x)
3. Assembly: ψ(x)-x = Ω±(3√x · lll(x))

SORRY COUNT: 2 atomic sub-sorries
  (1) rh_psi_truncated_explicit_formula — truncated explicit formula for ψ under RH
  (2) psiMainTerm_oscillates_large — Dirichlet phase alignment (Littlewood omega)

PROVED:
  log_sq_eventually_le_sqrt_mul_lll — growth domination (pure real analysis)
  rh_psi_minus_x_oscillates_large — from (1) + (2) + growth domination
  rh_psi_explicit_formula_error — from (1) + growth domination
  rh_psi_main_term_oscillates — from rh_psi_minus_x_oscillates_large + error bound

Reference: Littlewood 1914; Montgomery-Vaughan §15.2.

Co-authored-by: Claude (Anthropic), GPT Pro (OpenAI)
-/

import Littlewood.Aristotle.Standalone.CombinedAtomsFromDeepBlockers
import Littlewood.Aristotle.DirichletPhaseAlignment

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.RHPsiWitnessFromZeroSum

open Filter Complex
open GrowthDomination
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.DirichletPhaseAlignment (ZerosBelow)

-- ============================================================
-- 0. Concrete main term definition
-- ============================================================

/-- The explicit-formula main term for ψ, defined as the real part of the
truncated zero sum Σ_{|γ|≤x} x^ρ/ρ. -/
def psiMainTerm (x : ℝ) : ℝ :=
  (∑ ρ ∈ ZerosBelow x, ((x : ℂ) ^ ρ) / ρ).re

-- ============================================================
-- 1. Sub-sorry 1: Truncated explicit formula (O(log²x) error)
-- ============================================================

/-- Truncated explicit formula under RH (analytic input).
Under RH with T = x, the explicit formula gives
  |ψ(x) - x + Σ_{|γ|≤x} Re(x^ρ/ρ)| ≤ (log x)².

This follows from ExplicitFormulaPsiHyp_V3 with T = x:
  error ≤ C·(√x·log x/√x + log x) = 2C·log x ≤ (log x)² eventually. -/
private lemma rh_psi_truncated_explicit_formula
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMainTerm x| ≤ (Real.log x) ^ 2 := by
  sorry

-- ============================================================
-- 2. Growth domination (PROVED)
-- ============================================================

/-- Growth domination: `log²x ≤ √x · lll(x)` eventually.
Proof: from `log_le_rpow_eventually (1/4)`, `(log x)^2 ≤ (x^{1/4})^2 = √x ≤ √x · lll(x)`. -/
private lemma log_sq_eventually_le_sqrt_mul_lll :
    ∀ᶠ x in atTop, (Real.log x) ^ 2 ≤ Real.sqrt x * lll x := by
  filter_upwards [log_le_rpow_eventually (1/4) (by positivity),
    lll_eventually_ge_one, eventually_ge_atTop (1 : ℝ)] with x hlog hlll hx
  have hx_nn : (0 : ℝ) ≤ x := by linarith
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h_sq : (Real.log x) ^ 2 ≤ (x ^ (1/4 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlog_nn hlog 2
  have h_eq : (x ^ (1/4 : ℝ)) ^ 2 = Real.sqrt x := by
    rw [← Real.rpow_natCast (x ^ (1/4 : ℝ)) 2, ← Real.rpow_mul hx_nn]
    simp [Real.sqrt_eq_rpow]; ring_nf
  calc (Real.log x) ^ 2 ≤ (x ^ (1/4 : ℝ)) ^ 2 := h_sq
    _ = Real.sqrt x := h_eq
    _ ≤ Real.sqrt x * lll x := le_mul_of_one_le_right (Real.sqrt_nonneg x) hlll

-- ============================================================
-- 3. Proof of rh_psi_explicit_formula_error (proved from 1 + growth dom)
-- ============================================================

/-- **Explicit formula error bound for ψ**.
Under RH, psiMainTerm approximates x - ψ(x) with error ≤ √x · lll(x). -/
theorem rh_psi_explicit_formula_error
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ psiMain : ℝ → ℝ,
      (∀ᶠ x in atTop,
        |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x) := by
  refine ⟨psiMainTerm, ?_⟩
  filter_upwards [rh_psi_truncated_explicit_formula hRH,
    log_sq_eventually_le_sqrt_mul_lll] with x hx_trunc hx_dom
  exact le_trans hx_trunc hx_dom

-- ============================================================
-- 4. Sub-sorry 2: psiMainTerm oscillation (Dirichlet phase alignment)
-- ============================================================

/-- The zero-sum main term Σ Re(x^ρ/ρ) oscillates cofinally with amplitude
±4√x·lll(x). This follows from Dirichlet simultaneous approximation on
zero phases (`exists_large_x_phases_aligned_finset`) combined with the
lower bound `bound_real_part_of_sum_aligned` and the divergence of
Σ Re(1/ρ) (`HardyCriticalLineZerosHyp_V3.sum_re_inv_rho_diverges`).
The constant 4 provides margin for absorbing the O(log²x) error. -/
private lemma psiMainTerm_oscillates_large
    (hRH : ZetaZeros.RiemannHypothesis) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMainTerm x ≥ 4 * (Real.sqrt x * lll x)) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMainTerm x ≤ -(4 * (Real.sqrt x * lll x))) := by
  -- Dirichlet phase alignment on zeros in the explicit formula.
  sorry

-- ============================================================
-- 5. Proof of rh_psi_minus_x_oscillates_large (PROVED from 1+4+growth dom)
-- ============================================================

/-- **ψ(x)-x oscillation**. Under RH, `ψ(x) - x` has cofinal oscillations
of size Ω±(3√x · lll(x)). Proved by combining:
  (1) truncated explicit formula error O(log²x) from sub-sorry 1,
  (2) psiMainTerm oscillation ±4√x·lll(x) from sub-sorry 2,
  (3) growth domination log²x ≤ √x·lll(x). -/
private lemma rh_psi_minus_x_oscillates_large
    (hRH : ZetaZeros.RiemannHypothesis) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (chebyshevPsi x - x) ≤ -(3 * (Real.sqrt x * lll x))) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      3 * (Real.sqrt x * lll x) ≤ (chebyshevPsi x - x)) := by
  -- Combine error bound and growth domination into single eventually
  have hE : ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMainTerm x| ≤ (Real.log x) ^ 2 ∧
        (Real.log x) ^ 2 ≤ Real.sqrt x * lll x :=
    (rh_psi_truncated_explicit_formula hRH).and log_sq_eventually_le_sqrt_mul_lll
  rcases (Filter.eventually_atTop.1 hE) with ⟨X0, hX0⟩
  -- Main term oscillation
  rcases psiMainTerm_oscillates_large hRH with ⟨h_main_pos, h_main_neg⟩
  constructor
  · -- Large positive psiMainTerm ⇒ large negative ψ(x)-x
    intro X
    rcases h_main_pos (max X X0) with ⟨z, hYz, hz_main⟩
    have hzX : X < z := lt_of_le_of_lt (le_max_left _ _) hYz
    have hzX0 : X0 ≤ z := le_trans (le_max_right _ _) (le_of_lt hYz)
    obtain ⟨h_err_z, h_log_z⟩ := hX0 z hzX0
    have h_upper : (chebyshevPsi z - z) + psiMainTerm z ≤ (Real.log z) ^ 2 :=
      (abs_le.mp h_err_z).2
    exact ⟨z, hzX, by nlinarith⟩
  · -- Large negative psiMainTerm ⇒ large positive ψ(x)-x
    intro X
    rcases h_main_neg (max X X0) with ⟨z, hYz, hz_main⟩
    have hzX : X < z := lt_of_le_of_lt (le_max_left _ _) hYz
    have hzX0 : X0 ≤ z := le_trans (le_max_right _ _) (le_of_lt hYz)
    obtain ⟨h_err_z, h_log_z⟩ := hX0 z hzX0
    have h_lower : -((Real.log z) ^ 2) ≤ (chebyshevPsi z - z) + psiMainTerm z :=
      (abs_le.mp h_err_z).1
    exact ⟨z, hzX, by nlinarith⟩

-- ============================================================
-- 6. Proof of rh_psi_main_term_oscillates (unchanged)
-- ============================================================

/-- **psiMain oscillation**.
Under RH, any function approximating x - ψ(x) with error ≤ √x·lll(x)
must oscillate between ±2√x·lll(x) cofinally. -/
theorem rh_psi_main_term_oscillates
    (hRH : ZetaZeros.RiemannHypothesis)
    (psiMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMain x ≤ -(2 * (Real.sqrt x * lll x))) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x * lll x) ≤ psiMain x) := by
  -- Extract a concrete threshold beyond which the error bound holds.
  rcases (Filter.eventually_atTop.1 h_error) with ⟨B, hB⟩
  -- Deep oscillation input for `ψ(x) - x`.
  rcases rh_psi_minus_x_oscillates_large hRH with ⟨h_osc_neg, h_osc_pos⟩
  constructor
  · intro X
    -- Large positive ψ(x)-x ⇒ large negative psiMain.
    rcases h_osc_pos (max X B) with ⟨x, hx_gt, hx_pos⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx_gt
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    have h_err_x :
        |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x := hB x hBx
    set A : ℝ := Real.sqrt x * lll x with hA
    have h_upper : (chebyshevPsi x - x) + psiMain x ≤ A :=
      (abs_le.mp h_err_x).2
    refine ⟨x, hXx, ?_⟩
    nlinarith
  · intro X
    -- Large negative ψ(x)-x ⇒ large positive psiMain.
    rcases h_osc_neg (max X B) with ⟨x, hx_gt, hx_neg⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx_gt
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx_gt)
    have h_err_x :
        |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x := hB x hBx
    set A : ℝ := Real.sqrt x * lll x with hA
    have h_lower : -A ≤ (chebyshevPsi x - x) + psiMain x :=
      (abs_le.mp h_err_x).1
    refine ⟨x, hXx, ?_⟩
    nlinarith

/-! ## Main theorem: RhPsiWitnessData from the two sub-results -/

/-- **RhPsiWitnessData proved** from explicit formula + oscillation.

The proof:
1. From rh_psi_explicit_formula_error: get psiMain with error bound
2. From rh_psi_main_term_oscillates: get cofinal negative AND positive oscillation
3. Combine into the witness triple -/
theorem rhPsiWitness_proved : RhPsiWitnessData := by
  intro hRH
  obtain ⟨psiMain, h_error⟩ := rh_psi_explicit_formula_error hRH
  obtain ⟨h_neg, h_pos⟩ := rh_psi_main_term_oscillates hRH psiMain h_error
  exact ⟨psiMain, h_error, h_neg, h_pos⟩

end Aristotle.Standalone.RHPsiWitnessFromZeroSum
