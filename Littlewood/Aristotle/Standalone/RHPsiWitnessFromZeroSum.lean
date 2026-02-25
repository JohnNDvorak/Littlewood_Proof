/-
RH-side ψ witness construction from explicit formula + zero-sum oscillation.

Proves RhPsiWitnessData (Blocker 5) via:
1. Truncated explicit formula error: under RH, ψ(x) ≈ x - psiMainTerm(x)
   with error eventually ≤ (log x)² ≤ √x · lll(x)
2. psiMainTerm oscillation: psiMainTerm is cofinally ≥ 4√x·lll(x) AND ≤ -4√x·lll(x)
3. Assembly: ψ(x)-x = Ω±(3√x · lll(x))

SORRY COUNT: 2 atomic sub-sorries
  (1) explicit_formula_psi_at_T_eq_x — truncated explicit formula for ψ at T=x (unconditional)
  (2) psiMainTerm_oscillates_large — cofinal oscillation of zero sum (under RH)

PROVED:
  rh_psi_truncated_explicit_formula — from (1) + chebyshevPsi bridge + growth bound
  log_sq_eventually_le_sqrt_mul_lll — growth domination (pure real analysis)
  rh_psi_minus_x_oscillates_large — from above + (2) + growth domination
  rh_psi_explicit_formula_error — from above + growth domination
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
-- 1. Sub-sorry 1: Truncated explicit formula at T=x (standalone)
-- ============================================================

/-- **Truncated explicit formula for ψ at T=x** (analytic input).
There exists a uniform constant C such that for all x ≥ 2:
  |ψ(x) - x + Σ_{|γ|≤x} Re(x^ρ/ρ)| ≤ C · log x.

This is the T=x specialization of the full truncated explicit formula:
  |ψ(x) - x + Σ_{|γ|≤T} Re(x^ρ/ρ)| ≤ C'·(√x·log T/√T + log x)
which at T=x gives error ≤ C'·(log x + log x) = 2C'·log x.
Unconditional (does not require RH). Reference: Montgomery-Vaughan §12.5. -/
private theorem explicit_formula_psi_at_T_eq_x :
    ∃ C : ℝ, ∀ x : ℝ, x ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow x, ((x : ℂ) ^ ρ) / ρ).re)| ≤ C * Real.log x := by
  sorry

/-- Truncated explicit formula: |ψ(x) - x + psiMainTerm(x)| ≤ (log x)².
Proved from `explicit_formula_psi_at_T_eq_x` + growth bound. Unconditional. -/
private lemma rh_psi_truncated_explicit_formula :
    ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMainTerm x| ≤ (Real.log x) ^ 2 := by
  obtain ⟨C, hC⟩ := explicit_formula_psi_at_T_eq_x
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    (Filter.tendsto_atTop.1 Real.tendsto_log_atTop) |C|] with x hx hxlog
  -- Bridge: both chebyshevPsi definitions sum vonMangoldt over {0,..,⌊x⌋}
  have h_bridge : chebyshevPsi x = Aristotle.DirichletPhaseAlignment.chebyshevPsi x := by
    simp only [chebyshevPsi, Chebyshev.psi, Aristotle.DirichletPhaseAlignment.chebyshevPsi]
    symm
    have h0 : (0 : ℕ) ∉ Finset.Ioc 0 ⌊x⌋₊ := by simp [Finset.mem_Ioc]
    have hinsert : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
      ext n; simp [Finset.mem_range]
    rw [hinsert, Finset.sum_insert h0, ArithmeticFunction.map_zero, zero_add]
  -- Transfer explicit formula bound to root chebyshevPsi + psiMainTerm
  have h_bound : |(chebyshevPsi x - x) + psiMainTerm x| ≤ C * Real.log x := by
    have hEF := hC x hx
    have h_eq : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow x, ((x : ℂ) ^ ρ) / ρ).re) =
        (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) + psiMainTerm x := by
      simp [psiMainTerm, sub_neg_eq_add]
    rw [h_bridge, ← h_eq]; exact hEF
  -- C * log x ≤ (log x)² for log x ≥ |C|
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  calc |(chebyshevPsi x - x) + psiMainTerm x|
      ≤ C * Real.log x := h_bound
    _ ≤ |C| * Real.log x := by nlinarith [le_abs_self C]
    _ ≤ Real.log x * Real.log x := by nlinarith
    _ = (Real.log x) ^ 2 := by ring

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
psiMainTerm approximates x - ψ(x) with error ≤ √x · lll(x). Unconditional. -/
theorem rh_psi_explicit_formula_error :
    ∃ psiMain : ℝ → ℝ,
      (∀ᶠ x in atTop,
        |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x) := by
  refine ⟨psiMainTerm, ?_⟩
  filter_upwards [rh_psi_truncated_explicit_formula,
    log_sq_eventually_le_sqrt_mul_lll] with x hx_trunc hx_dom
  exact le_trans hx_trunc hx_dom

-- ============================================================
-- 4. Sub-sorry 2: psiMainTerm oscillation
-- ============================================================

/-- **psiMainTerm oscillates cofinally with amplitude ±4√x·lll(x)** (under RH).

The proof combines two ingredients:
  (a) **Reciprocal norm sum divergence** (unconditional):
      `∑_{ρ ∈ ZerosBelow T} 1/‖ρ‖ → ∞` as T → ∞.
      Follows from Riemann-von Mangoldt `N(T) ~ T log T/(2π)` and
      partial summation: `∑_{0<γ≤T} 1/γ ~ (1/(2π))(log T)²`.
      Reference: Titchmarsh §9.4.

  (b) **Oscillation from unbounded sum** (under RH):
      Under RH, `Re(x^ρ/ρ) = √x · cos(γ log x − arg ρ)/|ρ|`.
      After Dirichlet alignment of K = N(T) zeros, the aligned sum
      is `≥ (1−ε)·√x·∑_{|γ|≤T} 1/|ρ|`. The tower bound from Dirichlet
      (`x ≤ exp((2π/ε)^K)`) keeps `lll(x) = O(log K)`, while the
      aligned sum grows as `(log T)² ≫ lll(x)`.

      Tail control via L²-mean-value or Ingham/Tauberian contradiction.
      Reference: Ingham 1932, Theorem 5; Montgomery-Vaughan §15.2 (Thm 15.11). -/
private lemma psiMainTerm_oscillates_large
    (hRH : ZetaZeros.RiemannHypothesis) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMainTerm x ≥ 4 * (Real.sqrt x * lll x)) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMainTerm x ≤ -(4 * (Real.sqrt x * lll x))) := by
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
    rh_psi_truncated_explicit_formula.and log_sq_eventually_le_sqrt_mul_lll
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
  obtain ⟨psiMain, h_error⟩ := rh_psi_explicit_formula_error
  obtain ⟨h_neg, h_pos⟩ := rh_psi_main_term_oscillates hRH psiMain h_error
  exact ⟨psiMain, h_error, h_neg, h_pos⟩

end Aristotle.Standalone.RHPsiWitnessFromZeroSum
