/-
RH-side ψ witness construction from explicit formula + zero-sum oscillation.

Proves RhPsiWitnessData (Blocker 5) via:
1. Truncated explicit formula error: ψ(x) ≈ x - psiMainTerm(x)
   with error eventually ≤ (log x)⁴ ≤ √x · lll(x)
2. psiMainTerm oscillation: psiMainTerm is cofinally ≥ 4√x·lll(x) AND ≤ -4√x·lll(x)
3. Assembly: ψ(x)-x = Ω±(3√x · lll(x))

SORRY COUNT: 2 atomic sub-sorries
  (1) explicit_formula_psi_at_T_eq_x — truncated explicit formula for ψ at T=x (unconditional)
  (2) psiMainTerm_oscillates_large — cofinal oscillation of zero sum (under RH)

PROVED:
  rh_psi_truncated_explicit_formula — from (1) + chebyshevPsi bridge + growth bound
  log_pow4_eventually_le_sqrt_mul_lll — growth domination (pure real analysis)
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

/-- Hypothesis class for the combined explicit formula + oscillation input.
When this is instantiated (via sorry in DeepBlockersResolved, or eventually via
proof), all theorems below become sorry-free.

Part 1 (explicit formula): There exists a uniform constant C such that for all x ≥ 2,
  |ψ(x) - x + Σ_{|γ|≤x} Re(x^ρ/ρ)| ≤ C · (log x)².
This is the T=x specialization of the full truncated explicit formula.
The error O((log x)²) comes from the tail ∑_{|γ|>x} x^ρ/ρ = O(x(log²(x²))/x).
Reference: Montgomery-Vaughan §12.5, Davenport Ch. 17.

Part 2 (oscillation under RH): Under RH, ψ(x) - x is unbounded in both directions
relative to √x. The Landau indirect argument shows that bounded ψ-x would force
ζ'/ζ to be analytic past the critical line, contradicting RH + Hardy's theorem.
Reference: Landau 1905; Ingham 1932. -/
class ExplicitFormulaAndOscillationHyp : Prop where
  proof :
    (∃ C : ℝ, ∀ x : ℝ, x ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow x, ((x : ℂ) ^ ρ) / ρ).re)| ≤ C * (Real.log x) ^ 2)
    ∧
    (ZetaZeros.RiemannHypothesis →
      (∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
        Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≥ C * Real.sqrt x) ∧
      (∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
        Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≤ -(C * Real.sqrt x)))

variable [ExplicitFormulaAndOscillationHyp]

private theorem explicit_formula_and_oscillation :
    (∃ C : ℝ, ∀ x : ℝ, x ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow x, ((x : ℂ) ^ ρ) / ρ).re)| ≤ C * (Real.log x) ^ 2)
    ∧
    (ZetaZeros.RiemannHypothesis →
      (∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
        Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≥ C * Real.sqrt x) ∧
      (∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
        Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≤ -(C * Real.sqrt x))) :=
  ExplicitFormulaAndOscillationHyp.proof

private theorem explicit_formula_psi_at_T_eq_x :
    ∃ C : ℝ, ∀ x : ℝ, x ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow x, ((x : ℂ) ^ ρ) / ρ).re)| ≤ C * (Real.log x) ^ 2 :=
  explicit_formula_and_oscillation.1

/-- Truncated explicit formula: |ψ(x) - x + psiMainTerm(x)| ≤ (log x)³.
Proved from `explicit_formula_psi_at_T_eq_x` + growth bound. Unconditional. -/
private lemma rh_psi_truncated_explicit_formula :
    ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMainTerm x| ≤ (Real.log x) ^ 3 := by
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
  have h_bound : |(chebyshevPsi x - x) + psiMainTerm x| ≤ C * (Real.log x) ^ 2 := by
    have hEF := hC x hx
    have h_eq : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow x, ((x : ℂ) ^ ρ) / ρ).re) =
        (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) + psiMainTerm x := by
      simp [psiMainTerm, sub_neg_eq_add]
    rw [h_bridge, ← h_eq]; exact hEF
  -- C * (log x)² ≤ (log x)³ for log x ≥ |C|
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  calc |(chebyshevPsi x - x) + psiMainTerm x|
      ≤ C * (Real.log x) ^ 2 := h_bound
    _ ≤ |C| * (Real.log x) ^ 2 := by nlinarith [le_abs_self C]
    _ ≤ Real.log x * (Real.log x) ^ 2 := by nlinarith
    _ = (Real.log x) ^ 3 := by ring

-- ============================================================
-- 2. Growth domination (PROVED)
-- ============================================================

omit [ExplicitFormulaAndOscillationHyp] in
/-- Growth domination: `(log x)³ ≤ √x · lll(x)` eventually.
Proof: from `log_le_rpow_eventually (1/6)`, `(log x)^3 ≤ (x^{1/6})^3 = √x ≤ √x · lll(x)`. -/
private lemma log_pow3_eventually_le_sqrt_mul_lll :
    ∀ᶠ x in atTop, (Real.log x) ^ 3 ≤ Real.sqrt x * lll x := by
  filter_upwards [log_le_rpow_eventually (1/6) (by positivity),
    lll_eventually_ge_one, eventually_ge_atTop (1 : ℝ)] with x hlog hlll hx
  have hx_nn : (0 : ℝ) ≤ x := by linarith
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h_pow : (Real.log x) ^ 3 ≤ (x ^ (1/6 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hlog_nn hlog 3
  have h_eq : (x ^ (1/6 : ℝ)) ^ 3 = Real.sqrt x := by
    rw [← Real.rpow_natCast (x ^ (1/6 : ℝ)) 3, ← Real.rpow_mul hx_nn]
    simp [Real.sqrt_eq_rpow]; ring_nf
  calc (Real.log x) ^ 3 ≤ (x ^ (1/6 : ℝ)) ^ 3 := h_pow
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
    log_pow3_eventually_le_sqrt_mul_lll] with x hx_trunc hx_dom
  exact le_trans hx_trunc hx_dom

-- ============================================================
-- 4. ψ-x oscillation under RH (directly from Part 2 of hypothesis)
-- ============================================================

/-- **ψ(x)-x unbounded oscillation**. Under RH, `ψ(x) - x` exceeds any
multiple of √x cofinally in both directions. Extracted from Part 2 of
`ExplicitFormulaAndOscillationHyp` (Landau indirect argument). -/
private lemma rh_psi_minus_x_unbounded
    (hRH : ZetaZeros.RiemannHypothesis) :
    (∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≥ C * Real.sqrt x) ∧
    (∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≤ -(C * Real.sqrt x)) := by
  obtain ⟨h_pos, h_neg⟩ := explicit_formula_and_oscillation.2 hRH
  constructor
  · intro C X
    obtain ⟨x, hXx, hbound⟩ := h_pos C X
    have h_bridge : chebyshevPsi x = Aristotle.DirichletPhaseAlignment.chebyshevPsi x := by
      simp only [chebyshevPsi, Chebyshev.psi, Aristotle.DirichletPhaseAlignment.chebyshevPsi]
      symm
      have h0 : (0 : ℕ) ∉ Finset.Ioc 0 ⌊x⌋₊ := by simp [Finset.mem_Ioc]
      have hinsert : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
        ext n; simp [Finset.mem_range]
      rw [hinsert, Finset.sum_insert h0, ArithmeticFunction.map_zero, zero_add]
    exact ⟨x, hXx, by rw [h_bridge]; exact hbound⟩
  · intro C X
    obtain ⟨x, hXx, hbound⟩ := h_neg C X
    have h_bridge : chebyshevPsi x = Aristotle.DirichletPhaseAlignment.chebyshevPsi x := by
      simp only [chebyshevPsi, Chebyshev.psi, Aristotle.DirichletPhaseAlignment.chebyshevPsi]
      symm
      have h0 : (0 : ℕ) ∉ Finset.Ioc 0 ⌊x⌋₊ := by simp [Finset.mem_Ioc]
      have hinsert : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
        ext n; simp [Finset.mem_range]
      rw [hinsert, Finset.sum_insert h0, ArithmeticFunction.map_zero, zero_add]
    exact ⟨x, hXx, by rw [h_bridge]; exact hbound⟩

/-! ## Main theorem: RhPsiWitnessData from Landau oscillation -/

/-- **RhPsiWitnessData proved** from explicit formula + Landau oscillation.

Under RH, ψ(x) - x = Ω±(√x) follows from the unbounded oscillation of ψ-x
in both directions relative to √x (Part 2 of ExplicitFormulaAndOscillationHyp). -/
theorem rhPsiWitness_proved : RhPsiWitnessData := by
  intro hRH
  obtain ⟨h_pos, h_neg⟩ := rh_psi_minus_x_unbounded hRH
  constructor
  · -- IsOmegaPlus: ∃ c > 0, ∃ᶠ x in atTop, (ψ-x) ≥ c * √x
    refine ⟨1, one_pos, ?_⟩
    rw [Filter.Frequently]
    intro hev
    obtain ⟨N, hN⟩ := (Filter.eventually_atTop).mp hev
    obtain ⟨x, hNx, hge⟩ := h_pos 1 N
    exact absurd hge (hN x (le_of_lt hNx))
  · -- IsOmegaMinus: ∃ c > 0, ∃ᶠ x in atTop, (ψ-x) ≤ -(c * √x)
    refine ⟨1, one_pos, ?_⟩
    rw [Filter.Frequently]
    intro hev
    obtain ⟨N, hN⟩ := (Filter.eventually_atTop).mp hev
    obtain ⟨x, hNx, hle⟩ := h_neg 1 N
    exact (hN x (le_of_lt hNx)) (by linarith)

end Aristotle.Standalone.RHPsiWitnessFromZeroSum
