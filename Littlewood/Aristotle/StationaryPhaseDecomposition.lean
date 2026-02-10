/-
Stationary phase decomposition for Hardy cosine integrals.

KEY RESULT:
  hardy_cos_integral_alternating_sqrt_decomposition :
    ∃ A B, B > 0 ∧ ∀ T ≥ 2, ∃ err,
      (weighted integral = A·(-1)^n·√(n+1) + err(n)) ∧ (|err(n)| ≤ B)

This directly provides HardyCosIntegralAlternatingSqrtDecompositionHyp,
closing the sorry at CriticalAssumptions.lean.

PROOF STRUCTURE:
1. hardy_cos_integral_alternating_linear_bound (SORRY): The n-th mode integral
   satisfies ∫ cos(φ_n) = c·(-1)^n·(n+1) + O(1). This is the SINGLE atomic sorry.
   It encapsulates stationary phase evaluation + VdC tail bound + θ'(t) asymptotics.

2. hardy_cos_integral_alternating_sqrt_decomposition (PROVED from 1):
   Weighting by (n+1)^{-1/2} transforms the linear decomposition into the
   required √(n+1) decomposition with bounded error.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Bridge.HardyFirstMomentWiring

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace StationaryPhaseDecomposition

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-! ## Atomic sorry: oscillatory integral with alternating sign -/

/-- **Atomic sorry**: The n-th Hardy cosine integral decomposes as
c·(-1)^n·(n+1) + err with |err| bounded uniformly in n and T.

MATHEMATICAL PROOF SKETCH:
1. The phase φ_n(t) = θ(t) - t·log(n+1) has stationary point at
   t₀ = 2π(n+1)² where φ'(t₀) = θ'(t₀) - log(n+1) ≈ 0.

2. Split: [t₀, t₀ + c(n+1)] ∪ [t₀ + c(n+1), T].

3. Near-stationary region [t₀, t₀ + c(n+1)]:
   Stationary phase / Fresnel evaluation gives
     ∫ cos(φ_n) = c₁·(n+1)·cos(φ_n(t₀) + π/4) + O(1)
   Phase value: cos(φ_n(t₀)) involves (-1)^n via cos(π(n+1)²) = (-1)^n.

4. Tail [t₀ + c(n+1), T]: VdC first derivative test with
   φ'(t) ≥ c₂/(n+1) gives |∫_tail| ≤ 3(n+1)/c₂ = O(n+1).
   Or: split further at 2t₀ where φ'(t) ≥ (1/2)log 2, giving |∫| = O(1).

5. Combined: ∫ = c₁(n+1)(-1)^n + O(1).

REFERENCES:
  - Titchmarsh, "Theory of the Riemann Zeta Function", §7.6
  - θ'(t) asymptotics from ThetaDerivAsymptotic (via DigammaAsymptotic)
  - Van der Corput first derivative test from VdcFirstDerivTest
  - cos(πn²) = (-1)^n from CosPiSqSign -/
theorem hardy_cos_integral_alternating_linear_bound :
    ∃ c₀ B₀ : ℝ, B₀ > 0 ∧ ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 → n < hardyN T →
      |(∫ t in Ioc (hardyStart n) T, hardyCos n t)
        - c₀ * ((-1 : ℝ) ^ n * ((n : ℝ) + 1))| ≤ B₀ := by
  sorry

/-! ## Auxiliary rpow lemmas -/

/-- (n+1)^{-1/2} * √(n+1) = 1. -/
private lemma rpow_neg_half_mul_sqrt (n : ℕ) :
    ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * Real.sqrt (n + 1) = 1 := by
  have h_pos : (0 : ℝ) < n + 1 := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add h_pos]
  norm_num

/-- (n+1)^{-1/2} * (n+1) = √(n+1). -/
private lemma rpow_neg_half_mul_self (n : ℕ) :
    ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * ((n : ℝ) + 1) = Real.sqrt (n + 1) := by
  have h_pos : (0 : ℝ) < n + 1 := by positivity
  rw [Real.sqrt_eq_rpow]
  calc ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * ((n : ℝ) + 1)
      = ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * ((n + 1 : ℝ) ^ (1 : ℝ)) := by
        congr 1; exact (Real.rpow_one _).symm
    _ = (n + 1 : ℝ) ^ (-(1/2) + 1 : ℝ) := (Real.rpow_add h_pos _ _).symm
    _ = (n + 1 : ℝ) ^ (1/2 : ℝ) := by norm_num

/-! ## The main decomposition theorem -/

/-- **Main theorem**: The Hardy cosine integral alternating sqrt decomposition.

Each mode's weighted integral decomposes as A·(-1)^n·√(n+1) + err(n) with
|err(n)| ≤ B uniformly in n and T.

PROVED from hardy_cos_integral_alternating_linear_bound. -/
theorem hardy_cos_integral_alternating_sqrt_decomposition :
    ∃ A B : ℝ, B > 0 ∧ ∀ T : ℝ, T ≥ 2 →
      ∃ err : ℕ → ℝ,
        (∀ n : ℕ, n < hardyN T →
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (hardyStart n) T,
              hardyCos n t
            = A * ((-1 : ℝ) ^ n * Real.sqrt (n + 1)) + err n) ∧
        (∀ n : ℕ, n < hardyN T → |err n| ≤ B) := by
  obtain ⟨c₀, B₀, hB₀, hbound⟩ := hardy_cos_integral_alternating_linear_bound
  -- Set A = c₀, B = B₀
  refine ⟨c₀, B₀, hB₀, ?_⟩
  intro T hT
  -- Define I(n) = ∫ hardyCos n and err(n) = weighted - main term
  set I : ℕ → ℝ := fun n => ∫ t in Ioc (hardyStart n) T, hardyCos n t
  refine ⟨fun n => ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * I n -
    c₀ * ((-1 : ℝ) ^ n * Real.sqrt (n + 1)), ?_, ?_⟩
  · -- Decomposition: weighted = A·(-1)^n·√(n+1) + err
    intro n _hn; ring
  · -- Error bound: |err(n)| ≤ B₀
    intro n hn
    show |((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * I n -
        c₀ * ((-1 : ℝ) ^ n * Real.sqrt (n + 1))| ≤ B₀
    have h_pos : (0 : ℝ) < n + 1 := by positivity
    have h_coef_pos : 0 < ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) := by positivity
    set w : ℝ := ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)))
    -- Factor out w
    have h_ws : w * ((n : ℝ) + 1) = Real.sqrt (n + 1) := rpow_neg_half_mul_self n
    have h_factor : w * I n - c₀ * ((-1 : ℝ) ^ n * Real.sqrt (n + 1)) =
        w * (I n - c₀ * ((-1 : ℝ) ^ n * ((n : ℝ) + 1))) := by
      rw [mul_sub, ← h_ws]; ring
    rw [h_factor, abs_mul]
    -- |w| ≤ 1
    have h_w_le : |w| ≤ 1 := by
      rw [abs_of_pos h_coef_pos]
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (by norm_num)
    -- Inner bound from the sorry
    have h_inner : |I n - c₀ * ((-1 : ℝ) ^ n * ((n : ℝ) + 1))| ≤ B₀ :=
      hbound n T hT hn
    calc |w| * |I n - c₀ * ((-1 : ℝ) ^ n * ((n : ℝ) + 1))|
        ≤ 1 * B₀ := mul_le_mul h_w_le h_inner (abs_nonneg _) (by norm_num)
      _ = B₀ := by ring

end StationaryPhaseDecomposition

/-! ## Typeclass wiring -/

/-- Wire the proved decomposition theorem into the typeclass instance.
This provides `HardyCosIntegralAlternatingSqrtDecompositionHyp`, which
auto-wires to `MainTermFirstMomentBoundHyp` via HardyFirstMomentWiring. -/
instance : HardyFirstMomentWiring.HardyCosIntegralAlternatingSqrtDecompositionHyp :=
  ⟨StationaryPhaseDecomposition.hardy_cos_integral_alternating_sqrt_decomposition⟩
