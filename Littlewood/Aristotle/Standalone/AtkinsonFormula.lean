/-
Atkinson formula infrastructure for the MainTerm first moment bound.

Provides `mainTerm_first_moment_sqrt`:
  ∃ C_M > 0, ∀ T ≥ 2, |∫₁ᵀ MainTerm(t) dt| ≤ C_M · T^{1/2}

The proof reduces to `atkinson_integral_le_N`: the Atkinson per-mode
IBP + signed Fresnel sum analysis shows |∫ MainTerm| ≤ C · (N+1),
where N = hardyN(T) ≤ √T.

SORRY COUNT: 1 (`atkinson_weighted_sum_bound`)
  The weighted cosine integral sum bound:
  |Σ_{n<N} (n+1)^{-1/2} · ∫ cos(θ(t) - t·log(n+1))| ≤ C · (N+1)

  PROOF STATUS (Agent analysis 2026-03-16):
  The proof splits into DIAGONAL (resonant block) + OFF-DIAGONAL (tail).

  DIAGONAL — INFRASTRUCTURE COMPLETE:
  - `hardyCos_firstBlock_anchor_main_term_eventually` (StationaryPhaseMainMode):
    w_n · J_n = completeModeTarget(n) + O(1) for the complete first block.
  - `completeModeTarget_sum_bound_range` (StationaryPhaseDecomposition):
    |Σ completeModeTarget| = O(√N) via Abel alternating cancellation.
  - Total diagonal: O(N).

  OFF-DIAGONAL TAILS — GAP:
  - VdC first derivative gives |tail of mode n| = O(n+1), so weighted
    tail is O(√(n+1)), summing to O(N^{3/2}). This is INSUFFICIENT.
  - The TRUE per-mode tail is O(√(n+1)) (not O(n+1)), giving O(1)
    after weighting and O(N) sum. This requires Fresnel evaluation
    precision (stationary phase remainder estimate R_n = O(√(n+1))).
  - NEEDED: Quantitative θ(t) expansion to cubic order near the
    stationary point t₀ = 2π(n+1)², showing the Fresnel tail
    contribution is bounded uniformly after weighting.

  NOTE: `HardyCosIntegralSqrtModeBoundHyp` (|I_n| ≤ B·√(n+1))
  is FALSE — the Fresnel main term gives I_n = Θ(n+1). The O(N) result
  requires signed cancellation on the main terms, NOT absolute bounding.

Reference: Atkinson 1949, Acta Math. 81; Titchmarsh 1951 §4.15.
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.ThetaDerivAsymptotic
import Littlewood.Aristotle.ThetaDerivMonotone
import Littlewood.Aristotle.CosPiSqSign

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Filter Topology
open HardyEstimatesPartial

namespace Aristotle.Standalone.AtkinsonFormula

/-! ## Section 1: hardyN bound -/

/-- hardyN(T) + 1 ≤ 2√T for T ≥ 1. -/
private theorem hardyN_add_one_le (T : ℝ) (hT : T ≥ 1) :
    (↑(hardyN T) : ℝ) + 1 ≤ 2 * Real.sqrt T := by
  have hN : (↑(hardyN T) : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have h1 : Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T :=
    Real.sqrt_le_sqrt (div_le_self (by linarith) (by linarith [Real.pi_gt_three]))
  have h2 : (1 : ℝ) ≤ Real.sqrt T := by
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
  linarith

/-! ## Section 2: Abel bound for alternating series with increasing terms -/

/-- For an increasing nonneg sequence, |Σ_{n<N} (-1)^n a_n| ≤ a_{N-1}. -/
theorem abel_alternating_bound (a : ℕ → ℝ) (ha_nn : ∀ n, 0 ≤ a n)
    (ha_mono : Monotone a) (N : ℕ) (hN : 0 < N) :
    |∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * a n| ≤ a (N - 1) := by
  set S := fun N => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * a n with hS_def
  suffices h_refined : ∀ N : ℕ, 0 < N →
    (Even N → S N ≤ 0 ∧ -(a (N - 1)) ≤ S N) ∧
    (Odd N → 0 ≤ S N ∧ S N ≤ a (N - 1)) by
    obtain ⟨h_even, h_odd⟩ := h_refined N hN
    rcases Nat.even_or_odd N with hpar | hpar
    · obtain ⟨h1, h2⟩ := h_even hpar
      rw [abs_le]; exact ⟨h2, le_trans h1 (ha_nn _)⟩
    · obtain ⟨h1, h2⟩ := h_odd hpar
      rw [abs_le]; exact ⟨le_trans (neg_nonpos_of_nonneg (ha_nn _)) h1, h2⟩
  intro M hM
  induction M with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk; constructor
      · intro h; exact absurd h (by decide)
      · intro _; simp [hS_def, ha_nn 0]
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      obtain ⟨ih_even, ih_odd⟩ := ih hk_pos
      simp only [hS_def] at ih_even ih_odd ⊢
      rw [Finset.sum_range_succ]
      constructor
      · intro hpar
        have hk_odd : Odd k := by rw [Nat.odd_iff]; rw [Nat.even_iff] at hpar; omega
        obtain ⟨hSk_nn, hSk_upper⟩ := ih_odd hk_odd
        have hpow : (-1 : ℝ) ^ k * a k = -(a k) := by rw [Odd.neg_one_pow hk_odd]; ring
        rw [hpow]
        show S k + -(a k) ≤ 0 ∧ -(a ((k + 1) - 1)) ≤ S k + -(a k)
        simp only [Nat.add_sub_cancel]
        have hmk : a (k - 1) ≤ a k := ha_mono (Nat.sub_le k 1)
        constructor <;> linarith
      · intro hpar
        have hk_even : Even k := by rw [Nat.even_iff]; rw [Nat.odd_iff] at hpar; omega
        obtain ⟨hSk_upper, hSk_lower⟩ := ih_even hk_even
        have hpow : (-1 : ℝ) ^ k * a k = a k := by rw [Even.neg_one_pow hk_even]; ring
        rw [hpow]
        show 0 ≤ S k + a k ∧ S k + a k ≤ a ((k + 1) - 1)
        simp only [Nat.add_sub_cancel]
        have hmk : a (k - 1) ≤ a k := ha_mono (Nat.sub_le k 1)
        constructor <;> linarith

/-! ## Section 3: Atkinson weighted sum bound

The deep analytical content: the weighted sum of per-mode cosine integrals
satisfies a signed cancellation bound.

|Σ_{n<N} (n+1)^{-1/2} · ∫_{hardyStart(n)}^T cos(θ(t) - t·log(n+1)) dt|
≤ C · (N + 1)

PROOF STRUCTURE (Atkinson 1949):
1. Fubini: ∫ MainTerm = 2 Σ (n+1)^{-1/2} ∫ cos(φ_n) — PROVED (hardySum_integral_eq)
2. Per-mode stationary phase evaluation:
   I_n = (-1)^{n+1} · c₀ · (n+1) + R_n, |R_n| ≤ C_rem · √(n+1)
   — Uses Stirling for θ at 2π(n+1)² + Fresnel evaluation + VdC tail
   — cos(π(n+1)²) = (-1)^{n+1} PROVED in CosPiSqSign
3. After weighting by (n+1)^{-1/2}:
   (n+1)^{-1/2} · I_n = (-1)^{n+1} · c₀ · √(n+1) + r_n, |r_n| ≤ C_rem
4. Signed sum: |Σ (-1)^{n+1} c₀ √(n+1)| ≤ c₀·√N — Abel bound (PROVED)
5. Remainder sum: |Σ r_n| ≤ C_rem·N — triangle inequality
6. Assembly: c₀·√N + C_rem·N ≤ (c₀+C_rem)·(N+1)

NOTE: A previous version had `per_mode_weighted_bound` claiming
(n+1)^{-1/2} · |I_n| ≤ B uniformly. This is FALSE: the Fresnel integral
at the stationary point t₀ = 2π(n+1)² gives I_n = Θ(n+1), so the
weighted ABSOLUTE value is Θ(√(n+1)), not O(1). The correct bound
requires signed cancellation across modes (Atkinson's key insight).
-/

/-- **Atkinson weighted sum bound**: the weighted sum of per-mode cosine
    integrals satisfies |Σ (n+1)^{-1/2} · ∫ hardyCos n| ≤ C · (N+1).

    This is the analytical heart of the Atkinson formula.
    The per-mode integrals are NOT individually O(√(n+1)) after weighting —
    they grow as Θ(√(n+1)) — but the signed alternation gives cancellation.

    The proof uses:
    (a) Stationary phase: I_n = (-1)^{n+1} c₀(n+1) + O(√(n+1))
        - cos(π(n+1)²) = (-1)^{n+1}  (PROVED: CosPiSqSign)
        - Fresnel evaluation near t₀ = 2π(n+1)²
        - VdC first derivative tail
    (b) After (n+1)^{-1/2} weight: signed sum + O(1) remainders
    (c) Abel alternating bound on √(n+1) terms (PROVED above)
    (d) Triangle inequality on O(1) remainders

    Reference: Atkinson 1949, Acta Math. 81; Titchmarsh 1951 §4.15. -/
/-!
### Per-mode decomposition gap analysis

The O(N+1) bound decomposes via block structure:

  S = Σ w_n I_n = [diagonal] + [off-diagonal tails]

**Diagonal** (resonant block integrals): PROVABLE as O(N).
  - `hardyCos_firstBlock_anchor_main_term_eventually` (StationaryPhaseMainMode)
    gives w_n·J_n = completeModeTarget(n) + O(1) for n ≥ N0.
  - `completeModeTarget_sum_bound_range` (StationaryPhaseDecomposition)
    gives |Σ completeModeTarget| ≤ K·√N via Abel alternating cancellation.
  - Small modes (n < N0) bounded by `small_modes_weighted_sum_bound`.
  - Total diagonal: O(√N) + O(N) + O(1) = O(N).

**Off-diagonal tails** (mode n on blocks k > n): BOTTLENECK.
  - VdC first derivative gives |tail of mode n| ≤ 3/(φ'_n(hardyStart(n+1)))
    ≈ 3(n+1). After weighting: O(√(n+1)). Sum: O(N^{3/2}).
  - VdC second derivative gives |tail of mode n| ≤ 8/√(θ''(T))
    ≈ C·(N+1). After weighting: O(N/√(n+1)). Sum: O(N^{3/2}).
  - The TRUE bound is O(1) after weighting (from Fresnel evaluation
    precision), but requires quantitative control on θ''' that is not
    in the codebase.

**Needed**: A Fresnel tail bound showing that for n ≥ N0,
  |w_n · ∫_{hardyStart(n+1)}^T hardyCos n t dt| ≤ C_tail,
  i.e., the off-resonant tail grows as O(√(n+1)), not O(n+1).
  This follows from the stationary phase remainder estimate and
  requires θ(t) = (t/2)log(t/(2π)) - t/2 - π/8 + O(1/t) precision.

Reference: Atkinson 1949, Acta Math. 81, §3 (evaluation of R_n).
-/

private theorem atkinson_weighted_sum_bound :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∑ n ∈ Finset.range (hardyN T),
        ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t|
      ≤ C * ((↑(hardyN T) : ℝ) + 1) := by
  -- Atkinson 1949: per-mode stationary phase + signed cancellation.
  -- Diagonal contribution: O(N) via signed cancellation (infrastructure in
  -- StationaryPhaseMainMode + CosPiSqSign + AbelSummation).
  -- Off-diagonal tails: O(1) per weighted mode (requires Fresnel precision
  -- on the stationary phase remainder — the specific gap).
  -- See gap analysis above for details.
  sorry

/-- Assembly: the weighted sum bound gives the signed Fresnel bound
    on the MainTerm integral via the Fubini result. -/
private theorem atkinson_signed_fresnel_bound :
    ∃ C_atk > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_atk * ((↑(hardyN T) : ℝ) + 1) := by
  obtain ⟨C, hC, h_sum⟩ := atkinson_weighted_sum_bound
  refine ⟨2 * C, by positivity, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  -- Fubini: ∫ MainTerm = hardySumInt T = 2 · Σ weighted integrals
  have h_fubini : ∫ t in Ioc 1 T, MainTerm t = hardySumInt T := by
    rw [MainTerm_eq_hardySum]
    exact hardySum_integral_eq T hT1
  rw [h_fubini, hardySumInt]
  set N := hardyN T
  calc |2 * ∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t|
      = 2 * |∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ 2 * (C * ((↑N : ℝ) + 1)) := by
        gcongr; exact h_sum T hT
    _ = 2 * C * ((↑N : ℝ) + 1) := by ring

/-! ## Section 4: Assembly -/

/-- **Atkinson evaluation**: |∫₁ᵀ MainTerm(t) dt| ≤ C_atk · (hardyN(T) + 1). -/
private theorem atkinson_integral_le_N :
    ∃ C_atk > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_atk * ((↑(hardyN T) : ℝ) + 1) :=
  atkinson_signed_fresnel_bound

/-- **MainTerm first moment O(√T) bound** (Atkinson formula).

    Combines the Atkinson evaluation |∫ MainTerm| ≤ C_atk · (N+1)
    with the hardyN bound N+1 ≤ 2√T to get the O(√T) bound.

    Reference: Atkinson 1949; Titchmarsh 1951 §4.15. -/
theorem mainTerm_first_moment_sqrt :
    ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ ((1 : ℝ) / 2) := by
  obtain ⟨C_atk, hC_pos, h_atk⟩ := atkinson_integral_le_N
  refine ⟨2 * C_atk, by positivity, fun T hT => ?_⟩
  calc |∫ t in Ioc 1 T, MainTerm t|
      ≤ C_atk * ((↑(hardyN T) : ℝ) + 1) := h_atk T hT
    _ ≤ C_atk * (2 * Real.sqrt T) := by
        gcongr; exact hardyN_add_one_le T (by linarith)
    _ = 2 * C_atk * Real.sqrt T := by ring
    _ = 2 * C_atk * T ^ ((1 : ℝ) / 2) := by
        congr 1; exact Real.sqrt_eq_rpow T

end Aristotle.Standalone.AtkinsonFormula
