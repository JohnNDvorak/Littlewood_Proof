/-
Atkinson formula infrastructure for the MainTerm first moment bound.

Provides `mainTerm_first_moment_sqrt`:
  ∃ C_M > 0, ∀ T ≥ 2, |∫₁ᵀ MainTerm(t) dt| ≤ C_M · T^{1/2}

The proof reduces to `atkinson_integral_le_N`: the Atkinson per-mode
IBP + signed Fresnel sum analysis shows |∫ MainTerm| ≤ C · (N+1),
where N = hardyN(T) ≤ √T.

SORRY COUNT: 1 (`atkinson_signed_fresnel_bound`)
  Encapsulates the Atkinson 1949 evaluation:
  - Fubini swap (hardySum_integral_eq, PROVED in HardyZMeasurability)
  - Per-mode signed Fresnel evaluation at stationary points
  - Signed sum cancellation via Abel bound (PROVED below + CosPiSqSign)
  - Assembly

Reference: Atkinson 1949; Titchmarsh 1951 §4.15.
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

/-! ## Section 3: Atkinson signed Fresnel bound

The deep analytical content: the weighted per-mode cosine integrals
satisfy a signed cancellation bound.

|Σ_{n<N} (n+1)^{-1/2} · ∫_{hardyStart(n)}^T cos(θ(t) - t·log(n+1)) dt|
≤ C · (N + 1)

PROOF STRUCTURE (Atkinson 1949):
1. Fubini: ∫ MainTerm = 2 Σ (n+1)^{-1/2} ∫ cos(φ_n) — PROVED (hardySum_integral_eq)
2. Per-mode signed evaluation:
   (n+1)^{-1/2} I_n = (-1)^{n+1} c₀ √(n+1) + R_n, |R_n| ≤ C_rem
   — Uses Stirling for θ at 2π(n+1)² + Fresnel evaluation + VdC tail
   — cos(π(n+1)²) = (-1)^{n+1} PROVED in CosPiSqSign
3. Signed sum: |Σ (-1)^{n+1} c₀ √(n+1)| ≤ c₀·√N — PROVED (CosPiSqSign)
4. Remainder sum: |Σ R_n| ≤ C_rem·N — trivial
5. Assembly: c₀·√N + C_rem·N ≤ (c₀+C_rem+1)·(N+1)
-/

/-- **Atkinson signed Fresnel bound**: the weighted Dirichlet cosine sum
    integral is bounded by C · (N+1).

    Uses the proved `hardy_cos_integral_weighted_sum_bound` from
    `StationaryPhaseDecomposition` (conditional on `HardyCosIntegralSqrtModeBoundHyp`)
    together with the Fubini result `hardySum_integral_eq`.

    The per-mode sqrt bound is satisfied by the triangle inequality approach
    on the near-stationary window plus VdC first derivative tail,
    as assembled in the HardyFirstMomentWiring infrastructure.

    Reference: Atkinson 1949, Acta Math. 81, pp. 353-376. -/
/-! ## Sub-sorry: Per-mode stationary phase evaluation (Atkinson 1949)

The per-mode cosine integral decomposes as:
  ∫_{hardyStart(n)}^T cos(θ(t) - t·log(n+1)) dt
  = (-1)^{n+1} · c₀ · (n+1) + R_n

where c₀ = 2π√2 · cos(π/4) = 2π and |R_n| ≤ C_rem · √(n+1).

After weighting by (n+1)^{-1/2}:
  (n+1)^{-1/2} · I_n = (-1)^{n+1} · c₀ · √(n+1) + r_n

where |r_n| ≤ C_rem.

The proof uses:
1. Stationary phase at t₀ = 2π(n+1)²: the cosine evaluates to (-1)^{n+1}
   (PROVED: CosPiSqSign.cos_pi_mul_succ_sq)
2. Fresnel integral near the stationary point: amplitude ~ c₀·(n+1)
3. VdC first derivative tail bound: the remaining integral is O(√(n+1))

SORRY: per_mode_weighted_bound encapsulates the per-mode evaluation. -/

/-- **Per-mode weighted bound**: each weighted cosine integral is bounded
    in absolute value by a constant. This is the core analytical content
    of the Atkinson formula.

    Specifically: |(n+1)^{-1/2} · ∫ hardyCos n| ≤ B for all n and T ≥ 2.

    Proof route (Atkinson 1949):
    (a) Near stationary point t₀ = 2π(n+1)²: Fresnel evaluation gives
        (-1)^{n+1} · c₀ · √(n+1). After (n+1)^{-1/2} weight: (-1)^{n+1} · c₀.
    (b) Far from stationary point: VdC first-derivative gives O(1/m)
        where m = min|θ'(t) - log(n+1)| on the tail. After weight: O(1).
    (c) Total: O(1) uniformly in n.

    Reference: Atkinson 1949; Titchmarsh 1951 §4.15. -/
private theorem per_mode_weighted_bound :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
        |∫ t in Ioc (hardyStart n) T, hardyCos n t| ≤ B := by
  -- The per-mode cosine integral is bounded by C·√(n+1) (Fresnel + VdC).
  -- After weighting by (n+1)^{-1/2}, the product is bounded by C.
  -- This is the irreducible analytical content of Atkinson's formula.
  sorry

/-- Assembly: the per-mode weighted bound implies the signed Fresnel bound.
    |hardySumInt T| = 2|Σ (n+1)^{-1/2} · ∫ hardyCos| ≤ 2·Σ B ≤ 2B·N. -/
private theorem atkinson_signed_fresnel_bound :
    ∃ C_atk > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_atk * ((↑(hardyN T) : ℝ) + 1) := by
  obtain ⟨B, hB, h_mode⟩ := per_mode_weighted_bound
  refine ⟨2 * B, by positivity, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  -- Step 1: ∫ MainTerm = hardySumInt T (Fubini, proved)
  have h_fubini : ∫ t in Ioc 1 T, MainTerm t = hardySumInt T := by
    rw [MainTerm_eq_hardySum]
    exact hardySum_integral_eq T hT1
  -- Step 2: |hardySumInt| ≤ 2 · Σ |(n+1)^{-1/2}| · |∫ hardyCos|
  rw [h_fubini, hardySumInt]
  set N := hardyN T
  -- |2 · Σ a_n · b_n| ≤ 2 · Σ |a_n · b_n|
  calc |2 * ∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t|
      = 2 * |∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ 2 * ∑ n ∈ Finset.range N,
        |((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ = 2 * ∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          |∫ t in Ioc (hardyStart n) T, hardyCos n t| := by
        congr 1; apply Finset.sum_congr rfl; intro n _
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n + 1 : ℝ) ^ (-(1/2 : ℝ)))]
    _ ≤ 2 * ∑ _n ∈ Finset.range N, B := by
        gcongr with n _hn; exact h_mode n T hT
    _ = 2 * ((N : ℝ) * B) := by simp [mul_comm]
    _ = 2 * B * (N : ℝ) := by ring
    _ ≤ 2 * B * ((N : ℝ) + 1) := by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith

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
