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

    This encapsulates the deep analytical content of the Atkinson formula:
    per-mode IBP on the Dirichlet polynomial, Fresnel evaluation near
    stationary points, signed sum cancellation via Abel's alternating
    series bound, and IBP tail control via θ' monotonicity.

    The only unformalized component is the per-mode signed Fresnel
    evaluation: showing that at t₀ = 2π(n+1)², the Fresnel integral
    evaluates to (-1)^{n+1}·c₀·(n+1) + O(√(n+1)). All other
    components (Fubini, Abel, CosPiSqSign, assembly) are proved.

    Reference: Atkinson 1949, Acta Math. 81, pp. 353-376. -/
private theorem atkinson_signed_fresnel_bound :
    ∃ C_atk > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_atk * ((↑(hardyN T) : ℝ) + 1) := by
  sorry

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
