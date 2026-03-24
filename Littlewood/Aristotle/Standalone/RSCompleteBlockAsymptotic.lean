/-
Riemann-Siegel complete-block asymptotic sorry and wiring to PerBlockSignedBoundHyp.

This file defines a clean atomic sorry (`rsCompleteBlockWithResidual_sorry`) encoding
the Riemann-Siegel per-block sign structure on COMPLETE blocks with partial-block
interpolation, then wires it to `PerBlockSignedBoundHyp`.

## Mathematical content

On the k-th complete block (hardyStart k, hardyStart(k+1)):
  ∫ ErrorTerm ≈ (-1)^k · A · √(k+1)
with uniformly bounded per-block error (Clause 1), bounded cumulative
residual sum (Clause 2), and partial-block sign interpolation (Clause 3).

## Wiring

Clause 3 provides partial-block interpolation: the integral over any initial
sub-interval of a block is α times the complete-block leading term (α ∈ [0,1])
with error at most B. Combined with Clauses 1 and 2, a convex combination
argument shows the integral stays within the alternating sum structure.

## References
- Siegel, "Über Riemanns Nachlaß zur analytischen Zahlentheorie" (1932)
- Titchmarsh, "The Theory of the Riemann Zeta-Function", §4.16-4.17

SORRY COUNT: 1 (rs_block_analysis)
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.RSBlockDecomposition
import Littlewood.Aristotle.AbelSummation
import Littlewood.Aristotle.RSBlockBounds

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RSCompleteBlockAsymptotic

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.Standalone.AtkinsonFormula
open Aristotle.Standalone.SiegelSaddleExpansionHyp
open Aristotle.Standalone.GabckePhaseCouplingHyp

variable [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
variable [AtkinsonSmallShiftPrefixBoundHyp]
variable [AtkinsonLargeShiftPrefixBoundHyp]
variable [AtkinsonShiftedCorrectionPrefixBoundHyp]
variable [SiegelSaddleExpansionHyp]
variable [GabckePhaseCouplingHyp]

/-- Convex combination absolute value bound. -/
private lemma abs_convex_le_max (a b α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |(1 - α) * a + α * b| ≤ max |a| |b| :=
  calc |(1 - α) * a + α * b|
      ≤ |(1 - α) * a| + |α * b| := abs_add_le _ _
    _ = (1 - α) * |a| + α * |b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 - α by linarith),
            abs_of_nonneg hα0]
    _ ≤ (1 - α) * max |a| |b| + α * max |a| |b| :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hα0)
    _ = max |a| |b| := by ring

/-- Per-block integral sign structure on COMPLETE blocks, partial-block
interpolation, and centered residual cancellation.

**Clause 1** (per-block sign structure): Each complete block integral is
`(-1)^k · A · √(k+1)` plus uniformly bounded error B.

**Clause 2** (centered residual cancellation): The partial sums of block
errors are bounded by R independent of N.

**Clause 3** (partial-block interpolation): On any initial sub-interval
`(hardyStart k, T]` of a complete block, the integral is α times the
complete-block leading term (α ∈ [0,1]) with error at most B. This
encodes the constant-sign property of ErrorTerm within each block. -/
def RSCompleteBlockWithResidualHyp : Prop :=
  ∃ (A B R : ℝ), A > 0 ∧ B ≥ 0 ∧ R ≥ 0 ∧
    -- Clause 1: per-block sign structure on COMPLETE blocks
    (∀ k : ℕ,
      |(∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)| ≤ B) ∧
    -- Clause 2: centered residual on complete blocks
    (∀ N : ℕ,
      |∑ k ∈ Finset.range N,
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ R) ∧
    -- Clause 3: partial block interpolation
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ (α : ℝ), 0 ≤ α ∧ α ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - α * ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ B)

/-- Unified RS block analysis: the single atomic sorry for B3.

The block integral of ErrorTerm decomposes as:
  ∫_{block k} ErrorTerm = (-1)^k · (A·√(k+1) + c(k))
where A > 0 is the Fresnel constant, c(k) ≥ 0 captures the sign-definite
correction, and c is antitone on k ≥ 1 (corrections decay).

Additionally, partial-block integrals interpolate: the partial integral
is β times the full-block integral (β ∈ [0,1]) with bounded error C₂.

The block integral clause uses exact equality (not bounds). This is essential:
Clause 2 needs the errors to be EXACTLY (-1)^k · c_k to apply alternating
series bounds. c_k is existentially quantified and defined as
c_k := (-1)^k · (∫ ErrorTerm) - A √(k+1). The hard analytic content is
proving c_k ≥ 0 (sign-definite) and AntitoneOn c (Ici 1) (decay).

REFERENCES: Siegel 1932 §3; Titchmarsh §4.16-4.17. -/
private theorem rs_block_analysis :
    ∃ (A : ℝ) (c : ℕ → ℝ) (C₂ : ℝ),
      A > 0 ∧
      (∀ k, 0 ≤ c k) ∧
      AntitoneOn c (Ici (1 : ℕ)) ∧
      (∀ k : ℕ,
        (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          = (-1 : ℝ) ^ k * (A * Real.sqrt ((k : ℝ) + 1) + c k)) ∧
      C₂ ≥ 0 ∧
      (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
        ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
          |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
            - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                     ErrorTerm t)| ≤ C₂) := by
  exact Aristotle.RSBlockBounds.rs_block_analysis_proof

/-- Helper: c k ≤ max (c 0) (c 1) for all k, from atom hypotheses.
    For k = 0: trivially c 0 ≤ max (c 0) (c 1).
    For k ≥ 1: AntitoneOn c (Ici 1) gives c k ≤ c 1 ≤ max (c 0) (c 1). -/
private lemma c_le_max {c : ℕ → ℝ} (hc_anti : AntitoneOn c (Ici (1 : ℕ)))
    (k : ℕ) : c k ≤ max (c 0) (c 1) := by
  rcases k with _ | k
  · exact le_max_left _ _
  · -- AntitoneOn: a ∈ s → b ∈ s → a ≤ b → f b ≤ f a
    -- Want c(k+1) ≤ c 1. Set a=1, b=k+1.
    exact le_trans (hc_anti (Set.mem_Ici.mpr (le_refl 1))
      (Set.mem_Ici.mpr (by omega : 1 ≤ k + 1)) (by omega : 1 ≤ k + 1))
      (le_max_right _ _)

/-- Assembly: wire the unified atom into `RSCompleteBlockWithResidualHyp`.

From the atom, block errors are e_k = (-1)^k c_k. Clause 1 uses |e_k| ≤ max(c 0, c 1).
Clause 2 splits at k=0 and applies `alternating_antitone_sum_le_first` to the tail.
Clause 3 uses the interpolation from the atom with triangle inequality.

B = max(c 0, c 1) + C₂, R = c 0 + c 1. -/
theorem rsCompleteBlockWithResidual_sorry :
    RSCompleteBlockWithResidualHyp := by
  obtain ⟨A, c, C₂, hA, hc_nn, hc_anti, hblock_eq, hC₂_nn, hinterp⟩ := rs_block_analysis
  -- Constants
  set B := max (c 0) (c 1) + C₂
  set R := c 0 + c 1
  refine ⟨A, B, R, hA, ?_, ?_, ?_, ?_, ?_⟩
  · -- B ≥ 0
    have : max (c 0) (c 1) ≥ 0 := le_trans (hc_nn 0) (le_max_left _ _)
    linarith
  · -- R ≥ 0
    linarith [hc_nn 0, hc_nn 1]
  · -- Clause 1: per-block sign structure
    intro k
    -- ∫ = (-1)^k (A √(k+1) + c k), so error = (-1)^k c_k
    rw [hblock_eq k]
    rw [show (-1 : ℝ) ^ k * (A * Real.sqrt (↑k + 1) + c k)
          - (-1 : ℝ) ^ k * A * Real.sqrt (↑k + 1)
        = (-1 : ℝ) ^ k * c k from by ring]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (hc_nn k)]
    -- c k ≤ max(c 0, c 1) ≤ max(c 0, c 1) + C₂ = B
    calc c k ≤ max (c 0) (c 1) := c_le_max hc_anti k
      _ ≤ max (c 0) (c 1) + C₂ := le_add_of_nonneg_right hC₂_nn
  · -- Clause 2: centered residual cancellation
    intro N
    -- Each summand = (-1)^k c_k
    have h_summand : ∀ k ∈ Finset.range N,
        (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)
        = (-1 : ℝ) ^ k * c k := by
      intro k _
      rw [hblock_eq k]; ring
    rw [Finset.sum_congr rfl h_summand]
    -- Split: ∑_{k<N} (-1)^k c_k
    rcases N with _ | N
    · -- N = 0: empty sum
      simp; linarith [hc_nn 0, hc_nn 1]
    · -- N = n+1: split off k=0 term, then bound tail via alternating antitone
      rw [Finset.sum_range_succ', pow_zero, one_mul]
      -- Goal: |∑_{k<N} (-1)^(k+1) c(k+1) + c 0| ≤ c 0 + c 1
      rw [show ∀ (x y : ℝ), |x + y| = |y + x| from fun x y => by rw [add_comm]]
      -- Goal: |c 0 + ∑_{k<N} (-1)^(k+1) c(k+1)| ≤ c 0 + c 1
      calc |c 0 + ∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * c (k + 1)|
          ≤ |c 0| + |∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * c (k + 1)| :=
            abs_add_le _ _
        _ = c 0 + |∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * c (k + 1)| := by
            rw [abs_of_nonneg (hc_nn 0)]
        _ ≤ c 0 + c 1 := by
            gcongr
            -- Factor out (-1): (-1)^(k+1) = (-1) * (-1)^k
            -- ∑ (-1)^(k+1) c(k+1) = (-1) * ∑ (-1)^k c(k+1)
            have h_factor : ∀ k : ℕ,
                (-1 : ℝ) ^ (k + 1) * c (k + 1) = (-1 : ℝ) * ((-1 : ℝ) ^ k * c (k + 1)) := by
              intro k; rw [pow_succ]; ring
            rw [Finset.sum_congr rfl (fun k _ => h_factor k), ← Finset.mul_sum,
                abs_mul, abs_neg, abs_one, one_mul]
            -- Now bound |∑_{k<N} (-1)^k c(k+1)| ≤ c 1
            -- Define a(k) = c(k+1). Then a is antitone and nonneg.
            -- By alternating_antitone_sum_le_first: |∑_{k<N} (-1)^k a(k)| ≤ a 0 = c 1
            rcases N with _ | M
            · simp; exact hc_nn 1
            · -- N = M + 1, sum over range (M+1)
              have h_anti_shift : Antitone (fun k => c (k + 1)) := by
                intro i j hij
                -- Antitone: i ≤ j → c(j+1) ≤ c(i+1)
                -- AntitoneOn: a ∈ s → b ∈ s → a ≤ b → f b ≤ f a
                -- Set a = i+1, b = j+1
                exact hc_anti (Set.mem_Ici.mpr (by omega : 1 ≤ i + 1))
                  (Set.mem_Ici.mpr (by omega : 1 ≤ j + 1)) (by omega : i + 1 ≤ j + 1)
              have h_nn_shift : ∀ k, 0 ≤ (fun k => c (k + 1)) k := fun k => hc_nn (k + 1)
              exact AbelSummation.alternating_antitone_sum_le_first
                (fun k => c (k + 1)) h_nn_shift h_anti_shift M
  · -- Clause 3: partial-block interpolation
    intro k T hkT hTk
    obtain ⟨β, hβ0, hβ1, hβ_bound⟩ := hinterp k T hkT hTk
    refine ⟨β, hβ0, hβ1, ?_⟩
    -- Strategy: rewrite ∫_{full} via hblock_eq in hβ_bound, then triangle inequality.
    -- hβ_bound: |∫_{partial} - β · ∫_{full}| ≤ C₂
    -- hblock_eq: ∫_{full} = (-1)^k (A √(k+1) + c_k)
    -- Goal: |∫_{partial} - β · (-1)^k A √(k+1)| ≤ B
    -- = |(∫_{partial} - β · ∫_{full}) + β · (∫_{full} - (-1)^k A √(k+1))|
    -- = |(∫_{partial} - β · ∫_{full}) + β · (-1)^k · c_k|
    -- ≤ C₂ + β · c_k ≤ C₂ + max(c 0, c 1) = B
    set I_full := ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t
    set I_part := ∫ t in Ioc (hardyStart k) T, ErrorTerm t
    have hI_full : I_full = (-1 : ℝ) ^ k * (A * Real.sqrt (↑k + 1) + c k) := hblock_eq k
    -- Rewrite goal using algebra
    have h_split : I_part - β * ((-1 : ℝ) ^ k * A * Real.sqrt (↑k + 1))
        = (I_part - β * I_full) + β * ((-1 : ℝ) ^ k * c k) := by
      rw [hI_full]; ring
    rw [h_split]
    have h_abs_beta : |β * ((-1 : ℝ) ^ k * c k)| = β * c k := by
      rw [abs_mul, abs_mul, abs_of_nonneg hβ0, abs_pow, abs_neg, abs_one, one_pow,
          one_mul, abs_of_nonneg (hc_nn k)]
    calc |(I_part - β * I_full) + β * ((-1 : ℝ) ^ k * c k)|
        ≤ |I_part - β * I_full| + |β * ((-1 : ℝ) ^ k * c k)| := abs_add_le _ _
      _ ≤ C₂ + β * c k := add_le_add hβ_bound (le_of_eq h_abs_beta)
      _ ≤ C₂ + max (c 0) (c 1) := by
          have : β * c k ≤ max (c 0) (c 1) :=
            le_trans (mul_le_of_le_one_left (hc_nn k) hβ1) (c_le_max hc_anti k)
          linarith
      _ = max (c 0) (c 1) + C₂ := by ring

/-- Wire `RSCompleteBlockWithResidualHyp` to `PerBlockSignedBoundHyp`.

The proof decomposes ∫₁ᵀ ErrorTerm into head + complete blocks + partial
block, applies Clauses 1–3, and uses a convex combination bound to keep
the partial block's contribution within the alternating sum structure. -/
theorem perBlockSignedBoundHyp_of_blockAsymptotic
    (hyp : RSCompleteBlockWithResidualHyp) :
    Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp := by
  obtain ⟨A, B, R, hA, hB, hR, hC1, hC2, hC3⟩ := hyp
  -- Global error constant
  let Bsmall : ℝ := ∫ t in Ioc (1 : ℝ) (2 * Real.pi), ‖ErrorTerm t‖
  let head_int : ℝ := |∫ t in Ioc (1 : ℝ) (hardyStart 0), ErrorTerm t|
  let Bglobal : ℝ := max Bsmall (head_int + R + B)
  have hBg_nn : (0 : ℝ) ≤ Bglobal :=
    le_max_of_le_left (integral_nonneg (fun _ => norm_nonneg _))
  refine ⟨A, Bglobal, hA, hBg_nn, ?_⟩
  intro T hT
  by_cases hT_long : 2 * Real.pi ≤ T
  · -- === Case T ≥ 2π: block decomposition ===
    have hT_nonneg : (0 : ℝ) ≤ T := by linarith
    let M := hardyN T
    have hM_pos : 0 < M := by
      have : hardyStart 0 ≤ T := by
        rw [Aristotle.HardyNProperties.hardyStart_formula]; simpa using hT_long
      exact (hardyN_lt_iff 0 T hT_nonneg).2 this
    let n := M - 1
    have hM_eq : M = n + 1 := (Nat.succ_pred_eq_of_pos hM_pos).symm
    -- Block boundary facts
    have hstart_n_le : hardyStart n ≤ T :=
      (hardyN_lt_iff n T hT_nonneg).1 (Nat.pred_lt (Nat.pos_iff_ne_zero.mp hM_pos))
    have hT_lt_startM : T < hardyStart M := by
      by_contra h; push_neg at h
      exact Nat.lt_irrefl M ((hardyN_lt_iff M T hT_nonneg).2 h)
    have hT_le_succ : T ≤ hardyStart (n + 1) := by
      rw [← hM_eq]; exact le_of_lt hT_lt_startM
    -- Block decomposition (from RSBlockDecomposition)
    have hdecomp :=
      Aristotle.RSBlockDecomposition.errorTerm_block_sum T (show T ≥ 2 by linarith)
    -- Head simplification: min T (hardyStart 0) = hardyStart 0
    have hhead_min : min T (hardyStart 0) = hardyStart 0 := by
      apply min_eq_right
      rw [Aristotle.HardyNProperties.hardyStart_formula]; simpa using hT_long
    -- Complete blocks: for k < n, clamped = complete
    have hcomplete_eq : ∀ k, k ∈ Finset.range n →
        (∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
          = ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := by
      intro k hk
      have hk_lt_n : k < n := Finset.mem_range.mp hk
      have hk_lt_M : k < M := by rw [hM_eq]; omega
      have hk1_lt_M : k + 1 < M := by rw [hM_eq]; omega
      rw [min_eq_right ((hardyN_lt_iff k T hT_nonneg).1 hk_lt_M),
          min_eq_right ((hardyN_lt_iff (k + 1) T hT_nonneg).1 hk1_lt_M)]
    -- Partial block: clamped_n = partial from hardyStart n to T
    have hpartial_eq :
        (∫ t in Ioc (min T (hardyStart n)) (min T (hardyStart (n + 1))), ErrorTerm t)
          = ∫ t in Ioc (hardyStart n) T, ErrorTerm t := by
      rw [min_eq_right hstart_n_le, min_eq_left hT_le_succ]
    -- Split the block sum: ∑_{k<M} = ∑_{k<n} + last term
    have hsum_split :
        Finset.sum (Finset.range M)
            (fun k => ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
          = Finset.sum (Finset.range n)
              (fun k => ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                ErrorTerm t)
            + ∫ t in Ioc (min T (hardyStart n)) (min T (hardyStart (n + 1))), ErrorTerm t := by
      rw [hM_eq]; exact Finset.sum_range_succ _ n
    -- Integral decomposition: I = head + ∑ complete + partial
    have hI_eq :
        ∫ t in Ioc 1 T, ErrorTerm t
          = (∫ t in Ioc 1 (hardyStart 0), ErrorTerm t)
            + (∑ k ∈ Finset.range n,
                ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
            + (∫ t in Ioc (hardyStart n) T, ErrorTerm t) := by
      rw [hdecomp, hhead_min, hsum_split, Finset.sum_congr rfl hcomplete_eq, hpartial_eq,
          add_assoc]
    -- Alternating sum
    let S : ℕ → ℝ := fun N =>
      ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)
    have hS_succ : S (n + 1) = S n + (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1) :=
      Finset.sum_range_succ _ n
    -- Clause 2: cumulative residual bound
    have hresid_bound : |∑ k ∈ Finset.range n,
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ R := hC2 n
    -- Clause 3: partial block interpolation
    obtain ⟨α, hα0, hα1, hη⟩ := hC3 n T hstart_n_le hT_le_succ
    -- Algebraic decomposition of complete block sum
    have hcomplete_sum :
        ∑ k ∈ Finset.range n,
          ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t
        = A * S n
          + ∑ k ∈ Finset.range n,
              ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
                - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)) := by
      conv_lhs =>
        arg 2; ext k
        rw [show (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
              = (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)
                + ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
                    - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))
          from by ring]
      rw [Finset.sum_add_distrib]
      congr 1
      simp_rw [show ∀ k : ℕ,
          (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)
            = A * ((-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1))
        from fun k => by ring]
      exact (Finset.mul_sum ..).symm
    -- Convex combination identity
    have hconvex_eq :
        (1 - α) * S n + α * S (n + 1)
          = S n + α * ((-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)) := by
      rw [hS_succ]; ring
    -- Key bound: |∫| ≤ A * max(|S n|, |S(n+1)|) + Bglobal
    have hM_le_sqrt : (M : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
      have := Aristotle.HardyNProperties.hardyN_le_sqrt T (show T ≥ 2 by linarith)
      linarith
    -- Abbreviations for readability
    set head_val := ∫ t in Ioc (1 : ℝ) (hardyStart 0), ErrorTerm t
    set resid_sum := ∑ k ∈ Finset.range n,
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))
    set partial_val := ∫ t in Ioc (hardyStart n) T, ErrorTerm t
    set η := partial_val - α * ((-1 : ℝ) ^ n * A * Real.sqrt ((n : ℝ) + 1))
    -- η bound from Clause 3
    have hη_bound : |η| ≤ B := hη
    -- The integral in terms of convex combination
    have hI_conv :
        ∫ t in Ioc 1 T, ErrorTerm t
          = A * ((1 - α) * S n + α * S (n + 1)) + (head_val + resid_sum + η) := by
      rw [hI_eq, hcomplete_sum, hconvex_eq]
      simp only [η]
      ring
    -- Main bound
    have hbound :
        |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ A * max |S n| |S (n + 1)| + (head_int + R + B) := by
      rw [hI_conv]
      calc |A * ((1 - α) * S n + α * S (n + 1)) + (head_val + resid_sum + η)|
          ≤ |A * ((1 - α) * S n + α * S (n + 1))| + |head_val + resid_sum + η| :=
            abs_add_le _ _
        _ ≤ A * max |S n| |S (n + 1)| + (|head_val| + |resid_sum| + |η|) := by
            gcongr
            · rw [abs_mul, abs_of_pos hA]
              exact mul_le_mul_of_nonneg_left
                (abs_convex_le_max _ _ α hα0 hα1) (le_of_lt hA)
            · calc |head_val + resid_sum + η|
                  ≤ |head_val + resid_sum| + |η| := abs_add_le _ _
                _ ≤ |head_val| + |resid_sum| + |η| := by
                    gcongr; exact abs_add_le _ _
        _ ≤ A * max |S n| |S (n + 1)| + (head_int + R + B) := by
            have h_head_le : |head_val| ≤ head_int := by
              simp [head_val, head_int]
            have h_resid_le : |resid_sum| ≤ R := by
              simpa [resid_sum] using hresid_bound
            nlinarith [h_head_le, h_resid_le, hη_bound]
    -- Choose N based on which alternating sum is larger
    have hbound_Bg :
        |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ A * max |S n| |S (n + 1)| + Bglobal := by
      calc |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ A * max |S n| |S (n + 1)| + (head_int + R + B) := hbound
        _ ≤ A * max |S n| |S (n + 1)| + Bglobal := by
            gcongr; exact le_max_right _ _
    by_cases h_which : |S n| ≤ |S (n + 1)|
    · -- Use N = n (alternating sum has n+1 terms)
      refine ⟨n, ?_, ?_⟩
      · -- (n + 1 : ℝ) ≤ T^{1/2}
        calc ((n : ℝ) + 1) = (M : ℝ) := by exact_mod_cast hM_eq.symm
          _ ≤ T ^ (1 / 2 : ℝ) := hM_le_sqrt
      · -- |∫| ≤ A * |S(n+1)| + Bglobal
        calc |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * max |S n| |S (n + 1)| + Bglobal := hbound_Bg
          _ = A * |S (n + 1)| + Bglobal := by rw [max_eq_right h_which]
    · -- Use N = n - 1 (need n ≥ 1)
      push_neg at h_which
      have hn_pos : 0 < n := by
        by_contra h; push_neg at h
        have hn0 : n = 0 := by omega
        rw [hn0] at h_which
        dsimp only [S] at h_which
        rw [Finset.sum_range_zero] at h_which
        simp [abs_zero] at h_which
        linarith
      refine ⟨n - 1, ?_, ?_⟩
      · -- (n - 1 + 1 : ℝ) ≤ T^{1/2}, i.e., n ≤ T^{1/2}
        have hn_eq : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
        calc ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hn_eq
          _ ≤ (M : ℝ) := by exact_mod_cast Nat.pred_le M
          _ ≤ T ^ (1 / 2 : ℝ) := hM_le_sqrt
      · -- |∫| ≤ A * |S n| + Bglobal
        have hn_eq : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
        calc |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * max |S n| |S (n + 1)| + Bglobal := hbound_Bg
          _ = A * |S n| + Bglobal := by rw [max_eq_left (le_of_lt h_which)]
          _ = A * |S (n - 1 + 1)| + Bglobal := by rw [hn_eq]
  · -- === Case T < 2π: trivial bound ===
    push_neg at hT_long
    refine ⟨0, ?_, ?_⟩
    · -- (0 + 1 : ℝ) ≤ T^{1/2}
      simp only [Nat.cast_zero, zero_add]
      exact Real.one_le_rpow (show (1 : ℝ) ≤ T by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    · -- |∫| ≤ A * |S 1| + Bglobal
      have h_int_bound :
          |∫ t in Ioc 1 T, ErrorTerm t| ≤ Bsmall := by
        calc |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ ∫ t in Ioc 1 T, ‖ErrorTerm t‖ := by
              rw [show |∫ t in Ioc 1 T, ErrorTerm t|
                    = ‖∫ t in Ioc 1 T, ErrorTerm t‖
                from (Real.norm_eq_abs _).symm]
              exact norm_integral_le_integral_norm _
          _ ≤ ∫ t in Ioc 1 (2 * Real.pi), ‖ErrorTerm t‖ := by
              exact setIntegral_mono_set
                (errorTerm_integrable (2 * Real.pi)).norm
                (ae_of_all _ (fun _ => norm_nonneg _))
                (Eventually.of_forall (fun t ht =>
                  ⟨ht.1, le_trans ht.2 (le_of_lt hT_long)⟩))
          _ = Bsmall := rfl
      calc |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ Bsmall := h_int_bound
        _ ≤ Bglobal := le_max_left _ _
        _ ≤ A * |∑ k ∈ Finset.range (0 + 1),
                (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + Bglobal := by
            linarith [mul_nonneg (le_of_lt hA) (abs_nonneg (∑ k ∈ Finset.range 1,
                (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)))]

end Aristotle.Standalone.RSCompleteBlockAsymptotic
