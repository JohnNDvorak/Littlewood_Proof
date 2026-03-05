# Aristotle Prompt D (Ultra Self-Contained, No Repo Access)

You are solving one deep Lean sorry with **zero access to our repository**.
Everything you need is below: full target file context and full transitive local dependency closure.

## Task
Complete **`rs_block_analysis`** with no `axiom`, `admit`, or `sorry`, preserving the declaration signature exactly.

## Output Requirements
1. Return Lean code that replaces the `sorry` in `rs_block_analysis`.
2. If helper lemmas are needed, include complete Lean code for them in the same response.
3. Do not require any external files not present in this prompt.
4. Keep namespace/import assumptions consistent with provided code.

## Version Contract
- Lean 4 + Mathlib 4 environment.
- No project-local file access beyond the code pasted in this prompt.

## Target File
- `Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean`

## Target Declaration Snippet (from target file)
```lean
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
```

## Local Dependency Closure Included
- File count: 9
- Total bytes: 23628

### Included Local Files (transitive `import Littlewood.*` closure)
- `Littlewood/Aristotle/AbelSummation.lean`
- `Littlewood/Aristotle/HardyEstimatesPartial.lean`
- `Littlewood/Aristotle/HardyNProperties.lean`
- `Littlewood/Aristotle/HardyZCauchySchwarz.lean`
- `Littlewood/Aristotle/HardyZFirstMoment.lean`
- `Littlewood/Aristotle/HardyZMeasurability.lean`
- `Littlewood/Aristotle/IntervalPartition.lean`
- `Littlewood/Aristotle/RSBlockDecomposition.lean`
- `Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean`

## Full File: `Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean`
```lean
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
  -- Future drop-in when the separate RS block development is stabilized:
  -- `exact Aristotle.RSBlockBounds.rs_block_analysis_proof`
  sorry

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
```

## Full Dependency File: `Littlewood/Aristotle/AbelSummation.lean`
```lean
/-
Abel summation (summation by parts) and alternating series bound.

KEY RESULTS:
  abel_summation: ∑_{k=0}^{n} f(k)*g(k) = F(n)*g(n) - ∑_{k=0}^{n-1} F(k)*(g(k+1)-g(k))
  alternating_sum_le_last: |∑_{k=0}^{n} (-1)^k * a_k| ≤ a_n for monotone nonneg a

These are needed for the Hardy first moment analysis: VdC per-mode gives T^{3/4}
(insufficient), but the alternating sign structure from stationary phase gives
cos(πn²) = (-1)^n, and this bound brings the total down to T^{1/4}.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace AbelSummation

open Finset

/-- Partial sum F(n) = ∑_{k=0}^{n} f(k). -/
def partialSum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), f k

@[simp] lemma partialSum_zero (f : ℕ → ℝ) : partialSum f 0 = f 0 := by
  simp [partialSum]

lemma partialSum_succ (f : ℕ → ℝ) (n : ℕ) :
    partialSum f (n + 1) = partialSum f n + f (n + 1) := by
  simp [partialSum, Finset.sum_range_succ]

/-- The two-term recurrence: S(n+2) = S(n) + (-1)^{n+1}·a(n+1) + (-1)^{n+2}·a(n+2).
    Simplifies to S(n+2) = S(n) + (-1)^n·(a(n+2) - a(n+1)). -/
private lemma alternating_sum_step (a : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 3), (-1 : ℝ) ^ k * a k =
    (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * a k) +
    (-1 : ℝ) ^ n * (a (n + 2) - a (n + 1)) := by
  rw [show n + 3 = (n + 2) + 1 from by omega, Finset.sum_range_succ,
      show n + 2 = (n + 1) + 1 from by omega, Finset.sum_range_succ]
  ring

/-- Alternating partial sum bound:
    |∑_{k=0}^{n} (-1)^k * a_k| ≤ a_n
    when a is monotone increasing and nonneg.

    Proof by strong induction with step 2:
    |S(n+2)| = |S(n) + (-1)^n (a(n+2)-a(n+1))|
             ≤ |S(n)| + (a(n+2)-a(n+1))   [triangle, monotone]
             ≤ a(n) + a(n+2) - a(n+1)       [IH]
             ≤ a(n+2)                         [a(n) ≤ a(n+1)] -/
theorem alternating_sum_le_last (a : ℕ → ℝ)
    (h_nonneg : ∀ k, 0 ≤ a k)
    (h_mono : Monotone a) (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * a k| ≤ a n := by
  induction n using Nat.strongRec' with
  | _ n ih =>
    match n with
    | 0 =>
      simp only [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, pow_zero, one_mul]
      exact le_of_eq (abs_of_nonneg (h_nonneg 0))
    | 1 =>
      simp only [show (1 : ℕ) + 1 = 2 from rfl, Finset.sum_range_succ,
        Finset.sum_range_zero, pow_zero, one_mul, pow_one, neg_one_mul, zero_add]
      -- Goal: |a 0 + -a 1| ≤ a 1
      rw [show a 0 + -a 1 = -(a 1 - a 0) from by ring, abs_neg,
          abs_of_nonneg (sub_nonneg.mpr (h_mono (by omega)))]
      linarith [h_nonneg 0]
    | n + 2 =>
      rw [alternating_sum_step]
      calc |∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * a k + (-1 : ℝ) ^ n * (a (n + 2) - a (n + 1))|
          ≤ |∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * a k| + |(-1 : ℝ) ^ n * (a (n + 2) - a (n + 1))| :=
            abs_add_le _ _
        _ ≤ a n + (a (n + 2) - a (n + 1)) := by
            have h1 := ih n (by omega)
            have h2 : |(-1 : ℝ) ^ n * (a (n + 2) - a (n + 1))| = a (n + 2) - a (n + 1) := by
              rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
                  abs_of_nonneg (sub_nonneg.mpr (h_mono (by omega)))]
            linarith
        _ ≤ a (n + 2) := by linarith [h_mono (show n ≤ n + 1 from by omega)]

/-- Reindexing identity: ∑_{j<n+1} (-1)^(n-j) a(j) = (-1)^n · ∑_{j<n+1} (-1)^j a(j).
    Since (-1)^(n-j) = (-1)^n · (-1)^(-j) = (-1)^n · (-1)^j for natural exponents. -/
private lemma alternating_sum_reverse_sign (a : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - j) * a j =
    (-1 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * a j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← mul_assoc, ← pow_add, show n + j = (n - j) + 2 * j from by omega,
      pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

theorem alternating_antitone_sum_le_first (a : ℕ → ℝ)
    (h_nonneg : ∀ k, 0 ≤ a k)
    (h_anti : Antitone a) (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * a k| ≤ a 0 := by
  -- Define reversed sequence b(k) = a(n-k). Then b is monotone nonneg.
  set b : ℕ → ℝ := fun k => a (n - k) with hb_def
  have hb_mono : Monotone b := fun i j hij => h_anti (Nat.sub_le_sub_left hij n)
  have hb_nonneg : ∀ k, 0 ≤ b k := fun k => h_nonneg _
  -- alternating_sum_le_last gives |∑_{k<n+1} (-1)^k b(k)| ≤ b(n) = a(0)
  have h_last := alternating_sum_le_last b hb_nonneg hb_mono n
  simp only [hb_def, Nat.sub_self] at h_last
  -- h_last : |∑_{k<n+1} (-1)^k a(n-k)| ≤ a 0
  -- Use sum_range_reflect to reindex: ∑_{k<n+1} f(n-k) = ∑_{k<n+1} f(k)
  -- where f(k) = (-1)^k * a(n-k)... but that doesn't directly help.
  -- Instead, directly rewrite ∑(-1)^k a(n-k) using the reverse sign lemma.
  -- sum_range_reflect gives: ∑_{j<m} f(m-1-j) = ∑_{j<m} f(j)
  -- With m = n+1, f(j) = (-1)^(n-j) * a(j):
  -- ∑_{j<n+1} (-1)^(n-(n-j)) * a(n-j) = ∑_{j<n+1} (-1)^(n-j) * a(j)
  -- LHS = ∑_{j<n+1} (-1)^j * a(n-j) (since n-(n-j) = j for j ≤ n)
  -- So: ∑_{j<n+1} (-1)^j a(n-j) = ∑_{j<n+1} (-1)^(n-j) a(j)
  --                                = (-1)^n · ∑_{j<n+1} (-1)^j a(j)
  -- Therefore |∑(-1)^j a(j)| = |(-1)^n · ∑(-1)^j a(j)| = |∑(-1)^j a(n-j)| ≤ a 0
  have h_reflect : ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * a (n - j)
      = ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - j) * a j := by
    rw [← Finset.sum_range_reflect (fun j => (-1 : ℝ) ^ (n - j) * a j) (n + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    show (-1 : ℝ) ^ j * a (n - j) = (-1 : ℝ) ^ (n - (n - j)) * a (n - j)
    rw [Nat.sub_sub_self hj_le]
  rw [h_reflect, alternating_sum_reverse_sign] at h_last
  rwa [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h_last

end AbelSummation
```

## Full Dependency File: `Littlewood/Aristotle/HardyEstimatesPartial.lean`
```lean
/-
This file was generated by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1de9e757-d492-4eb5-886c-23a29769fca0

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle's budget for this request has been reached.
Partial progress: defines HardyEstimates structure and basic lemmas.
Budget exhausted before main theorem could be proved.

NOTE: Uses Complex.log.im for theta (vs Complex.arg in other Hardy files).
For z ∈ slitPlane, (Complex.log z).im = Complex.arg z, so equivalent.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyEstimatesPartial

/-
Hardy's theta function. This normalizes the phase of zeta on the critical line.
θ(t) = Im(log Γ(1/4 + it/2)) - (t/2) log π
-/
def hardyTheta (t : ℝ) : ℝ :=
  (Complex.log (Complex.Gamma (1/4 + Complex.I * (t/2)))).im - (t/2) * Real.log Real.pi

/-
Hardy's Z function. This is REAL-VALUED on the real line.
Z(t) = exp(iθ(t)) * ζ(1/2 + it)

Key property: Z(t) ∈ ℝ for all t, and Z(t) = 0 ↔ ζ(1/2+it) = 0.
-/
def hardyZ (t : ℝ) : ℝ :=
  (Complex.exp (Complex.I * hardyTheta t) * riemannZeta (1/2 + Complex.I * t)).re

/-
The set of zeros of zeta on the critical line.
-/
def zetaCriticalZeros : Set ℝ :=
  {t : ℝ | riemannZeta (1/2 + Complex.I * t) = 0}

/-
The set of sign changes of a real function.
-/
def signChanges (f : ℝ → ℝ) : Set ℝ :=
  {t : ℝ | ∃ ε > 0, ∃ t₁ t₂, t - ε < t₁ ∧ t₁ < t ∧ t < t₂ ∧ t₂ < t + ε ∧
    f t₁ * f t₂ < 0}

/-
The exponential factor has modulus 1.
-/
lemma exp_iTheta_norm (t : ℝ) :
    ‖Complex.exp (Complex.I * hardyTheta t)‖ = 1 := by
      norm_num [ Complex.norm_exp ]

/-
Structure capturing the key analytic estimates and properties required for Hardy's theorem.
-/
structure HardyEstimates where
  mean_square_lower : ∃ c > 0, ∃ T₀ > 0, ∀ T ≥ T₀,
    c * T * Real.log T ≤ ∫ t in Set.Ioc 1 T, (hardyZ t)^2
  first_moment_upper : ∀ ε > 0, ∃ C > 0, ∃ T₀ > 0, ∀ T ≥ T₀,
    |∫ t in Set.Ioc 1 T, hardyZ t| ≤ C * T^(1/2 + ε)
  hardyZ_continuous : Continuous hardyZ

end HardyEstimatesPartial
```

## Full Dependency File: `Littlewood/Aristotle/HardyNProperties.lean`
```lean
/- 
Elementary properties of `hardyN` / `hardyStart`.
-/

import Mathlib
import Littlewood.Aristotle.HardyZMeasurability

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.HardyNProperties

open Real
open HardyEstimatesPartial

/-- Explicit formula for `hardyStart`. -/
theorem hardyStart_formula (k : ℕ) :
    hardyStart k = 2 * Real.pi * ((k + 1 : ℝ)) ^ 2 := by
  simp [hardyStart]

/-- `hardyN` is constant on each breakpoint block `[hardyStart k, hardyStart (k+1))`. -/
theorem hardyN_constant_on_block (k : ℕ) (t : ℝ)
    (ht : hardyStart k ≤ t) (ht' : t < hardyStart (k + 1)) :
    hardyN t = k + 1 := by
  have h_start_nonneg : 0 ≤ hardyStart k := by
    simp [hardyStart]
    positivity
  have ht_nonneg : 0 ≤ t := le_trans h_start_nonneg ht
  have h_low : k < hardyN t := (hardyN_lt_iff k t ht_nonneg).2 ht
  have h_not_high : ¬ (k + 1 < hardyN t) := by
    intro h
    have h_le : hardyStart (k + 1) ≤ t := (hardyN_lt_iff (k + 1) t ht_nonneg).1 h
    linarith
  exact Nat.le_antisymm (Nat.not_lt.mp h_not_high) (Nat.succ_le_of_lt h_low)

/-- A convenient global upper bound: `hardyN T + 1 ≤ T^(1/2)` for `T ≥ 2`. -/
theorem hardyN_le_sqrt (T : ℝ) (hT : T ≥ 2) :
    ((hardyN T : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) := by
  have hT_nonneg : 0 ≤ T := by linarith
  have h_floor :
      (hardyN T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) := by
    exact Nat.floor_le (Real.sqrt_nonneg _)
  by_cases hN0 : hardyN T = 0
  ·
    have hT_ge_one : (1 : ℝ) ≤ T := by linarith
    have h1 : (1 : ℝ) ≤ T ^ (1 / 2 : ℝ) := Real.one_le_rpow hT_ge_one (by norm_num)
    simpa [hN0] using h1
  · have hN1 : 1 ≤ hardyN T := Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr hN0)
    have hN1_real : (1 : ℝ) ≤ (hardyN T : ℝ) := by exact_mod_cast hN1
    have h_lhs_two :
        ((hardyN T : ℝ) + 1) ≤ 2 * (hardyN T : ℝ) := by
      nlinarith
    have h_two_floor :
        (2 : ℝ) * (hardyN T : ℝ) ≤ 2 * Real.sqrt (T / (2 * Real.pi)) := by
      exact mul_le_mul_of_nonneg_left h_floor (by positivity)
    have h_const : (2 : ℝ) / Real.sqrt (2 * Real.pi) ≤ 1 := by
      have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
      have h2_le_sqrt : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
        have hsq : (2 : ℝ) ^ 2 ≤ (Real.sqrt (2 * Real.pi)) ^ 2 := by
          calc
            (2 : ℝ) ^ 2 = 4 := by ring
            _ ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
            _ = (Real.sqrt (2 * Real.pi)) ^ 2 := by
              symm
              exact Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
        nlinarith [hsq, Real.sqrt_nonneg (2 * Real.pi)]
      exact (div_le_iff₀ h_sqrt_pos).2 (by simpa using h2_le_sqrt)
    have h_sqrt_div :
        Real.sqrt (T / (2 * Real.pi)) = Real.sqrt T / Real.sqrt (2 * Real.pi) := by
      rw [Real.sqrt_div hT_nonneg]
    have h_two_sqrt :
        2 * Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T := by
      rw [h_sqrt_div]
      calc
        2 * (Real.sqrt T / Real.sqrt (2 * Real.pi))
            = ((2 : ℝ) / Real.sqrt (2 * Real.pi)) * Real.sqrt T := by
              ring
        _ ≤ 1 * Real.sqrt T := by
              exact mul_le_mul_of_nonneg_right h_const (Real.sqrt_nonneg _)
        _ = Real.sqrt T := by ring
    calc
      ((hardyN T : ℝ) + 1) ≤ 2 * (hardyN T : ℝ) := h_lhs_two
      _ ≤ 2 * Real.sqrt (T / (2 * Real.pi)) := h_two_floor
      _ ≤ Real.sqrt T := h_two_sqrt
      _ = T ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]

/-- Exact length of one breakpoint block. -/
theorem block_length (k : ℕ) :
    hardyStart (k + 1) - hardyStart k = 2 * Real.pi * (2 * (k : ℝ) + 3) := by
  simp [hardyStart]
  ring

end Aristotle.HardyNProperties
```

## Full Dependency File: `Littlewood/Aristotle/HardyZCauchySchwarz.lean`
```lean
/-
Integrated from Aristotle output d7cdd34c-76c2-4f83-bfdb-dd88618d143e.
Hardy Z Cauchy-Schwarz + alternative formula.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

KEY RESULTS (ALL PROVED - 0 sorries):
- integral_cauchy_schwarz: Cauchy-Schwarz for integrals on Ioc
- exp_im_log_eq_div_abs: exp(i·Im(log z)) = z/‖z‖
- hardyZ_eq_alt: alternative formula for Z
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace HardyEstimatesPartial

lemma integral_cauchy_schwarz (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : IntegrableOn f (Ioc a b)) (hf2 : IntegrableOn (fun t => f t ^ 2) (Ioc a b)) :
    (∫ t in Ioc a b, |f t|)^2 ≤ (b - a) * ∫ t in Ioc a b, (f t)^2 := by
  have h_cauchy_schwarz : (∫ t in Set.Ioc a b, (abs (f t) - (∫ u in Set.Ioc a b, abs (f u)) / (b - a)) ^ 2) ≥ 0 := by
    exact MeasureTheory.integral_nonneg fun t => sq_nonneg _;
  simp_all +decide [ sub_sq, MeasureTheory.integral_sub, MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul ];
  rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ] at h_cauchy_schwarz;
  · simp_all +decide [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, le_of_lt hab ];
    nlinarith [ mul_div_cancel₀ ( ∫ t in Set.Ioc a b, |f t| ) ( sub_ne_zero_of_ne hab.ne' ) ];
  · exact hf2;
  · exact MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( hf.norm ) _ ) _;
  · exact MeasureTheory.Integrable.sub hf2 ( MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( hf.norm ) _ ) _ );
  · norm_num

lemma exp_im_log_eq_div_abs {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (I * (Complex.log z).im) = z / ↑‖z‖ := by
      have h_euler : Complex.exp (Complex.I * Complex.arg z) = Complex.cos (Complex.arg z) + Complex.I * Complex.sin (Complex.arg z) := by
        convert Complex.exp_mul_I _ using 2 <;> ring;
      have h_div : z / ‖z‖ = Complex.cos (Complex.arg z) + Complex.I * Complex.sin (Complex.arg z) := by
        have h_div : z = ‖z‖ * Complex.exp (Complex.I * Complex.arg z) := by
          nth_rw 1 [ ← Complex.norm_mul_exp_arg_mul_I z ] ; ring;
        grind;
      convert h_euler using 2 ; norm_num [ Complex.log_im ]

lemma hardyZ_eq_alt (t : ℝ) :
    hardyZ t = ((Complex.Gamma (1/4 + I * (t/2))) / ↑‖Complex.Gamma (1/4 + I * (t/2))‖ *
    Complex.exp (-I * (t/2) * Real.log Real.pi) * riemannZeta (1/2 + I * t)).re := by
      have h_exp : Complex.exp (Complex.I * hardyTheta t) = (Complex.Gamma (1 / 4 + Complex.I * (t / 2))) / ‖Complex.Gamma (1 / 4 + Complex.I * (t / 2))‖ * Complex.exp (-Complex.I * (t / 2) * Real.log Real.pi) := by
        have h_exp : Complex.exp (Complex.I * hardyTheta t) = Complex.exp (Complex.I * (Complex.log (Complex.Gamma (1/4 + Complex.I * (t/2)))).im - Complex.I * (t/2) * Real.log Real.pi) := by
          simp [hardyTheta];
          ring;
        have h_exp : Complex.exp (Complex.I * (Complex.log (Complex.Gamma (1/4 + Complex.I * (t/2)))).im) = Complex.Gamma (1/4 + Complex.I * (t/2)) / ‖Complex.Gamma (1/4 + Complex.I * (t/2))‖ := by
          convert exp_im_log_eq_div_abs _ using 1;
          exact Complex.Gamma_ne_zero_of_re_pos ( by norm_num [ Complex.add_re, Complex.mul_re ] );
        simp_all +decide [ mul_assoc, ← Complex.exp_add ];
        rw [ ← h_exp, ← Complex.exp_add ] ; ring;
      exact h_exp ▸ rfl

end HardyEstimatesPartial
```

## Full Dependency File: `Littlewood/Aristotle/HardyZFirstMoment.lean`
```lean
/-
Integrated from Aristotle output 02ebb71b-1b17-4bd6-adb0-04a4bc289ecb.
Hardy Z first moment infrastructure.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

KEY RESULTS (ALL PROVED - 0 sorries):
- hardyZ_abs_le: |Z(t)| ≤ ‖ζ(1/2+it)‖
- hardyZ_first_moment_crude: ∃ C > 0, |∫ Z| ≤ C·T
- MainTerm / ErrorTerm: approximate functional equation decomposition
- hardyZ_first_moment_bound_conditional: conditional first moment O(T^{1/2+ε})
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZMeasurability

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace HardyEstimatesPartial

/-
The exponential factor has modulus 1 (alternate name for compatibility).
-/
private lemma exp_iTheta_abs (t : ℝ) : ‖Complex.exp (I * hardyTheta t)‖ = 1 :=
  exp_iTheta_norm t

/-
Z equals the real part of exp(iθ)ζ, which equals |ζ| times a phase factor. So |Z(t)| ≤ |ζ(1/2+it)|
-/
lemma hardyZ_abs_le (t : ℝ) : |hardyZ t| ≤ ‖riemannZeta (1/2 + I * t)‖ := by
  unfold hardyZ
  calc |(Complex.exp (I * hardyTheta t) * riemannZeta (1/2 + I * t)).re|
       ≤ ‖Complex.exp (I * hardyTheta t) * riemannZeta (1/2 + I * t)‖ :=
           Complex.abs_re_le_norm _
       _ = ‖Complex.exp (I * hardyTheta t)‖ * ‖riemannZeta (1/2 + I * t)‖ :=
           Complex.norm_mul _ _
       _ = 1 * ‖riemannZeta (1/2 + I * t)‖ := by rw [exp_iTheta_abs]
       _ = ‖riemannZeta (1/2 + I * t)‖ := one_mul _

/-
Crude first moment bound
-/
theorem hardyZ_first_moment_crude (T : ℝ) (hT : T ≥ 2) :
    ∃ C > 0, |∫ t in Ioc 1 T, hardyZ t| ≤ C * T := by
  refine' ⟨ ( |∫ t in Set.Ioc 1 T, hardyZ t| + 1 ) / ( T ), _, _ ⟩;
  · exact div_pos ( add_pos_of_nonneg_of_pos ( abs_nonneg _ ) zero_lt_one ) ( by positivity );
  · rw [ div_mul_cancel₀ _ ( by positivity ) ] ; linarith

/-
Main term of the approximate functional equation for Z(t)
-/
def MainTerm (t : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
    (n + 1 : ℝ) ^ (-(1/2 : ℝ)) * Real.cos (hardyTheta t - t * Real.log (n + 1))

/-
Error term of the approximate functional equation for Z(t)
-/
def ErrorTerm (t : ℝ) : ℝ := hardyZ t - MainTerm t

lemma MainTerm_eq_hardySum : MainTerm = hardySum := by
  funext t
  simp [MainTerm, hardySum, hardyN]

lemma ErrorTerm_eq_hardyRemainder : ErrorTerm = hardyRemainder := by
  funext t
  simp [ErrorTerm, hardyRemainder, MainTerm_eq_hardySum]

lemma mainTerm_integrable (T : ℝ) : IntegrableOn MainTerm (Ioc 1 T) := by
  simpa [MainTerm_eq_hardySum] using hardySum_integrable T

lemma errorTerm_integrable (T : ℝ) : IntegrableOn ErrorTerm (Ioc 1 T) := by
  simpa [ErrorTerm_eq_hardyRemainder] using hardyRemainder_integrable T

/-
Conditional first moment bound assuming bounds on MainTerm and ErrorTerm
-/
theorem hardyZ_first_moment_bound_conditional (ε : ℝ) (_hε : ε > 0)
    (h_integrable_main : ∀ T ≥ 1, IntegrableOn MainTerm (Ioc 1 T))
    (h_integrable_error : ∀ T ≥ 1, IntegrableOn ErrorTerm (Ioc 1 T))
    (h_main_bound : ∃ C₁ > 0, ∀ T ≥ 2, |∫ t in Ioc 1 T, MainTerm t| ≤ C₁ * T^(1/2 + ε))
    (h_error_bound : ∃ C₂ > 0, ∀ T ≥ 2, |∫ t in Ioc 1 T, ErrorTerm t| ≤ C₂ * T^(1/2 + ε)) :
    ∃ C > 0, ∃ T₀ > 0, ∀ T ≥ T₀, |∫ t in Ioc 1 T, hardyZ t| ≤ C * T^(1/2 + ε) := by
      obtain ⟨C₁, hC₁_pos, hC₁⟩ := h_main_bound
      obtain ⟨C₂, hC₂_pos, hC₂⟩ := h_error_bound
      use C₁ + C₂, by linarith, 2, by linarith;
      have h_split : ∀ T ≥ 2, ∫ t in Set.Ioc 1 T, hardyZ t = (∫ t in Set.Ioc 1 T, MainTerm t) + (∫ t in Set.Ioc 1 T, ErrorTerm t) := by
        intro T hT; rw [ ← MeasureTheory.integral_add ( h_integrable_main T ( by linarith ) ) ( h_integrable_error T ( by linarith ) ) ] ; exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by unfold ErrorTerm; ring;
      exact fun T hT => by rw [ h_split T hT ] ; exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp ( hC₁ T hT ), abs_le.mp ( hC₂ T hT ), Real.rpow_pos_of_pos ( by linarith : 0 < T ) ( 1 / 2 + ε ) ], by nlinarith [ abs_le.mp ( hC₁ T hT ), abs_le.mp ( hC₂ T hT ), Real.rpow_pos_of_pos ( by linarith : 0 < T ) ( 1 / 2 + ε ) ] ⟩ ;

theorem hardyZ_first_moment_bound_conditional_two_bounds (ε : ℝ) (hε : ε > 0)
    (h_main_bound : ∃ C₁ > 0, ∀ T ≥ 2, |∫ t in Ioc 1 T, MainTerm t| ≤ C₁ * T^(1/2 + ε))
    (h_error_bound : ∃ C₂ > 0, ∀ T ≥ 2, |∫ t in Ioc 1 T, ErrorTerm t| ≤ C₂ * T^(1/2 + ε)) :
    ∃ C > 0, ∃ T₀ > 0, ∀ T ≥ T₀, |∫ t in Ioc 1 T, hardyZ t| ≤ C * T^(1/2 + ε) := by
  refine hardyZ_first_moment_bound_conditional ε hε ?_ ?_ h_main_bound h_error_bound
  · intro T hT
    exact mainTerm_integrable T
  · intro T hT
    exact errorTerm_integrable T

end HardyEstimatesPartial
```

## Full Dependency File: `Littlewood/Aristotle/HardyZMeasurability.lean`
```lean
/-
Integrated from Aristotle output af770898-b0c2-4f99-8c30-d87eb4516b46.
Hardy Z measurability, integrability, and integral decomposition infrastructure.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

KEY RESULTS:
- hardyN: approximate functional equation truncation point
- hardySum: main sum in the approximate functional equation for Z(t)
- hardyN_measurable, hardyTheta_measurable, hardyTerm_measurable, hardySum_measurable
- hardySum_bounded, hardySum_integrable, hardyZ_integrable, hardyRemainder_integrable
- hardySum_integral_eq: interchange of integral and sum for ∫Z
- hardyPhase_continuous: continuity of the Hardy phase factor
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZCauchySchwarz

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace HardyEstimatesPartial

/-
The truncation point for the approximate functional equation: N(t) = ⌊√(t/2π)⌋.
-/
noncomputable def hardyN (t : ℝ) : ℕ := Nat.floor (Real.sqrt (t / (2 * Real.pi)))

/-
The main sum in the approximate functional equation for Z(t).
-/
noncomputable def hardySum (t : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range (hardyN t), ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * Real.cos (hardyTheta t - t * Real.log (n + 1))

/-
The remainder term: Z(t) - main sum.
-/
noncomputable def hardyRemainder (t : ℝ) : ℝ := hardyZ t - hardySum t

lemma hardyZ_split (t : ℝ) : hardyZ t = hardySum t + hardyRemainder t := by
  simp [hardyRemainder]

/-
Individual term in the main sum.
-/
noncomputable def hardyTerm (n : ℕ) (t : ℝ) : ℝ :=
  ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * Real.cos (hardyTheta t - t * Real.log (n + 1))

lemma hardyN_measurable : Measurable hardyN := by
  convert Measurable.comp ( show Measurable ( fun t => Nat.floor t ) from _ ) ( show Measurable ( fun t => Real.sqrt ( t / ( 2 * Real.pi ) ) ) from _ ) using 1;
  · exact measurable_id'.nat_floor;
  · exact Measurable.sqrt ( measurable_id'.div_const _ )

lemma hardyTheta_measurable : Measurable hardyTheta := by
  apply_rules [ Measurable.sub, Measurable.mul, measurable_id, measurable_const ];
  have h_arg_measurable : Measurable (fun a : ℝ => Complex.Gamma (1 / 4 + Complex.I * (a / 2))) := by
    refine' Continuous.measurable _;
    refine' continuous_iff_continuousAt.mpr _;
    intro x;
    refine' ( Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.continuousAt ) |> ContinuousAt.comp <| Continuous.continuousAt <| by continuity;
    norm_num [ Complex.ext_iff ];
    exact fun m hm => by linarith;
  exact Measurable.comp ( Complex.measurable_im ) ( Complex.measurable_log.comp h_arg_measurable )

lemma hardyTerm_measurable (n : ℕ) : Measurable (fun t => hardyTerm n t) := by
  apply_rules [ Measurable.mul, Measurable.cos, measurableSet_Iic ];
  · exact measurable_const;
  · exact Measurable.sub ( hardyTheta_measurable ) ( measurable_id.mul_const _ )

lemma hardySum_measurable : Measurable hardySum := by
  refine' measurable_of_tendsto_metrizable ( fun n => _ ) _;
  exact fun n t => ∑ i ∈ Finset.range n, ( if i < Nat.floor ( Real.sqrt ( t / ( 2 * Real.pi ) ) ) then 2 * ( ( i + 1 : ℝ ) ^ ( - ( 1 / 2 : ℝ ) ) ) * Real.cos ( hardyTheta t - t * Real.log ( i + 1 ) ) else 0 );
  · refine' Finset.measurable_sum _ fun i _ => _;
    exact Measurable.ite ( measurableSet_lt measurable_const <| by exact Measurable.nat_floor <| by exact Measurable.sqrt <| by exact measurable_id'.div_const _ ) ( by exact Measurable.mul ( by exact measurable_const ) <| Real.continuous_cos.measurable.comp <| by exact Measurable.sub ( hardyTheta_measurable ) <| by exact measurable_id'.mul <| by exact measurable_const ) measurable_const;
  · refine' tendsto_pi_nhds.mpr _;
    intro x;
    convert Summable.hasSum _ |> HasSum.tendsto_sum_nat using 1;
    rw [ tsum_eq_sum ];
    any_goals exact Finset.range ⌊Real.sqrt ( x / ( 2 * Real.pi ) ) ⌋₊;
    · rw [ Finset.sum_congr rfl fun i hi => if_pos <| Finset.mem_range.mp hi ];
      unfold hardySum;
      unfold hardyN; norm_num [ mul_assoc, Finset.mul_sum _ _ _ ] ;
    · grind;
    · refine' summable_of_ne_finset_zero _;
      exacts [ Finset.range ⌊Real.sqrt ( x / ( 2 * Real.pi ) ) ⌋₊, fun n hn => if_neg <| by simpa using hn ]

lemma hardySum_bounded (T : ℝ) : ∃ M : ℝ, ∀ t ∈ Set.Ioc 1 T, |hardySum t| ≤ M := by
  use 2 * ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (T / (2 * Real.pi)))), ((n + 1 : ℝ) ^ (-(1/2 : ℝ)));
  intros t ht
  have hN_bound : hardyN t ≤ Nat.floor (Real.sqrt (T / (2 * Real.pi))) := by
    exact Nat.floor_mono <| Real.sqrt_le_sqrt <| div_le_div_of_nonneg_right ht.2 <| by positivity;
  rw [ abs_le ];
  constructor <;> rw [ hardySum ];
  · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun i hi => show ( ( i : ℝ ) + 1 ) ^ ( - ( 1 / 2 : ℝ ) ) * Real.cos ( hardyTheta t - t * Real.log ( i + 1 ) ) ≥ - ( ( i : ℝ ) + 1 ) ^ ( - ( 1 / 2 : ℝ ) ) from _ ) zero_le_two );
    · norm_num [ Finset.sum_neg_distrib ];
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hN_bound ) fun _ _ _ => by positivity;
    · nlinarith [ Real.neg_one_le_cos ( hardyTheta t - t * Real.log ( i + 1 ) ), Real.rpow_pos_of_pos ( by linarith : 0 < ( i : ℝ ) + 1 ) ( - ( 1 / 2 ) ) ];
  · exact mul_le_mul_of_nonneg_left ( le_trans ( Finset.sum_le_sum fun _ _ => mul_le_of_le_one_right ( by positivity ) ( Real.cos_le_one _ ) ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hN_bound ) fun _ _ _ => by positivity ) ) zero_le_two

lemma hardySum_integrable (T : ℝ) : MeasureTheory.IntegrableOn hardySum (Set.Ioc 1 T) MeasureTheory.volume := by
  have h_integrable : MeasureTheory.IntegrableOn (fun t => hardySum t) (Set.Ioc 1 T) := by
    have h_bounded : ∃ M : ℝ, ∀ t ∈ Set.Ioc 1 T, |hardySum t| ≤ M :=
      hardySum_bounded T
    refine' MeasureTheory.Integrable.mono' _ _ _;
    exacts [ fun _ => h_bounded.choose, Continuous.integrableOn_Ioc ( by continuity ), ( hardySum_measurable.aestronglyMeasurable ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun x hx => h_bounded.choose_spec x hx ];
  convert h_integrable using 1

/-
exp(i · Im(log z)) = z / ‖z‖ for z ≠ 0.
-/
lemma exp_im_log_eq_div_norm (z : ℂ) (hz : z ≠ 0) :
  Complex.exp (Complex.I * (Complex.log z).im) = z / ↑‖z‖ := by
  simp +decide [ Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
  simp +decide [ mul_div_mul_right, hz, Complex.cos_arg, Complex.sin_arg ]

/-
The Hardy phase factor Γ(s)/|Γ(s)| · exp(-it/2 · log π).
-/
noncomputable def hardyPhase (t : ℝ) : ℂ :=
  let s := 1/4 + Complex.I * (t/2)
  (Complex.Gamma s / ↑‖Complex.Gamma s‖) * Complex.exp (-Complex.I * (t/2) * Real.log Real.pi)

/-
Alternative formula for Z(t) using the phase factor.
-/
noncomputable def hardyZ_alt (t : ℝ) : ℝ :=
  let s := 1/4 + Complex.I * (t/2)
  let G := Complex.Gamma s
  let phase := (G / ↑‖G‖) * Complex.exp (-Complex.I * (t/2) * Real.log Real.pi)
  (phase * riemannZeta (1/2 + Complex.I * t)).re

lemma hardyZ_eq_hardyZ_alt (t : ℝ) : hardyZ t = hardyZ_alt t := by
  have h_exp : Complex.exp (Complex.I * hardyTheta t) = (Complex.Gamma (1/4 + Complex.I * (t/2)) / ↑‖Complex.Gamma (1/4 + Complex.I * (t/2))‖) * Complex.exp (-Complex.I * (t/2) * Real.log Real.pi) := by
    have h_exp : Complex.exp (Complex.I * (Complex.log (Complex.Gamma (1 / 4 + Complex.I * (t / 2)))).im) = Complex.Gamma (1 / 4 + Complex.I * (t / 2)) / ↑‖Complex.Gamma (1 / 4 + Complex.I * (t / 2))‖ := by
      convert exp_im_log_eq_div_norm _ _ using 1;
      exact Complex.Gamma_ne_zero_of_re_pos ( by norm_num [ Complex.add_re, Complex.div_re, Complex.mul_re ] );
    convert congr_arg ( fun x : ℂ => x * Complex.exp ( - ( Complex.I * t * Real.log Real.pi / 2 ) ) ) h_exp using 1 <;> ring;
    rw [ ← Complex.exp_add ] ; norm_cast ; norm_num [ mul_assoc, mul_comm, mul_left_comm, hardyTheta ] ; ring;
    norm_num [ Rat.divInt_eq_div ];
  convert congr_arg Complex.re ( congrArg ( fun x => x * riemannZeta ( 1 / 2 + Complex.I * t ) ) h_exp ) using 1

/-
The starting point where term n enters the sum: t₀(n) = 2π(n+1)².
-/
noncomputable def hardyStart (n : ℕ) : ℝ := 2 * Real.pi * (n + 1)^2

lemma hardyN_lt_iff (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
  n < hardyN t ↔ hardyStart n ≤ t := by
  rw [ show hardyN t = Nat.floor ( Real.sqrt ( t / ( 2 * Real.pi ) ) ) by rfl ];
  rw [ Nat.lt_iff_add_one_le, Nat.le_floor_iff ( by positivity ), Real.le_sqrt ] <;> norm_num [ ht, Real.pi_pos.le ];
  · rw [ le_div_iff₀ ( by positivity ), mul_comm ] ; norm_cast ; aesop;
  · positivity;
  · positivity

noncomputable def hardyCos (n : ℕ) (t : ℝ) : ℝ := Real.cos (hardyTheta t - t * Real.log (n + 1))

noncomputable def hardySumInt (T : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range (hardyN T), ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * ∫ t in Set.Ioc (hardyStart n) T, hardyCos n t

lemma hardyPhase_continuous : Continuous hardyPhase := by
  refine' Continuous.mul _ _;
  · refine' Continuous.div _ _ _;
    · refine' continuous_iff_continuousAt.mpr _;
      intro x;
      refine' Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.continuousAt |> ContinuousAt.comp <| Continuous.continuousAt <| by continuity;
      norm_num [ Complex.ext_iff ];
      exact fun m hm => by linarith;
    · refine' Complex.continuous_ofReal.comp _;
      refine' Continuous.norm _;
      refine' continuous_iff_continuousAt.mpr fun x => _;
      refine' ( Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.continuousAt ) |> ContinuousAt.comp <| Continuous.continuousAt <| by continuity;
      norm_num [ Complex.ext_iff ];
      exact fun m hm => by linarith;
    · norm_num [ Complex.Gamma_ne_zero ];
      exact fun x => Complex.Gamma_ne_zero_of_re_pos ( by norm_num [ Complex.add_re, Complex.mul_re, Complex.div_re ] );
  · fun_prop

/-
Indicator version of hardyTerm: nonzero only when n < hardyN(t).
-/
noncomputable def hardyTermIndicator (n : ℕ) (t : ℝ) : ℝ :=
  if n < hardyN t then hardyTerm n t else 0

lemma hardySum_eq_sum_indicator (t : ℝ) :
  hardySum t = 2 * ∑' n : ℕ, hardyTermIndicator n t := by
  rw [ tsum_eq_sum ];
  any_goals exact Finset.range ( hardyN t );
  · unfold hardySum hardyTermIndicator; ring;
    exact congrArg₂ _ ( Finset.sum_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_range.mp hx ) ] ; unfold hardyTerm; ring ) rfl;
  · unfold hardyTermIndicator; aesop

lemma hardySum_eq_finite_sum_indicator (T : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 1 T) :
  hardySum t = 2 * ∑ n ∈ Finset.range (hardyN T), hardyTermIndicator n t := by
  have hN : hardyN t ≤ hardyN T := by
    exact Nat.floor_mono <| Real.sqrt_le_sqrt <| div_le_div_of_nonneg_right ht.2 <| by positivity;
  have h_sum_eq : ∑ n ∈ Finset.range (hardyN T), hardyTermIndicator n t = ∑ n ∈ Finset.range (hardyN t), hardyTermIndicator n t := by
    rw [ ← Finset.sum_subset ( Finset.range_mono hN ) ];
    unfold hardyTermIndicator; aesop;
  rw [ h_sum_eq, ← Finset.sum_congr rfl fun n hn => ?_ ];
  convert hardySum_eq_sum_indicator t using 1;
  rw [ tsum_eq_sum ];
  · unfold hardyTermIndicator; aesop;
  · rfl

lemma hardyTermIndicator_zero_of_ge (n : ℕ) (T : ℝ) (hn : hardyN T ≤ n) :
  ∀ t ∈ Set.Ioc 1 T, hardyTermIndicator n t = 0 := by
  have h_le : ∀ t ∈ Set.Ioc 1 T, hardyN t ≤ hardyN T := by
    exact fun t ht => Nat.floor_mono <| Real.sqrt_le_sqrt <| div_le_div_of_nonneg_right ht.2 <| by positivity;
  exact fun t ht => if_neg <| not_lt_of_ge <| le_trans ( h_le t ht ) hn

lemma hardyTermIndicator_eq_of_lt (n : ℕ) (T : ℝ) (hn : n < hardyN T) :
  ∀ t ∈ Set.Ioc 1 T, hardyTermIndicator n t = if hardyStart n ≤ t then hardyTerm n t else 0 := by
  have h_indicator_eq : ∀ t ∈ Set.Ioc (1 : ℝ) T, n < hardyN t ↔ hardyStart n ≤ t := by
    intros t ht
    have h_indicator_eq : n < hardyN t ↔ hardyStart n ≤ t := by
      convert hardyN_lt_iff n t ( by linarith [ ht.1 ] ) using 1
    exact h_indicator_eq;
  unfold hardyTermIndicator; aesop;

lemma hardyTermIndicator_integral_of_ge (n : ℕ) (T : ℝ) (hT : 1 ≤ T) (hn : hardyN T ≤ n) :
  ∫ t in Set.Ioc 1 T, hardyTermIndicator n t = 0 := by
  have h_zero : ∀ t ∈ Set.Ioc 1 T, hardyTermIndicator n t = 0 :=
    hardyTermIndicator_zero_of_ge n T hn
  exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero h_zero

lemma hardyTermIndicator_integral_of_lt (n : ℕ) (T : ℝ) (hT : 1 ≤ T) (hn : n < hardyN T) :
  ∫ t in Set.Ioc 1 T, hardyTermIndicator n t = ∫ t in Set.Ioc (hardyStart n) T, hardyTerm n t := by
  have h_integral_support : ∫ t in Set.Ioc 1 T, hardyTermIndicator n t = ∫ t in Set.Ioc (hardyStart n) T ∩ Set.Ioc 1 T, hardyTerm n t := by
    have h_indicator_eq : ∀ t ∈ Set.Ioc 1 T, hardyTermIndicator n t = if hardyStart n ≤ t then hardyTerm n t else 0 :=
      hardyTermIndicator_eq_of_lt n T hn
    rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    rw [ ← MeasureTheory.integral_congr_ae ];
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.1 ( MeasureTheory.measure_singleton ( hardyStart n ) ) ] with x hxop;
    grind;
  rw [ h_integral_support, Set.inter_eq_left.mpr ];
  refine' Set.Ioc_subset_Ioc _ le_rfl;
  exact one_le_mul_of_one_le_of_one_le ( by linarith [ Real.pi_gt_three ] ) ( by ring_nf; nlinarith [ Real.pi_gt_three ] )

/-
Key theorem: the integral of hardySum equals the sum of individual term integrals.
∫₁ᵀ hardySum(t) dt = 2 Σₙ (n+1)^{-1/2} ∫_{t₀(n)}^T cos(θ(t) - t log(n+1)) dt
-/
lemma hardySum_integral_eq (T : ℝ) (hT : 1 ≤ T) :
  ∫ t in Set.Ioc 1 T, hardySum t = hardySumInt T := by
  have h_sum_eq : ∫ t in Set.Ioc 1 T, hardySum t = ∫ t in Set.Ioc 1 T, 2 * ∑ n ∈ Finset.range (hardyN T), hardyTermIndicator n t := by
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => hardySum_eq_finite_sum_indicator T t ht ▸ rfl;
  rw [ h_sum_eq, MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum ];
  · rw [ Finset.sum_congr rfl fun i hi => ?_ ];
    rotate_left;
    use fun n => ∫ t in Set.Ioc ( hardyStart n ) T, hardyTerm n t;
    · rw [ ← hardyTermIndicator_integral_of_lt i T hT ];
      exact Finset.mem_range.mp hi;
    · unfold hardyTerm; norm_num [ mul_assoc, MeasureTheory.integral_const_mul ] ;
      rfl;
  · intro n hn;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun t => ( n + 1 : ℝ ) ^ ( - ( 1 / 2 : ℝ ) );
    · norm_num;
    · refine' Measurable.aestronglyMeasurable _;
      refine' Measurable.ite _ _ _;
      · exact measurableSet_lt measurable_const ( hardyN_measurable );
      · exact hardyTerm_measurable n;
      · exact measurable_const;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht;
      unfold hardyTermIndicator;
      unfold hardyTerm;
      split_ifs <;> norm_num;
      · rw [ abs_of_nonneg ( by positivity ) ] ; exact mul_le_of_le_one_right ( by positivity ) ( Real.abs_cos_le_one _ );
      · positivity

/-
Z(t) is integrable on (1, T].
-/
lemma hardyZ_integrable (T : ℝ) : MeasureTheory.IntegrableOn hardyZ (Set.Ioc 1 T) MeasureTheory.volume := by
  have h_cont : Continuous (fun t => hardyZ t) := by
    have h_simplified : ∀ t, hardyZ t = (hardyPhase t * riemannZeta (1 / 2 + Complex.I * t)).re := by
      convert hardyZ_eq_hardyZ_alt using 1;
    simp +decide only [h_simplified];
    refine' Complex.continuous_re.comp _;
    refine' Continuous.mul _ _;
    · exact hardyPhase_continuous;
    · refine' continuous_iff_continuousAt.mpr _;
      intro t;
      refine' ContinuousAt.comp ( show ContinuousAt ( fun s : ℂ => riemannZeta s ) _ from _ ) _;
      · refine' ( differentiableAt_riemannZeta _ ).continuousAt;
        norm_num [ Complex.ext_iff ];
      · exact Continuous.continuousAt ( by continuity );
  exact h_cont.integrableOn_Ioc

/-
The remainder Z(t) - hardySum(t) is integrable on (1, T].
-/
lemma hardyRemainder_integrable (T : ℝ) : MeasureTheory.IntegrableOn hardyRemainder (Set.Ioc 1 T) MeasureTheory.volume := by
  exact MeasureTheory.Integrable.sub ( hardyZ_integrable T ) ( hardySum_integrable T )

/-
The cosine integral for term n.
-/
noncomputable def hardyCosIntegral (n : ℕ) (T : ℝ) : ℝ := ∫ t in Set.Ioc (hardyStart n) T, hardyCos n t

end HardyEstimatesPartial
```

## Full Dependency File: `Littlewood/Aristotle/IntervalPartition.lean`
```lean
/- 
Finite interval-partition lemmas for set integrals on `Ioc`.

These lemmas are lightweight infrastructure for decomposing
`∫ t in Ioc a b, f t` across adjacent breakpoints.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.IntervalPartition

open MeasureTheory Set

/-- Split a set integral across a single adjacent breakpoint. -/
theorem integral_split_at (f : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hf1 : IntegrableOn f (Set.Ioc a b)) (hf2 : IntegrableOn f (Set.Ioc b c)) :
    ∫ t in Set.Ioc a c, f t ∂volume =
      ∫ t in Set.Ioc a b, f t ∂volume + ∫ t in Set.Ioc b c, f t ∂volume := by
  have h_union := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl b))
    measurableSet_Ioc hf1 hf2
  rw [Ioc_union_Ioc_eq_Ioc hab hbc] at h_union
  exact h_union

private lemma bp_zero_le (bp : ℕ → ℝ) :
    ∀ N : ℕ, (∀ k, k < N → bp k ≤ bp (k + 1)) → bp 0 ≤ bp N
  | 0, _ => le_rfl
  | N + 1, h => by
      have h_prev : bp 0 ≤ bp N := bp_zero_le bp N (fun k hk =>
        h k (Nat.lt_trans hk (Nat.lt_succ_self N)))
      exact le_trans h_prev (h N (Nat.lt_succ_self N))

/-- Integrability of `f` on the whole interval from integrability on adjacent blocks. -/
theorem integrableOn_split_finitely (f : ℝ → ℝ) (bp : ℕ → ℝ) :
    ∀ N : ℕ,
      (∀ k, k < N → bp k ≤ bp (k + 1)) →
      (∀ k, k < N → IntegrableOn f (Set.Ioc (bp k) (bp (k + 1)))) →
      IntegrableOn f (Set.Ioc (bp 0) (bp N))
  | 0, _, _ => by
      simpa using (integrableOn_empty : IntegrableOn f (∅ : Set ℝ))
  | N + 1, h_mono, h_int => by
      have h_monoN : ∀ k, k < N → bp k ≤ bp (k + 1) := by
        intro k hk
        exact h_mono k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have h_intN : ∀ k, k < N → IntegrableOn f (Set.Ioc (bp k) (bp (k + 1))) := by
        intro k hk
        exact h_int k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have h_left : IntegrableOn f (Set.Ioc (bp 0) (bp N)) :=
        integrableOn_split_finitely f bp N h_monoN h_intN
      have h_right : IntegrableOn f (Set.Ioc (bp N) (bp (N + 1))) :=
        h_int N (Nat.lt_succ_self N)
      have h_union : IntegrableOn f
          ((Set.Ioc (bp 0) (bp N)) ∪ Set.Ioc (bp N) (bp (N + 1))) :=
        h_left.union h_right
      have h0N : bp 0 ≤ bp N := bp_zero_le bp N h_monoN
      have hN : bp N ≤ bp (N + 1) := h_mono N (Nat.lt_succ_self N)
      have h_set :
          (Set.Ioc (bp 0) (bp N)) ∪ Set.Ioc (bp N) (bp (N + 1))
            = Set.Ioc (bp 0) (bp (N + 1)) :=
        Ioc_union_Ioc_eq_Ioc h0N hN
      simpa [h_set] using h_union

private noncomputable def blockInt (f : ℝ → ℝ) (bp : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∫ t in Set.Ioc (bp k) (bp (k + 1)), f t ∂volume

/-- Split a set integral along finitely many adjacent breakpoints. -/
theorem integral_split_finitely (f : ℝ → ℝ) (bp : ℕ → ℝ) :
    ∀ N : ℕ,
      (∀ k, k < N → bp k ≤ bp (k + 1)) →
      (∀ k, k < N → IntegrableOn f (Set.Ioc (bp k) (bp (k + 1)))) →
      ∫ t in Set.Ioc (bp 0) (bp N), f t ∂volume
        = Finset.sum (Finset.range N) (fun k => blockInt f bp k)
  | 0, _, _ => by
      simp
  | N + 1, h_mono, h_int => by
      have h_monoN : ∀ k, k < N → bp k ≤ bp (k + 1) := by
        intro k hk
        exact h_mono k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have h_intN : ∀ k, k < N → IntegrableOn f (Set.Ioc (bp k) (bp (k + 1))) := by
        intro k hk
        exact h_int k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have h_left_int : IntegrableOn f (Set.Ioc (bp 0) (bp N)) :=
        integrableOn_split_finitely f bp N h_monoN h_intN
      have h_right_int : IntegrableOn f (Set.Ioc (bp N) (bp (N + 1))) :=
        h_int N (Nat.lt_succ_self N)
      have h0N : bp 0 ≤ bp N := bp_zero_le bp N h_monoN
      have hN : bp N ≤ bp (N + 1) := h_mono N (Nat.lt_succ_self N)
      have h_split :
          ∫ t in Set.Ioc (bp 0) (bp (N + 1)), f t ∂volume =
            ∫ t in Set.Ioc (bp 0) (bp N), f t ∂volume +
              ∫ t in Set.Ioc (bp N) (bp (N + 1)), f t ∂volume :=
        integral_split_at f (bp 0) (bp N) (bp (N + 1)) h0N hN h_left_int h_right_int
      calc
        ∫ t in Set.Ioc (bp 0) (bp (N + 1)), f t ∂volume
            = ∫ t in Set.Ioc (bp 0) (bp N), f t ∂volume +
                ∫ t in Set.Ioc (bp N) (bp (N + 1)), f t ∂volume := h_split
        _ = Finset.sum (Finset.range N) (fun k => blockInt f bp k) + blockInt f bp N := by
              rw [integral_split_finitely f bp N h_monoN h_intN]
              rfl
        _ = Finset.sum (Finset.range (N + 1)) (fun k => blockInt f bp k) := by
              rw [Finset.sum_range_succ]

end Aristotle.IntervalPartition
```

## Full Dependency File: `Littlewood/Aristotle/RSBlockDecomposition.lean`
```lean
/-
Riemann-Siegel block decomposition infrastructure.

This file proves the interval-partition wiring for `ErrorTerm` and isolates
the deep RS sign-structure input as `PerBlockSignedBoundHyp` (supplied externally).

SORRY COUNT: 0 (parameterized on PerBlockSignedBoundHyp)
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.IntervalPartition
import Littlewood.Aristotle.HardyNProperties

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RSBlockDecomposition

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

private lemma hardyStart_le_succ (k : ℕ) :
    hardyStart k ≤ hardyStart (k + 1) := by
  have hlen := Aristotle.HardyNProperties.block_length k
  have hnonneg : 0 ≤ 2 * Real.pi * (2 * (k : ℝ) + 3) := by positivity
  linarith

private lemma hardyStart_ge_one (k : ℕ) : (1 : ℝ) ≤ hardyStart k := by
  rw [Aristotle.HardyNProperties.hardyStart_formula]
  have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hsq : (1 : ℝ) ≤ ((k + 1 : ℝ) ^ 2) := by nlinarith [hk1]
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  nlinarith

/-- Decompose the `ErrorTerm` integral into an initial short interval plus
finitely many breakpoint blocks `min T (hardyStart k)`. -/
theorem errorTerm_block_sum (T : ℝ) (hT : T ≥ 2) :
    ∫ t in Ioc 1 T, ErrorTerm t ∂volume =
      ∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t ∂volume
        + Finset.sum (Finset.range (hardyN T))
            (fun k =>
              ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                ErrorTerm t ∂volume) := by
  let bp : ℕ → ℝ := fun k => min T (hardyStart k)
  have h_total_integrable : IntegrableOn ErrorTerm (Ioc 1 T) := errorTerm_integrable T
  have h_bp_mono : ∀ k, k < hardyN T → bp k ≤ bp (k + 1) := by
    intro k _hk
    dsimp [bp]
    exact min_le_min_left T (hardyStart_le_succ k)
  have h_block_integrable :
      ∀ k, k < hardyN T → IntegrableOn ErrorTerm (Ioc (bp k) (bp (k + 1))) := by
    intro k _hk
    refine h_total_integrable.mono_set ?_
    intro x hx
    have hbp_ge_one : (1 : ℝ) ≤ bp k := by
      dsimp [bp]
      exact le_min (by linarith) (hardyStart_ge_one k)
    have hx_lower : 1 < x := lt_of_le_of_lt hbp_ge_one hx.1
    have hx_upper : x ≤ T := le_trans hx.2 (min_le_left T (hardyStart (k + 1)))
    exact ⟨hx_lower, hx_upper⟩
  have hT_nonneg : 0 ≤ T := by linarith
  have h_bpN : bp (hardyN T) = T := by
    dsimp [bp]
    apply min_eq_left
    by_contra hcontra
    have hstart_lt : hardyStart (hardyN T) < T := lt_of_not_ge hcontra
    have hlt : hardyN T < hardyN T :=
      (hardyN_lt_iff (hardyN T) T hT_nonneg).2 (le_of_lt hstart_lt)
    exact (Nat.lt_irrefl _ hlt)
  have h_tail_integrable : IntegrableOn ErrorTerm (Ioc (bp 0) T) := by
    have h_tail_integrable' :
        IntegrableOn ErrorTerm (Ioc (bp 0) (bp (hardyN T))) :=
      Aristotle.IntervalPartition.integrableOn_split_finitely
        ErrorTerm bp (hardyN T) h_bp_mono h_block_integrable
    simpa [h_bpN] using h_tail_integrable'
  have h_head_integrable : IntegrableOn ErrorTerm (Ioc 1 (bp 0)) := by
    refine h_total_integrable.mono_set ?_
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (min_le_left T (hardyStart 0))⟩
  have h_bp0_ge_one : (1 : ℝ) ≤ bp 0 := by
    dsimp [bp]
    exact le_min (by linarith) (hardyStart_ge_one 0)
  have h_bp0_le_T : bp 0 ≤ T := by
    dsimp [bp]
    exact min_le_left T (hardyStart 0)
  have h_head_tail_split :
      ∫ t in Ioc 1 T, ErrorTerm t ∂volume =
        ∫ t in Ioc 1 (bp 0), ErrorTerm t ∂volume
          + ∫ t in Ioc (bp 0) T, ErrorTerm t ∂volume :=
    Aristotle.IntervalPartition.integral_split_at
      ErrorTerm 1 (bp 0) T h_bp0_ge_one h_bp0_le_T h_head_integrable h_tail_integrable
  have h_tail_sum :
      ∫ t in Ioc (bp 0) T, ErrorTerm t ∂volume =
        Finset.sum (Finset.range (hardyN T))
          (fun k => ∫ t in Ioc (bp k) (bp (k + 1)), ErrorTerm t ∂volume) := by
    calc
      ∫ t in Ioc (bp 0) T, ErrorTerm t ∂volume
          = ∫ t in Ioc (bp 0) (bp (hardyN T)), ErrorTerm t ∂volume := by
              simpa [h_bpN]
      _ = Finset.sum (Finset.range (hardyN T))
            (fun k => ∫ t in Ioc (bp k) (bp (k + 1)), ErrorTerm t ∂volume) := by
            simpa using
              Aristotle.IntervalPartition.integral_split_finitely
                ErrorTerm bp (hardyN T) h_bp_mono h_block_integrable
  calc
    ∫ t in Ioc 1 T, ErrorTerm t ∂volume
        = ∫ t in Ioc 1 (bp 0), ErrorTerm t ∂volume
            + ∫ t in Ioc (bp 0) T, ErrorTerm t ∂volume := h_head_tail_split
    _ = ∫ t in Ioc 1 (bp 0), ErrorTerm t ∂volume
          + Finset.sum (Finset.range (hardyN T))
              (fun k => ∫ t in Ioc (bp k) (bp (k + 1)), ErrorTerm t ∂volume) := by
            rw [h_tail_sum]
    _ = ∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t ∂volume
          + Finset.sum (Finset.range (hardyN T))
              (fun k =>
                ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                  ErrorTerm t ∂volume) := by
            simp [bp]

/-- Hypothesis: global alternating-√ decomposition from RS sign structure
(Titchmarsh §4.16, Siegel 1932).

The integral of the Riemann-Siegel error term decomposes into an alternating
sum of √(k+1) terms plus bounded error. Supplied externally.

NOTE (2026-03): The original definition included a per-block local clause
requiring |∫_block_k ErrorTerm - (-1)^k·A·√(k+1)| ≤ B. This clause is
FALSE: at breakpoint values T = hardyStart(k), the block is empty (integral = 0)
while the center term is A·√(k+1), giving unbounded residual as k→∞.
The local clause was dead code — never consumed downstream. Removed. -/
def PerBlockSignedBoundHyp : Prop :=
  ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
    ∀ T : ℝ, T ≥ 2 →
      ∃ N : ℕ,
        ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
        |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B

theorem per_block_signed_bound (hyp : PerBlockSignedBoundHyp) :
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      ∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B :=
  hyp

/-- Wire the block-level atomic input into the global alternating-`sqrt`
decomposition needed by `RSBreakpointDecomposition`. -/
theorem errorTerm_alternatingSqrt_decomposition_from_blocks
    (hyp : PerBlockSignedBoundHyp) :
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      ∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B :=
  hyp

end Aristotle.RSBlockDecomposition
```

