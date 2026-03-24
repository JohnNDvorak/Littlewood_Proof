/-
Infrastructure for Gabcke phase coupling (Satz 4): sub-lemmas toward closing
the GabckePhaseCouplingHyp sorry.

## Mathematical content

The signed block correction is:
  c(k) = (-1)^k · ∫_{block k} ErrorTerm(t) dt - A · √(k+1)

Gabcke's Satz 4 asserts AntitoneOn c (Ici 1). The proof strategy:
1. Express each block integral via the saddle-point expansion (uses SiegelSaddleExpansionHyp)
2. Show the leading term is 4π·A·√(k+1) with a remainder that is O(1/√k)
3. Use concavity of √ to show the A·√(k+1) terms decrease faster than remainders

This file provides algebraic infrastructure and key reduction lemmas.
Part 11 reduces the full antitonicity to `remainder_antitone_for_ge_one`,
which is the irreducible signed content of Gabcke Satz 4.

SORRY COUNT: 0
  RESOLVED blockers:
    (a) adjacent antitonicity of the signed block remainder for k ≥ 1
        is now reduced to an adjacent weighted-remainder leaf on block
        coordinates; `GabckeSignedProfileHyp` remains a stronger sufficient
        route
    (b) errorTermOnBlock_continuousOn (made public in RSExpansionProof)
    (c) CoV identity: blockRemainder_eq_integral_density (proved)
    (d) Integrability: remainderDensity_integrableOn (proved)
    (e) blockRemainder antitonicity reduction to density: now constructive
        via blockRemainder_antitone_of_density_antitone_ae
  REMAINING analytic input:
    the current tree closes everything down to an adjacent weighted-remainder
    comparison on matched block coordinates. The stronger profile package
    `GabckeSignedProfileHyp` remains as one sufficient route, but the actual
    pointwise leaf used by the density argument is now isolated separately.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.HardyThetaSmooth
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Bridge.HardySetupInstance
import Littlewood.Aristotle.Standalone.FresnelSaddlePointInfra
import Littlewood.Aristotle.Standalone.SteepestDescentContour
import Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp
import Littlewood.Aristotle.Standalone.GabckeFresnelMonotone

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.GabckePhaseCouplingInfra

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam Aristotle.ErrorTermExpansion
open Aristotle.Standalone.FresnelSaddlePointInfra
open Aristotle.Standalone.SteepestDescentContour
open Aristotle.Standalone.SiegelSaddleExpansionHyp
open Aristotle.Standalone.GabckeFresnelMonotone

/-! ## Part 1: Sign structure of (-1)^k across consecutive blocks -/

/-- (-1)^(k+1) = -(-1)^k. The sign alternates. -/
theorem neg_one_pow_succ (k : ℕ) :
    (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by
  rw [pow_succ]; ring

/-- (-1)^k * (-1)^k = 1. The sign squared is always 1. -/
theorem neg_one_pow_sq (k : ℕ) :
    (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  rw [← pow_add, show k + k = 2 * k from by ring]
  simp [pow_mul]

/-- |(-1)^k| = 1 for all k. -/
theorem abs_neg_one_pow (k : ℕ) :
    |(-1 : ℝ) ^ k| = 1 := by
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-! ## Part 2: Consecutive block correction difference

The key identity for antitonicity is:
  c(k) - c(k+1) = (-1)^k · [I_k + I_{k+1}] - A · [√(k+1) - √(k+2)]

where I_k = ∫_{block k} ErrorTerm(t) dt and we used (-1)^{k+1} = -(-1)^k.

Since √ is concave, √(k+1) - √(k+2) < 0, so -A·[√(k+1) - √(k+2)] > 0.
The question is whether this positive contribution dominates.
-/

/-- The signed block correction difference decomposes as:
    c(k) - c(k+1)
    = (-1)^k · [I_k + I_{k+1}]
      - A · (√(k+1) - √(k+2))

    where I_k = ∫_{block k} ErrorTerm(t) dt. -/
theorem correction_diff_decomposition (A : ℝ)
    (I : ℕ → ℝ) -- I k = ∫ block k ErrorTerm dt
    (c : ℕ → ℝ)
    (hc : ∀ k, c k = (-1 : ℝ) ^ k * I k - A * Real.sqrt ((k : ℝ) + 1)) :
    ∀ k, c k - c (k + 1) =
      (-1 : ℝ) ^ k * (I k + I (k + 1)) -
      A * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2)) := by
  intro k
  rw [hc k, hc (k + 1)]
  rw [neg_one_pow_succ k]
  push_cast
  ring

/-! ## Part 3: √ concavity gives the positive contribution

From RSBlockParam.sqrt_decrement_antitone:
  √(k+2) - √(k+1) ≤ √(k+1) - √k

We need: √(k+1) - √(k+2) < 0, so -A·(√(k+1) - √(k+2)) > 0 when A > 0.
-/

/-- √(k+2) > √(k+1) for all k. -/
theorem sqrt_succ_lt (k : ℕ) :
    Real.sqrt ((k : ℝ) + 1) < Real.sqrt ((k : ℝ) + 2) := by
  apply Real.sqrt_lt_sqrt (by positivity) (by linarith)

/-- √(k+1) - √(k+2) < 0 for all k. -/
theorem sqrt_diff_neg (k : ℕ) :
    Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2) < 0 := by
  linarith [sqrt_succ_lt k]

/-- For A > 0: -A · (√(k+1) - √(k+2)) > 0.
    This is the positive "concavity bonus" in each correction difference. -/
theorem concavity_bonus_pos (A : ℝ) (hA : 0 < A) (k : ℕ) :
    0 < -(A * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2))) := by
  have h := sqrt_diff_neg k
  nlinarith

/-- The concavity bonus is antitone: larger k gives smaller bonus.
    -A·(√(k+1) - √(k+2)) ≥ -A·(√(k+2) - √(k+3))  for k ≥ 1, A > 0. -/
theorem concavity_bonus_antitone (A : ℝ) (hA : 0 < A) (k : ℕ) (hk : 1 ≤ k) :
    -(A * (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 3)))
    ≤ -(A * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2))) := by
  -- Equivalently: A*(√(k+2)-√(k+3)) ≥ A*(√(k+1)-√(k+2)) reversed
  -- Actually: we need √(k+2)-√(k+1) ≤ √(k+3)-√(k+2) to FAIL.
  -- Rather: the bonus is -A*(√(k+1)-√(k+2)) = A*(√(k+2)-√(k+1))
  -- We need A*(√(k+2)-√(k+1)) ≥ A*(√(k+3)-√(k+2)), i.e., concavity of √.
  have h_decr := sqrt_decrement_antitone (k + 1) (by omega)
  -- h_decr : √(k+3) - √(k+2) ≤ √(k+2) - √(k+1)
  -- Rewrite the casts
  have h1 : Real.sqrt ((↑(k + 1) : ℝ) + 2) = Real.sqrt ((k : ℝ) + 3) := by
    congr 1; push_cast; ring
  have h2 : Real.sqrt ((↑(k + 1) : ℝ) + 1) = Real.sqrt ((k : ℝ) + 2) := by
    congr 1; push_cast; ring
  have h3 : Real.sqrt (↑(k + 1) : ℝ) = Real.sqrt ((k : ℝ) + 1) := by
    congr 1; push_cast; ring
  rw [h1, h2, h3] at h_decr
  nlinarith

/-! ## Part 4: blockCorrectionA positivity

The constant A = 4π · ∫₀¹ Ψ(p) dp is positive since Ψ > 0 on [0,1].
-/

/-- blockCorrectionA = 4π · ∫₀¹ rsPsi(p) dp is positive.
    Follows from rsPsi_integral_pos. -/
theorem blockCorrectionA_pos :
    0 < 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p) := by
  have h1 : 0 < Real.pi := Real.pi_pos
  have h2 : 0 < ∫ p in Ioc (0 : ℝ) 1, rsPsi p := rsPsi_integral_pos
  positivity

/-! ## Part 5: Weighted rsPsi integral bounds

The saddle-point expansion gives (via CoV):
  (-1)^k · ∫_{block k} ErrorTerm(t) dt
  ≈ (2π/t)^{1/4} · 4π · ∫₀¹ √(k+1+p) · Ψ(p) dp

The √(k+1+p) factor is bounded between √(k+1) and √(k+2).
-/

/-- Upper bound: √(k+1+p) ≤ √(k+2) for p ∈ [0,1]. -/
theorem sqrt_block_upper (k : ℕ) (p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.sqrt ((k : ℝ) + 1 + p) ≤ Real.sqrt ((k : ℝ) + 2) := by
  apply Real.sqrt_le_sqrt; linarith

/-- Lower bound: √(k+1) ≤ √(k+1+p) for p ≥ 0. -/
theorem sqrt_block_lower (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) :
    Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt ((k : ℝ) + 1 + p) := by
  apply Real.sqrt_le_sqrt; linarith

/-- The weighted integral ∫₀¹ √(k+1+p) · Ψ(p) dp is at most
    √(k+2) · ∫₀¹ Ψ(p) dp. -/
theorem rsPsi_weighted_integral_upper (k : ℕ) :
    (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
    ≤ Real.sqrt ((k : ℝ) + 2) * (∫ p in Ioc (0 : ℝ) 1, rsPsi p) := by
  rw [mul_comm]
  have h_mono : ∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p
      ≤ ∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 2) * rsPsi p := by
    apply integral_mono_ae
    · have hcont : ContinuousOn (fun p => Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) (Icc 0 1) := by
        apply ContinuousOn.mul
        · apply ContinuousOn.sqrt
          exact continuousOn_const.add continuousOn_id
        · exact rsPsi_continuousOn
      exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact rsPsi_integrableOn.const_mul _
    · apply (ae_restrict_mem measurableSet_Ioc).mono
      intro p hp
      have hpsi_nn : 0 ≤ rsPsi p := rsPsi_nonneg_on p (Ioc_subset_Icc_self hp)
      exact mul_le_mul_of_nonneg_right
        (sqrt_block_upper k p hp.1.le hp.2) hpsi_nn
  have h_eq : ∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 2) * rsPsi p
      = Real.sqrt ((k : ℝ) + 2) * (∫ p in Ioc (0 : ℝ) 1, rsPsi p) := by
    have := integral_smul (𝕜 := ℝ) (Real.sqrt ((k : ℝ) + 2))
      (fun p => rsPsi p) (μ := volume.restrict (Ioc 0 1))
    simp only [smul_eq_mul] at this
    exact this
  linarith

/-- The difference of consecutive weighted integrals satisfies:
    ∫ √(k+1+p)·Ψ dp - ∫ √(k+2+p)·Ψ dp
    ≥ (√(k+1) - √(k+2)) · ∫ Ψ dp

    This uses the lower/upper bounds on √(k+1+p). -/
theorem weighted_integral_diff_lower (k : ℕ) :
    (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2)) *
      (∫ p in Ioc (0 : ℝ) 1, rsPsi p)
    ≤ (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
      - (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 2 + p) * rsPsi p) := by
  -- Lower bound on first integral: ≥ √(k+1) · ∫Ψ
  have h_lo := rsPsi_weighted_integral_lower k
  -- Upper bound on second integral: ≤ √(k+3) · ∫Ψ
  -- Actually we need: ∫√(k+2+p)Ψ ≤ √(k+3)·∫Ψ which follows from rsPsi_weighted_integral_upper
  -- But the difference ≥ √(k+1)·∫Ψ - √(k+3)·∫Ψ = (√(k+1)-√(k+3))·∫Ψ which is too loose.
  -- Better: use pointwise √(k+1+p) - √(k+2+p) ≥ √(k+1) - √(k+2) (since √(a+p)-√(b+p) is
  -- increasing in p when a < b -- NO, it's decreasing).
  -- Actually √(a+p) - √(b+p) for a < b is negative and increasing (less negative) as p grows.
  -- That doesn't help directly. Let's just use the integral form.
  -- We have: first ≥ √(k+1)·∫Ψ and second ≤ √(k+3)·∫Ψ, so
  -- difference ≥ √(k+1)·∫Ψ - √(k+3)·∫Ψ. But we claimed ≥ (√(k+1)-√(k+2))·∫Ψ.
  -- Since √(k+2) ≤ √(k+3), this is √(k+1)-√(k+2) ≥ √(k+1)-√(k+3). True!
  -- More precisely: second ≤ √(k+2+1)·∫Ψ = √(k+3)·∫Ψ. But we want ≤ √(k+2)·∫Ψ is WRONG
  -- since √(k+2+p) ≥ √(k+2) for p ≥ 0.
  -- OK so the bound with √(k+3) is what we get.
  -- But (√(k+1) - √(k+3)) ≤ (√(k+1) - √(k+2)) since √(k+3) ≥ √(k+2). YES.
  -- So: diff ≥ (√(k+1) - √(k+3))·∫Ψ, and we need ≥ (√(k+1)-√(k+2))·∫Ψ.
  -- Since √(k+1)-√(k+3) ≤ √(k+1)-√(k+2), and ∫Ψ > 0, this would require
  -- (√(k+1)-√(k+3))·∫Ψ ≥ (√(k+1)-√(k+2))·∫Ψ, i.e., √(k+1)-√(k+3) ≥ √(k+1)-√(k+2),
  -- i.e., -√(k+3) ≥ -√(k+2), i.e., √(k+2) ≥ √(k+3). FALSE.
  -- So this approach doesn't work as stated. The correct pointwise bound needs more care.
  -- Let me use the integral subtraction directly.
  have h_int_pos : 0 < ∫ p in Ioc (0 : ℝ) 1, rsPsi p := rsPsi_integral_pos
  -- Direct approach: ∫ (√(k+1+p) - √(k+2+p)) · Ψ(p) dp
  -- and √(k+1+p) - √(k+2+p) is a negative function of p.
  -- We bound it below pointwise: √(k+1+p) - √(k+2+p) ≥ √(k+1+1) - √(k+2+1) = √(k+2) - √(k+3)
  -- Wait, that's the WRONG direction. √(k+1+p) - √(k+2+p) is negative and gets LESS negative
  -- as p grows (concavity). So the minimum is at p = 0: √(k+1) - √(k+2).
  -- So √(k+1+p) - √(k+2+p) ≥ √(k+1) - √(k+2) for all p ∈ [0,1]. YES!
  -- Because: d/dp [√(a+p) - √(b+p)] = 1/(2√(a+p)) - 1/(2√(b+p)) > 0 when a < b (since √(a+p) < √(b+p)).
  -- So the function is increasing in p, minimum at p = 0.
  -- Great, so: ∫ [√(k+1+p) - √(k+2+p)] · Ψ dp ≥ (√(k+1)-√(k+2)) · ∫ Ψ dp.
  -- This is: first - second ≥ (√(k+1)-√(k+2)) · ∫ Ψ dp.
  -- Rewrite as an integral inequality.
  have h_diff_lower : ∀ p, p ∈ Ioc (0 : ℝ) 1 →
      (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2)) * rsPsi p
      ≤ (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 2 + p)) * rsPsi p := by
    intro p hp
    have hpsi_nn : 0 ≤ rsPsi p := rsPsi_nonneg_on p (Ioc_subset_Icc_self hp)
    apply mul_le_mul_of_nonneg_right _ hpsi_nn
    -- Need: √(k+1) - √(k+2) ≤ √(k+1+p) - √(k+2+p) for p ≥ 0
    -- Equivalently: √(k+1+p) - √(k+1) ≥ √(k+2+p) - √(k+2)
    -- This follows from concavity of √: the increment √(a+p) - √(a) is smaller for larger a.
    -- Specifically: √ is concave, so for a < b and p > 0:
    --   √(a+p) - √(a) ≥ √(b+p) - √(b)
    -- We use: √ is concave on [0,∞), i.e., √((1-t)x + ty) ≥ (1-t)√x + t√y.
    -- Direct approach: sufficient to show f(p) = (√(k+1+p) - √(k+2+p)) - (√(k+1) - √(k+2)) ≥ 0
    -- f(0) = 0 and f'(p) = 1/(2√(k+1+p)) - 1/(2√(k+2+p)) ≥ 0.
    -- Alternatively: rearrange as √(k+2) - √(k+1) ≥ √(k+2+p) - √(k+1+p)
    -- i.e., the increment of √ over an interval of length 1 starting at (k+1) is at least as large
    -- as the increment over the same-length interval starting at (k+1+p).
    -- This is: √ concave ⟹ √(b) - √(a) ≥ √(b+p) - √(a+p) for b > a, p > 0.
    -- Let's prove this via nlinarith + sqrt properties.
    suffices h : Real.sqrt ((k : ℝ) + 2 + p) - Real.sqrt ((k : ℝ) + 2)
        ≤ Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1) by linarith
    -- Use: for 0 ≤ a ≤ b and 0 ≤ p:
    --   √(a+p) - √a ≥ √(b+p) - √b
    -- Proof: (√(a+p)-√a)(√(a+p)+√a) = p = (√(b+p)-√b)(√(b+p)+√b)
    -- and √(a+p)+√a ≤ √(b+p)+√b, so √(a+p)-√a ≥ √(b+p)-√b.
    have ha : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) ≤ (k : ℝ) + 2 := by positivity
    have hab : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by linarith
    have hp_nn : 0 ≤ p := le_of_lt hp.1
    -- √(a+p) + √a ≤ √(b+p) + √b
    have h_sum_le : Real.sqrt ((k : ℝ) + 1 + p) + Real.sqrt ((k : ℝ) + 1)
        ≤ Real.sqrt ((k : ℝ) + 2 + p) + Real.sqrt ((k : ℝ) + 2) := by
      have h1 : Real.sqrt ((k : ℝ) + 1 + p) ≤ Real.sqrt ((k : ℝ) + 2 + p) :=
        Real.sqrt_le_sqrt (by linarith)
      have h2 : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt ((k : ℝ) + 2) :=
        Real.sqrt_le_sqrt (by linarith)
      linarith
    -- Both sums are positive
    have h_sum_a_pos : 0 < Real.sqrt ((k : ℝ) + 1 + p) + Real.sqrt ((k : ℝ) + 1) := by
      positivity
    have h_sum_b_pos : 0 < Real.sqrt ((k : ℝ) + 2 + p) + Real.sqrt ((k : ℝ) + 2) := by
      positivity
    -- Conjugate multiplication: (√x - √y)(√x + √y) = x - y
    have h_conj_a : (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) *
        (Real.sqrt ((k : ℝ) + 1 + p) + Real.sqrt ((k : ℝ) + 1)) = p := by
      have := Real.mul_self_sqrt (show (0:ℝ) ≤ (k:ℝ) + 1 + p by linarith)
      have := Real.mul_self_sqrt (show (0:ℝ) ≤ (k:ℝ) + 1 by positivity)
      nlinarith [sq_abs (Real.sqrt ((k : ℝ) + 1 + p)), sq_abs (Real.sqrt ((k : ℝ) + 1))]
    have h_conj_b : (Real.sqrt ((k : ℝ) + 2 + p) - Real.sqrt ((k : ℝ) + 2)) *
        (Real.sqrt ((k : ℝ) + 2 + p) + Real.sqrt ((k : ℝ) + 2)) = p := by
      have := Real.mul_self_sqrt (show (0:ℝ) ≤ (k:ℝ) + 2 + p by linarith)
      have := Real.mul_self_sqrt (show (0:ℝ) ≤ (k:ℝ) + 2 by positivity)
      nlinarith [sq_abs (Real.sqrt ((k : ℝ) + 2 + p)), sq_abs (Real.sqrt ((k : ℝ) + 2))]
    -- From conjugate: diff_a = p / sum_a, diff_b = p / sum_b
    -- Since sum_a ≤ sum_b, diff_a ≥ diff_b
    by_cases hp_zero : p = 0
    · subst hp_zero; simp
    · have hp_pos : 0 < p := lt_of_le_of_ne hp_nn (Ne.symm hp_zero)
      rw [show Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)
          = p / (Real.sqrt ((k : ℝ) + 1 + p) + Real.sqrt ((k : ℝ) + 1)) from by
        rw [eq_div_iff h_sum_a_pos.ne.symm]; linarith [h_conj_a]]
      rw [show Real.sqrt ((k : ℝ) + 2 + p) - Real.sqrt ((k : ℝ) + 2)
          = p / (Real.sqrt ((k : ℝ) + 2 + p) + Real.sqrt ((k : ℝ) + 2)) from by
        rw [eq_div_iff h_sum_b_pos.ne.symm]; linarith [h_conj_b]]
      exact div_le_div_of_nonneg_left hp_pos.le h_sum_a_pos h_sum_le
  -- Now integrate
  have h_sub_int :
      (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
      - (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 2 + p) * rsPsi p)
      = ∫ p in Ioc (0 : ℝ) 1,
          (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 2 + p)) * rsPsi p := by
    rw [← integral_sub]
    · congr 1; ext p; ring
    · -- integrability of first
      have hcont1 : ContinuousOn (fun p => Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) (Icc 0 1) := by
        apply ContinuousOn.mul
        · apply ContinuousOn.sqrt; exact continuousOn_const.add continuousOn_id
        · exact rsPsi_continuousOn
      exact hcont1.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · -- integrability of second
      have hcont2 : ContinuousOn (fun p => Real.sqrt ((k : ℝ) + 2 + p) * rsPsi p) (Icc 0 1) := by
        apply ContinuousOn.mul
        · apply ContinuousOn.sqrt; exact continuousOn_const.add continuousOn_id
        · exact rsPsi_continuousOn
      exact hcont2.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [h_sub_int]
  -- Now use pointwise bound + integration
  have h_const_int :
      (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2)) *
        (∫ p in Ioc (0 : ℝ) 1, rsPsi p)
      = ∫ p in Ioc (0 : ℝ) 1,
          (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2)) * rsPsi p := by
    have := integral_smul (𝕜 := ℝ)
      (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2))
      (fun p => rsPsi p) (μ := volume.restrict (Ioc 0 1))
    simp only [smul_eq_mul] at this
    exact this.symm
  rw [h_const_int]
  apply integral_mono_ae
  · exact rsPsi_integrableOn.const_mul _
  · have hcont : ContinuousOn
        (fun p => (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 2 + p)) * rsPsi p)
        (Icc 0 1) := by
      apply ContinuousOn.mul
      · apply ContinuousOn.sub
        · apply ContinuousOn.sqrt; exact continuousOn_const.add continuousOn_id
        · apply ContinuousOn.sqrt; exact continuousOn_const.add continuousOn_id
      · exact rsPsi_continuousOn
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact (ae_restrict_mem measurableSet_Ioc).mono (fun p hp => h_diff_lower p hp)

/-! ## Part 6: Antitone criterion via sufficient block estimates

If we can show that for each k ≥ 1, the signed block integral sum
(-1)^k · (I_k + I_{k+1}) is nonneg and at least
A · (√(k+1) - √(k+2)), then c(k) - c(k+1) ≥ 0.
-/

/-- **Sufficient condition for antitonicity**: if for each k ≥ 1,
    (-1)^k · (I_k + I_{k+1}) ≥ A · (√(k+1) - √(k+2))
    then c is antitone on Ici 1. -/
theorem antitone_from_block_estimate
    (A : ℝ) (I : ℕ → ℝ) (c : ℕ → ℝ)
    (hc : ∀ k, c k = (-1 : ℝ) ^ k * I k - A * Real.sqrt ((k : ℝ) + 1))
    (h_est : ∀ k : ℕ, 1 ≤ k →
      A * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2))
      ≤ (-1 : ℝ) ^ k * (I k + I (k + 1))) :
    AntitoneOn c (Ici (1 : ℕ)) := by
  -- First establish consecutive step: c(k) ≥ c(k+1) for k ≥ 1
  have h_step : ∀ k : ℕ, 1 ≤ k → c (k + 1) ≤ c k := by
    intro k hk
    have := correction_diff_decomposition A I c hc k
    linarith [h_est k hk]
  -- Then extend to arbitrary a ≤ b via telescoping
  intro a (ha : 1 ≤ a) b (_hb : 1 ≤ b) (hab : a ≤ b)
  -- Prove by induction on b - a
  have key : ∀ n : ℕ, 1 ≤ a → c (a + n) ≤ c a := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro ha'
      have h_an : 1 ≤ a + n := le_trans ha' (Nat.le_add_right a n)
      calc c (a + (n + 1)) = c ((a + n) + 1) := by ring_nf
        _ ≤ c (a + n) := h_step (a + n) h_an
        _ ≤ c a := ih ha'
  have h_eq : b = a + (b - a) := by omega
  rw [h_eq]; exact key (b - a) ha

/-! ## Part 7: Block integral sign structure from saddle expansion

Under the saddle-point expansion (SiegelSaddleExpansionHyp), the block integral
of ErrorTerm on block k is approximately:
  ∫_{block k} ErrorTerm(t) dt ≈ (-1)^k · 4π · ∫₀¹ (2π/t(k,p))^{1/4} · √(k+1+p) · Ψ(p) · 4π(k+1+p) dp

where we used CoV t = 2π(k+1+p)² and dt = 4π(k+1+p) dp.

The sign (-1)^k enters naturally from the expansion. So:
  (-1)^k · ∫_{block k} ErrorTerm = 4π · ∫₀¹ (2π/t(k,p))^{1/4} · Ψ(p) · 4π(k+1+p) dp
which is positive.
-/

/-- 2π / blockCoord k p = 1/(k+1+p)². -/
theorem two_pi_div_blockCoord (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    2 * Real.pi / blockCoord k p = 1 / ((k : ℝ) + 1 + p) ^ 2 := by
  unfold blockCoord; field_simp

/-- On block k, 1/√(k+1+p) is positive when p ≥ 0. -/
theorem inv_sqrt_block_pos (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    0 < 1 / Real.sqrt ((k : ℝ) + 1 + p) := by
  positivity

/-- The (2π/blockCoord k p)^{1/4} factor squared equals 1/(k+1+p).
    Key identity: ((1/x²)^{1/4})^2 = (1/x²)^{1/2} = 1/x for x > 0. -/
theorem quarter_power_sq_on_block (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    ((2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4)) ^ 2 =
    1 / ((k : ℝ) + 1 + p) := by
  have hkp : 0 < (k : ℝ) + 1 + p := by positivity
  rw [two_pi_div_blockCoord k p hp]
  -- Rewrite LHS using rpow
  set x := ((k : ℝ) + 1 + p) with hx_def
  have hx_pos : 0 < x := hkp
  -- (1/x²)^{1/4} is nonneg
  have h_base_nn : (0 : ℝ) ≤ 1 / x ^ 2 := by positivity
  -- Use rpow_natCast to convert ^ 2 to rpow
  conv_lhs => rw [sq]
  -- ((1/x²)^{1/4}) * ((1/x²)^{1/4}) = (1/x²)^{1/4 + 1/4}
  rw [← Real.rpow_add (by positivity : 0 < 1 / x ^ 2)]
  -- 1/4 + 1/4 = 1/2
  have h_exp : (1 : ℝ) / 4 + 1 / 4 = 1 / 2 := by norm_num
  rw [h_exp, ← Real.sqrt_eq_rpow,
      Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_sq hx_pos.le]

/-! ## Part 8: Jacobian and amplitude product simplification

On block k at parameter p, the Jacobian is 4π(k+1+p) and the amplitude factor
is (2π/t)^{1/4} = 1/√(k+1+p). Their product simplifies to 4π·√(k+1+p).
-/

/-- The product of amplitude factor and Jacobian on block k:
    (2π/t)^{1/4} · 4π(k+1+p) = 4π · √(k+1+p).
    This is the key simplification for block integrals under the saddle expansion. -/
theorem amplitude_jacobian_product (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    1 / Real.sqrt ((k : ℝ) + 1 + p) * (4 * Real.pi * ((k : ℝ) + 1 + p)) =
    4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) := by
  have hkp : 0 < (k : ℝ) + 1 + p := by positivity
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1 + p) := Real.sqrt_pos_of_pos hkp
  have hsqrt_ne : Real.sqrt ((k : ℝ) + 1 + p) ≠ 0 := ne_of_gt hsqrt_pos
  -- 1/√x · (4π·x) = 4π · x/√x = 4π · √x
  -- x = √x · √x, so x/√x = √x
  have h_sq : ((k : ℝ) + 1 + p) = Real.sqrt ((k : ℝ) + 1 + p) * Real.sqrt ((k : ℝ) + 1 + p) :=
    (Real.mul_self_sqrt hkp.le).symm
  field_simp
  linarith [Real.sq_sqrt hkp.le]

/-! ## Part 9: Signed block integral positivity (conditional on saddle expansion)

Under the saddle-point expansion, (-1)^k · ∫_{block k} ErrorTerm dt ≈ positive.
Specifically, the leading term of (-1)^k · I_k equals the positive quantity:
  4π · ∫₀¹ √(k+1+p) · Ψ(p) dp
which is at least 4π · √(k+1) · ∫₀¹ Ψ(p) dp = blockCorrectionA · √(k+1).
-/

/-- The leading asymptotic of (-1)^k · I_k from the saddle-point expansion.
    This is 4π · ∫₀¹ √(k+1+p) · Ψ(p) dp, which is positive. -/
def leadingBlockIntegral (k : ℕ) : ℝ :=
  4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)

/-- The leading block integral is positive for all k. -/
theorem leadingBlockIntegral_pos (k : ℕ) : 0 < leadingBlockIntegral k := by
  unfold leadingBlockIntegral
  apply mul_pos (by positivity)
  -- ∫ √(k+1+p) · Ψ(p) dp ≥ √(k+1) · ∫ Ψ(p) dp > 0
  have h_lower := rsPsi_weighted_integral_lower k
  have h_int_pos := rsPsi_integral_pos
  have h_sqrt_nn : 0 ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
  -- √(k+1) · ∫Ψ ≥ 0 and √(k+1) · ∫Ψ ≤ ∫ √(k+1+p)·Ψ
  -- so ∫ √(k+1+p)·Ψ ≥ √(k+1) · ∫Ψ ≥ 0 · ∫Ψ = 0
  -- Actually need strictly positive.
  have h_sqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos_of_pos (by positivity)
  have : 0 < Real.sqrt ((k : ℝ) + 1) * (∫ p in Ioc (0 : ℝ) 1, rsPsi p) :=
    mul_pos h_sqrt_pos h_int_pos
  linarith

/-- Lower bound: leadingBlockIntegral k ≥ blockCorrectionA · √(k+1)
    where blockCorrectionA = 4π · ∫₀¹ Ψ dp.

    This follows from √(k+1+p) ≥ √(k+1) for p ≥ 0. -/
theorem leadingBlockIntegral_lower (k : ℕ) :
    (4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)) * Real.sqrt ((k : ℝ) + 1)
    ≤ leadingBlockIntegral k := by
  unfold leadingBlockIntegral
  have h := rsPsi_weighted_integral_lower k
  nlinarith [Real.pi_pos]

/-- Upper bound: leadingBlockIntegral k ≤ blockCorrectionA · √(k+2). -/
theorem leadingBlockIntegral_upper (k : ℕ) :
    leadingBlockIntegral k ≤
    (4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)) * Real.sqrt ((k : ℝ) + 2) := by
  unfold leadingBlockIntegral
  have h := rsPsi_weighted_integral_upper k
  nlinarith [Real.pi_pos]

/-- The sum of consecutive leading block integrals is at least
    blockCorrectionA · (√(k+1) + √(k+2)). -/
theorem consecutive_leading_lower (k : ℕ) :
    (4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)) *
      (Real.sqrt ((k : ℝ) + 1) + Real.sqrt ((k : ℝ) + 2))
    ≤ leadingBlockIntegral k + leadingBlockIntegral (k + 1) := by
  have h1 := leadingBlockIntegral_lower k
  have h2 := leadingBlockIntegral_lower (k + 1)
  -- leadingBlockIntegral(k+1) ≥ A · √(k+2)
  have h2' : (4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)) * Real.sqrt ((k : ℝ) + 2)
      ≤ leadingBlockIntegral (k + 1) := by
    convert h2 using 2; push_cast; ring
  linarith

/-- For the block estimate: A · (√(k+1) - √(k+2)) ≤ A · (√(k+1) + √(k+2)) - 2A·√(k+2).
    This is trivially A·(√(k+1)-√(k+2)) = A·√(k+1) + A·(-√(k+2)). -/
theorem block_estimate_from_leading (k : ℕ) (A : ℝ) (_hA : 0 < A)
    (L_k L_k1 : ℝ)
    (hL_k : A * Real.sqrt ((k : ℝ) + 1) ≤ L_k)
    (hL_k1 : A * Real.sqrt ((k : ℝ) + 2) ≤ L_k1) :
    A * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2))
    ≤ L_k + L_k1 - 2 * A * Real.sqrt ((k : ℝ) + 2) := by
  nlinarith

/-! ## Part 10: Block integral remainder bounds (conditional on SiegelSaddleExpansionHyp)

Under the saddle-point expansion, the block integral I_k decomposes as:
  I_k = (-1)^k · leadingBlockIntegral(k) + remainder

The remainder is bounded by integrating the pointwise bound from gabcke_from_hyp.
-/

/-- The leading block integral expressed via CoV matches blockCoord/blockParam.
    On block k, using t = blockCoord(k,p) = 2π(k+1+p)²:
      (2π/t)^{1/4} · Ψ(blockParam k t) = (2π/t)^{1/4} · Ψ(p)
    since blockParam(k, blockCoord(k,p)) = p. -/
theorem blockParam_on_coord (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    blockParam k (blockCoord k p) = p :=
  blockParam_blockCoord k p hp

/-- The block integral error term: for t in block k, the next-order correction
    (2π/t)^{1/4} · (1/4) · t^{-1/2} is bounded by (1/4) · (k+1)^{-3/2}
    times a universal constant (since (2π/t)^{1/4} ≤ (k+1)^{-1/2} and
    t^{-1/2} ≤ (2π)^{-1/2} · (k+1)^{-1} on block k).

    This bounds the O(t^{-3/4}) remainder after extracting the leading RS correction. -/
theorem block_error_bound_at_param (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) *
      ((1 / 4) * (blockCoord k p) ^ (-(1 : ℝ) / 2)) ≤
    1 / 4 := by
  have h_mem : blockCoord k p ∈ Icc (hardyStart k) (hardyStart (k + 1)) :=
    blockCoord_mem_Icc k (Set.mem_Icc.mpr ⟨hp0, hp1⟩)
  have h2pi := block_ge_two_pi k (blockCoord k p) h_mem.1
  exact next_order_product_le_quarter (blockCoord k p) h2pi

/-- Summary: the saddle expansion remainder (amplitude × next-order) is at most 1/4
    on any block. This is a consequence of FresnelSaddlePointInfra. -/
theorem saddle_remainder_uniform (k : ℕ) (t : ℝ) (ht : hardyStart k ≤ t) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * ((1 / 4) * t ^ (-(1 : ℝ) / 2)) ≤ 1 / 4 := by
  exact next_order_product_le_quarter t (block_ge_two_pi k t ht)

/-! ## Part 11: Block integral remainder — reducing to signed remainder antitonicity

The signed block integral decomposes as:
  (-1)^k · I_k = leadingBlockIntegral(k) + blockRemainder(k)

where the remainder captures all higher-order saddle-point corrections.
The key irreducible content of Gabcke Satz 4 is that blockRemainder is antitone:
  blockRemainder(k) ≥ blockRemainder(k+1) for k ≥ 1.

Combined with the concavity surplus from Part 5, this implies the full
block estimate condition in block_estimate_suffices.
-/

/-- The block remainder: the signed block integral minus its leading asymptotic.
    R(k) = (-1)^k · I_k - leadingBlockIntegral(k)
    where I_k = ∫_{block k} ErrorTerm(t) dt.

    Under the saddle-point expansion, |R(k)| = O(k^{-1/2}). The irreducible
    content of Gabcke Satz 4 is that R(k) is antitone. -/
def blockRemainder (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
    - leadingBlockIntegral k

/-- Decomposition: the block estimate condition reduces to leading + remainder.
    (-1)^k · (I_k + I_{k+1}) = (L_k - L_{k+1}) + (R_k - R_{k+1)). -/
theorem block_sum_decomposition (k : ℕ) :
    (-1 : ℝ) ^ k *
      ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t) +
       (∫ t in Ioc (hardyStart (k + 1)) (hardyStart (k + 2)), ErrorTerm t))
    = (leadingBlockIntegral k - leadingBlockIntegral (k + 1))
      + (blockRemainder k - blockRemainder (k + 1)) := by
  unfold blockRemainder leadingBlockIntegral
  rw [neg_one_pow_succ k]
  ring

/-- The leading term difference dominates the block correction concavity bonus:
    L_k - L_{k+1} ≥ A · (√(k+1) - √(k+2)).

    This is a direct consequence of weighted_integral_diff_lower. -/
theorem leading_diff_ge_correction (k : ℕ) :
    (4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)) *
      (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2))
    ≤ leadingBlockIntegral k - leadingBlockIntegral (k + 1) := by
  unfold leadingBlockIntegral
  -- leadingBlockIntegral(k+1) = 4π · ∫ √((k+1)+1+p) · Ψ dp = 4π · ∫ √(k+2+p) · Ψ dp
  have h_cast : ∀ p : ℝ,
      Real.sqrt ((↑(k + 1) : ℝ) + 1 + p) = Real.sqrt ((k : ℝ) + 2 + p) := by
    intro p; congr 1; push_cast; ring
  simp_rw [h_cast]
  have h := weighted_integral_diff_lower k
  nlinarith [Real.pi_pos]

/-- **Key reduction**: the block estimate condition is equivalent to
    blockRemainder(k) ≥ blockRemainder(k+1).

    Proof:
    (-1)^k·(I_k+I_{k+1}) = (L_k-L_{k+1}) + (R_k-R_{k+1})
    From leading_diff_ge_correction: L_k - L_{k+1} ≥ A·(√(k+1)-√(k+2))
    So the block estimate A·(√(k+1)-√(k+2)) ≤ (-1)^k·(I_k+I_{k+1})
    holds iff R_k ≥ R_{k+1}. -/
theorem block_estimate_iff_remainder_antitone (k : ℕ) :
    (blockRemainder k ≥ blockRemainder (k + 1)) →
    (4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, rsPsi p)) *
      (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2))
    ≤ (-1 : ℝ) ^ k *
      ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t) +
       (∫ t in Ioc (hardyStart (k + 1)) (hardyStart (k + 2)), ErrorTerm t)) := by
  intro h_rem
  rw [block_sum_decomposition]
  have h_lead := leading_diff_ge_correction k
  linarith

/-! ## Part 11a: Signed saddle-point coefficient

The Gabcke expansion (Satz 4) shows that the signed saddle-point remainder
(-1)^k · saddlePointRemainder(k, t) is nonneg for t in block k. Specifically:

  (-1)^k · R(k,t) = c₁(p)/√t + O(1/t)

where c₁(p) = cos(π·p)/8 + ... is the first Gabcke correction coefficient
(Gabcke 1979, Tabelle 1). Since c₁(p) > 0 for all p ∈ [0,1] (ranging from
0.0417 at p=0,1 to 0.0833 at p=1/2), the signed remainder is nonneg.

This is the genuine irreducible content of Gabcke Satz 4 beyond the absolute
bound of Satz 1. The absolute bound |R| ≤ (1/4)/√t is already captured by
SiegelSaddleExpansionHyp. The signed positivity requires the phase structure.

We formalize the "signed saddle-point remainder" σ(k,t) := (-1)^k ·
saddlePointRemainder(k,t) and provide:
- The definition
- The absolute bound (from SiegelSaddleExpansionHyp, 0 sorry)
- The 1/√ decay of the absolute bound in k
- The reduction of blockRemainder antitonicity to a pointwise density comparison

The remaining obstruction is now a single smaller signed leaf:
(a) adjacent antitonicity of `blockRemainder` for `k ≥ 1`.
This is the exact form consumed by `remainder_antitone_for_ge_one`, and it
remains steepest-descent content at the same level as
SiegelSaddleExpansionHyp.contour_saddle_bound. -/

/-- The signed saddle-point remainder: σ(k,t) := (-1)^k · saddlePointRemainder(k,t).
    This is the sign-corrected steepest-descent remainder on block k. -/
def signedSPR (k : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * saddlePointRemainder k t

/-- The weighted signed saddle-point remainder on block coordinates.
    This is the exact `ρ/(4π)` density after the Jacobian/amplitude cancellation. -/
def weightedSignedSPR (k : ℕ) (p : ℝ) : ℝ :=
  Real.sqrt ((k : ℝ) + 1 + p) * signedSPR k (blockCoord k p)

/-- The block-independent signed profile suggested by Gabcke's asymptotic.
    It is normalized using the `k = 1` block so that the remaining obstruction
    is precisely the `1 / √(k+1+p)` scaling plus positivity of this profile. -/
def gabckeSignedProfile (p : ℝ) : ℝ :=
  Real.sqrt (2 + p) * weightedSignedSPR 1 p

/-- The absolute value of signedSPR equals the absolute value of saddlePointRemainder.
    Since |(-1)^k| = 1, the sign factor doesn't affect the absolute value. -/
theorem abs_signedSPR (k : ℕ) (t : ℝ) :
    |signedSPR k t| = |saddlePointRemainder k t| := by
  unfold signedSPR
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- The chosen signed profile reproduces the weighted remainder on the `k = 1`
    block by construction. -/
private theorem weightedSignedSPR_one_eq_profile (p : ℝ) (hp : 0 ≤ p) :
    weightedSignedSPR 1 p = gabckeSignedProfile p / Real.sqrt (2 + p) := by
  unfold gabckeSignedProfile
  have hsqrt_pos : 0 < Real.sqrt (2 + p) := by positivity
  field_simp [hsqrt_pos.ne']

/-- On the normalization block `k = 1`, the Gabcke profile is exactly the block
    coordinate factor `(2 + p)` times the signed saddle remainder. -/
private theorem gabckeSignedProfile_eq_block1_signedSPR (p : ℝ) (hp : 0 ≤ p) :
    gabckeSignedProfile p = (2 + p) * signedSPR 1 (blockCoord 1 p) := by
  have htwo_nonneg : 0 ≤ 2 + p := by linarith
  have hsq : Real.sqrt (2 + p) * Real.sqrt (2 + p) = 2 + p := by
    simpa [sq] using Real.sq_sqrt htwo_nonneg
  have hweighted :
      weightedSignedSPR 1 p = Real.sqrt (2 + p) * signedSPR 1 (blockCoord 1 p) := by
    unfold weightedSignedSPR
    congr 1
    norm_num
  unfold gabckeSignedProfile
  rw [hweighted]
  calc
    Real.sqrt (2 + p) * (Real.sqrt (2 + p) * signedSPR 1 (blockCoord 1 p))
        = (Real.sqrt (2 + p) * Real.sqrt (2 + p)) * signedSPR 1 (blockCoord 1 p) := by
            ring
    _ = (2 + p) * signedSPR 1 (blockCoord 1 p) := by rw [hsq]

/-! ## Part 11b: Sufficient condition for remainder antitonicity via density comparison

The blockRemainder can be expressed via CoV as an integral of remainderDensity
over [0,1] (from GabckeFresnelMonotone). If the density is pointwise antitone
in k, then blockRemainder is antitone by integral_mono.

This theorem is sorry-free: it's pure integration theory. -/

/-- Sufficient condition for remainder antitonicity: if the remainder density
    is pointwise antitone on [0,1] for k ≥ 1, then blockRemainder is antitone.

    This reduces the block-level antitonicity to a pointwise comparison of
    the remainder density function. The hypotheses:
    - h_cov_k/h_cov_k1: CoV identities (require errorTermOnBlock continuity)
    - h_pw: pointwise density comparison (requires signed Gabcke bound)
    - h_int_k/h_int_k1: integrability (from continuity of the density) -/
theorem blockRemainder_antitone_of_density_antitone (k : ℕ) (_hk : 1 ≤ k)
    (h_cov_k : blockRemainder k = ∫ p in Ioc (0:ℝ) 1, remainderDensity k p)
    (h_cov_k1 : blockRemainder (k + 1) = ∫ p in Ioc (0:ℝ) 1, remainderDensity (k + 1) p)
    (h_pw : ∀ p, p ∈ Ioc (0:ℝ) 1 →
      remainderDensity (k + 1) p ≤ remainderDensity k p)
    (h_int_k : IntegrableOn (remainderDensity k) (Ioc 0 1))
    (h_int_k1 : IntegrableOn (remainderDensity (k + 1)) (Ioc 0 1)) :
    blockRemainder (k + 1) ≤ blockRemainder k := by
  rw [h_cov_k, h_cov_k1]
  exact integral_mono_ae h_int_k1 h_int_k
    ((ae_restrict_mem measurableSet_Ioc).mono (fun p hp => h_pw p hp))

/-- Measure-theoretic variant: an almost-everywhere density comparison on
    `Ioc (0,1]` already implies block-remainder antitonicity. This is the form
    needed after removing the measure-zero endpoint `p = 1` from the atomic
    signed Gabcke leaves. -/
theorem blockRemainder_antitone_of_density_antitone_ae (k : ℕ) (_hk : 1 ≤ k)
    (h_cov_k : blockRemainder k = ∫ p in Ioc (0:ℝ) 1, remainderDensity k p)
    (h_cov_k1 : blockRemainder (k + 1) = ∫ p in Ioc (0:ℝ) 1, remainderDensity (k + 1) p)
    (h_pw :
      ∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        remainderDensity (k + 1) p ≤ remainderDensity k p)
    (h_int_k : IntegrableOn (remainderDensity k) (Ioc 0 1))
    (h_int_k1 : IntegrableOn (remainderDensity (k + 1)) (Ioc 0 1)) :
    blockRemainder (k + 1) ≤ blockRemainder k := by
  rw [h_cov_k, h_cov_k1]
  exact integral_mono_ae h_int_k1 h_int_k h_pw

/-- The Gabcke absolute bound is antitone in k (from GabckeFresnelMonotone):
    the bound π/(√(2π)·√(k+2+p)) ≤ π/(√(2π)·√(k+1+p)).
    This gives that the ABSOLUTE BOUND on remainderDensity decreases with k. -/
theorem gabcke_abs_bound_antitone' (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.pi / (Real.sqrt (2 * Real.pi) * Real.sqrt ((k : ℝ) + 2 + p)) ≤
    Real.pi / (Real.sqrt (2 * Real.pi) * Real.sqrt ((k : ℝ) + 1 + p)) :=
  gabcke_abs_bound_antitone k p hp0 hp1

/-! ## Part 11c: CoV identity for blockRemainder

The change of variables t = blockCoord(k,p) transforms the block integral
∫_{block k} ErrorTerm(t) dt into ∫₀¹ ErrorTerm(blockCoord(k,p)) · J(k,p) dp.

Combined with the definition of blockRemainder and remainderDensity, this gives:
  blockRemainder(k) = ∫₀¹ remainderDensity(k,p) dp

This is the first blocker for closing the sorry (now resolved). -/

/-- The block integral of ErrorTerm via CoV:
    ∫_{block k} ErrorTerm = ∫₀¹ errorTermOnBlock(k, blockCoord(k,p)) · J(k,p) dp.

    Requires errorTermOnBlock_continuousOn as a hypothesis (proved in
    RSExpansionProof.lean, but that file is not imported to avoid cycles). -/
theorem block_integral_errorTerm_cov' (k : ℕ)
    (hcont : ContinuousOn (errorTermOnBlock k)
      (Icc (hardyStart k) (hardyStart (k + 1)))) :
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t
      = ∫ p in Ioc 0 1,
          errorTermOnBlock k (blockCoord k p) * blockJacobian k p := by
  rw [← errorTermOnBlock_integral_eq k]
  exact block_integral_cov k (errorTermOnBlock k) hcont

/-- On the open block interior, errorTermOnBlock agrees with ErrorTerm:
    For p ∈ (0,1), blockCoord maps into the open block where the two agree. -/
theorem errorTerm_eq_on_blockCoord (k : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    errorTermOnBlock k (blockCoord k p) = ErrorTerm (blockCoord k p) := by
  apply errorTermOnBlock_eq_errorTerm
  · -- hardyStart k ≤ blockCoord k p (strict inequality for p > 0)
    rw [← blockCoord_zero k]
    exact le_of_lt (blockCoord_strictMonoOn_nonneg k
      (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr hp0.le)
      hp0)
  · -- blockCoord k p < hardyStart (k+1) (strict for p < 1)
    rw [← blockCoord_one k]
    exact blockCoord_strictMonoOn k
      (Set.mem_Icc.mpr ⟨hp0.le, hp1.le⟩)
      (Set.right_mem_Icc.mpr (by norm_num : (0:ℝ) ≤ 1))
      hp1

/-- On the open parameter interval (0,1), errorTermOnBlock equals ErrorTerm
    on the block coordinate. This gives a.e. equality on Ioc 0 1
    (the singleton {1} has measure zero). -/
private theorem ae_Ioo_of_Ioc :
    ∀ᵐ p ∂(volume.restrict (Ioc (0:ℝ) 1)), p ∈ Ioo (0:ℝ) 1 := by
  have h1 := ae_restrict_mem (μ := volume) measurableSet_Ioc (s := Ioc (0:ℝ) 1)
  have h2 : ∀ᵐ p ∂(volume.restrict (Ioc (0:ℝ) 1)), p ≠ (1:ℝ) := by
    apply ae_restrict_of_ae
    exact ae_iff.mpr (measure_mono_null (fun x hx => by simp at hx; exact hx)
      Real.volume_singleton)
  exact (h1.and h2).mono (fun p ⟨hp, hne⟩ => ⟨hp.1, lt_of_le_of_ne hp.2 hne⟩)

/-- Re(exp(Ix)) = cos(x), used to transfer continuity from the smooth phase. -/
private lemma re_exp_I_mul_ofReal (x : ℝ) :
    (Complex.exp (Complex.I * (x : ℂ))).re = Real.cos x := by
  rw [mul_comm, Complex.exp_mul_I]
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_im]

/-- The cosine phase in `errorTermOnBlock` matches the smooth Hardy phase. -/
private theorem cos_hardyPhase_eq_cos_smooth_local (n : ℕ) (t : ℝ) :
    Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1)) =
    Real.cos (HardyThetaSmooth.hardyPhaseSmooth n t) := by
  have h := HardyThetaSmooth.exp_hardyPhaseSmooth_eq n t
  rw [← re_exp_I_mul_ofReal, ← re_exp_I_mul_ofReal, h]

/-- The cosine sum in `errorTermOnBlock` is continuous. -/
private theorem continuous_cosSum_local (k : ℕ) :
    Continuous (fun t => (2 : ℝ) * ∑ n ∈ Finset.range (k + 1),
      ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * Real.cos (hardyTheta t - t * Real.log (n + 1))) := by
  apply continuous_const.mul
  apply continuous_finset_sum
  intro n _
  apply continuous_const.mul
  have h_eq : (fun t => Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))) =
      (fun t => Real.cos (HardyThetaSmooth.hardyPhaseSmooth n t)) := by
    funext t
    exact cos_hardyPhase_eq_cos_smooth_local n t
  rw [h_eq]
  exact Real.continuous_cos.comp (HardyThetaSmooth.differentiable_hardyPhaseSmooth n).continuous

/-- Local continuity certificate for `errorTermOnBlock` on the k-th block.
    This mirrors the proof in `RSExpansionProof` without importing that file. -/
private theorem errorTermOnBlock_continuousOn_local (k : ℕ) :
    ContinuousOn (errorTermOnBlock k) (Icc (hardyStart k) (hardyStart (k + 1))) := by
  unfold errorTermOnBlock
  apply Continuous.continuousOn
  apply Continuous.sub
  · exact HardySetupInstance.hardyZ_continuous
  · exact continuous_cosSum_local k

/-- The `ErrorTerm(blockCoord(k,p)) * J(k,p)` density is integrable on `(0,1]`
    once the block-local surrogate is known to be continuous on the closed block. -/
private theorem errorTerm_density_integrableOn (k : ℕ)
    (hcont : ContinuousOn (errorTermOnBlock k)
      (Icc (hardyStart k) (hardyStart (k + 1)))) :
    IntegrableOn (fun p => ErrorTerm (blockCoord k p) * blockJacobian k p) (Ioc 0 1) := by
  have hcont_block : ContinuousOn
      (fun p => errorTermOnBlock k (blockCoord k p) * blockJacobian k p)
      (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.mul
    · exact hcont.comp (blockCoord_continuous k).continuousOn (fun p hp => blockCoord_mem_Icc k hp)
    · exact (blockJacobian_continuous k).continuousOn
  have hint_block :
      IntegrableOn (fun p => errorTermOnBlock k (blockCoord k p) * blockJacobian k p) (Ioc 0 1) :=
    hcont_block.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h_ae :
      (fun p => errorTermOnBlock k (blockCoord k p) * blockJacobian k p)
        =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun p => ErrorTerm (blockCoord k p) * blockJacobian k p) := by
    filter_upwards [ae_Ioo_of_Ioc] with p hp
    rw [errorTerm_eq_on_blockCoord k p hp.1 hp.2]
  exact hint_block.congr_fun_ae h_ae

/-- The signed `ErrorTerm` contribution to `remainderDensity` is integrable. -/
private theorem signedErrorDensity_integrableOn (k : ℕ)
    (hcont : ContinuousOn (errorTermOnBlock k)
      (Icc (hardyStart k) (hardyStart (k + 1)))) :
    IntegrableOn (fun p => (-1 : ℝ) ^ k * ErrorTerm (blockCoord k p) * blockJacobian k p)
      (Ioc 0 1) := by
  have h_err := errorTerm_density_integrableOn k hcont
  have hsigned :
      IntegrableOn (fun p => (-1 : ℝ) ^ k * (ErrorTerm (blockCoord k p) * blockJacobian k p))
        (Ioc 0 1) :=
    h_err.const_mul ((-1 : ℝ) ^ k)
  exact hsigned.congr_fun (fun p _hp => by simp [mul_assoc]) measurableSet_Ioc

/-- The explicit leading-density term in `remainderDensity` is integrable. -/
private theorem leadingDensity_integrableOn (k : ℕ) :
    IntegrableOn (fun p => 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) (Ioc 0 1) := by
  have hsqrtpsi : ContinuousOn
      (fun p => Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
      (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.sqrt
      exact continuousOn_const.add continuousOn_id
    · exact rsPsi_continuousOn
  have hcont : ContinuousOn
      (fun p => 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
      (Icc (0 : ℝ) 1) := by
    have hconstmul :
        ContinuousOn (fun p => (4 * Real.pi) * (Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p))
          (Icc (0 : ℝ) 1) :=
      continuousOn_const.mul hsqrtpsi
    simpa [mul_assoc] using hconstmul
  exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The remainder density is integrable on `(0,1]` once the block-local
    surrogate for `ErrorTerm` is continuous on the closed block. -/
theorem remainderDensity_integrableOn (k : ℕ)
    (hcont : ContinuousOn (errorTermOnBlock k)
      (Icc (hardyStart k) (hardyStart (k + 1)))) :
    IntegrableOn (remainderDensity k) (Ioc 0 1) := by
  unfold remainderDensity
  exact (signedErrorDensity_integrableOn k hcont).sub (leadingDensity_integrableOn k)

/-- Change-of-variables identity for `blockRemainder` in terms of `remainderDensity`. -/
theorem blockRemainder_eq_integral_density (k : ℕ)
    (hcont : ContinuousOn (errorTermOnBlock k)
      (Icc (hardyStart k) (hardyStart (k + 1)))) :
    blockRemainder k = ∫ p in Ioc (0 : ℝ) 1, remainderDensity k p := by
  unfold blockRemainder leadingBlockIntegral remainderDensity
  rw [block_integral_errorTerm_cov' k hcont]
  have h_ae :
      (fun p => errorTermOnBlock k (blockCoord k p) * blockJacobian k p)
        =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun p => ErrorTerm (blockCoord k p) * blockJacobian k p) := by
    filter_upwards [ae_Ioo_of_Ioc] with p hp
    rw [errorTerm_eq_on_blockCoord k p hp.1 hp.2]
  have h_cov_integral :
      ∫ p in Ioc (0 : ℝ) 1, errorTermOnBlock k (blockCoord k p) * blockJacobian k p
        = ∫ p in Ioc (0 : ℝ) 1, ErrorTerm (blockCoord k p) * blockJacobian k p :=
    integral_congr_ae h_ae
  rw [h_cov_integral]
  have hsigned :
      (-1 : ℝ) ^ k *
          ∫ p in Ioc (0 : ℝ) 1, ErrorTerm (blockCoord k p) * blockJacobian k p
        = ∫ p in Ioc (0 : ℝ) 1,
            (-1 : ℝ) ^ k * ErrorTerm (blockCoord k p) * blockJacobian k p := by
    calc
      (-1 : ℝ) ^ k *
          ∫ p in Ioc (0 : ℝ) 1, ErrorTerm (blockCoord k p) * blockJacobian k p
        = ∫ p in Ioc (0 : ℝ) 1,
            (-1 : ℝ) ^ k * (ErrorTerm (blockCoord k p) * blockJacobian k p) := by
            simpa [smul_eq_mul] using (integral_smul ((-1 : ℝ) ^ k)
              (fun p => ErrorTerm (blockCoord k p) * blockJacobian k p)
              (μ := volume.restrict (Ioc (0 : ℝ) 1))).symm
      _ = ∫ p in Ioc (0 : ℝ) 1,
            (-1 : ℝ) ^ k * ErrorTerm (blockCoord k p) * blockJacobian k p := by
            congr 1
            ext p
            simp [mul_assoc]
  have hleading :
      4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p
        = ∫ p in Ioc (0 : ℝ) 1,
            4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p := by
    calc
      4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p
        = ∫ p in Ioc (0 : ℝ) 1,
            (4 * Real.pi) * (Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) := by
            simpa [smul_eq_mul] using (integral_smul (4 * Real.pi)
              (fun p => Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
              (μ := volume.restrict (Ioc (0 : ℝ) 1))).symm
      _ = ∫ p in Ioc (0 : ℝ) 1,
            4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p := by
            congr 1
            ext p
            ring_nf
  rw [hsigned, hleading, ← integral_sub
    (signedErrorDensity_integrableOn k hcont) (leadingDensity_integrableOn k)]

/-- The remaining irreducible signed Gabcke input: pointwise antitonicity of the
    remainder density on the parameter interval. -/
private theorem remainderDensity_eq_weighted_signedSPR (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    remainderDensity k p =
      4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * signedSPR k (blockCoord k p) := by
  set t := blockCoord k p
  set amp : ℝ := (2 * Real.pi / t) ^ ((1 : ℝ) / 4)
  have ht_pos : 0 < t := by
    dsimp [t]
    rw [blockCoord_eq]
    positivity
  have hamp_pos : 0 < amp := by
    dsimp [amp]
    exact Real.rpow_pos_of_pos (div_pos (by positivity) ht_pos) _
  have h_signed :
      amp * signedSPR k t =
        (-1 : ℝ) ^ k * ErrorTerm t - amp * rsPsi (blockParam k t) := by
    unfold signedSPR saddlePointRemainder
    dsimp [amp]
    field_simp [hamp_pos.ne']
    rw [mul_sub]
    calc
      (-1 : ℝ) ^ k * ErrorTerm t -
          (-1 : ℝ) ^ k * ((2 * Real.pi / t) ^ ((1 : ℝ) / 4) * (-1 : ℝ) ^ k * rsPsi (blockParam k t))
        = (-1 : ℝ) ^ k * ErrorTerm t -
            (((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)) := by
              ring
      _ = (-1 : ℝ) ^ k * ErrorTerm t - (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
            rsPsi (blockParam k t) := by
              rw [neg_one_pow_sq k]
              ring
  have h_ampJ : amp * blockJacobian k p =
      4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) := by
    dsimp [amp, t]
    exact amplitude_times_jacobian k p hp
  have h_density :
      remainderDensity k p =
        (-1 : ℝ) ^ k * ErrorTerm t * blockJacobian k p - amp * blockJacobian k p * rsPsi p := by
    calc
      remainderDensity k p
        = (-1 : ℝ) ^ k * ErrorTerm (blockCoord k p) * blockJacobian k p -
            amp * blockJacobian k p * rsPsi p := by
              unfold remainderDensity
              rw [← h_ampJ]
      _ = (-1 : ℝ) ^ k * ErrorTerm t * blockJacobian k p - amp * blockJacobian k p * rsPsi p := by
              simp [t]
  calc
    remainderDensity k p
      = (-1 : ℝ) ^ k * ErrorTerm t * blockJacobian k p - amp * blockJacobian k p * rsPsi p := h_density
    _ = blockJacobian k p * (((-1 : ℝ) ^ k * ErrorTerm t) - amp * rsPsi p) := by ring
    _ = blockJacobian k p * (amp * signedSPR k t) := by
          rw [h_signed, blockParam_on_coord k p hp]
    _ = (amp * blockJacobian k p) * signedSPR k t := by ring
    _ = 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * signedSPR k t := by rw [h_ampJ]
    _ = 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * signedSPR k (blockCoord k p) := by
          simp [t]

/-- Algebraic factorization of the remainder density into the positive block
    Jacobian times the signed pointwise gap between `ErrorTerm` and its leading
    saddle term. -/
private theorem remainderDensity_eq_jacobian_gap (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    remainderDensity k p =
      blockJacobian k p *
        (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
          (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p) := by
  set t := blockCoord k p
  set amp : ℝ := (2 * Real.pi / t) ^ ((1 : ℝ) / 4)
  have h_ampJ : amp * blockJacobian k p =
      4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) := by
    dsimp [amp, t]
    exact amplitude_times_jacobian k p hp
  calc
    remainderDensity k p
      = (-1 : ℝ) ^ k * ErrorTerm (blockCoord k p) * blockJacobian k p -
          amp * blockJacobian k p * rsPsi p := by
            unfold remainderDensity
            rw [← h_ampJ]
    _ = (-1 : ℝ) ^ k * ErrorTerm t * blockJacobian k p - amp * blockJacobian k p * rsPsi p := by
          simp [t]
    _ = blockJacobian k p * (((-1 : ℝ) ^ k * ErrorTerm t) - amp * rsPsi p) := by
          ring
    _ = blockJacobian k p *
          (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
            (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p) := by
          simp [t, amp]

/-- The signed density gap on block coordinates is exactly the saddle amplitude
    times the signed saddle-point remainder. -/
private theorem densityGap_eq_amp_mul_signedSPR (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
      (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p) =
      (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * signedSPR k (blockCoord k p) := by
  set t := blockCoord k p
  set amp : ℝ := (2 * Real.pi / t) ^ ((1 : ℝ) / 4)
  have ht_pos : 0 < t := by
    dsimp [t]
    rw [blockCoord_eq]
    positivity
  have hamp_pos : 0 < amp := by
    dsimp [amp]
    exact Real.rpow_pos_of_pos (div_pos (by positivity) ht_pos) _
  have hsigned :
      amp * signedSPR k t =
        (-1 : ℝ) ^ k * ErrorTerm t - amp * rsPsi (blockParam k t) := by
    unfold signedSPR saddlePointRemainder
    dsimp [amp]
    field_simp [hamp_pos.ne']
    rw [mul_sub]
    calc
      (-1 : ℝ) ^ k * ErrorTerm t -
          (-1 : ℝ) ^ k * ((2 * Real.pi / t) ^ ((1 : ℝ) / 4) * (-1 : ℝ) ^ k * rsPsi (blockParam k t))
        = (-1 : ℝ) ^ k * ErrorTerm t -
            (((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)) := by
              ring
      _ = (-1 : ℝ) ^ k * ErrorTerm t - (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
            rsPsi (blockParam k t) := by
              rw [neg_one_pow_sq k]
              ring
  calc
    (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
        (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p)
      = (-1 : ℝ) ^ k * ErrorTerm t - amp * rsPsi (blockParam k t) := by
          rw [blockParam_on_coord k p hp]
    _ = amp * signedSPR k t := by rw [hsigned]
    _ = (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * signedSPR k (blockCoord k p) := by
          simp [t, amp]

/-- On block coordinates, multiplying the saddle amplitude by `u = k + 1 + p`
    gives `√u`. -/
private theorem block_u_mul_amp_eq_sqrt (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    ((k : ℝ) + 1 + p) * (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) =
      Real.sqrt ((k : ℝ) + 1 + p) := by
  set amp : ℝ := (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4)
  set u : ℝ := (k : ℝ) + 1 + p
  have h_ampJ := amplitude_times_jacobian k p hp
  have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
  have hscaled : (4 * Real.pi) * (u * amp) = (4 * Real.pi) * Real.sqrt u := by
    calc
      (4 * Real.pi) * (u * amp) = amp * (4 * Real.pi * u) := by ring
      _ = 4 * Real.pi * Real.sqrt u := by
            simpa [u, amp, blockJacobian_eq] using h_ampJ
  exact mul_left_cancel₀ h4pi_ne hscaled

/-- The weighted density gap is exactly the linear `u · signedSPR`
    normalization on block coordinates. -/
private theorem weightedDensityGap_eq_linear_signedSPR (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    (((k : ℝ) + 1 + p) * Real.sqrt ((k : ℝ) + 1 + p)) *
        (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
          (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p) =
      ((k : ℝ) + 1 + p) * signedSPR k (blockCoord k p) := by
  set u : ℝ := (k : ℝ) + 1 + p
  set amp : ℝ := (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4)
  set s : ℝ := signedSPR k (blockCoord k p)
  have hu_nonneg : 0 ≤ u := by
    have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    dsimp [u]
    linarith
  have hgap :
      (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
        (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p) = amp * s := by
    simpa [amp, s] using densityGap_eq_amp_mul_signedSPR k p hp
  have huamp : u * amp = Real.sqrt u := by
    simpa [u, amp] using block_u_mul_amp_eq_sqrt k p hp
  calc
    (u * Real.sqrt u) *
        (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
          (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p)
      = (u * Real.sqrt u) * (amp * s) := by rw [hgap]
    _ = (u * amp) * (Real.sqrt u * s) := by ring
    _ = Real.sqrt u * (Real.sqrt u * s) := by rw [huamp]
    _ = (Real.sqrt u * Real.sqrt u) * s := by ring
    _ = u * s := by
          have hsq : Real.sqrt u * Real.sqrt u = u := by
            simpa [sq] using (Real.sq_sqrt hu_nonneg)
          rw [hsq]
    _ = ((k : ℝ) + 1 + p) * signedSPR k (blockCoord k p) := by
          simp [u, s]

/-- The normalized weighted signed saddle remainder is exactly the block
    parameter `u = k + 1 + p` times the signed pointwise gap between
    `ErrorTerm` and its leading saddle term. This removes the residual square
    root and division structure from the adjacent-block comparison. -/
private theorem weightedSignedSPR_eq_linear_gap (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    weightedSignedSPR k p =
      ((k : ℝ) + 1 + p) *
        (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
          (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p) := by
  set u : ℝ := (k : ℝ) + 1 + p
  set amp : ℝ := (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4)
  set s : ℝ := signedSPR k (blockCoord k p)
  have huamp : u * amp = Real.sqrt u := by
    simpa [u, amp] using block_u_mul_amp_eq_sqrt k p hp
  have hgap :
      amp * s =
        (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
          (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p) := by
    simpa [amp, s] using (densityGap_eq_amp_mul_signedSPR k p hp).symm
  calc
    weightedSignedSPR k p = Real.sqrt u * s := by
      simp [weightedSignedSPR, u, s]
    _ = (u * amp) * s := by rw [huamp]
    _ = u * (amp * s) := by ring
    _ = u *
          (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
            (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p) := by
          rw [hgap]
    _ = ((k : ℝ) + 1 + p) *
          (((-1 : ℝ) ^ k * ErrorTerm (blockCoord k p)) -
            (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p) := by
          simp [u]

/-- The signed profile already has the expected Gabcke-size control:
    its magnitude is bounded by the universal next-order constant.
    The remaining leaf is therefore purely about sign, not size. -/
private theorem gabckeSignedProfile_abs_le [SiegelSaddleExpansionHyp]
    (p : ℝ) (hp : p ∈ Ioc (0 : ℝ) 1) :
    |gabckeSignedProfile p| ≤ 1 / (4 * Real.sqrt (2 * Real.pi)) := by
  have hp0 : 0 ≤ p := le_of_lt hp.1
  have hp1 : p ≤ 1 := hp.2
  have hmem : blockCoord 1 p ∈ Icc (hardyStart 1) (hardyStart (1 + 1)) :=
    blockCoord_mem_Icc 1 (Set.mem_Icc.mpr ⟨hp0, hp1⟩)
  have ht_pos : 0 < blockCoord 1 p := by
    rw [blockCoord_eq]
    positivity
  have hrem := SiegelSaddleExpansionHyp.remainder_bound 1 (blockCoord 1 p) hmem.1 hmem.2 ht_pos
  rw [← abs_signedSPR] at hrem
  have htwo_nonneg : 0 ≤ 2 + p := by linarith
  have htwo_pos : 0 < 2 + p := by linarith
  have habs :
      |gabckeSignedProfile p| ≤ (2 + p) * ((1 / 4) * (blockCoord 1 p) ^ (-(1 : ℝ) / 2)) := by
    rw [gabckeSignedProfile_eq_block1_signedSPR p hp0, abs_mul, abs_of_nonneg htwo_nonneg]
    exact mul_le_mul_of_nonneg_left hrem htwo_nonneg
  have hrpow :
      (blockCoord 1 p) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt (blockCoord 1 p) := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) from by ring]
    rw [Real.rpow_neg ht_pos.le]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
    rw [show ((blockCoord 1 p) ^ ((2 : ℝ)⁻¹))⁻¹ = 1 / (blockCoord 1 p) ^ ((2 : ℝ)⁻¹) from by ring]
    congr 1
    rw [show ((2 : ℝ)⁻¹) = 1 / 2 from by norm_num]
    exact (Real.sqrt_eq_rpow (blockCoord 1 p)).symm
  have hcoord : blockCoord 1 p = 2 * Real.pi * (2 + p) ^ 2 := by
    rw [blockCoord_eq]
    ring
  calc
    |gabckeSignedProfile p|
      ≤ (2 + p) * ((1 / 4) * (blockCoord 1 p) ^ (-(1 : ℝ) / 2)) := habs
    _ = (1 / 4) * (2 + p) * (1 / Real.sqrt (blockCoord 1 p)) := by
          rw [hrpow]
          ring
    _ = (1 / 4) * (2 + p) * (1 / (Real.sqrt (2 * Real.pi) * (2 + p))) := by
          rw [hcoord, Real.sqrt_mul (by positivity) ((2 + p) ^ 2),
            Real.sqrt_sq (by linarith : 0 ≤ 2 + p)]
    _ = 1 / (4 * Real.sqrt (2 * Real.pi)) := by
          field_simp [htwo_pos.ne']

/-- Localized Gabcke signed-profile input.

    This packages the remaining signed Satz 4 content in the exact density-level
    form used below:
    1. the weighted signed saddle remainder has the block profile
       `gabckeSignedProfile(p) / √(k+1+p)` on matched block coordinates
    2. that profile is nonnegative on `Ioc (0,1]`

    With these two fields in hand, the adjacent density comparison is purely
    algebraic via `inv_sqrt_block_antitone`. -/
class GabckeSignedProfileHyp : Prop where
  weightedSignedSPR_eq_profile :
    ∀ k : ℕ, ∀ p : ℝ, p ∈ Ioc (0 : ℝ) 1 →
      weightedSignedSPR k p =
        gabckeSignedProfile p / Real.sqrt ((k : ℝ) + 1 + p)
  profile_nonneg :
    ∀ p : ℝ, p ∈ Ioc (0 : ℝ) 1 → 0 ≤ gabckeSignedProfile p

/-- Minimal signed Gabcke input actually consumed by the density route:
    adjacent antitonicity of the normalized weighted signed saddle remainder
    on matched block coordinates. This is strictly weaker than the explicit
    profile package above and is the honest remaining pointwise leaf. -/
def GabckeSignedAdjacentProp : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ p : ℝ, p ∈ Ioc (0 : ℝ) 1 →
    weightedSignedSPR (k + 1) p ≤ weightedSignedSPR k p

/-- Thin class wrapper around the theorem-first adjacent Gabcke leaf. This
    keeps existing instance-style downstream use stable while exposing the
    pointwise theorem shape directly. -/
class GabckeSignedAdjacentHyp : Prop where
  weightedSignedSPR_adjacent : GabckeSignedAdjacentProp

/-- Extract the theorem-first adjacent Gabcke leaf from the wrapper class. -/
theorem gabckeSignedAdjacentProp_of_hyp [h : GabckeSignedAdjacentHyp] :
    GabckeSignedAdjacentProp :=
  h.weightedSignedSPR_adjacent

/-- Package the theorem-first adjacent Gabcke leaf into the legacy class
    wrapper. -/
theorem gabckeSignedAdjacentHyp_of_prop
    (h : GabckeSignedAdjacentProp) : GabckeSignedAdjacentHyp where
  weightedSignedSPR_adjacent := h

/-- The explicit Gabcke profile is bounded above by the universal quarter-size
    coefficient once its sign is supplied. -/
private theorem gabckeSignedProfile_le [SiegelSaddleExpansionHyp]
    [hprof : GabckeSignedProfileHyp] (p : ℝ) (hp : p ∈ Ioc (0 : ℝ) 1) :
    gabckeSignedProfile p ≤ 1 / (4 * Real.sqrt (2 * Real.pi)) := by
  have habs := gabckeSignedProfile_abs_le p hp
  have hnn := hprof.profile_nonneg p hp
  rw [abs_of_nonneg hnn] at habs
  exact habs

/-- Atomic Gabcke Satz 4 leaf, reduced to the exact adjacent profile statement
    consumed on the main path:
    for `k ≥ 1`, the signed block remainder is antitone across adjacent blocks.

    This is strictly smaller than the previous a.e. density leaf:
    all CoV, density, Jacobian, amplitude, and endpoint bookkeeping is
    discharged constructively above it, and the only remaining content is the
    signed profile identity and positivity encoded in
    `GabckeSignedProfileHyp`.

    The adjacent comparison itself is now constructive from that profile:
    `gabckeSignedProfile(p) / √(k+2+p) ≤ gabckeSignedProfile(p) / √(k+1+p)`.

    Reference: Gabcke 1979 Satz 4, Tabelle 1; Siegel 1932 §3. -/
private theorem weightedSignedSPR_adjacent_atomic [hprof : GabckeSignedProfileHyp]
    (k : ℕ) (_hk : 1 ≤ k) :
    ∀ p, p ∈ Ioc (0 : ℝ) 1 →
      weightedSignedSPR (k + 1) p ≤ weightedSignedSPR k p := by
  intro p hp
  have hp0 : 0 ≤ p := le_of_lt hp.1
  have hscale :
      1 / Real.sqrt ((k : ℝ) + 2 + p) ≤
        1 / Real.sqrt ((k : ℝ) + 1 + p) :=
    inv_sqrt_block_antitone k p hp0
  have hnn : 0 ≤ gabckeSignedProfile p := hprof.profile_nonneg p hp
  have hcast : ((↑(k + 1) : ℝ) + 1 + p) = (k : ℝ) + 2 + p := by
    push_cast
    ring
  rw [hprof.weightedSignedSPR_eq_profile (k + 1) p hp,
    hprof.weightedSignedSPR_eq_profile k p hp, hcast]
  calc
    gabckeSignedProfile p / Real.sqrt ((k : ℝ) + 2 + p)
      = gabckeSignedProfile p * (1 / Real.sqrt ((k : ℝ) + 2 + p)) := by
          simp [div_eq_mul_inv]
    _ ≤ gabckeSignedProfile p * (1 / Real.sqrt ((k : ℝ) + 1 + p)) := by
          exact mul_le_mul_of_nonneg_left hscale hnn
    _ = gabckeSignedProfile p / Real.sqrt ((k : ℝ) + 1 + p) := by
          simp [div_eq_mul_inv]

/-- The explicit signed profile is one sufficient way to produce the smaller
    adjacent weighted-remainder hypothesis used downstream. -/
instance [GabckeSignedProfileHyp] : GabckeSignedAdjacentHyp where
  weightedSignedSPR_adjacent := weightedSignedSPR_adjacent_atomic

/-- The stronger explicit profile package also supplies the theorem-first
    adjacent Gabcke leaf directly. -/
theorem gabckeSignedAdjacentProp_of_profile [GabckeSignedProfileHyp] :
    GabckeSignedAdjacentProp :=
  weightedSignedSPR_adjacent_atomic

/-- Atomic Gabcke Satz 4 leaf specialized to the density used in the CoV
    argument. All Jacobian/amplitude algebra has been discharged above, so the
    only remaining signed content is adjacent antitonicity of the normalized
    weighted signed saddle-point remainder. -/
private theorem remainderDensity_adjacent_ae_atomic [GabckeSignedAdjacentHyp]
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      remainderDensity (k + 1) p ≤ remainderDensity k p := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with p hp
  have hp0 : 0 ≤ p := le_of_lt hp.1
  calc
    remainderDensity (k + 1) p
      = 4 * Real.pi * weightedSignedSPR (k + 1) p := by
          simpa [weightedSignedSPR, mul_assoc] using
            remainderDensity_eq_weighted_signedSPR (k + 1) p hp0
    _ ≤ 4 * Real.pi * weightedSignedSPR k p := by
          exact mul_le_mul_of_nonneg_left
            (GabckeSignedAdjacentHyp.weightedSignedSPR_adjacent k hk p hp)
            (by positivity)
    _ = remainderDensity k p := by
          symm
          simpa [weightedSignedSPR, mul_assoc] using remainderDensity_eq_weighted_signedSPR k p hp0

/-- Adjacent block antitonicity follows constructively from the a.e. density
comparison together with the already-proved CoV and integrability lemmas. -/
private theorem blockRemainder_adjacent_antitone_atomic [GabckeSignedAdjacentHyp]
    (k : ℕ) (hk : 1 ≤ k) :
    blockRemainder (k + 1) ≤ blockRemainder k := by
  let hcont_k : ContinuousOn (errorTermOnBlock k)
      (Icc (hardyStart k) (hardyStart (k + 1))) :=
    errorTermOnBlock_continuousOn_local k
  let hcont_k1 : ContinuousOn (errorTermOnBlock (k + 1))
      (Icc (hardyStart (k + 1)) (hardyStart (k + 2))) :=
    errorTermOnBlock_continuousOn_local (k + 1)
  exact blockRemainder_antitone_of_density_antitone_ae k hk
    (blockRemainder_eq_integral_density k hcont_k)
    (blockRemainder_eq_integral_density (k + 1) hcont_k1)
    (remainderDensity_adjacent_ae_atomic k hk)
    (remainderDensity_integrableOn k hcont_k)
    (remainderDensity_integrableOn (k + 1) hcont_k1)

/-- **Signed remainder antitonicity** (Gabcke Satz 4, irreducible content).

    The block remainder R(k) = (-1)^k · I_k - L_k is antitone for k ≥ 1.

    PROOF CHAIN (Gabcke 1979 Satz 4):
    (1) Via CoV: R(k) = ∫₀¹ ρ(k,p) dp where ρ = remainderDensity.
    (2) ρ(k,p) = 4π√(k+1+p) · signedSPR(k, blockCoord(k,p))
        where signedSPR = (-1)^k · saddlePointRemainder.
    (3) signedSPR(k,t) ≥ 0 for t in block k, k ≥ 1.
        This is the SIGNED Gabcke bound: c₁(p) > 0 for p ∈ [0,1].
    (4) signedSPR(k,blockCoord(k,p)) ≈ c₁(p)/(√(2π)·(k+1+p))
    (5) 4π√(k+1+p) · c₁(p)/(√(2π)·(k+1+p)) = 4π·c₁(p)/(√(2π)·√(k+1+p))
    (6) This is antitone in k, so ρ(k,p) ≥ ρ(k+1,p) pointwise.
    (7) By integral_mono (blockRemainder_antitone_of_density_antitone):
        R(k) ≥ R(k+1).

    EXPLICIT ANALYTIC INPUT:
    The localized signed content of Gabcke Satz 4 is now isolated in
    `GabckeSignedAdjacentHyp`: adjacent pointwise antitonicity of the weighted
    signed saddle remainder on matched block coordinates. The stronger
    profile package `GabckeSignedProfileHyp` remains a sufficient way to build
    that smaller input. Once the adjacent comparison is supplied, all
    surrounding reduction steps are constructive:
    - Step (1): CoV via blockRemainder_eq_integral_density +
      errorTermOnBlock_continuousOn_local
    - Step (7): integral_mono via blockRemainder_antitone_of_density_antitone_ae
    - Integrability: remainderDensity_integrableOn
    - Amplitude/Jacobian: amplitude_times_jacobian (GabckeFresnelMonotone)
    - 1/sqrt decay: inv_sqrt_block_antitone (GabckeFresnelMonotone)

    Reference: Gabcke 1979 Satz 4, Tabelle 1; Siegel 1932 §3. -/
private theorem signed_remainder_density_monotone [GabckeSignedAdjacentHyp]
    (k : ℕ) (hk : 1 ≤ k) :
    blockRemainder (k + 1) ≤ blockRemainder k := by
  exact blockRemainder_adjacent_antitone_atomic k hk

theorem remainder_antitone_for_ge_one_of_adjacent [GabckeSignedAdjacentHyp]
    (k : ℕ) (hk : 1 ≤ k) :
    blockRemainder (k + 1) ≤ blockRemainder k :=
  signed_remainder_density_monotone k hk

/-- The direct theorem-first adjacent-pointwise Gabcke route. This is the
    smallest external theorem surface for the remainder antitonicity step;
    `GabckeSignedAdjacentHyp` remains only as a compatibility wrapper. -/
theorem remainder_antitone_for_ge_one_of_adjacent_prop
    (h : GabckeSignedAdjacentProp) (k : ℕ) (hk : 1 ≤ k) :
    blockRemainder (k + 1) ≤ blockRemainder k := by
  let _ : GabckeSignedAdjacentHyp := gabckeSignedAdjacentHyp_of_prop h
  exact remainder_antitone_for_ge_one_of_adjacent k hk

/-- Main exported remainder-antitonicity theorem.

    This file's honest explicit boundary is now the smaller adjacent-pointwise
    input `GabckeSignedAdjacentHyp`.  All remaining CoV, density, Jacobian,
    amplitude, and integrability steps are already constructive above. -/
theorem remainder_antitone_for_ge_one [GabckeSignedAdjacentHyp]
    (k : ℕ) (hk : 1 ≤ k) :
    blockRemainder (k + 1) ≤ blockRemainder k :=
  remainder_antitone_for_ge_one_of_adjacent k hk

/-- Legacy wrapper through the stronger explicit profile surface. The actual
    density argument only needs `GabckeSignedAdjacentHyp`, and the profile
    package supplies it via the instance above. -/
theorem remainder_antitone_for_ge_one_of_profile [GabckeSignedProfileHyp]
    (k : ℕ) (hk : 1 ≤ k) :
    blockRemainder (k + 1) ≤ blockRemainder k :=
  remainder_antitone_for_ge_one_of_adjacent_prop
    gabckeSignedAdjacentProp_of_profile k hk

/-! ## Part 12: Steepest-descent adjacent coupling — TRUE replacement for
    false GabckeBlockIndependence

GabckeBlockIndependence (exact k-independence of the normalized signed
remainder) is mathematically false: higher-order terms in the steepest-descent
expansion break exact k-independence. However, the steepest-descent structure
DOES give two weaker TRUE properties that together imply the adjacent
monotonicity `GabckeSignedAdjacentProp`:

(A) **Signed positivity on all blocks k ≥ 1**: the Fresnel phase structure
    ensures `signedSPR k (blockCoord k p) ≥ 0` for all k ≥ 1, not just k = 1.
    The leading Fresnel coefficient c₁(p) > 0 on (0,1], and the remainder is
    O(1/(k+1+p)) smaller, so positivity holds for all k ≥ 1.

(B) **Normalized remainder nonincreasing**: the product
    `(k+1+p) · signedSPR k (blockCoord k p)` converges to `c₁(p)/√(2π)` from
    above as k → ∞ (the corrections are positive and O(1/(k+1+p))). Hence
    this product is nonincreasing in k for k ≥ 1.

These two properties combine to give adjacent monotonicity:
  wSPR(k+1,p) = u_{k+1}/√(k+2+p) ≤ u_k/√(k+2+p) ≤ u_k/√(k+1+p) = wSPR(k,p)
where u_k = (k+1+p) · signedSPR k (blockCoord k p) ≥ 0 and u_{k+1} ≤ u_k.

Reference: Gabcke 1979 Satz 4; steepest-descent expansion §3. -/

/-- Steepest-descent adjacent coupling hypothesis.

    This packages the TRUE content of Gabcke Satz 4 that replaces the false
    `GabckeBlockIndependence`. The steepest-descent expansion on consecutive
    blocks gives:
    (A) The signed saddle-point remainder is nonneg on all blocks k ≥ 1
        (from the Fresnel phase structure: the leading coefficient c₁(p) > 0).
    (B) The normalized product `(k+1+p) · signedSPR k (blockCoord k p)` is
        nonincreasing in k (the asymptotic expansion converges from above).

    Both conditions are TRUE, unlike `GabckeBlockIndependence` which falsely
    claimed exact k-independence. -/
class SteepestDescentAdjacentCoupling : Prop where
  /-- The signed saddle-point remainder is nonneg on all blocks k ≥ 1.
      This generalizes `GabckeSignPositivity` (which only asserts k = 1) to
      all blocks, using the universal Fresnel phase structure. -/
  signed_nonneg :
    ∀ k : ℕ, 1 ≤ k → ∀ p : ℝ, p ∈ Ioc (0 : ℝ) 1 →
      0 ≤ signedSPR k (blockCoord k p)
  /-- The normalized signed remainder `(k+1+p) · signedSPR k (blockCoord k p)`
      is nonincreasing in k for k ≥ 1. This is weaker than block independence
      (which claims constancy) but captures the monotone convergence of the
      steepest-descent expansion to its asymptotic limit. -/
  normalized_antitone :
    ∀ k : ℕ, 1 ≤ k → ∀ p : ℝ, p ∈ Ioc (0 : ℝ) 1 →
      ((k : ℝ) + 2 + p) * signedSPR (k + 1) (blockCoord (k + 1) p) ≤
        ((k : ℝ) + 1 + p) * signedSPR k (blockCoord k p)

/-
PROBLEM
`GabckeSignedAdjacentProp` from the steepest-descent adjacent coupling.

    The proof combines the two coupling conditions:
    1. `u_{k+1} ≤ u_k` (normalized antitone) gives
       `u_{k+1}/√(k+2+p) ≤ u_k/√(k+2+p)`
    2. `u_k ≥ 0` (signed nonneg) gives `u_k/√(k+2+p) ≤ u_k/√(k+1+p)`
       since `√(k+2+p) ≥ √(k+1+p)` and dividing a nonneg number by a
       larger positive denominator gives a smaller result.

    Together: `wSPR(k+1) ≤ wSPR(k)`.

PROVIDED SOLUTION
The proof combines two coupling conditions from SteepestDescentAdjacentCoupling:

1. signed_nonneg: signedSPR k (blockCoord k p) ≥ 0 for k ≥ 1
2. normalized_antitone: (k+2+p) · signedSPR(k+1, blockCoord(k+1,p)) ≤ (k+1+p) · signedSPR(k, blockCoord(k,p))

We need to show weightedSignedSPR (k+1) p ≤ weightedSignedSPR k p.

Unfolding weightedSignedSPR, this is:
  √(k+2+p) · signedSPR(k+1, blockCoord(k+1,p)) ≤ √(k+1+p) · signedSPR(k, blockCoord(k,p))

Note ((k+1:ℕ):ℝ) + 1 + p = (k:ℝ) + 2 + p (by push_cast; ring).

Set u_k = (k+1+p) · signedSPR(k, blockCoord(k,p)) and u_k1 = (k+2+p) · signedSPR(k+1, blockCoord(k+1,p)).

Key facts:
- u_k ≥ 0 (from signed_nonneg and positivity of (k+1+p))
- u_k1 ≤ u_k (from normalized_antitone)
- √(k+1+p) > 0, √(k+2+p) > 0, √(k+1+p) ≤ √(k+2+p)

The goal √(k+2+p) · s₁ ≤ √(k+1+p) · s₀ where s₀ = signedSPR k ..., s₁ = signedSPR(k+1,...)
is equivalent to u_k1/√(k+2+p) ≤ u_k/√(k+1+p) since √a · x = (a·x)/√a when √a·√a = a.

Then: u_k1/√(k+2+p) ≤ u_k/√(k+2+p) (by div_le_div_of_nonneg_right since u_k1 ≤ u_k and √(k+2+p) ≥ 0)
      ≤ u_k/√(k+1+p) (by div_le_div_of_nonneg_left since u_k ≥ 0 and √(k+1+p) ≤ √(k+2+p))
-/
theorem gabckeSignedAdjacentProp_of_coupling
    [hc : SteepestDescentAdjacentCoupling] :
    GabckeSignedAdjacentProp := by
  intro k hk p hp;
  obtain ⟨h₁, h₂⟩ := hc;
  -- By combining the results from h₁ and h₂, we can conclude the proof.
  have h_combined : Real.sqrt ((k + 2 + p) * (k + 1 + p)) * signedSPR (k + 1) (blockCoord (k + 1) p) ≤ (k + 1 + p) * signedSPR k (blockCoord k p) := by
    refine' le_trans _ ( h₂ k hk p hp );
    exact mul_le_mul_of_nonneg_right ( Real.sqrt_le_iff.mpr ⟨ by nlinarith [ hp.1 ], by nlinarith [ hp.1, hp.2 ] ⟩ ) ( h₁ _ ( by linarith ) _ hp );
  convert div_le_div_of_nonneg_right h_combined ( Real.sqrt_nonneg ( k + 1 + p ) ) using 1;
  · rw [ eq_div_iff ];
    · unfold weightedSignedSPR; rw [ Real.sqrt_mul <| by linarith [ hp.1 ] ] ; ring;
      push_cast; ring;
    · exact ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ hp.1 ];
  · unfold weightedSignedSPR; rw [ eq_div_iff ( ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ hp.1 ] ) ] ; ring;
    rw [ Real.sq_sqrt ] <;> linarith [ hp.1 ]

/-- Instance: steepest-descent adjacent coupling provides `GabckeSignedAdjacentHyp`. -/
instance [SteepestDescentAdjacentCoupling] : GabckeSignedAdjacentHyp :=
  gabckeSignedAdjacentHyp_of_prop gabckeSignedAdjacentProp_of_coupling

/-- The steepest-descent coupling route also provides block-correction
    antitonicity via the existing chain. -/
theorem remainder_antitone_for_ge_one_of_coupling
    [SteepestDescentAdjacentCoupling]
    (k : ℕ) (hk : 1 ≤ k) :
    blockRemainder (k + 1) ≤ blockRemainder k :=
  remainder_antitone_for_ge_one_of_adjacent_prop
    gabckeSignedAdjacentProp_of_coupling k hk

end Aristotle.Standalone.GabckePhaseCouplingInfra