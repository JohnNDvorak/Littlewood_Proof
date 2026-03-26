/-
B3 block structure obligations derived from the RS expansion hypothesis.

The three B3 obligations (c_fn nonneg, antitone, interpolation) are derived
from the Riemann-Siegel pointwise expansion on blocks. The derivation uses:

1. Change of variables (block_integral_cov) to convert block integrals
   to integrals over [0,1] with Jacobian 4π(k+1+p)
2. The algebraic identity (2π/t)^{1/4} = (k+1+p)^{-1/2} on blocks
3. rsPsi positivity and the weighted integral lower bound
4. Concavity of √ for the antitone property

## Architecture

The proof requires C_R ≤ 1/2 (Gabcke 1979 gives C_R ≈ 0.127). This ensures
the RS correction dominates the remainder for all blocks.

SORRY COUNT: 0 (antitone + interpolation supplied as hypotheses from RSExpansionProof)

Reference: Siegel 1932 §3; Edwards Ch. 7.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.HardyNProperties

set_option maxHeartbeats 3200000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B3BlockStructureFromExpansion

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.ErrorTermExpansion Aristotle.RSBlockParam Aristotle.HardyNProperties

-- ============================================================
-- Signed block integral lower bound
-- ============================================================

/-- Algebraic identity: (2π / (2π·a²))^{1/4} = a^{-1/2} for a > 0.
    Used for the leading-order RS term after change of variables. -/
private theorem rpow_quarter_simplify' (a : ℝ) (h : 0 < a) :
    (2 * Real.pi / (2 * Real.pi * a ^ 2)) ^ ((1 : ℝ) / 4) = a ^ (-(1 : ℝ) / 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have step1 : 2 * Real.pi / (2 * Real.pi * a ^ 2) = a ^ (-(2 : ℝ)) := by
    have ha2 : a ^ 2 = a ^ ((2 : ℕ) : ℝ) := (rpow_natCast a 2).symm
    rw [ha2, show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_cast]
    rw [rpow_neg h.le]
    field_simp
  rw [step1, ← rpow_mul h.le]
  norm_num

/-- Algebraic identity: (2π·a²)^{-3/4} = (2π)^{-3/4} · a^{-3/2} for a > 0.
    Used for the RS remainder term after change of variables. -/
private theorem rpow_neg_three_quarter_simplify (a : ℝ) (h : 0 < a) :
    (2 * Real.pi * a ^ 2) ^ (-(3 : ℝ) / 4) =
    (2 * Real.pi) ^ (-(3 : ℝ) / 4) * a ^ (-(3 : ℝ) / 2) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have ha2 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
  rw [show (2 : ℝ) * Real.pi * a ^ 2 = (2 * Real.pi) * a ^ 2 from by ring]
  rw [mul_rpow hpi.le ha2]
  congr 1
  rw [show a ^ 2 = a ^ ((2 : ℕ) : ℝ) from (rpow_natCast a 2).symm,
      show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_cast,
      ← rpow_mul h.le]
  norm_num

/-- Pointwise signed lower bound: (-1)^k · ErrorTerm(t) ≥ leading - remainder.
    From |ET - (-1)^k · L| ≤ R, we get (-1)^k · ET ≥ L - R via
    |(-1)^k · ET - L| = |(-1)^k| · |ET - (-1)^k · L| = |ET - (-1)^k · L| ≤ R. -/
private theorem signed_pointwise_lower (k : ℕ) (t : ℝ)
    (C_R : ℝ)
    (h : |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) -
      C_R * t ^ (-(3 : ℝ) / 4) ≤ (-1 : ℝ) ^ k * ErrorTerm t := by
  -- From |ET - (-1)^k · A| ≤ B, we get:
  --   -B ≤ ET - (-1)^k * A  (from -|x| ≤ x combined with |x| ≤ B)
  -- i.e., (-1)^k * A - B ≤ ET
  -- Then multiply by (-1)^k to get A - B ≤ (-1)^k * ET (using (-1)^{2k} = 1)
  -- For the multiplication, case-split on parity of k.
  have h_lb : ErrorTerm t ≥
      (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) -
      C_R * t ^ (-(3 : ℝ) / 4) := by
    have := neg_abs_le (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
        rsPsi (blockParam k t))
    linarith
  have h_ub : ErrorTerm t ≤
      (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) +
      C_R * t ^ (-(3 : ℝ) / 4) := by
    have := le_abs_self (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
        rsPsi (blockParam k t))
    linarith
  -- Case split on parity
  rcases Int.even_or_odd (k : ℤ) with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- Even: (-1)^k = 1
    have hpow : (-1 : ℝ) ^ k = 1 := Even.neg_one_pow ⟨m.toNat, by omega⟩
    rw [hpow] at h_lb ⊢; linarith
  · -- Odd: (-1)^k = -1
    have hpow : (-1 : ℝ) ^ k = -1 := Odd.neg_one_pow ⟨m.toNat, by omega⟩
    rw [hpow] at h_ub ⊢; linarith

private theorem signed_integral_lower_bound
    (C_R : ℝ) (_hCR_pos : 0 < C_R)
    (h_rs : ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t < hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4))
    (k : ℕ) :
    4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
      - C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
          ∫ p in Ioc (0 : ℝ) 1, ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2))
    ≤ (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t) := by
  -- Positivity prerequisites
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hhs_pos : 0 < hardyStart k := by rw [hardyStart_formula]; positivity
  -- Step 1: Define the lower-bound function
  set lb : ℝ → ℝ := fun t =>
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) -
      C_R * t ^ (-(3 : ℝ) / 4)
  -- Step 2: lb is continuous on the closed block (since t > 0 throughout)
  have hlb_cont : ContinuousOn lb (Icc (hardyStart k) (hardyStart (k + 1))) := by
    apply ContinuousOn.sub
    · -- (2π/t)^{1/4} * Ψ(blockParam k t) is continuous
      apply ContinuousOn.mul
      · -- (2π/t)^{1/4} is continuous for t > 0: exponent 1/4 > 0
        exact (ContinuousOn.div continuousOn_const continuousOn_id
          (fun t ht => ne_of_gt (lt_of_lt_of_le hhs_pos ht.1))).rpow_const
          (fun _ _ => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))
      · -- Ψ(blockParam k t) is continuous
        exact rsPsi_continuousOn.comp
          (ContinuousOn.sub
            (ContinuousOn.sqrt (ContinuousOn.div continuousOn_id continuousOn_const
              (fun _ _ => ne_of_gt h2pi)))
            continuousOn_const)
          (fun t ht => by
            constructor
            · exact blockParam_nonneg k t ht.1
            · -- blockParam k t ≤ 1 when t ≤ hardyStart(k+1)
              unfold blockParam
              have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
              have hk2 : (0 : ℝ) ≤ (k : ℝ) + 2 := by positivity
              suffices h : Real.sqrt (t / (2 * Real.pi)) ≤ (k : ℝ) + 2 by linarith
              calc Real.sqrt (t / (2 * Real.pi))
                  ≤ Real.sqrt (hardyStart (k + 1) / (2 * Real.pi)) :=
                    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ht.2 (le_of_lt hpi))
                _ = Real.sqrt (((k : ℝ) + 2) ^ 2) := by
                    congr 1; rw [hardyStart_formula]; push_cast; field_simp; ring
                _ = (k : ℝ) + 2 := Real.sqrt_sq hk2)
    · -- C_R * t^{-3/4} is continuous for t > 0
      exact continuousOn_const.mul
        (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hhs_pos ht.1))))
  -- Step 3: The signed pointwise lower bound holds on the block
  have h_ptwise_ae : lb ≤ᵐ[volume.restrict (Ioc (hardyStart k) (hardyStart (k + 1)))] fun t => (-1 : ℝ) ^ k * ErrorTerm t := by
    have h_ne : ∀ᵐ t ∂(volume : Measure ℝ),
        t ≠ hardyStart (k + 1) := by
      rw [Filter.eventually_iff]; simp only [ne_eq]
      exact measure_mono_null (fun t ht => by simpa using ht) Real.volume_singleton
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h_ne] with t ht_ne ht
    exact signed_pointwise_lower k t C_R
      (h_rs k t (le_of_lt ht.1) (lt_of_le_of_ne ht.2 ht_ne) (lt_trans hhs_pos ht.1))
  -- Step 4: Integrability of lb on Ioc
  have hlb_int : IntegrableOn lb (Ioc (hardyStart k) (hardyStart (k + 1))) :=
    hlb_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  -- Step 5: Integrability of (-1)^k * ErrorTerm on Ioc
  have hET_block_int : IntegrableOn ErrorTerm
      (Ioc (hardyStart k) (hardyStart (k + 1))) := by
    have h_big := errorTerm_integrable (hardyStart (k + 1))
    have h1_le_hs : 1 ≤ hardyStart k := by
      rw [hardyStart_formula]
      have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; nlinarith
      nlinarith [Real.pi_gt_three]
    exact h_big.mono_set (Ioc_subset_Ioc_left h1_le_hs)
  have hET_int : IntegrableOn (fun t => (-1 : ℝ) ^ k * ErrorTerm t)
      (Ioc (hardyStart k) (hardyStart (k + 1))) :=
    hET_block_int.const_mul _
  -- Step 6: Integral monotonicity: ∫ lb ≤ ∫ (-1)^k · ET
  have h_int_mono : ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), lb t
      ≤ ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          (-1 : ℝ) ^ k * ErrorTerm t := by
    exact setIntegral_mono_ae_restrict hlb_int hET_int h_ptwise_ae
  -- Step 7: ∫ (-1)^k · ET = (-1)^k · ∫ ET
  have h_factor : ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
      (-1 : ℝ) ^ k * ErrorTerm t =
      (-1 : ℝ) ^ k * ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := by
    simp_rw [← smul_eq_mul]
    exact integral_smul _ _
  -- Step 8: Apply COV to lb via block_integral_cov
  have h_cov : ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), lb t
      = ∫ p in Ioc (0 : ℝ) 1, lb (blockCoord k p) * blockJacobian k p :=
    block_integral_cov k lb hlb_cont
  -- Step 9: Simplify lb(blockCoord k p) * blockJacobian(k, p)
  -- We need: lb(bc p) * bj p = 4π·√(k+1+p)·Ψ(p) - C_R·4π·(2π)^{-3/4}·(k+1+p)^{-1/2}
  have h_simplify : ∀ p ∈ Ioc (0 : ℝ) 1,
      lb (blockCoord k p) * blockJacobian k p =
      4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p -
      C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
        ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2)) := by
    intro p hp
    have hp0 : 0 < p := hp.1
    have hkp : (0 : ℝ) < (k : ℝ) + 1 + p := by positivity
    -- blockParam_blockCoord: blockParam k (blockCoord k p) = p
    have hbp : blockParam k (blockCoord k p) = p :=
      blockParam_blockCoord k p hp0.le
    -- Unfold blockCoord and blockJacobian
    -- blockCoord k p = 2π(k+1+p)², blockJacobian k p = 4π(k+1+p)
    have hbc : blockCoord k p = 2 * Real.pi * ((k : ℝ) + 1 + p) ^ 2 := rfl
    have hbj : blockJacobian k p = 4 * Real.pi * ((k : ℝ) + 1 + p) := rfl
    -- (2π / blockCoord)^{1/4} = (k+1+p)^{-1/2}
    have h_leading_rpow :
        (2 * Real.pi / (blockCoord k p)) ^ ((1 : ℝ) / 4) = ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) := by
      rw [hbc]; exact rpow_quarter_simplify' ((k : ℝ) + 1 + p) hkp
    -- blockCoord^{-3/4} = (2π)^{-3/4} · (k+1+p)^{-3/2}
    have h_error_rpow :
        (blockCoord k p) ^ (-(3 : ℝ) / 4) =
        (2 * Real.pi) ^ (-(3 : ℝ) / 4) * ((k : ℝ) + 1 + p) ^ (-(3 : ℝ) / 2) := by
      rw [hbc]; exact rpow_neg_three_quarter_simplify ((k : ℝ) + 1 + p) hkp
    -- (k+1+p)^{-1/2} * 4π(k+1+p) = 4π · √(k+1+p)
    -- Need: a^{-1/2} * (4π * a) = 4π * a^{1/2} = 4π * √a
    have h_prod1 : ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * (4 * Real.pi * ((k : ℝ) + 1 + p)) =
        4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) := by
      rw [Real.sqrt_eq_rpow]
      have h_rpow_combine : ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * ((k : ℝ) + 1 + p) =
          ((k : ℝ) + 1 + p) ^ ((1 : ℝ) / 2) := by
        conv_rhs => rw [show (1 : ℝ) / 2 = -(1 : ℝ) / 2 + 1 from by ring]
        rw [rpow_add hkp, rpow_one]
      nlinarith
    -- Assemble: lb(bc p) * bj p
    simp only [lb, hbp]
    -- LHS = ((2π/bc)^{1/4} * Ψ(p) - C_R * bc^{-3/4}) * bj
    -- = (2π/bc)^{1/4} * Ψ(p) * bj - C_R * bc^{-3/4} * bj
    rw [sub_mul, h_leading_rpow, h_error_rpow, hbj]
    -- LHS = (k+1+p)^{-1/2} * Ψ(p) * (4π(k+1+p)) - C_R * ((2π)^{-3/4} * (k+1+p)^{-3/2}) * (4π(k+1+p))
    -- Need to show this equals: 4π·√(k+1+p)·Ψ(p) - C_R·(4π·(2π)^{-3/4}·(k+1+p)^{-1/2})
    -- Leading: (k+1+p)^{-1/2} * rsPsi p * 4π(k+1+p) = 4π·√(k+1+p)·rsPsi p
    have hlead : ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * rsPsi p *
        (4 * Real.pi * ((k : ℝ) + 1 + p)) =
        4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p := by
      rw [show ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * rsPsi p *
          (4 * Real.pi * ((k : ℝ) + 1 + p)) =
          (((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * (4 * Real.pi * ((k : ℝ) + 1 + p))) *
          rsPsi p from by ring]
      rw [h_prod1]
    -- Error: C_R * ((2π)^{-3/4} * (k+1+p)^{-3/2}) * 4π(k+1+p)
    --   = C_R * (4π · (2π)^{-3/4} · (k+1+p)^{-1/2})
    have herr : C_R * ((2 * Real.pi) ^ (-(3 : ℝ) / 4) * ((k : ℝ) + 1 + p) ^ (-(3 : ℝ) / 2)) *
        (4 * Real.pi * ((k : ℝ) + 1 + p)) =
        C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
          ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2)) := by
      rw [show C_R * ((2 * Real.pi) ^ (-(3 : ℝ) / 4) * ((k : ℝ) + 1 + p) ^ (-(3 : ℝ) / 2)) *
          (4 * Real.pi * ((k : ℝ) + 1 + p)) =
          C_R * ((2 * Real.pi) ^ (-(3 : ℝ) / 4) *
            (((k : ℝ) + 1 + p) ^ (-(3 : ℝ) / 2) * ((k : ℝ) + 1 + p)) *
            (4 * Real.pi)) from by ring]
      have h1 : ((k : ℝ) + 1 + p) ^ (-(3 : ℝ) / 2) * ((k : ℝ) + 1 + p) =
          ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) := by
        conv_rhs => rw [show (-(1 : ℝ) / 2 : ℝ) = -(3 : ℝ) / 2 + 1 from by ring]
        rw [rpow_add hkp, rpow_one]
      rw [h1]; ring
    rw [hlead, herr]
  -- Step 10: The integral of the simplified form equals the LHS
  have h_integral_eq :
      ∫ p in Ioc (0 : ℝ) 1, lb (blockCoord k p) * blockJacobian k p =
      4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) -
      C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
        ∫ p in Ioc (0 : ℝ) 1, ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun p hp => h_simplify p hp)]
    -- Split integral of difference
    have h_int1 : IntegrableOn
        (fun p => 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) (Ioc 0 1) := by
      have hcont : ContinuousOn
          (fun p => 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) (Icc 0 1) := by
        apply ContinuousOn.mul
        · apply ContinuousOn.mul continuousOn_const
          · exact ContinuousOn.sqrt (continuousOn_const.add continuousOn_id)
        · exact rsPsi_continuousOn
      exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have h_int2 : IntegrableOn
        (fun p => C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
          ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2))) (Ioc 0 1) := by
      have hcont : ContinuousOn
          (fun p => C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
            ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2))) (Icc 0 1) := by
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.mul continuousOn_const
        exact ContinuousOn.rpow (continuousOn_const.add continuousOn_id) continuousOn_const
          (fun p hp => Or.inl (ne_of_gt (show (0 : ℝ) < (k : ℝ) + 1 + p from by linarith [hp.1])))
      exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [integral_sub h_int1 h_int2]
    congr 1
    · -- Factor out 4π from the first integral: 4π * ∫ f = ∫ (4π * f)
      symm
      simp_rw [show ∀ p, 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p =
          (4 * Real.pi) * (Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) from fun p => by ring]
      rw [integral_const_mul]
    · -- Factor out C_R * 4π * (2π)^{-3/4} from the second integral
      symm
      simp_rw [show ∀ p, C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
          ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2)) =
          (C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4))) *
          ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) from fun p => by ring]
      rw [integral_const_mul]; ring
  -- Step 11: Chain everything together
  calc 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) -
      C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
        ∫ p in Ioc (0 : ℝ) 1, ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2))
    = ∫ p in Ioc (0 : ℝ) 1, lb (blockCoord k p) * blockJacobian k p := h_integral_eq.symm
    _ = ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), lb t := h_cov.symm
    _ ≤ ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          (-1 : ℝ) ^ k * ErrorTerm t := h_int_mono
    _ = (-1 : ℝ) ^ k * ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := h_factor


-- ============================================================
-- Correction dominates remainder
-- ============================================================

/-- For C_R ≤ 1/2, the positive correction 4π∫(√(k+1+p)-√(k+1))·Ψ dp
    is at least C_R · 4π(2π)^{-3/4} · ∫(k+1+p)^{-1/2} dp.
    This uses cos(π/4)·(2π)^{3/4}/4 > 1/2. -/
-- Helper: concavity of √ gives √(a+p) - √a ≥ p·(√(a+1) - √a) for p ∈ [0,1]
private lemma sqrt_concavity_lower (a : ℝ) (ha : 0 < a) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (Real.sqrt (a + 1) - Real.sqrt a) ≤ Real.sqrt (a + p) - Real.sqrt a := by
  have h_convex : a + p = (1 - p) * a + p * (a + 1) := by ring
  have h_concave := Real.strictConcaveOn_sqrt.concaveOn.2
    (Set.mem_Ici.mpr (le_of_lt ha)) (Set.mem_Ici.mpr (show (0:ℝ) ≤ a + 1 by linarith))
    (show (0:ℝ) ≤ 1 - p by linarith) hp0 (show (1 - p) + p = 1 by linarith)
  simp only [smul_eq_mul] at h_concave
  rw [h_convex]; linarith

-- Helper: ∫₀¹ p dp = 1/2
private lemma integral_id_Ioc' : ∫ p in Ioc (0 : ℝ) 1, p = 1 / 2 := by
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  simp [integral_id]

-- Helper: ∫₀¹ (a+p)^{-1/2} dp = 2(√(a+1) - √a) for a > 0, via FTC
private lemma integral_rpow_neg_half' (a : ℝ) (ha : 0 < a) :
    ∫ p in Ioc (0 : ℝ) 1, (a + p) ^ (-(1 : ℝ) / 2) =
    2 * (Real.sqrt (a + 1) - Real.sqrt a) := by
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  have hderiv : ∀ p ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun p => 2 * Real.sqrt (a + p)) ((a + p) ^ (-(1 : ℝ) / 2)) p := by
    intro p hp
    rw [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hp
    have hap : 0 < a + p := by linarith [hp.1]
    have h_add : HasDerivAt (fun p => a + p) 1 p := (hasDerivAt_id p).const_add a
    have h_sqrt := h_add.sqrt (ne_of_gt hap)
    have h_2sqrt := h_sqrt.const_mul 2
    refine h_2sqrt.congr_deriv ?_
    have : 0 < Real.sqrt (a + p) := Real.sqrt_pos.mpr hap
    have h1 : 2 * (1 / (2 * Real.sqrt (a + p))) = (Real.sqrt (a + p))⁻¹ := by field_simp
    rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt hap)]
    norm_num
  have hint : IntervalIntegrable (fun p => (a + p) ^ (-(1 : ℝ) / 2)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow (continuousOn_const.add continuousOn_id) continuousOn_const
    intro p hp
    rw [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hp
    left; exact ne_of_gt (show 0 < a + p by linarith [hp.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [add_zero]; ring

-- Helper: (2π)^{-3/4} ≤ √2/4, proved via π > 3
private lemma two_pi_rpow_neg_three_fourth_le :
    (2 * Real.pi) ^ (-(3 : ℝ) / 4) ≤ Real.sqrt 2 / 4 := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_nn : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt h2pi_pos
  suffices h_main : 2 * Real.sqrt 2 ≤ (2 * Real.pi) ^ ((3 : ℝ) / 4) by
    rw [show (-(3:ℝ)/4 : ℝ) = -((3:ℝ)/4) from by ring, Real.rpow_neg h2pi_nn]
    calc ((2 * Real.pi) ^ ((3 : ℝ) / 4))⁻¹
        ≤ (2 * Real.sqrt 2)⁻¹ := inv_anti₀ (by positivity) h_main
      _ = Real.sqrt 2 / 4 := by
          field_simp; nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 from by norm_num)]
  suffices h4 : (2 * Real.sqrt 2) ^ 4 ≤ ((2 * Real.pi) ^ ((3:ℝ)/4)) ^ 4 by
    by_contra hlt; push_neg at hlt
    exact not_le.mpr (pow_lt_pow_left₀ hlt (Real.rpow_nonneg h2pi_nn _) (by omega)) h4
  have h_rhs : ((2 * Real.pi) ^ ((3:ℝ)/4)) ^ 4 = (2 * Real.pi) ^ 3 := by
    rw [← Real.rpow_natCast ((2 * Real.pi) ^ ((3:ℝ)/4)) 4, ← Real.rpow_mul h2pi_nn]
    norm_num
  rw [h_rhs]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h_lhs : (2 * Real.sqrt 2) ^ 4 = 64 := by nlinarith [hsq2]
  have h_rhs2 : (2 * Real.pi) ^ 3 ≥ 216 := by
    have : (2 * Real.pi) ^ 3 = 8 * Real.pi ^ 3 := by ring
    rw [this]; have : Real.pi ^ 3 = Real.pi * Real.pi * Real.pi := by ring
    rw [this]; nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  linarith

private theorem correction_dominates_remainder
    (C_R : ℝ) (hCR_pos : 0 < C_R) (hCR_le : C_R ≤ 1 / 2)
    (k : ℕ) :
    C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
      ∫ p in Ioc (0 : ℝ) 1, ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2))
    ≤ 4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1,
        (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p := by
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpi_pos : (0 : ℝ) < 4 * Real.pi := by positivity
  -- Step 1: Evaluate LHS integral via FTC
  have h_int_eval := integral_rpow_neg_half' ((k : ℝ) + 1) hk1_pos
  rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 from by ring] at h_int_eval
  have h_sqrt_diff_pos : 0 < Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1) :=
    sub_pos.mpr (Real.sqrt_lt_sqrt (by positivity) (by linarith))
  -- Step 2: Pointwise: √(k+1+p)-√(k+1) ≥ p·(√(k+2)-√(k+1)) by concavity
  have h_rhs_lower : ∀ p ∈ Ioc (0 : ℝ) 1,
      p * (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p
      ≤ (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p := by
    intro p hp
    apply mul_le_mul_of_nonneg_right _ (rsPsi_nonneg_on p (Ioc_subset_Icc_self hp))
    rw [show (k : ℝ) + 2 = (k : ℝ) + 1 + 1 from by ring]
    exact sqrt_concavity_lower _ hk1_pos p (le_of_lt hp.1) hp.2
  -- Step 3: Integrate concavity bound
  have h_int1 : IntegrableOn
      (fun p => p * (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p) (Ioc 0 1) :=
    ((continuousOn_id.mul continuousOn_const).mul rsPsi_continuousOn).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have h_int2 : IntegrableOn
      (fun p => (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p) (Ioc 0 1) :=
    (((ContinuousOn.sqrt (continuousOn_const.add continuousOn_id)).sub
      continuousOn_const).mul rsPsi_continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h_rhs_int_lower :
      (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) *
        ∫ p in Ioc (0 : ℝ) 1, p * rsPsi p
      ≤ ∫ p in Ioc (0 : ℝ) 1,
        (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p := by
    calc _ = ∫ p in Ioc (0 : ℝ) 1,
          (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) * (p * rsPsi p) := by
          rw [show (fun p => (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) * (p * rsPsi p)) =
            (fun p => (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) • (p * rsPsi p)) from by
              ext; simp [smul_eq_mul]]
          rw [integral_smul]; simp [smul_eq_mul]
      _ = ∫ p in Ioc (0 : ℝ) 1,
          p * (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p := by
          congr 1; ext p; ring
      _ ≤ _ := integral_mono_ae h_int1 h_int2
          ((ae_restrict_mem measurableSet_Ioc).mono fun p hp => h_rhs_lower p hp)
  -- Step 4: ∫₀¹ p·Ψ dp ≥ cos(π/4)/2 = √2/4
  have h_psi_lower : ∀ p ∈ Ioc (0 : ℝ) 1,
      p * Real.cos (Real.pi / 4) ≤ p * rsPsi p := by
    intro p hp
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hp.1)
    have ⟨hp0, hp1⟩ := Ioc_subset_Icc_self hp
    simp only [rsPsi]
    rw [← Real.cos_abs (Real.pi * (2 * p ^ 2 - 2 * p + 1/4))]
    have harg_abs : |Real.pi * (2 * p ^ 2 - 2 * p + 1/4)| ≤ Real.pi / 4 := by
      rw [abs_le]; constructor
      · nlinarith [Real.pi_pos, sq_nonneg (p - 1/2)]
      · have : p * (p - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 (by linarith)
        nlinarith [Real.pi_pos]
    exact Real.strictAntiOn_cos.antitoneOn
      (Set.mem_Icc.mpr ⟨abs_nonneg _, le_trans harg_abs
        (div_le_self (le_of_lt Real.pi_pos) (by norm_num))⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt (div_pos Real.pi_pos (by norm_num)),
        div_le_self (le_of_lt Real.pi_pos) (by norm_num)⟩) harg_abs
  have h_int_p_psi_lower :
      Real.cos (Real.pi / 4) * (1 / 2) ≤ ∫ p in Ioc (0 : ℝ) 1, p * rsPsi p := by
    calc Real.cos (Real.pi / 4) * (1 / 2)
        = Real.cos (Real.pi / 4) * ∫ p in Ioc (0 : ℝ) 1, p := by rw [integral_id_Ioc']
      _ = ∫ p in Ioc (0 : ℝ) 1, p * Real.cos (Real.pi / 4) := by
          simp_rw [show ∀ p : ℝ, p * Real.cos (Real.pi / 4) =
            Real.cos (Real.pi / 4) * p from fun p => mul_comm _ _]
          simp_rw [← smul_eq_mul]
          exact (integral_smul (Real.cos (Real.pi / 4)) _).symm
      _ ≤ _ := integral_mono_ae
          ((continuous_id.mul continuous_const).continuousOn.integrableOn_Icc.mono_set
            Ioc_subset_Icc_self)
          ((continuousOn_id.mul rsPsi_continuousOn).integrableOn_Icc.mono_set
            Ioc_subset_Icc_self)
          ((ae_restrict_mem measurableSet_Ioc).mono fun p hp => h_psi_lower p hp)
  -- Step 5: Assemble via calc
  rw [h_int_eval]
  calc C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
        (2 * (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1))))
      = 4 * Real.pi * (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) *
        (C_R * (2 * Real.pi) ^ (-(3 : ℝ) / 4) * 2) := by ring
    _ ≤ 4 * Real.pi * (Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) *
        (Real.sqrt 2 / 4) := by
        apply mul_le_mul_of_nonneg_left _ (by nlinarith)
        calc C_R * (2 * Real.pi) ^ (-(3 : ℝ) / 4) * 2
            ≤ C_R * (Real.sqrt 2 / 4) * 2 := by
              have h_bound := two_pi_rpow_neg_three_fourth_le
              have h_rpow_nn := Real.rpow_nonneg (show (0:ℝ) ≤ 2 * Real.pi by positivity) (-(3:ℝ)/4)
              nlinarith
          _ = C_R * (Real.sqrt 2 / 2) := by ring
          _ ≤ (1 / 2) * (Real.sqrt 2 / 2) := by nlinarith [Real.sqrt_nonneg 2]
          _ = Real.sqrt 2 / 4 := by ring
    _ = 4 * Real.pi * ((Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) *
        (Real.cos (Real.pi / 4) * (1 / 2))) := by rw [Real.cos_pi_div_four]; ring
    _ ≤ 4 * Real.pi * ((Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)) *
        ∫ p in Ioc (0 : ℝ) 1, p * rsPsi p) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_int_p_psi_lower (le_of_lt h_sqrt_diff_pos))
          (le_of_lt hpi_pos)
    _ ≤ 4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1,
        (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p :=
        mul_le_mul_of_nonneg_left h_rhs_int_lower (le_of_lt hpi_pos)

-- ============================================================
-- Signed integral upper bound (companion to signed_integral_lower_bound)
-- ============================================================

/-- Pointwise signed upper bound: (-1)^k · ErrorTerm(t) ≤ leading + remainder.
    From |ET - (-1)^k · L| ≤ R, we get (-1)^k · ET ≤ L + R. -/
private theorem signed_pointwise_upper (k : ℕ) (t : ℝ)
    (C_R : ℝ)
    (h : |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    (-1 : ℝ) ^ k * ErrorTerm t ≤
      (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) +
      C_R * t ^ (-(3 : ℝ) / 4) := by
  have h_ub : ErrorTerm t ≤
      (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) +
      C_R * t ^ (-(3 : ℝ) / 4) := by
    have := le_abs_self (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
        rsPsi (blockParam k t))
    linarith
  have h_lb : ErrorTerm t ≥
      (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) -
      C_R * t ^ (-(3 : ℝ) / 4) := by
    have := neg_abs_le (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
        rsPsi (blockParam k t))
    linarith
  rcases Int.even_or_odd (k : ℤ) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hpow : (-1 : ℝ) ^ k = 1 := Even.neg_one_pow ⟨m.toNat, by omega⟩
    rw [hpow] at h_ub ⊢; linarith
  · have hpow : (-1 : ℝ) ^ k = -1 := Odd.neg_one_pow ⟨m.toNat, by omega⟩
    rw [hpow] at h_lb ⊢; linarith

private theorem signed_integral_upper_bound
    (C_R : ℝ) (_hCR_pos : 0 < C_R)
    (h_rs : ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t < hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4))
    (k : ℕ) :
    (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t) ≤
    4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
      + C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
          ∫ p in Ioc (0 : ℝ) 1, ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2)) := by
  -- Positivity prerequisites
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hhs_pos : 0 < hardyStart k := by rw [hardyStart_formula]; positivity
  -- Step 1: Define the upper-bound function
  set ub : ℝ → ℝ := fun t =>
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t) +
      C_R * t ^ (-(3 : ℝ) / 4)
  -- Step 2: ub is continuous on the closed block
  have hub_cont : ContinuousOn ub (Icc (hardyStart k) (hardyStart (k + 1))) := by
    apply ContinuousOn.add
    · apply ContinuousOn.mul
      · exact (ContinuousOn.div continuousOn_const continuousOn_id
          (fun t ht => ne_of_gt (lt_of_lt_of_le hhs_pos ht.1))).rpow_const
          (fun _ _ => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))
      · exact rsPsi_continuousOn.comp
          (ContinuousOn.sub
            (ContinuousOn.sqrt (ContinuousOn.div continuousOn_id continuousOn_const
              (fun _ _ => ne_of_gt h2pi)))
            continuousOn_const)
          (fun t ht => by
            constructor
            · exact blockParam_nonneg k t ht.1
            · unfold blockParam
              have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
              have hk2 : (0 : ℝ) ≤ (k : ℝ) + 2 := by positivity
              suffices h : Real.sqrt (t / (2 * Real.pi)) ≤ (k : ℝ) + 2 by linarith
              calc Real.sqrt (t / (2 * Real.pi))
                  ≤ Real.sqrt (hardyStart (k + 1) / (2 * Real.pi)) :=
                    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ht.2 (le_of_lt hpi))
                _ = Real.sqrt (((k : ℝ) + 2) ^ 2) := by
                    congr 1; rw [hardyStart_formula]; push_cast; field_simp; ring
                _ = (k : ℝ) + 2 := Real.sqrt_sq hk2)
    · exact continuousOn_const.mul
        (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hhs_pos ht.1))))
  -- Step 3: The signed pointwise upper bound holds on the block
  have h_ptwise_ae : (fun t => (-1 : ℝ) ^ k * ErrorTerm t) ≤ᵐ[volume.restrict (Ioc (hardyStart k) (hardyStart (k + 1)))] ub := by
    have h_ne : ∀ᵐ t ∂(volume : Measure ℝ),
        t ≠ hardyStart (k + 1) := by
      rw [Filter.eventually_iff]; simp only [ne_eq]
      exact measure_mono_null (fun t ht => by simpa using ht) Real.volume_singleton
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h_ne] with t ht_ne ht
    exact signed_pointwise_upper k t C_R
      (h_rs k t (le_of_lt ht.1) (lt_of_le_of_ne ht.2 ht_ne) (lt_trans hhs_pos ht.1))
  -- Step 4: Integrability
  have hub_int : IntegrableOn ub (Ioc (hardyStart k) (hardyStart (k + 1))) :=
    hub_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hET_block_int : IntegrableOn ErrorTerm
      (Ioc (hardyStart k) (hardyStart (k + 1))) := by
    have h_big := errorTerm_integrable (hardyStart (k + 1))
    have h1_le_hs : 1 ≤ hardyStart k := by
      rw [hardyStart_formula]
      have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; nlinarith
      nlinarith [Real.pi_gt_three]
    exact h_big.mono_set (Ioc_subset_Ioc_left h1_le_hs)
  have hET_int : IntegrableOn (fun t => (-1 : ℝ) ^ k * ErrorTerm t)
      (Ioc (hardyStart k) (hardyStart (k + 1))) :=
    hET_block_int.const_mul _
  -- Step 5: Integral monotonicity: ∫ (-1)^k · ET ≤ ∫ ub
  have h_int_mono : ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
      (-1 : ℝ) ^ k * ErrorTerm t
      ≤ ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ub t := by
    exact setIntegral_mono_ae_restrict hET_int hub_int h_ptwise_ae
  -- Step 6: Factor (-1)^k
  have h_factor : ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
      (-1 : ℝ) ^ k * ErrorTerm t =
      (-1 : ℝ) ^ k * ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := by
    simp_rw [← smul_eq_mul]; exact integral_smul _ _
  -- Step 7: Apply COV to ub
  have h_cov : ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ub t
      = ∫ p in Ioc (0 : ℝ) 1, ub (blockCoord k p) * blockJacobian k p :=
    block_integral_cov k ub hub_cont
  -- Step 8: Simplify ub(blockCoord k p) * blockJacobian(k, p)
  -- Exactly as in signed_integral_lower_bound but with + instead of -
  have h_simplify : ∀ p ∈ Ioc (0 : ℝ) 1,
      ub (blockCoord k p) * blockJacobian k p =
      4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p +
      C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
        ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2)) := by
    intro p hp
    have hp0 : 0 < p := hp.1
    have hkp : (0 : ℝ) < (k : ℝ) + 1 + p := by positivity
    have hbp : blockParam k (blockCoord k p) = p := blockParam_blockCoord k p hp0.le
    have hbc : blockCoord k p = 2 * Real.pi * ((k : ℝ) + 1 + p) ^ 2 := rfl
    have hbj : blockJacobian k p = 4 * Real.pi * ((k : ℝ) + 1 + p) := rfl
    have h_leading_rpow :
        (2 * Real.pi / (blockCoord k p)) ^ ((1 : ℝ) / 4) = ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) := by
      rw [hbc]; exact rpow_quarter_simplify' ((k : ℝ) + 1 + p) hkp
    have h_error_rpow :
        (blockCoord k p) ^ (-(3 : ℝ) / 4) =
        (2 * Real.pi) ^ (-(3 : ℝ) / 4) * ((k : ℝ) + 1 + p) ^ (-(3 : ℝ) / 2) := by
      rw [hbc]; exact rpow_neg_three_quarter_simplify ((k : ℝ) + 1 + p) hkp
    have h_prod1 : ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * (4 * Real.pi * ((k : ℝ) + 1 + p)) =
        4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) := by
      rw [Real.sqrt_eq_rpow]
      have h_rpow_combine : ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * ((k : ℝ) + 1 + p) =
          ((k : ℝ) + 1 + p) ^ ((1 : ℝ) / 2) := by
        conv_rhs => rw [show (1 : ℝ) / 2 = -(1 : ℝ) / 2 + 1 from by ring]
        rw [rpow_add hkp, rpow_one]
      nlinarith
    simp only [ub, hbp]
    rw [add_mul, h_leading_rpow, h_error_rpow, hbj]
    have hlead : ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * rsPsi p *
        (4 * Real.pi * ((k : ℝ) + 1 + p)) =
        4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p := by
      rw [show ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * rsPsi p *
          (4 * Real.pi * ((k : ℝ) + 1 + p)) =
          (((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) * (4 * Real.pi * ((k : ℝ) + 1 + p))) *
          rsPsi p from by ring]
      rw [h_prod1]
    have herr : C_R * ((2 * Real.pi) ^ (-(3 : ℝ) / 4) * ((k : ℝ) + 1 + p) ^ (-(3 : ℝ) / 2)) *
        (4 * Real.pi * ((k : ℝ) + 1 + p)) =
        C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
          ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2)) := by
      rw [show C_R * ((2 * Real.pi) ^ (-(3 : ℝ) / 4) * ((k : ℝ) + 1 + p) ^ (-(3 : ℝ) / 2)) *
          (4 * Real.pi * ((k : ℝ) + 1 + p)) =
          C_R * ((2 * Real.pi) ^ (-(3 : ℝ) / 4) *
            (((k : ℝ) + 1 + p) ^ (-(3 : ℝ) / 2) * ((k : ℝ) + 1 + p)) *
            (4 * Real.pi)) from by ring]
      have h1 : ((k : ℝ) + 1 + p) ^ (-(3 : ℝ) / 2) * ((k : ℝ) + 1 + p) =
          ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) := by
        conv_rhs => rw [show (-(1 : ℝ) / 2 : ℝ) = -(3 : ℝ) / 2 + 1 from by ring]
        rw [rpow_add hkp, rpow_one]
      rw [h1]; ring
    rw [hlead, herr]
  -- Step 9: Integral equals sum
  have h_integral_eq :
      ∫ p in Ioc (0 : ℝ) 1, ub (blockCoord k p) * blockJacobian k p =
      4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) +
      C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
        ∫ p in Ioc (0 : ℝ) 1, ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun p hp => h_simplify p hp)]
    have h_int1 : IntegrableOn
        (fun p => 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) (Ioc 0 1) := by
      have hcont : ContinuousOn
          (fun p => 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) (Icc 0 1) := by
        apply ContinuousOn.mul
        · apply ContinuousOn.mul continuousOn_const
          · exact ContinuousOn.sqrt (continuousOn_const.add continuousOn_id)
        · exact rsPsi_continuousOn
      exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have h_int2 : IntegrableOn
        (fun p => C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
          ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2))) (Ioc 0 1) := by
      have hcont : ContinuousOn
          (fun p => C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
            ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2))) (Icc 0 1) := by
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.mul continuousOn_const
        exact ContinuousOn.rpow (continuousOn_const.add continuousOn_id) continuousOn_const
          (fun p hp => Or.inl (ne_of_gt (show (0 : ℝ) < (k : ℝ) + 1 + p from by linarith [hp.1])))
      exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [integral_add h_int1 h_int2]
    congr 1
    · symm
      simp_rw [show ∀ p, 4 * Real.pi * Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p =
          (4 * Real.pi) * (Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) from fun p => by ring]
      rw [integral_const_mul]
    · symm
      simp_rw [show ∀ p, C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
          ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2)) =
          (C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4))) *
          ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2) from fun p => by ring]
      rw [integral_const_mul]; ring
  -- Step 10: Chain
  calc (-1 : ℝ) ^ k * ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t
    = ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          (-1 : ℝ) ^ k * ErrorTerm t := h_factor.symm
    _ ≤ ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ub t := h_int_mono
    _ = ∫ p in Ioc (0 : ℝ) 1, ub (blockCoord k p) * blockJacobian k p := h_cov
    _ = 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p) +
        C_R * (4 * Real.pi * (2 * Real.pi) ^ (-(3 : ℝ) / 4) *
          ∫ p in Ioc (0 : ℝ) 1, ((k : ℝ) + 1 + p) ^ (-(1 : ℝ) / 2)) := h_integral_eq

-- ============================================================
-- Main theorem
-- ============================================================

/-- **B3 block structure from RS expansion**: All three B3 obligations
    (nonnegativity, antitone, interpolation) derived from the pointwise
    RS expansion on blocks with C_R ≤ 1/2, plus the signed RS expansion
    properties (antitone and interpolation) that require higher-order
    Siegel expansion structure.

    - Nonnegativity: proved from the absolute-value RS bound alone
      (signed integral bounds + correction dominates remainder).
    - Antitone: requires the signed structure of the RS remainder (Gabcke 1979),
      supplied as hypothesis `h_antitone`.
    - Interpolation: requires sign coherence within blocks (Siegel 1932),
      supplied as hypothesis `h_interpolation`.

    Reference: Siegel 1932 §3; Titchmarsh §4.16-4.17; Edwards Ch. 7;
    Gabcke 1979 Satz 4. -/
theorem b3_block_structure_core
    (h_exp : ∃ C_R : ℝ, 0 < C_R ∧ C_R ≤ 1 / 2 ∧ ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t < hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4))
    (h_antitone :
      let A_val := 4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, rsPsi p
      let c_fn := fun k : ℕ =>
        (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - A_val * Real.sqrt ((k : ℝ) + 1)
      AntitoneOn c_fn (Ici (1 : ℕ)))
    (h_interpolation :
      ∃ C₂ : ℝ, C₂ ≥ 0 ∧
      (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
        ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
          |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
            - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                     ErrorTerm t)| ≤ C₂)) :
    let A_val := 4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, rsPsi p
    let c_fn := fun k : ℕ =>
      (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - A_val * Real.sqrt ((k : ℝ) + 1)
    (∀ k : ℕ, 0 ≤ c_fn k) ∧
    AntitoneOn c_fn (Ici (1 : ℕ)) ∧
    ∃ C₂ : ℝ, C₂ ≥ 0 ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                   ErrorTerm t)| ≤ C₂) := by
  obtain ⟨C_R, hCR_pos, hCR_le, h_rs⟩ := h_exp
  intro A_val c_fn
  refine ⟨?nonneg, ?antitone, ?interpolation⟩
  case nonneg =>
    intro k
    have h_lower := signed_integral_lower_bound C_R hCR_pos h_rs k
    have h_dom := correction_dominates_remainder C_R hCR_pos hCR_le k
    have h_split : 4 * Real.pi * (∫ p in Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p)
        = (4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, rsPsi p) * Real.sqrt ((k : ℝ) + 1)
          + 4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1,
              (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p := by
      rw [mul_comm (4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, rsPsi p) _]
      rw [show Real.sqrt ((k : ℝ) + 1) * (4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, rsPsi p) =
          4 * Real.pi * (Real.sqrt ((k : ℝ) + 1) * ∫ p in Ioc (0 : ℝ) 1, rsPsi p) from by ring]
      rw [← mul_add]; congr 1
      have h_eq : ∀ p : ℝ, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p =
          Real.sqrt ((k : ℝ) + 1) * rsPsi p +
          (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p := by intro p; ring
      simp_rw [h_eq]
      have h_int1 : IntegrableOn (fun p => Real.sqrt ((k : ℝ) + 1) * rsPsi p) (Ioc 0 1) :=
        rsPsi_integrableOn.const_mul _
      have h_int2 : IntegrableOn
          (fun p => (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p) (Ioc 0 1) :=
        ((ContinuousOn.sqrt (continuousOn_const.add continuousOn_id)).sub
          continuousOn_const).mul rsPsi_continuousOn |>.integrableOn_Icc.mono_set Ioc_subset_Icc_self
      rw [integral_add h_int1 h_int2]; congr 1
      have := integral_smul (𝕜 := ℝ) (Real.sqrt ((k : ℝ) + 1))
        rsPsi (μ := volume.restrict (Ioc 0 1))
      simp only [smul_eq_mul] at this; linarith
    show 0 ≤ (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - (4 * Real.pi * ∫ p in Ioc (0 : ℝ) 1, rsPsi p) * Real.sqrt ((k : ℝ) + 1)
    linarith
  case antitone =>
    -- Supplied by the signed RS expansion (Siegel 1932 §3, Gabcke 1979).
    -- Cannot be derived from the absolute-value bound alone; see rs_block_antitone
    -- in RSExpansionProof.lean for the mathematical justification.
    exact h_antitone
  case interpolation =>
    -- Supplied by the sign coherence property of ErrorTerm within blocks
    -- (Siegel 1932 §3). See rs_block_interpolation in RSExpansionProof.lean.
    exact h_interpolation

end Aristotle.Standalone.B3BlockStructureFromExpansion
