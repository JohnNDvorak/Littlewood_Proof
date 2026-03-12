/-
Bridge between the project's `ErrorTerm` (HardyZFirstMoment) and the RS module's
`rsApproxError` (RSBlockWiring).

The mathematical content is trivial: both definitions compute the same quantity
|Z(t) − 2·Re(e^{iθ}·S_N)|, just using different definition universes.

Key reconciliation steps:
1. RS.hardyTheta = project.hardyTheta (same formula up to ring)
2. RS.hardyZ.re = project.hardyZ (complex vs real Z)
3. Int.natAbs ⌊√(t/2π)⌋ = Nat.floor(√(t/2π)) (for nonneg inputs)
4. 2·Re(e^{iθ}·RS.hardySum N t) = project.MainTerm t (per-term identity)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.RSBlockWiring
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.HardyZRealV2

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace RSDefinitionBridge

open Complex Real Set Filter MeasureTheory HardyEstimatesPartial
open scoped Topology BigOperators

/-! ## Step 1: Theta agreement -/

/-- The RS module's `hardyTheta` equals the project's `hardyTheta`. -/
theorem rs_theta_eq (t : ℝ) :
    Aristotle.RiemannSiegelBound.hardyTheta t = HardyEstimatesPartial.hardyTheta t := by
  unfold Aristotle.RiemannSiegelBound.hardyTheta HardyEstimatesPartial.hardyTheta
  congr 1
  · congr 1; congr 1; ring_nf

/-! ## Step 2: Z function agreement -/

/-- RS complex `hardyZ` has `.re` equal to the project's real `hardyZ`. -/
theorem rs_hardyZ_re_eq (t : ℝ) :
    (Aristotle.RiemannSiegelBound.hardyZ t).re = HardyEstimatesPartial.hardyZ t := by
  unfold Aristotle.RiemannSiegelBound.hardyZ HardyEstimatesPartial.hardyZ
  rw [rs_theta_eq]

/-- RS complex `hardyZ` is real-valued (imaginary part = 0). -/
theorem rs_hardyZ_im_eq (t : ℝ) :
    (Aristotle.RiemannSiegelBound.hardyZ t).im = 0 := by
  have h1 : Aristotle.RiemannSiegelBound.hardyZ t = hardyZV2 t := by
    unfold Aristotle.RiemannSiegelBound.hardyZ hardyZV2
    rw [rs_theta_eq, HardyZTransfer.hardyTheta_eq_thetaV2]
  rw [h1]; exact hardyZV2_real t

/-! ## Step 3: N definitions match -/

/-- For `x ≥ 0`, `Int.natAbs ⌊x⌋ = Nat.floor x`. -/
theorem natAbs_intFloor_eq_natFloor {x : ℝ} (hx : 0 ≤ x) :
    Int.natAbs ⌊x⌋ = Nat.floor x := by
  have hfl : (0 : ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  have : ∀ n : ℤ, 0 ≤ n → n.natAbs = n.toNat := by
    intro n hn; cases n with
    | ofNat k => simp [Int.natAbs, Int.toNat]
    | negSucc k => omega
  rw [this _ hfl, Int.floor_toNat]

/-! ## Step 4: Per-term complex-to-real identity -/

/-- `Re(exp(↑a + I·↑b)) = exp(a) · cos(b)` for real `a`, `b`. -/
private theorem re_exp_real_add_I_mul_real (a b : ℝ) :
    (Complex.exp (↑a + I * ↑b)).re = Real.exp a * Real.cos b := by
  rw [show ↑a + I * ↑b = ↑a + ↑b * I from by ring, Complex.exp_add_mul_I]
  simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]
  conv_lhs => rw [show (cexp ↑a).re = Real.exp a from by
    have := Complex.ofReal_exp a; exact_mod_cast this.symm ▸ ofReal_re _]
  conv_lhs => rw [show (Complex.cos ↑b).re = Real.cos b from by
    have := Complex.ofReal_cos b; exact_mod_cast this.symm ▸ ofReal_re _]
  conv_lhs => rw [show (cexp ↑a).im = 0 from by
    have := Complex.ofReal_exp a; exact_mod_cast this.symm ▸ ofReal_im _]
  conv_lhs => rw [show (Complex.sin ↑b).im = 0 from by
    have := Complex.ofReal_sin b; exact_mod_cast this.symm ▸ ofReal_im _]
  ring

/-- For natural `m ≥ 1`: `Re(exp(I·θ) · (↑m)^{-(1/2) - I·t}) = m^{-1/2} · cos(θ - t·log m)`. -/
theorem re_exp_cpow_eq_cos (m : ℕ) (hm : 0 < m) (θ t : ℝ) :
    (Complex.exp (I * ↑θ) * (↑(m : ℝ) : ℂ) ^ (-(1/2 : ℂ) - I * ↑t)).re =
    (m : ℝ) ^ (-(1/2 : ℝ)) * Real.cos (θ - t * Real.log m) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm_ne : (↑(m : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hm_pos)
  rw [cpow_def_of_ne_zero hm_ne, (ofReal_log (le_of_lt hm_pos)).symm,
    ← Complex.exp_add]
  have harg : I * ↑θ + ↑(Real.log ↑m) * (-(1/2 : ℂ) - I * ↑t) =
      ↑(-(1/2 : ℝ) * Real.log ↑m) + I * ↑(θ - t * Real.log ↑m) := by
    push_cast; ring
  rw [harg, re_exp_real_add_I_mul_real, Real.rpow_def_of_pos hm_pos]
  ring_nf

/-! ## Step 5: Sum identity -/

/-- The real part of `exp(I·θ) · RS.hardySum N t` equals the project's cosine sum. -/
theorem re_exp_hardySum_eq (N : ℕ) (t : ℝ) :
    (Complex.exp (I * ↑(HardyEstimatesPartial.hardyTheta t)) *
      Aristotle.RiemannSiegelBound.hardySum N t).re =
    ∑ n ∈ Finset.range N,
      ((n + 1 : ℝ) ^ (-(1/2 : ℝ)) *
        Real.cos (HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1))) := by
  unfold Aristotle.RiemannSiegelBound.hardySum
  rw [Finset.mul_sum, Complex.re_sum]
  congr 1; ext n
  -- Reconcile coercion paths: (↑n + 1 : ℂ) = ↑(↑(n+1) : ℝ) and (↑n + 1 : ℝ) = ↑(n+1)
  rw [show (↑n + 1 : ℂ) = (↑(↑(n + 1) : ℝ) : ℂ) from by push_cast; ring,
    show (↑n + 1 : ℝ) = (↑(n + 1) : ℝ) from by push_cast; ring]
  exact re_exp_cpow_eq_cos (n + 1) (Nat.succ_pos n)
    (HardyEstimatesPartial.hardyTheta t) t

/-- `2 · Re(exp(I·θ) · RS.hardySum N t) = MainTerm t` when N = hardyN t. -/
theorem two_re_exp_hardySum_eq_mainTerm (t : ℝ) :
    2 * (Complex.exp (I * ↑(Aristotle.RiemannSiegelBound.hardyTheta t)) *
      Aristotle.RiemannSiegelBound.hardySum
        (Nat.floor (Real.sqrt (t / (2 * Real.pi)))) t).re =
    HardyEstimatesPartial.MainTerm t := by
  unfold HardyEstimatesPartial.MainTerm
  rw [rs_theta_eq]
  congr 1
  exact re_exp_hardySum_eq _ t

/-! ## Step 6: rsApproxError = |ErrorTerm| -/

/-- Norm of a real-valued complex number minus a real scalar. -/
private theorem norm_real_sub_real (z : ℂ) (hz : z.im = 0) (r : ℝ) :
    ‖z - (2 : ℂ) * ↑r‖ = |z.re - 2 * r| := by
  have hz_eq : z = ↑z.re := by
    apply Complex.ext_iff.mpr
    exact ⟨by simp, by simpa using hz⟩
  conv_lhs => rw [hz_eq, show (↑z.re : ℂ) - 2 * ↑r = ↑(z.re - 2 * r) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- `rsApproxError t = |ErrorTerm t|` for `t ≥ 0`. -/
theorem rsApproxError_eq_abs_errorTerm (t : ℝ) (_ht : 0 ≤ t) :
    Aristotle.RSBlockWiring.rsApproxError t = |HardyEstimatesPartial.ErrorTerm t| := by
  unfold Aristotle.RSBlockWiring.rsApproxError
  -- Simplify norm using Z being real-valued
  rw [norm_real_sub_real _ (rs_hardyZ_im_eq t)]
  -- RS.Z.re = project.Z
  rw [rs_hardyZ_re_eq]
  -- Match N definitions
  rw [natAbs_intFloor_eq_natFloor (Real.sqrt_nonneg _)]
  -- Match theta and sum = MainTerm
  rw [two_re_exp_hardySum_eq_mainTerm]
  -- |hardyZ t - MainTerm t| = |ErrorTerm t|
  unfold HardyEstimatesPartial.ErrorTerm
  rfl

/-! ## Step 7: Instance -/

/-- The bridge hypothesis: `|ErrorTerm t| ≤ rsApproxError t` holds trivially
    since `rsApproxError t = |ErrorTerm t|`. -/
instance : Aristotle.RSBlockWiring.ErrorTermRsApproxBridgeHyp where
  bound := fun t _ht => by
    rw [rsApproxError_eq_abs_errorTerm t (by linarith)]

end RSDefinitionBridge
