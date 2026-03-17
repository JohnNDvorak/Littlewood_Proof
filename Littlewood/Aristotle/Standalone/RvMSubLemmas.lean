/-
Sub-lemmas for the Riemann-von Mangoldt formula N(T) bound.

Two self-contained, sorry-free theorems:

## Sub-lemma 1: Bridge Lemma (logDeriv decomposition of RiemannXiAlt)

`logDeriv_RiemannXiAlt_decomposition`:
  logDeriv(RiemannXiAlt)(s) = 1/s + 1/(s-1) + logDeriv(completedRiemannZeta)(s)

This connects the entire xi function (defined via completedRiemannZeta₀, which
avoids poles) to the completed zeta logDeriv. The latter further decomposes as
  logDeriv(Λ) = -log(π)/2 + (1/2)ψ(s/2) + ζ'/ζ(s)
where ψ = Γ'/Γ is the digamma function.

## Sub-lemma 2: Right-edge digamma integral

`integral_log_half` (exact):
  ∫₁ᵀ log(t/2) dt = T·log(T/2) - T + 1 + log 2

`right_edge_digamma_integral` (asymptotic):
  (∫₁ᵀ log(t/2) dt) - (T·log(T/2) - T) = O(log T)

On the right vertical edge σ = 2 of the RvM contour, Re(ψ(1+it/2)) has
leading term log(t/2), and this integral captures the main contribution.

## References
- Titchmarsh, "The Theory of the Riemann Zeta-Function", Ch. 9
- Montgomery-Vaughan, "Multiplicative Number Theory I", Ch. 14

Co-authored-by: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
-/

import Mathlib

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace RvMSubLemmas

open Complex MeasureTheory Real Filter Asymptotics

/-! ## Sub-lemma 1: LogDeriv decomposition of RiemannXiAlt -/

/-- RiemannXiAlt(s) = (1/2)·(s·(s-1)·Λ₀(s) + 1) is entire by construction. -/
noncomputable def RiemannXiAlt (s : ℂ) : ℂ := (1/2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

/-- RiemannXiAlt is differentiable everywhere on ℂ (entire). -/
theorem RiemannXiAlt_entire : Differentiable ℂ RiemannXiAlt := by
  unfold RiemannXiAlt
  exact Differentiable.const_mul
    (Differentiable.add
      (Differentiable.mul (differentiable_id.mul (differentiable_id.sub_const 1))
        differentiable_completedZeta₀)
      (differentiable_const _)) _

/-- RiemannXiAlt(s) = (1/2)·s·(s-1)·completedRiemannZeta(s) for s ≠ 0, 1.
This uses the relation Λ₀(s) = Λ(s) + 1/s + 1/(1-s) so that
s(s-1)Λ₀(s) + 1 = s(s-1)Λ(s). -/
theorem RiemannXiAlt_eq_half_mul (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    RiemannXiAlt s = (1/2 : ℂ) * (s * (s - 1) * completedRiemannZeta s) := by
  unfold RiemannXiAlt
  have h := completedRiemannZeta_eq s; rw [h]
  have hs1 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp [h0, hs1]; ring

/-- **Bridge Lemma**: logDeriv of RiemannXiAlt decomposes as
  logDeriv(RiemannXiAlt)(s) = 1/s + 1/(s-1) + logDeriv(completedRiemannZeta)(s)

For s on the boundary of the RvM contour rectangle (where s ≠ 0, 1 and ζ ≠ 0),
this connects the entire xi function to the completed zeta logDeriv.

The proof:
1. Factor out the constant 1/2 (logDeriv is invariant under nonzero scalar).
2. Show RiemannXiAlt agrees with (1/2)·s(s-1)·Λ(s) near s (using Λ₀ = Λ + poles).
3. Compute deriv of s(s-1)Λ(s) via product rule: (2s-1)Λ + s(s-1)Λ'.
4. Divide by s(s-1)Λ to get 1/s + 1/(s-1) + Λ'/Λ. -/
theorem logDeriv_RiemannXiAlt_decomposition (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hcomp : completedRiemannZeta s ≠ 0) :
    logDeriv RiemannXiAlt s =
      1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hmul_ne : s * (s - 1) ≠ 0 := mul_ne_zero h0 hs1
  set g := fun z : ℂ => z * (z - 1) * completedRiemannZeta₀ z + 1 with hg_def
  -- Step 1: logDeriv(RiemannXiAlt) = logDeriv(g)
  have hld_const : logDeriv RiemannXiAlt s = logDeriv g s := by
    show logDeriv (fun z => (1/2 : ℂ) * g z) s = logDeriv g s
    exact logDeriv_const_mul s (1/2 : ℂ) (by norm_num)
  -- g agrees with s(s-1)Λ near s
  have hgf_eq : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → g z = z * (z - 1) * completedRiemannZeta z := by
    intro z hz0 hz1; simp only [hg_def]
    have h := completedRiemannZeta_eq z; rw [h]
    have hz1' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    field_simp [hz0, hz1']; ring
  have hg_at_s : g s = s * (s - 1) * completedRiemannZeta s := hgf_eq s h0 h1
  have hgf_nhds : g =ᶠ[nhds s] (fun z => z * (z - 1) * completedRiemannZeta z) :=
    Filter.Eventually.mono
      (IsOpen.mem_nhds (isOpen_ne.inter isOpen_ne) ⟨h0, h1⟩)
      (fun z ⟨hz0, hz1⟩ => hgf_eq z hz0 hz1)
  -- Step 2: logDeriv(g) = logDeriv(s(s-1)Λ)
  have hlogderiv_eq : logDeriv g s =
      logDeriv (fun z => z * (z - 1) * completedRiemannZeta z) s := by
    simp only [logDeriv_apply, hg_at_s, Filter.EventuallyEq.deriv_eq hgf_nhds]
  -- Step 3: Compute logDeriv by explicit deriv
  have hdLam : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta h0 h1
  have hd_poly : HasDerivAt (fun z : ℂ => z * (z - 1)) (2 * s - 1) s := by
    convert (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const (1 : ℂ)) using 1
    simp only [id]; ring
  have hd_prod : HasDerivAt (fun z => z * (z - 1) * completedRiemannZeta z)
      ((2 * s - 1) * completedRiemannZeta s + s * (s - 1) * deriv completedRiemannZeta s) s := by
    have h1 := hd_poly.mul hdLam.hasDerivAt
    have : ((fun z => z * (z - 1)) * completedRiemannZeta) = (fun z => z * (z - 1) * completedRiemannZeta z) := by
      ext z; simp [Pi.mul_apply]
    rwa [this] at h1
  have hd_full := hd_prod.const_mul (1/2 : ℂ)
  rw [hld_const, hlogderiv_eq]
  simp only [logDeriv_apply, hd_prod.deriv]
  field_simp [h0, hs1, hcomp]
  ring

/-! ## Sub-lemma 2: Right-edge digamma integral -/

/-- The integral of log(t/2) from 1 to T equals T·log(T/2) - T + 1 + log 2 exactly.

Proof by the fundamental theorem of calculus: the antiderivative of log(t/2)
is F(t) = t·log(t/2) - t, and F(T) - F(1) = T·log(T/2) - T - (log(1/2) - 1)
= T·log(T/2) - T + 1 + log 2. -/
theorem integral_log_half (T : ℝ) (hT : 1 ≤ T) :
    ∫ t in (1:ℝ)..T, Real.log (t / 2) = T * Real.log (T / 2) - T + 1 + Real.log 2 := by
  -- F(t) = t·log(t/2) - t has derivative log(t/2) for t > 0
  have hF : ∀ t ∈ Set.uIcc (1:ℝ) T,
      HasDerivAt (fun t => t * Real.log (t / 2) - t) (Real.log (t / 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht_pos : 0 < t := by linarith [ht.1]
    have ht2_ne : t / 2 ≠ 0 := ne_of_gt (by linarith)
    have hlog : HasDerivAt (fun t => Real.log (t / 2)) (1 / t) t := by
      have h1 : HasDerivAt (fun t => t / 2) (1/2 : ℝ) t := (hasDerivAt_id t).div_const 2
      have h2 := (Real.hasDerivAt_log ht2_ne).comp t h1
      convert h2 using 1; field_simp
    have hmul : HasDerivAt (fun t => t * Real.log (t / 2)) (Real.log (t / 2) + 1) t := by
      have := (hasDerivAt_id t).mul hlog
      simp only [id] at this; convert this using 1; field_simp
    exact (hmul.sub (hasDerivAt_id t)).congr_deriv (by ring)
  -- log(t/2) is continuous on [1, T]
  have hcont : ContinuousOn (fun t => Real.log (t / 2)) (Set.uIcc 1 T) := by
    refine ContinuousOn.comp Real.continuousOn_log (continuousOn_id.div_const 2) ?_
    intro t ht
    rw [Set.uIcc_of_le hT, Set.mem_Icc] at ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
  -- F(T) - F(1) = (T log(T/2) - T) - (1 · log(1/2) - 1)
  -- log(1/2) = -log 2
  have h12 : Real.log (1 / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0), Real.log_one, zero_sub]
  rw [h12]; ring

/-- **Right-edge digamma integral asymptotic**:
  (∫₁ᵀ log(t/2) dt) - (T·log(T/2) - T) = O(log T)

The exact error is the constant 1 + log 2 ≈ 1.693, so this is actually O(1),
but O(log T) is the form consumed by the RvM chain. -/
theorem right_edge_digamma_integral :
    (fun T => (∫ t in (1:ℝ)..T, Real.log (t / 2)) - (T * Real.log (T / 2) - T))
    =O[atTop] Real.log := by
  -- The difference is exactly 1 + log 2 for all T ≥ 1
  have h_const : ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1:ℝ)..T, Real.log (t / 2)) - (T * Real.log (T / 2) - T) = 1 + Real.log 2 := by
    intro T hT; rw [integral_log_half T hT]; ring
  -- A constant is O(log T)
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
  have hT1 : 1 ≤ T := le_trans (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)) hT
  rw [h_const T hT1]
  have hT_pos : 0 < T := by linarith
  have hlogT_ge : 1 ≤ Real.log T := by rwa [Real.le_log_iff_exp_le hT_pos]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have hlog2_lt1 : Real.log 2 < 1 := by
    have h2lt : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_lt_log_iff (by norm_num) (Real.exp_pos 1) |>.mpr h2lt
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

end RvMSubLemmas
