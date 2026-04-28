/-
# Perron Residue Atoms

Residue evaluation atoms needed by PerronFormulaAssembly:
1. Residue of x^s/s · (-ζ'/ζ) at s=1 is x  (Atom 1)
2. Residue at a zero ρ is -m(ρ) · x^ρ/ρ  (Atom 2)
3. Vertical integral bound at Re = 1/2  (Atom 3)

Uses Mathlib's Cauchy integral formula and existing Perron kernel norm bounds.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PerronAssemblyAtomics
import Littlewood.Aristotle.Standalone.ResidueExtraction
import Littlewood.Aristotle.LaurentExpansion
import Mathlib

set_option maxHeartbeats 3200000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex Real MeasureTheory Filter Metric

noncomputable section

namespace PerronResidueAtoms

/-! ## Atom 3: Vertical integral bound at Re = 1/2

This is the most concrete atom: bound the integral of
  -ζ'/ζ(1/2 + it) · x^(1/2+it) / (1/2+it)
on the vertical line Re = 1/2 from -T to T.

Strategy:
  ‖∫ t in (-T)..T, f(t)‖ ≤ (sup ‖f(t)‖) · 2T
  ‖f(t)‖ = ‖logDeriv ζ(1/2+it)‖ · ‖x^(1/2+it)‖ / ‖1/2+it‖
         ≤ C_zeta · √x / (1/2)  = 2 · C_zeta · √x

But for a cleaner bound, we use the hypothesis that absorbs everything:
  We bound via C_bound · √x where C_bound accounts for both ζ'/ζ and 1/s.
-/

/-- ‖1/2 + t*I‖ ≥ 1/2 for all t. -/
theorem norm_half_add_mul_I_ge (t : ℝ) : (1 : ℝ)/2 ≤ ‖(1/2 : ℂ) + (t : ℂ) * I‖ := by
  rw [show (1/2 : ℂ) + (t : ℂ) * I = ((1/2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I from by
    push_cast; ring]
  rw [Complex.norm_add_mul_I]
  apply le_sqrt_of_sq_le
  linarith [sq_nonneg t]

/-- Pointwise bound: the integrand norm is bounded by 2 · C_zeta · √x.
    Uses ‖x^(1/2+it)‖ = √x, the hypothesis ‖ζ'/ζ‖ ≤ C_zeta, and ‖1/2+it‖ ≥ 1/2. -/
theorem vertical_integrand_pointwise_bound (x t C_zeta : ℝ) (hx : 0 < x)
    (_hC : 0 ≤ C_zeta)
    (h_zeta : ‖logDeriv riemannZeta ((1/2 : ℂ) + (t : ℂ) * I)‖ ≤ C_zeta) :
    ‖-logDeriv riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) *
      ((x : ℂ) ^ ((1/2 : ℂ) + (t : ℂ) * I) / ((1/2 : ℂ) + (t : ℂ) * I))‖ ≤
    2 * C_zeta * Real.sqrt x := by
  -- Rewrite neg as negation of product for norm_neg
  rw [show (-logDeriv riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) *
        ((x : ℂ) ^ ((1/2 : ℂ) + (t : ℂ) * I) / ((1/2 : ℂ) + (t : ℂ) * I))) =
      -(logDeriv riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) *
        ((x : ℂ) ^ ((1/2 : ℂ) + (t : ℂ) * I) / ((1/2 : ℂ) + (t : ℂ) * I))) from by ring,
    norm_neg, norm_mul, norm_div]
  -- ‖ζ'/ζ‖ * (‖x^s‖ / ‖s‖) ≤ C_zeta * (√x / (1/2)) = 2 * C_zeta * √x
  have h_norm_x : ‖(x : ℂ) ^ ((1/2 : ℂ) + (t : ℂ) * I)‖ = Real.sqrt x :=
    PerronAssemblyAtomics.vertical_pointwise_norm_half_sqrt x t hx
  rw [h_norm_x]
  have h_denom : (1 : ℝ)/2 ≤ ‖(1/2 : ℂ) + (t : ℂ) * I‖ := norm_half_add_mul_I_ge t
  have h_denom_pos : (0 : ℝ) < ‖(1/2 : ℂ) + (t : ℂ) * I‖ := by linarith
  have h_sqrt_nn : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  -- √x / ‖s‖ ≤ √x / (1/2) = 2 * √x
  have h_div : Real.sqrt x / ‖(1/2 : ℂ) + (t : ℂ) * I‖ ≤ 2 * Real.sqrt x := by
    rw [div_le_iff₀ h_denom_pos]
    calc Real.sqrt x = Real.sqrt x * 1 := by ring
      _ ≤ Real.sqrt x * (2 * ‖(1/2 : ℂ) + (t : ℂ) * I‖) := by
          apply mul_le_mul_of_nonneg_left _ h_sqrt_nn
          linarith
      _ = 2 * Real.sqrt x * ‖(1/2 : ℂ) + (t : ℂ) * I‖ := by ring
  calc ‖logDeriv riemannZeta ((1/2 : ℂ) + (t : ℂ) * I)‖ *
        (Real.sqrt x / ‖(1/2 : ℂ) + (t : ℂ) * I‖)
      ≤ C_zeta * (2 * Real.sqrt x) :=
        mul_le_mul h_zeta h_div (div_nonneg h_sqrt_nn h_denom_pos.le) (by linarith)
    _ = 2 * C_zeta * Real.sqrt x := by ring

/-- **Atom 3: Vertical integral bound at Re = 1/2.**

Given a uniform bound C_zeta on ‖logDeriv ζ‖ along Re = 1/2 for |t| ≤ T,
the vertical integral is bounded by 4T · C_zeta · √x. -/
theorem vertical_half_bound (x T : ℝ) (hx : 2 ≤ x) (hT : 2 ≤ T)
    (C_zeta : ℝ) (hC : ∀ t, |t| ≤ T →
      ‖logDeriv riemannZeta ((1/2 : ℂ) + (t : ℂ) * I)‖ ≤ C_zeta) :
    ‖∫ t in (-T)..T, -logDeriv riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) *
      ((x : ℂ) ^ ((1/2 : ℂ) + (t : ℂ) * I) / ((1/2 : ℂ) + (t : ℂ) * I))‖ ≤
    4 * T * C_zeta * Real.sqrt x := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hT_pos : (0 : ℝ) < T := by linarith
  have hC_nn : 0 ≤ C_zeta := by
    have := hC 0 (by simp; linarith)
    exact le_trans (norm_nonneg _) this
  -- Apply norm_integral_le_of_norm_le_const with bound 2 * C_zeta * √x
  have hbound : ∀ t, t ∈ Set.uIoc (-T) T →
      ‖-logDeriv riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) *
        ((x : ℂ) ^ ((1/2 : ℂ) + (t : ℂ) * I) / ((1/2 : ℂ) + (t : ℂ) * I))‖ ≤
      2 * C_zeta * Real.sqrt x := by
    intro t ht
    have ht_abs : |t| ≤ T := by
      rw [Set.mem_uIoc] at ht
      rw [abs_le]
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
    exact vertical_integrand_pointwise_bound x t C_zeta hx_pos hC_nn (hC t ht_abs)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc ‖∫ t in (-T)..T, -logDeriv riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) *
        ((x : ℂ) ^ ((1/2 : ℂ) + (t : ℂ) * I) / ((1/2 : ℂ) + (t : ℂ) * I))‖
      ≤ 2 * C_zeta * Real.sqrt x * |T - -T| := h
    _ = 2 * C_zeta * Real.sqrt x * (2 * T) := by
        rw [show T - -T = 2 * T from by ring, abs_of_nonneg (by linarith)]
    _ = 4 * T * C_zeta * Real.sqrt x := by ring

/-! ## Atom 1: Residue of x^s/s · (-ζ'/ζ) at s=1 is x

The integrand g(s) = -logDeriv riemannZeta s · (x^s / s) has a simple pole at s=1
coming from the pole of ζ(s). The residue is:
  lim_{s→1} (s-1) · g(s) = lim [(s-1)·(-ζ'/ζ(s))] · [x^s/s] = 1 · x = x

This uses:
- `neg_zeta_logDeriv_residue_one`: (s-1)·(-ζ'/ζ(s)) → 1  (from LaurentExpansion.lean)
- CIF for the circle integral

The full proof requires showing the "removed singularity" function
  f(s) = (s-1) · g(s) = (s-1) · (-logDeriv ζ s) · (x^s / s)
is continuous on closedBall(1,R)\{1}, differentiable on ball(1,R)\{1}, and
has limit x at s=1. Then applying the CIF with removable singularities. -/

/-- Helper: the desingularized integrand (s-1)·(-logDeriv ζ s)·(x^s/s) is differentiable
    at any point z ≠ 1, z ≠ 0, ζ(z) ≠ 0. -/
private theorem desing_differentiableAt (x : ℝ) (hx : 0 < x) (z : ℂ)
    (hz_ne_1 : z ≠ 1) (hz_ne_0 : z ≠ 0) (hζ : riemannZeta z ≠ 0) :
    DifferentiableAt ℂ (fun s => (s - 1) * (-logDeriv riemannZeta s) * ((x : ℂ) ^ s / s)) z := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact differentiableAt_id.sub (differentiableAt_const 1)
    · apply DifferentiableAt.neg
      rw [show logDeriv riemannZeta = fun s => deriv riemannZeta s / riemannZeta s from by
        ext; exact logDeriv_apply _ _]
      apply DifferentiableAt.div
      · have hdo : DifferentiableOn ℂ (deriv riemannZeta) {(1 : ℂ)}ᶜ :=
          DifferentiableOn.deriv
            (fun w hw => (differentiableAt_riemannZeta
              (Set.mem_compl_singleton_iff.mp hw)).differentiableWithinAt)
            isOpen_compl_singleton
        exact (hdo z (Set.mem_compl_singleton_iff.mpr hz_ne_1)).differentiableAt
          (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hz_ne_1))
      · exact differentiableAt_riemannZeta hz_ne_1
      · exact hζ
  · exact (DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (by exact_mod_cast hx.ne'))).div differentiableAt_id hz_ne_0

/-- The "desingularized" integrand: f(s) = (s-1) · (-logDeriv ζ s) · (x^s / s).
    At s=1 this has a removable singularity with value x. -/
def desingularized_integrand (x : ℝ) (s : ℂ) : ℂ :=
  (s - 1) * (-logDeriv riemannZeta s) * ((x : ℂ) ^ s / s)

/-- The limit of the desingularized integrand at s=1 is x.
    Proof: (s-1)·(-ζ'/ζ(s)) → 1 and x^s/s → x^1/1 = x. -/
theorem desingularized_tendsto (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (desingularized_integrand x) (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ)
      (nhds ((x : ℂ))) := by
  unfold desingularized_integrand
  -- Factor 1: (s-1)*(-logDeriv ζ s) → 1
  -- From neg_zeta_logDeriv_residue_one after rewriting logDeriv = deriv/f
  have h1 : Filter.Tendsto (fun s : ℂ => (s - 1) * (-logDeriv riemannZeta s))
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 1) := by
    simp only [logDeriv_apply]
    have hres := neg_zeta_logDeriv_residue_one
    simp only [neg_div] at hres
    exact hres
  -- Factor 2: x^s/s → x^1/1 = x (by continuity at s = 1)
  have h2 : Filter.Tendsto (fun s : ℂ => (x : ℂ) ^ s / s)
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds ((x : ℂ) ^ (1 : ℂ) / (1 : ℂ))) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      (ContinuousAt.div (ContinuousAt.const_cpow continuousAt_id
        (Or.inl (by exact_mod_cast hx.ne'))) continuousAt_id one_ne_zero).tendsto
  rw [cpow_one, div_one] at h2
  -- Product of limits: 1 * x = x
  have h3 := h1.mul h2
  simp only [one_mul] at h3
  exact h3

/-- **Atom 1: Residue of x^s/s · (-ζ'/ζ) at s=1 is x.**

The circle integral of the Perron integrand around s=1 picks up
the residue 2πi · x from the simple pole of ζ at s=1.

Proof: Write g(s) = (s-1)⁻¹ · f(s) where f(s) = (s-1) · g(s) is the desingularized version.
f is continuous on closedBall(1,R)\{1}, differentiable on ball(1,R)\{1}, and has limit x
at s=1. The CIF for removable singularities gives ∮ (s-1)⁻¹ · f(s) = 2πi · x.

The hypothesis `hzf` asserts ζ has no zeros on closedBall(1,R) \ {1}. This holds for
small R since ζ has a pole (not a zero) at s=1; see `riemannZeta_ne_zero_near_one`. -/
theorem perron_residue_at_one (x : ℝ) (hx : 0 < x) (R : ℝ) (hR : 0 < R) (hR1 : R < 1)
    (hzf : ∀ z ∈ Metric.closedBall (1 : ℂ) R, z ≠ 1 → riemannZeta z ≠ 0) :
    ∮ z in C(1, R), -logDeriv riemannZeta z * ((x : ℂ) ^ z / z) =
      2 * π * I * (x : ℂ) := by
  -- Step 1: Rewrite integrand as (z-1)⁻¹ • desingularized on the circle
  have hint_eq : ∮ z in C(1, R), -logDeriv riemannZeta z * ((x : ℂ) ^ z / z) =
      ∮ z in C(1, R), (z - 1)⁻¹ • ((z - 1) * (-logDeriv riemannZeta z) *
        ((x : ℂ) ^ z / z)) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    simp only [smul_eq_mul]
    have hne : z ≠ 1 := by
      intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    field_simp [sub_ne_zero.mpr hne]
  rw [hint_eq]
  -- Step 2: Apply CIF with removable singularity
  have hcif := Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
    hR (Set.countable_empty : (∅ : Set ℂ).Countable)
    (show ContinuousOn (fun s => (s - 1) * (-logDeriv riemannZeta s) * ((x : ℂ) ^ s / s))
      (Metric.closedBall 1 R \ {1}) from fun z hz => by
        obtain ⟨hz_ball, hz_ne⟩ := Set.mem_diff_singleton.mp hz
        have hz_ne_0 : z ≠ 0 := by
          intro heq; rw [heq, Metric.mem_closedBall, Complex.dist_eq] at hz_ball
          simp at hz_ball; linarith
        exact (desing_differentiableAt x hx z hz_ne hz_ne_0
          (hzf z hz_ball hz_ne)).continuousAt.continuousWithinAt)
    (show ∀ z ∈ (Metric.ball (1 : ℂ) R \ {1}) \ ∅,
      DifferentiableAt ℂ (fun s => (s - 1) * (-logDeriv riemannZeta s) *
        ((x : ℂ) ^ s / s)) z from fun z hz => by
        simp only [Set.diff_empty] at hz
        obtain ⟨hz_ball, hz_ne⟩ := Set.mem_diff_singleton.mp hz
        have hz_ne_0 : z ≠ 0 := by
          intro heq; rw [heq, Metric.mem_ball, Complex.dist_eq] at hz_ball
          simp at hz_ball; linarith
        exact desing_differentiableAt x hx z hz_ne hz_ne_0
          (hzf z (Metric.ball_subset_closedBall hz_ball) hz_ne))
    (desingularized_tendsto x hx)
  rw [hcif, smul_eq_mul]

/-! ## Atom 2: Residue at a zero ρ is -m(ρ) · x^ρ/ρ

At a zero ρ of ζ with multiplicity m(ρ), -ζ'/ζ has a pole with residue -m(ρ).
The integrand g(s) = -logDeriv ζ(s) · x^s/s therefore has residue -m(ρ) · x^ρ/ρ.

Similar structure to Atom 1 but with analyticOrderAt for the multiplicity. -/

/-- **Atom 2: Residue at a zero ρ of ζ.**

∮_{|z-ρ|=R} (-ζ'/ζ(z)) · x^z/z dz = 2πi · (-m(ρ) · x^ρ/ρ)

where m(ρ) = (analyticOrderAt riemannZeta ρ).toNat is the multiplicity of the zero.

The proof mirrors Atom 1: the integrand is `(z-ρ)⁻¹ • f(z)` where
f(z) = (z-ρ) · (-logDeriv ζ z) · (x^z/z) is desingularized. The CIF for
removable singularities then gives `2πi · lim_{z→ρ} f(z)`.

Hypotheses:
- `htend`: the limit of the desingularized integrand at ρ.
  Mathematically: `(z-ρ)·(-logDeriv ζ z) → -m(ρ)` (logDeriv residue at a zero of order m),
  combined with `x^z/z → x^ρ/ρ` (continuity). This requires the factorization
  `ζ(z) = (z-ρ)^m · g(z)` with `g(ρ) ≠ 0`, which Mathlib's analyticOrderAt provides
  in principle but the logDeriv connection is not yet formalized.
- `hzf`: ζ has no OTHER zeros in closedBall(ρ,R) (besides ρ itself).
- `h_ne_one`: 1 ∉ closedBall(ρ,R), so ζ is holomorphic throughout.
- `h_ne_zero_ball`: 0 ∉ closedBall(ρ,R), so x^z/z is holomorphic. -/
theorem perron_residue_at_zero (x : ℝ) (hx : 0 < x) (ρ : ℂ)
    (_hρ_zero : riemannZeta ρ = 0) (_hρ_ne : ρ ≠ 0)
    (R : ℝ) (hR : 0 < R)
    (h_ne_one : (1 : ℂ) ∉ Metric.closedBall ρ R)
    (h_ne_zero_ball : (0 : ℂ) ∉ Metric.closedBall ρ R)
    (hzf : ∀ z ∈ Metric.closedBall ρ R, z ≠ ρ → riemannZeta z ≠ 0)
    (htend : Filter.Tendsto (fun z => (z - ρ) * (-logDeriv riemannZeta z) *
      ((x : ℂ) ^ z / z)) (nhdsWithin ρ {ρ}ᶜ)
      (nhds (-(analyticOrderAt riemannZeta ρ).toNat * (x : ℂ) ^ ρ / ρ))) :
    ∮ z in C(ρ, R), -logDeriv riemannZeta z * ((x : ℂ) ^ z / z) =
    2 * π * I * (-(analyticOrderAt riemannZeta ρ).toNat * (x : ℂ) ^ ρ / ρ) := by
  -- Step 1: Rewrite integrand as (z-ρ)⁻¹ • desingularized on the circle
  have hint_eq : ∮ z in C(ρ, R), -logDeriv riemannZeta z * ((x : ℂ) ^ z / z) =
      ∮ z in C(ρ, R), (z - ρ)⁻¹ • ((z - ρ) * (-logDeriv riemannZeta z) *
        ((x : ℂ) ^ z / z)) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    simp only [smul_eq_mul]
    have hne : z ≠ ρ := by
      intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    field_simp [sub_ne_zero.mpr hne]
  rw [hint_eq]
  -- Step 2: Apply CIF with removable singularity
  have hcif := Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
    hR (Set.countable_empty : (∅ : Set ℂ).Countable)
    (show ContinuousOn (fun z => (z - ρ) * (-logDeriv riemannZeta z) *
      ((x : ℂ) ^ z / z)) (Metric.closedBall ρ R \ {ρ}) from fun z hz => by
        obtain ⟨hz_ball, hz_ne⟩ := Set.mem_diff_singleton.mp hz
        have hz_ne_1 : z ≠ 1 := fun heq => h_ne_one (heq ▸ hz_ball)
        have hz_ne_0 : z ≠ 0 := fun heq => h_ne_zero_ball (heq ▸ hz_ball)
        -- DifferentiableAt implies ContinuousAt implies ContinuousWithinAt
        have hda : DifferentiableAt ℂ (fun z => (z - ρ) * (-logDeriv riemannZeta z) *
            ((x : ℂ) ^ z / z)) z := by
          apply DifferentiableAt.mul
          · apply DifferentiableAt.mul
            · exact differentiableAt_id.sub (differentiableAt_const ρ)
            · apply DifferentiableAt.neg
              rw [show logDeriv riemannZeta = fun s => deriv riemannZeta s / riemannZeta s from by
                ext; exact logDeriv_apply _ _]
              apply DifferentiableAt.div
              · have hdo : DifferentiableOn ℂ (deriv riemannZeta) {(1 : ℂ)}ᶜ :=
                  DifferentiableOn.deriv
                    (fun w hw => (differentiableAt_riemannZeta
                      (Set.mem_compl_singleton_iff.mp hw)).differentiableWithinAt)
                    isOpen_compl_singleton
                exact (hdo z (Set.mem_compl_singleton_iff.mpr hz_ne_1)).differentiableAt
                  (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hz_ne_1))
              · exact differentiableAt_riemannZeta hz_ne_1
              · exact hzf z hz_ball hz_ne
          · exact (DifferentiableAt.const_cpow differentiableAt_id
              (Or.inl (by exact_mod_cast hx.ne'))).div differentiableAt_id hz_ne_0
        exact hda.continuousAt.continuousWithinAt)
    (show ∀ z ∈ (Metric.ball ρ R \ {ρ}) \ ∅,
      DifferentiableAt ℂ (fun z => (z - ρ) * (-logDeriv riemannZeta z) *
        ((x : ℂ) ^ z / z)) z from fun z hz => by
        simp only [Set.diff_empty] at hz
        obtain ⟨hz_ball, hz_ne⟩ := Set.mem_diff_singleton.mp hz
        have hz_ne_1 : z ≠ 1 := fun heq => h_ne_one (heq ▸ Metric.ball_subset_closedBall hz_ball)
        have hz_ne_0 : z ≠ 0 := fun heq => h_ne_zero_ball (heq ▸ Metric.ball_subset_closedBall hz_ball)
        apply DifferentiableAt.mul
        · apply DifferentiableAt.mul
          · exact differentiableAt_id.sub (differentiableAt_const ρ)
          · apply DifferentiableAt.neg
            rw [show logDeriv riemannZeta = fun s => deriv riemannZeta s / riemannZeta s from by
              ext; exact logDeriv_apply _ _]
            apply DifferentiableAt.div
            · have hdo : DifferentiableOn ℂ (deriv riemannZeta) {(1 : ℂ)}ᶜ :=
                DifferentiableOn.deriv
                  (fun w hw => (differentiableAt_riemannZeta
                    (Set.mem_compl_singleton_iff.mp hw)).differentiableWithinAt)
                  isOpen_compl_singleton
              exact (hdo z (Set.mem_compl_singleton_iff.mpr hz_ne_1)).differentiableAt
                (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hz_ne_1))
            · exact differentiableAt_riemannZeta hz_ne_1
            · exact hzf z (Metric.ball_subset_closedBall hz_ball) hz_ne
        · exact (DifferentiableAt.const_cpow differentiableAt_id
            (Or.inl (by exact_mod_cast hx.ne'))).div differentiableAt_id hz_ne_0)
    htend
  rw [hcif, smul_eq_mul]

/-! ## Supporting lemmas for future sorry closure -/

/-- On the punctured disk around 1, x^s/s is holomorphic (s ≠ 0 since R < 1). -/
theorem cpow_div_differentiableOn_punctured (x : ℝ) (hx : 0 < x) (R : ℝ) (hR1 : R < 1) :
    DifferentiableOn ℂ (fun s => (x : ℂ) ^ s / s) (Metric.closedBall (1 : ℂ) R \ {1}) := by
  intro s hs
  have hs_ball := (Set.mem_diff _).mp hs |>.1
  have hs_ne_zero : s ≠ 0 := by
    intro heq
    rw [heq] at hs_ball
    simp only [Metric.mem_closedBall, Complex.dist_eq] at hs_ball
    norm_num at hs_ball
    linarith
  exact (PerronKernelAtomics.differentiableAt_cpow_div x hx s hs_ne_zero).differentiableWithinAt

/-- x^s/s is continuous at s=1 with value x (for x > 0). -/
theorem cpow_div_continuous_at_one (x : ℝ) (hx : 0 < x) :
    ContinuousAt (fun s => (x : ℂ) ^ s / s) 1 := by
  apply ContinuousAt.div
  · apply ContinuousAt.const_cpow continuousAt_id
    left
    exact_mod_cast hx.ne'
  · exact continuousAt_id
  · exact one_ne_zero

/-- x^s/s evaluates to x at s = 1 (for x > 0). -/
theorem cpow_div_at_one (x : ℝ) (_hx : 0 < x) :
    (x : ℂ) ^ (1 : ℂ) / (1 : ℂ) = (x : ℂ) := by
  rw [cpow_one, div_one]

/-- x^s/s is continuous on closedBall(1, R) (for x > 0, R < 1, so 0 ∉ closedBall). -/
theorem cpow_div_continuousOn_closedBall (x : ℝ) (hx : 0 < x) (R : ℝ)
    (_hR : 0 ≤ R) (hR1 : R < 1) :
    ContinuousOn (fun s => (x : ℂ) ^ s / s) (Metric.closedBall (1 : ℂ) R) := by
  intro s hs
  have hs_ne_zero : s ≠ 0 := by
    intro heq
    rw [heq] at hs
    simp only [Metric.mem_closedBall, Complex.dist_eq] at hs
    norm_num at hs
    linarith
  exact (PerronKernelAtomics.differentiableAt_cpow_div x hx s hs_ne_zero).continuousAt.continuousWithinAt

/-- x^s/s is differentiable on closedBall(1, R) (for x > 0, R < 1, so 0 ∉ closedBall). -/
theorem cpow_div_differentiableOn_closedBall (x : ℝ) (hx : 0 < x) (R : ℝ)
    (_hR : 0 ≤ R) (hR1 : R < 1) :
    DifferentiableOn ℂ (fun s => (x : ℂ) ^ s / s) (Metric.closedBall (1 : ℂ) R) := by
  intro s hs
  have hs_ne_zero : s ≠ 0 := by
    intro heq
    rw [heq] at hs
    simp only [Metric.mem_closedBall, Complex.dist_eq] at hs
    norm_num at hs
    linarith
  exact (PerronKernelAtomics.differentiableAt_cpow_div x hx s hs_ne_zero).differentiableWithinAt

end PerronResidueAtoms
