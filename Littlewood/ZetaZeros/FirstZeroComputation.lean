/-
First Zero of the Riemann Zeta Function — Computational Infrastructure

Goal: Prove `FirstZeroOrdinateHyp` by establishing that the first nontrivial
zero of ζ(s) has imaginary part γ₁ ∈ (14.13, 14.14), and γ₁ is minimal among
positive zero ordinates.

## Strategy

The proof decomposes into two independent sub-hypotheses:

### Sub-Hypothesis A: `FirstZeroExistsHyp`
There exists a zero of ζ on the critical line with Im ∈ (14.13, 14.14).

Proof route: Evaluate the Hardy Z-function Z(t) at t = 14.13 and t = 14.14
using the Riemann-Siegel formula with verified error bounds. Show Z changes
sign, apply IVT to get Z(t₀) = 0 for some t₀ ∈ (14.13, 14.14), then
convert to ζ(1/2 + it₀) = 0.

### Sub-Hypothesis B: `ZeroFreeBelow1413Hyp`
All nontrivial zeros with positive imaginary part have Im(ρ) > 14.13.

Proof route: Use Backlund's method — evaluate the argument of ζ on the
boundary of [0,1] × [0,14.13] to show the winding number is 0, hence
N(14.13) = 0.

### Assembly
Given both sub-hypotheses, the assembly theorem extracts the minimum
of the finite set of zero ordinates ≤ t₀ to construct the witness γ₁.
This uses `finite_zeros_le` from ZeroCountingFunction.lean.

## Status (2026-03-16)
- Assembly: PROVED (sorry-free given sub-hypotheses)
- Sub-Hypothesis A: Framework built, computation certificates TODO
- Sub-Hypothesis B: Framework built, computation certificates TODO
- IVT sign-change framework: PROVED
- Continuity of ζ on critical line: PROVED
- Critical line zero → zetaNontrivialZerosPos membership: PROVED

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.ZeroCountingFunction

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace ZetaZeros.FirstZeroComputation

open Complex Set MeasureTheory Topology Filter Real

/-! ## Part 1: Continuity of ζ on the Critical Line -/

/-- The map t ↦ 1/2 + it is continuous ℝ → ℂ. -/
theorem criticalLine_continuous :
    Continuous (fun t : ℝ => (1/2 : ℂ) + (t : ℂ) * I) := by
  fun_prop

/-- Points on the critical line are not equal to 1. -/
theorem criticalLine_ne_one (t : ℝ) :
    (1/2 : ℂ) + (t : ℂ) * I ≠ 1 := by
  intro h
  have := congr_arg Complex.re h
  simp at this

/-- ζ is continuous along the critical line. -/
theorem riemannZeta_continuous_criticalLine :
    Continuous (fun t : ℝ => riemannZeta ((1/2 : ℂ) + (t : ℂ) * I)) := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  exact ContinuousAt.comp
    (differentiableAt_riemannZeta (criticalLine_ne_one t)).continuousAt
    criticalLine_continuous.continuousAt

/-- The real part of ζ on the critical line is continuous. -/
theorem riemannZeta_re_continuous_criticalLine :
    Continuous (fun t : ℝ => (riemannZeta ((1/2 : ℂ) + (t : ℂ) * I)).re) :=
  Complex.continuous_re.comp riemannZeta_continuous_criticalLine

/-- The imaginary part of ζ on the critical line is continuous. -/
theorem riemannZeta_im_continuous_criticalLine :
    Continuous (fun t : ℝ => (riemannZeta ((1/2 : ℂ) + (t : ℂ) * I)).im) :=
  Complex.continuous_im.comp riemannZeta_continuous_criticalLine

/-- The norm of ζ on the critical line is continuous. -/
theorem riemannZeta_norm_continuous_criticalLine :
    Continuous (fun t : ℝ => ‖riemannZeta ((1/2 : ℂ) + (t : ℂ) * I)‖) :=
  continuous_norm.comp riemannZeta_continuous_criticalLine

/-! ## Part 2: Critical Line ↔ Nontrivial Zeros -/

/-- Imaginary part of a point on the critical line. -/
lemma critLine_im (t : ℝ) : ((1/2 : ℂ) + (t : ℂ) * I).im = t := by
  simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- A zero of ζ on the critical line with positive imaginary part is a nontrivial zero
    with positive imaginary part. -/
theorem criticalLine_zero_mem_pos {t : ℝ} (ht_pos : 0 < t)
    (hzero : riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) = 0) :
    (1/2 : ℂ) + (t : ℂ) * I ∈ zetaNontrivialZerosPos := by
  refine ⟨⟨hzero, ?_, ?_⟩, ?_⟩ <;>
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.add_im, Complex.ofReal_im, Complex.mul_im] <;>
    linarith

/-- A zero on the critical line with t > 0 gives t ∈ zetaZeroOrdinates. -/
theorem criticalLine_zero_ordinate {t : ℝ} (ht_pos : 0 < t)
    (hzero : riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) = 0) :
    t ∈ zetaZeroOrdinates :=
  ⟨(1/2 : ℂ) + (t : ℂ) * I, criticalLine_zero_mem_pos ht_pos hzero, critLine_im t⟩

/-- t₀ belongs to the image of zeros up to t₀. -/
private lemma t0_mem_image {t₀ : ℝ}
    (ht₀_mem : (1/2 : ℂ) + (t₀ : ℂ) * I ∈ zetaNontrivialZerosPos) :
    t₀ ∈ (·.im) '' (zetaNontrivialZerosPos ∩ {s : ℂ | s.im ≤ t₀}) := by
  refine ⟨(1/2 : ℂ) + (t₀ : ℂ) * I, ⟨ht₀_mem, ?_⟩, critLine_im t₀⟩
  simp [Set.mem_setOf_eq]

/-! ## Part 3: IVT Framework for Zero Detection -/

/-- If a continuous function changes sign on [a,b], there is a zero in (a,b). -/
theorem ivt_sign_change {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ t ∈ Set.Ioo a b, f t = 0 := by
  have hsub := intermediate_value_Icc (le_of_lt hab) hf
  have h0_mem : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt hfa, le_of_lt hfb⟩
  obtain ⟨t, ht_mem, ht_eq⟩ := hsub h0_mem
  refine ⟨t, ?_, ht_eq⟩
  constructor
  · rcases eq_or_lt_of_le ht_mem.1 with h | h
    · exfalso; rw [← h] at ht_eq; linarith
    · exact h
  · rcases eq_or_lt_of_le ht_mem.2 with h | h
    · exfalso; rw [h] at ht_eq; linarith
    · exact h

/-- Symmetric version: sign change from positive to negative. -/
theorem ivt_sign_change' {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hfa : 0 < f a) (hfb : f b < 0) :
    ∃ t ∈ Set.Ioo a b, f t = 0 := by
  have ⟨t, ht_mem, ht_eq⟩ := ivt_sign_change hab hf.neg (by linarith) (by linarith)
  exact ⟨t, ht_mem, by linarith⟩

/-! ## Part 4: Sub-Hypothesis Decomposition -/

/-- CLAIM A: There exists a zero of ζ on the critical line with imaginary part
    in the interval (14.13, 14.14).

    PROOF STRATEGY: Use the Hardy Z-function sign change.
    Z(14.13) ≈ -0.0073 < 0 and Z(14.14) ≈ +0.0637 > 0.
    By IVT, Z has a zero t₀ ∈ (14.13, 14.14), giving ζ(1/2+it₀) = 0.

    COMPUTATIONAL REQUIREMENTS:
    1. Verified bound: Z(14.13) < 0
    2. Verified bound: Z(14.14) > 0
    3. Continuity of Z on [14.13, 14.14]
    4. Z(t) = 0 ↔ ζ(1/2+it) = 0 -/
class FirstZeroExistsHyp : Prop where
  exists_zero : ∃ t ∈ Set.Ioo (14.13 : ℝ) 14.14,
    riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) = 0

/-- CLAIM B: The critical strip is zero-free below height 14.13.

    PROOF STRATEGY: Use Backlund's method or direct RvM computation.
    N(14.13) = 0, which means no nontrivial zero has 0 < Im(ρ) ≤ 14.13.

    COMPUTATIONAL REQUIREMENTS:
    1. Verified evaluation of (T/2π)log(T/2π) - T/2π + 7/8 at T = 14.13
    2. Verified bound on |S(T)| at T = 14.13
    3. Conclude N(14.13) = 0 -/
class ZeroFreeBelow1413Hyp : Prop where
  zero_free : ∀ ρ ∈ zetaNontrivialZerosPos, (14.13 : ℝ) < ρ.im

/-! ## Part 5: Assembly — From Sub-Hypotheses to FirstZeroOrdinateHyp

This is the core theorem: given both sub-hypotheses, construct
`FirstZeroOrdinateHyp` by extracting the minimum of the finite set
of zero ordinates up to t₀. -/

/-- Given both sub-hypotheses, construct FirstZeroOrdinateHyp. -/
instance instFirstZeroOrdinateHyp_of_subhyps
    [FirstZeroExistsHyp] [ZeroFreeBelow1413Hyp] :
    FirstZeroOrdinateHyp where
  bounds := by
    obtain ⟨t₀, ⟨hat₀, ht₀b⟩, hzero⟩ := FirstZeroExistsHyp.exists_zero
    have ht₀_pos : (0 : ℝ) < t₀ := by linarith
    have ht₀_mem := criticalLine_zero_mem_pos ht₀_pos hzero
    -- Finite zeros up to t₀
    have hfin := finite_zeros_le t₀
    -- The image set of ordinates ≤ t₀
    set S := (·.im) '' (zetaNontrivialZerosPos ∩ {s : ℂ | s.im ≤ t₀})
    have hS_fin : S.Finite := Set.Finite.image _ hfin
    have hS_ne : S.Nonempty := ⟨t₀, t0_mem_image ht₀_mem⟩
    -- Extract the minimum of the finite nonempty set S
    obtain ⟨γ₁, hγ₁_mem, hγ₁_min⟩ :=
      (⟨hS_fin.toFinset.min' (by rwa [Set.Finite.toFinset_nonempty]),
        hS_fin.mem_toFinset.mp (Finset.min'_mem _ _),
        fun x hx => Finset.min'_le _ _ (hS_fin.mem_toFinset.mpr hx)⟩ :
      ∃ m ∈ S, ∀ x ∈ S, m ≤ x)
    -- γ₁ is a zero ordinate
    have hγ₁_ord : γ₁ ∈ zetaZeroOrdinates := by
      obtain ⟨ρ, ⟨hρ_pos, _⟩, hrfl⟩ := hγ₁_mem
      exact ⟨ρ, hρ_pos, hrfl⟩
    -- γ₁ > 14.13 (from zero-free below 14.13)
    have hγ₁_low : 14.13 < γ₁ := by
      obtain ⟨ρ, ⟨hρ_pos, _⟩, hrfl⟩ := hγ₁_mem
      exact hrfl ▸ ZeroFreeBelow1413Hyp.zero_free ρ hρ_pos
    -- γ₁ < 14.14 (since γ₁ ≤ t₀ < 14.14)
    have hγ₁_high : γ₁ < 14.14 := by
      have : γ₁ ≤ t₀ := hγ₁_min t₀ (t0_mem_image ht₀_mem)
      linarith
    -- γ₁ is minimal among ALL zero ordinates
    have hγ₁_global : ∀ γ ∈ zetaZeroOrdinates, γ₁ ≤ γ := by
      intro γ ⟨ρ, hρ_pos, hrfl⟩
      by_cases hle : ρ.im ≤ t₀
      · rw [← hrfl]
        exact hγ₁_min ρ.im ⟨ρ, ⟨hρ_pos, hle⟩, rfl⟩
      · push_neg at hle
        rw [← hrfl]
        have : γ₁ ≤ t₀ := hγ₁_min t₀ (t0_mem_image ht₀_mem)
        linarith
    exact ⟨γ₁, hγ₁_ord, hγ₁_low, hγ₁_high, hγ₁_global⟩

/-! ## Part 6: Hardy Z-Function Equivalence

The Hardy Z-function Z(t) = e^{iθ(t)} ζ(1/2+it) is used for zero detection
because it is real-valued (by the functional equation). Key properties:
- |e^{iθ}| = 1, so Z(t) = 0 ↔ ζ(1/2+it) = 0
- Z real-valued means IVT applies directly to sign changes
-/

/-- Multiplication by a unit (‖u‖ = 1) preserves zeros. -/
theorem mul_unit_eq_zero_iff {w u : ℂ} (hu : ‖u‖ = 1) :
    u * w = 0 ↔ w = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (congr_arg (‖·‖) h |>.symm ▸ hu) (by norm_num)
    · exact h
  · intro h; rw [h, mul_zero]

/-- e^{iα} has norm 1. -/
theorem norm_exp_I_mul_real (α : ℝ) : ‖exp (I * (α : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I α

/-- e^{iα} · ζ(1/2+it) = 0 ↔ ζ(1/2+it) = 0. -/
theorem hardy_Z_zero_iff (α : ℝ) (t : ℝ) :
    exp (I * (α : ℂ)) * riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) = 0 ↔
    riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) = 0 :=
  mul_unit_eq_zero_iff (norm_exp_I_mul_real α)

/-- A complex number with zero imaginary and real part is zero. -/
theorem complex_real_and_re_zero {z : ℂ} (him : z.im = 0) (hre : z.re = 0) :
    z = 0 :=
  Complex.ext hre him

/-! ## Part 7: Sign-Change Reduction for FirstZeroExistsHyp

The reduction chain is:
  Hardy Z sign change data → Z has a zero in (a,b)
    → e^{iθ} · ζ has a zero → ζ has a zero → FirstZeroExistsHyp

This theorem shows that if ANY continuous real-valued function of the form
g(t) = e^{iα(t)} · ζ(1/2+it) satisfies g(a).re < 0 and g(b).re > 0,
and g is always real (im = 0), then ζ has a zero in (a,b). -/

/-- If a ℂ-valued function is always real (Im = 0) on [a,b], continuous, and
    its real part changes sign, then it has a zero in (a,b). -/
theorem sign_change_of_real_function
    {g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_real : ∀ t ∈ Set.Icc a b, (g t).im = 0)
    (hga : (g a).re < 0) (hgb : 0 < (g b).re) :
    ∃ t ∈ Set.Ioo a b, g t = 0 := by
  have hf_cont : ContinuousOn (fun t => (g t).re) (Set.Icc a b) :=
    Complex.continuous_re.comp_continuousOn hg_cont
  obtain ⟨t₀, ht₀, ht₀_eq⟩ := ivt_sign_change hab hf_cont hga hgb
  exact ⟨t₀, ht₀, complex_real_and_re_zero
    (hg_real t₀ (Set.Ioo_subset_Icc_self ht₀)) ht₀_eq⟩

/-- **Key reduction**: If we can find α : ℝ → ℝ such that:
    1. g(t) = e^{iα(t)} · ζ(1/2+it) is real-valued (Im = 0) on [a,b]
    2. g is continuous on [a,b]
    3. Re(g(a)) < 0 and Re(g(b)) > 0 (or vice versa)
    4. 0 < a
    Then `FirstZeroExistsHyp` holds (for the containing interval).

    In practice, α(t) = θ(t) = Im(log Γ(1/4 + it/2)) - (t/2)·log π
    is the Riemann-Siegel theta function. -/
theorem firstZeroExistsHyp_of_sign_change
    {g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (ha_pos : 0 < a) (ha_bound : (14.13 : ℝ) ≤ a) (hb_bound : b ≤ 14.14)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_real : ∀ t ∈ Set.Icc a b, (g t).im = 0)
    (hg_zero_iff : ∀ t ∈ Set.Icc a b,
      g t = 0 ↔ riemannZeta ((1/2 : ℂ) + (t : ℂ) * I) = 0)
    (hga : (g a).re < 0) (hgb : 0 < (g b).re) :
    FirstZeroExistsHyp where
  exists_zero := by
    obtain ⟨t₀, ht₀, ht₀_eq⟩ := sign_change_of_real_function hab hg_cont hg_real hga hgb
    exact ⟨t₀, ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩,
      (hg_zero_iff t₀ (Set.Ioo_subset_Icc_self ht₀)).mp ht₀_eq⟩

/-- ζ(s) = 0 iff ||ζ(s)|| = 0 -/
theorem riemannZeta_eq_zero_iff_norm_eq_zero (s : ℂ) :
    riemannZeta s = 0 ↔ ‖riemannZeta s‖ = 0 :=
  norm_eq_zero.symm

/-! ## Part 8: Final Reduction via Hardy Z Function

For any continuous, real-valued function Z : ℝ → ℂ satisfying
Z(t) = 0 ↔ ζ(1/2+it) = 0, a sign change of Re(Z) gives
a zeta zero. The Hardy Z function from HardyZRealV2.lean satisfies
these properties (proved there: `continuous_hardyZV2`,
`hardyZV2_real`, `hardyZV2_zero_iff_zeta_zero`).

The reduction chain is:
  [Re(Z 14.13) < 0] ∧ [Re(Z 14.14) > 0]
    → Z has a zero in (14.13, 14.14)     [by IVT]
    → ζ(1/2 + it₀) = 0 for some t₀ ∈ (14.13, 14.14)
    → FirstZeroExistsHyp
-/

/-- **Parametric reduction**: Given ANY continuous, real-valued function Z
    satisfying Z(t)=0 ↔ ζ(1/2+it)=0, a sign change on (14.13, 14.14)
    yields `FirstZeroExistsHyp`.

    In practice, Z = hardyZV2 from HardyZRealV2.lean, where:
    - `continuous_hardyZV2` : Continuous hardyZV2
    - `hardyZV2_real` : ∀ t, (hardyZV2 t).im = 0
    - `hardyZV2_zero_iff_zeta_zero` : hardyZV2 t = 0 ↔ ζ(1/2+I*t) = 0

    Numerical values: Z(14.13) ≈ -0.0073, Z(14.14) ≈ +0.0637. -/
theorem firstZeroExistsHyp_of_hardy_Z_signs
    {Z : ℝ → ℂ}
    (hZ_cont : Continuous Z)
    (hZ_real : ∀ t, (Z t).im = 0)
    (hZ_zero_iff : ∀ t, Z t = 0 ↔ riemannZeta (1/2 + I * t) = 0)
    (h_neg : (Z 14.13).re < 0)
    (h_pos : 0 < (Z 14.14).re) :
    FirstZeroExistsHyp where
  exists_zero := by
    -- Re(Z) is continuous
    have hZ_re_cont : Continuous (fun t : ℝ => (Z t).re) :=
      Complex.continuous_re.comp hZ_cont
    -- Apply IVT to get Re(Z(t₀)) = 0 for some t₀ ∈ (14.13, 14.14)
    obtain ⟨t₀, ht₀, ht₀_eq⟩ := ivt_sign_change (by norm_num : (14.13 : ℝ) < 14.14)
      hZ_re_cont.continuousOn h_neg h_pos
    -- Z(t₀) = 0 since Z is real and Re(Z(t₀)) = 0
    have hZ_zero : Z t₀ = 0 := complex_real_and_re_zero (hZ_real t₀) ht₀_eq
    -- ζ(1/2 + it₀) = 0
    have hzeta_zero : riemannZeta (1/2 + I * t₀) = 0 :=
      (hZ_zero_iff t₀).mp hZ_zero
    -- Convert I * t₀ to t₀ * I format
    have hformat : (1/2 : ℂ) + (t₀ : ℂ) * I = 1/2 + I * t₀ := by ring
    exact ⟨t₀, ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩, hformat ▸ hzeta_zero⟩

end ZetaZeros.FirstZeroComputation
