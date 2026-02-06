/-
The Stirling ratio Γ(z)/(z^{z-1/2}e^{-z}) is bounded on half-integer strips.
Proved via Phragmén-Lindelöf applied to the strip.

Co-authored-by: Claude Code <noreply@anthropic.com>
-/

import Littlewood.Aristotle.GammaGrowthGeneral

open Complex Real MeasureTheory Set Filter Topology Asymptotics
open scoped BigOperators Real Nat Classical

set_option maxHeartbeats 3200000

noncomputable section

namespace Aristotle.Bridge.StirlingRatioPL

open Aristotle.GammaGrowthGeneral

local notation "expR" => Real.exp

-- Inlined from GammaGrowthComplete to avoid circular dependency
private theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs]
  unfold Complex.GammaIntegral
  calc ‖∫ x in Ioi (0:ℝ), ↑((-x).exp) * (↑x : ℂ) ^ (s - 1)‖
      ≤ ∫ x in Ioi (0:ℝ), ‖↑((-x).exp) * (↑x : ℂ) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0:ℝ), (-x).exp * x ^ (s.re - 1) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        rw [Set.mem_Ioi] at hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _),
            Complex.norm_cpow_eq_rpow_re_of_pos hx (s - 1)]
        simp [Complex.sub_re]
    _ = Real.Gamma s.re := (Real.Gamma_eq_integral hs).symm

-- Boundary bound on a half-integer line for ALL t
private lemma boundary_bound_all (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (k₀ : ℤ) (hk₀ : σ₀ = 1/2 + (k₀ : ℝ))
    (hk₀_pos : 0 < 1/2 + (k₀ : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re = σ₀ → ‖stirling_ratio z‖ ≤ C := by
  -- Bound for |t| ≥ 1
  obtain ⟨B, hB⟩ := stirling_ratio_bound_on_lines k₀ hk₀_pos
  -- Bound for |t| ≤ 1 via continuity on compact segment
  have h_compact : ∃ M : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      ‖stirling_ratio (↑σ₀ + ↑t * I)‖ ≤ M := by
    have h_cont : ContinuousOn (fun t : ℝ => stirling_ratio (↑σ₀ + ↑t * I)) (Icc (-1) 1) := by
      unfold stirling_ratio stirling_kernel
      refine ContinuousOn.div ?_ ?_ ?_
      · -- Gamma is continuous at each boundary point
        refine continuousOn_of_forall_continuousAt fun t _ => ?_
        refine (Complex.differentiableAt_Gamma _ ?_).continuousAt.comp
          (Continuous.continuousAt (by continuity))
        intro m hm; simp [Complex.ext_iff] at hm; linarith [hm.1]
      · -- Kernel is continuous
        refine ContinuousOn.mul ?_ ?_
        · -- cpow part: z ↦ z^{z-1/2}
          refine continuousOn_of_forall_continuousAt fun t _ => ?_
          refine ContinuousAt.cpow ?_ ?_ ?_
          · exact Continuous.continuousAt (by continuity)
          · exact Continuous.continuousAt (by continuity)
          · rw [Complex.mem_slitPlane_iff]; left
            show 0 < (↑σ₀ + ↑t * I : ℂ).re
            simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
                  Complex.I_re, Complex.I_im, Complex.ofReal_im]
            exact hσ₀
        · -- exp part: z ↦ exp(-z)
          exact (Continuous.cexp (by continuity :
            Continuous (fun t : ℝ => -(↑σ₀ + ↑t * I : ℂ)))).continuousOn
      · -- Kernel is nonzero at each point
        intro t _
        refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
        have hz : (↑σ₀ + ↑t * I : ℂ) ≠ 0 := by
          intro h; have := congr_arg Complex.re h; simp at this; linarith
        simp only [Complex.cpow_def, if_neg hz]
        exact Complex.exp_ne_zero _
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc h_cont
    exact ⟨M, fun t ht => hM t ⟨by linarith [abs_le.mp ht], by linarith [abs_le.mp ht]⟩⟩
  obtain ⟨M, hM⟩ := h_compact
  -- Combined bound
  refine ⟨max (max B M) 1, by positivity, fun z hz => ?_⟩
  have h_eq : z = ↑σ₀ + ↑z.im * I :=
    Complex.ext (by simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, hz])
      (by simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re])
  rw [h_eq]
  by_cases ht : 1 ≤ |z.im|
  · -- Use stirling_ratio_bound_on_lines
    have h_cast : (↑σ₀ : ℂ) + ↑z.im * I = (1/2 + ↑k₀ : ℂ) + ↑z.im * I := by
      rw [hk₀]; push_cast; ring
    rw [h_cast]
    exact le_trans (hB z.im ht) (le_trans (le_max_left B M) (le_max_left _ _))
  · -- Use compact bound
    push_neg at ht
    exact le_trans (hM z.im ht.le) (le_trans (le_max_right B M) (le_max_left _ _))

-- Growth condition: stirling_ratio has sub-double-exponential growth in the strip
private lemma growth_condition (k : ℤ) (hk : 0 < 1/2 + (k : ℝ)) :
    ∃ c < π / ((1/2 + (k:ℝ) + 1) - (1/2 + (k:ℝ))), ∃ B,
      stirling_ratio =O[comap (_root_.abs ∘ im) atTop ⊓
        𝓟 (re ⁻¹' Ioo (1/2 + (k:ℝ)) (1/2 + (k:ℝ) + 1))]
        fun z ↦ expR (B * expR (c * |z.im|)) := by
  -- The strip has width 1, so π/(b-a) = π. We use c = 1 < π.
  refine ⟨(1 : ℝ), ?_, (1 : ℝ), ?_⟩
  · -- 1 < π/1
    have : (1/2 + (k:ℝ) + 1) - (1/2 + (k:ℝ)) = 1 := by ring
    rw [this, div_one]; exact Real.pi_gt_three.le.trans_lt' (by norm_num)
  · -- The =O bound
    -- Gamma bounded on compact σ-interval
    have h_Gamma_cont : ContinuousOn (fun σ : ℝ => Real.Gamma σ)
        (Icc (1/2+(k:ℝ)) (1/2+(k:ℝ)+1)) :=
      (Real.differentiableOn_Gamma_Ioi.mono (fun σ hσ => by
        simp only [Set.mem_Icc, Set.mem_Ioi] at *; linarith [hσ.1])).continuousOn
    obtain ⟨M_Γ, hM_Γ⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc h_Gamma_cont
    have hM_nn : 0 ≤ M_Γ :=
      le_trans (norm_nonneg _) (hM_Γ (1/2+(k:ℝ)) ⟨le_refl _, by linarith⟩)
    have hk_nn : (0:ℝ) ≤ (k:ℝ) := by
      by_contra h; push_neg at h
      have h1 : (k:ℤ) < 0 := by exact_mod_cast h
      have h2 : k ≤ (-1:ℤ) := by omega
      linarith [show (k:ℝ) ≤ -1 from by exact_mod_cast h2]
    set b := 1/2 + (k:ℝ) + 1
    -- =O packaging
    rw [Asymptotics.isBigO_iff]
    refine ⟨M_Γ * expR b, ?_⟩
    rw [Filter.eventually_inf_principal]
    apply Filter.Eventually.mono
      (Filter.preimage_mem_comap (Filter.Ici_mem_atTop (1:ℝ)))
    intro z hz hz_strip
    simp only [Function.comp, Set.mem_Ici] at hz
    simp only [Set.mem_preimage, Set.mem_Ioo] at hz_strip
    have h_re_pos : 0 < z.re := by linarith [hz_strip.1]
    -- ‖Γ(z)‖ ≤ M_Γ
    have h_num : ‖Complex.Gamma z‖ ≤ M_Γ := by
      calc ‖Complex.Gamma z‖
          ≤ Real.Gamma z.re := norm_Gamma_le_Gamma_re h_re_pos
        _ = ‖Real.Gamma z.re‖ := by
            rw [Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos h_re_pos)]
        _ ≤ M_Γ := hM_Γ z.re ⟨le_of_lt hz_strip.1, le_of_lt hz_strip.2⟩
    -- Kernel lower bound setup
    have hz_ne : z ≠ 0 := by intro h; rw [h] at h_re_pos; simp at h_re_pos
    have h_norm_ge : (1:ℝ) ≤ ‖z‖ := le_trans hz (abs_im_le_norm z)
    have h_rpow_ge : (1:ℝ) ≤ ‖z‖ ^ (z.re - 1/2) := by
      calc (1:ℝ) = ‖z‖ ^ (0:ℝ) := (rpow_zero _).symm
        _ ≤ ‖z‖ ^ (z.re - 1/2) :=
            Real.rpow_le_rpow_of_exponent_le h_norm_ge (by linarith [hz_strip.1])
    have h_arg : arg z * z.im ≤ π * |z.im| / 2 := by
      calc arg z * z.im ≤ |arg z * z.im| := le_abs_self _
        _ = |arg z| * |z.im| := abs_mul _ _
        _ ≤ π / 2 * |z.im| := mul_le_mul_of_nonneg_right
            (abs_arg_le_pi_div_two_iff.mpr h_re_pos.le) (abs_nonneg _)
        _ = π * |z.im| / 2 := by ring
    -- ‖kernel z‖ ≥ exp(-b) * exp(-π|t|/2)
    have h_kernel_lb : expR (-b) * expR (-π * |z.im| / 2) ≤ ‖stirling_kernel z‖ := by
      unfold stirling_kernel
      rw [norm_mul, norm_cpow_of_ne_zero hz_ne, Complex.norm_exp]
      have h_wre : (z - (1:ℂ)/2).re = z.re - 1/2 := by
        simp only [sub_re]; norm_num
      have h_wim : (z - (1:ℂ)/2).im = z.im := by
        simp only [sub_im]; norm_num
      rw [h_wre, h_wim, neg_re]
      -- Goal: exp(-b) * exp(-π|t|/2) ≤ (‖z‖^{σ-1/2} / exp(arg*t)) * exp(-σ)
      rw [div_mul_eq_mul_div, le_div_iff₀ (Real.exp_pos _)]
      -- Goal: exp(-b) * exp(-π|t|/2) * exp(arg*t) ≤ ‖z‖^{σ-1/2} * exp(-σ)
      rw [← Real.exp_add, ← Real.exp_add]
      calc expR (-b + -π * |z.im| / 2 + arg z * z.im)
          ≤ expR (-b) := Real.exp_le_exp.mpr (by nlinarith [h_arg])
        _ ≤ expR (-z.re) := Real.exp_le_exp.mpr (by linarith [hz_strip.2])
        _ = 1 * expR (-z.re) := (one_mul _).symm
        _ ≤ ‖z‖ ^ (z.re - 1/2) * expR (-z.re) :=
            mul_le_mul_of_nonneg_right h_rpow_ge (le_of_lt (Real.exp_pos _))
    -- Ratio bound: ‖ratio z‖ ≤ M_Γ * exp(b) * exp(π|t|/2)
    have h_kernel_pos : 0 < ‖stirling_kernel z‖ :=
      lt_of_lt_of_le (by positivity) h_kernel_lb
    have h_ratio : ‖stirling_ratio z‖ ≤ M_Γ * expR b * expR (π * |z.im| / 2) := by
      unfold stirling_ratio; rw [norm_div, div_le_iff₀ h_kernel_pos]
      have h_cancel : expR b * expR (-b) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h_cancel2 : expR (π * |z.im| / 2) * expR (-(π * |z.im| / 2)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc ‖Complex.Gamma z‖ ≤ M_Γ := h_num
        _ = M_Γ * (expR b * expR (-b)) * (expR (π * |z.im| / 2) *
              expR (-(π * |z.im| / 2))) := by rw [h_cancel, h_cancel2]; ring
        _ = M_Γ * expR b * expR (π * |z.im| / 2) *
              (expR (-b) * expR (-(π * |z.im| / 2))) := by ring
        _ ≤ M_Γ * expR b * expR (π * |z.im| / 2) * ‖stirling_kernel z‖ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc expR (-b) * expR (-(π * |z.im| / 2))
                = expR (-b) * expR (-π * |z.im| / 2) := by ring_nf
              _ ≤ ‖stirling_kernel z‖ := h_kernel_lb
    -- exp(π|t|/2) ≤ exp(exp(|t|))
    have h_exp_bound : π * |z.im| / 2 ≤ expR |z.im| := by
      have h1 : |z.im| ≤ expR (|z.im| - 1) := by linarith [add_one_le_exp (|z.im| - 1)]
      have h2 : (2:ℝ) ≤ expR 1 := by linarith [add_one_le_exp (1:ℝ)]
      calc π * |z.im| / 2 = (π / 2) * |z.im| := by ring
        _ ≤ 2 * |z.im| := by nlinarith [Real.pi_lt_four]
        _ ≤ expR 1 * |z.im| := by nlinarith
        _ ≤ expR 1 * expR (|z.im| - 1) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos _))
        _ = expR (1 + (|z.im| - 1)) := (Real.exp_add 1 (|z.im| - 1)).symm
        _ = expR |z.im| := by ring_nf
    -- Final =O bound
    simp only [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc ‖stirling_ratio z‖
        ≤ M_Γ * expR b * expR (π * |z.im| / 2) := h_ratio
      _ ≤ M_Γ * expR b * expR (expR |z.im|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h_exp_bound)
            (mul_nonneg hM_nn (le_of_lt (Real.exp_pos _)))
      _ = (M_Γ * expR b) * expR (expR |z.im|) := by ring

/-- The Stirling ratio is bounded on each half-integer strip [1/2+k, 1/2+k+1]. -/
theorem stirling_ratio_bounded_on_strip (k : ℤ) (hk : 0 < 1/2 + (k : ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, 1/2 + k ≤ z.re → z.re ≤ 1/2 + k + 1 →
      1 ≤ |z.im| → ‖stirling_ratio z‖ ≤ B := by
  -- Boundary bounds for all t
  have hk1 : 0 < 1/2 + ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
  obtain ⟨C_L, hCL_pos, hC_left⟩ := boundary_bound_all (1/2 + (k:ℝ)) hk k rfl hk
  obtain ⟨C_R, hCR_pos, hC_right⟩ := boundary_bound_all (1/2 + (k:ℝ) + 1) (by linarith) (k+1)
    (by push_cast; ring) hk1
  set C := max C_L C_R
  have hC_pos : 0 < C := lt_max_of_lt_left hCL_pos
  -- DiffContOnCl on the strip
  have h_diff : DiffContOnCl ℂ stirling_ratio (re ⁻¹' Ioo (1/2 + (k:ℝ)) (1/2 + (k:ℝ) + 1)) := by
    have := stirling_ratio_diff_cont k hk
    convert this using 2
  -- Growth condition
  have h_growth := growth_condition k hk
  -- Apply Phragmén-Lindelöf
  refine ⟨C, hC_pos, fun z hz₁ hz₂ _ => ?_⟩
  exact PhragmenLindelof.vertical_strip h_diff h_growth
    (fun w hw => le_trans (hC_left w hw) (le_max_left C_L C_R))
    (fun w hw => le_trans (hC_right w hw) (le_max_right C_L C_R))
    hz₁ hz₂

end Aristotle.Bridge.StirlingRatioPL

end
