/-
Landau's abscissa of convergence theorem: proves `LandauAbscissaHyp`.

For g(t) = C·t^α + σ·(t - ψ(t)) ≥ 0 (eventually), the Dirichlet integral
∫₁^∞ g(t)·t^{-(s+1)} dt converges absolutely for Re(s) > α.

SORRY COUNT: 0 (parameterized on RealIntegrabilityHyp section variable)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.PringsheimPsiAtom
import Littlewood.Aristotle.PringsheimTheorem
import Littlewood.Aristotle.ZetaPoleCancellation

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.LandauAbscissaConvergence

open Complex Real Filter Topology MeasureTheory Set

/-! ## Norm identity -/

/-- ‖↑(g) * (↑t)^{-(s+1)}‖ = |g| * t^{-(Re(s)+1)} for t > 0. -/
private theorem norm_complex_le_abs_real {g_val : ℝ} {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ‖(↑g_val : ℂ) * (↑t : ℂ) ^ (-(s + 1))‖ =
    |g_val| * t ^ (-(s.re + 1)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp only [neg_re, add_re, one_re]

/-! ## Complex integrability from real integrability -/

/-- Complex integrability follows from real integrability via norm comparison. -/
private theorem complex_integrableOn_of_real
    (C α σ_sign : ℝ) (s : ℂ)
    (h_real : IntegrableOn
      (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(s.re + 1)))
      (Ioi 1)) :
    IntegrableOn
      (fun t => (↑(PringsheimPsiAtom.genFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
  rw [IntegrableOn] at h_real ⊢
  -- Measurability: product of measurable functions on Ioi 1
  have h_meas : AEStronglyMeasurable
      (fun t => (↑(PringsheimPsiAtom.genFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      (volume.restrict (Ioi (1 : ℝ))) := by
    apply AEStronglyMeasurable.mul
    · have hm : Measurable (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t) := by
        unfold PringsheimPsiAtom.genFun
        exact (measurable_id.pow_const α |>.const_mul C).add
          ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign)
      exact (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable.restrict
    · exact (ContinuousOn.aestronglyMeasurable (fun t ht =>
        (continuousAt_ofReal_cpow_const t (-(s + 1))
          (Or.inr (ne_of_gt (lt_trans zero_lt_one (mem_Ioi.mp ht))))).continuousWithinAt)
        measurableSet_Ioi)
  -- Norm comparison: ‖complex‖ ≤ ‖real‖ a.e. on Ioi 1
  exact Integrable.mono h_real h_meas (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : (0 : ℝ) < t := lt_trans zero_lt_one (mem_Ioi.mp ht)
    rw [norm_complex_le_abs_real ht_pos s, Real.norm_eq_abs, abs_mul,
      abs_of_pos (rpow_pos_of_pos ht_pos _)])

/-! ## Real integrability for σ > 1 -/

/-- The real Dirichlet integral converges for σ > 1 (from g = O(t)). -/
private theorem real_integrableOn_gt_one
    (C : ℝ) (hC : 0 < C) (α : ℝ) (_hα : 1 / 2 < α) (hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (σ₀ : ℝ) (hσ₀ : 1 < σ₀) :
    IntegrableOn (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioi 1) := by
  -- Use genFun_le_linear: |g(t)| ≤ D*t for t ≥ 1
  obtain ⟨D, hD, hle⟩ := PringsheimPsiAtom.genFun_le_linear C hC α hα1 σ_sign hσ
  -- Dominate by D * t^{-σ₀} which is integrable for σ₀ > 1
  have h_bound : IntegrableOn (fun t : ℝ => D * t ^ (-σ₀)) (Ioi 1) := by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith : -σ₀ < -1)
      (by norm_num : (0:ℝ) < 1)).const_mul D
  apply h_bound.mono'
  · exact ((measurable_id.pow_const α |>.const_mul C).add
      ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign) |>.mul
        (measurable_id.pow_const (-(σ₀ + 1)))).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    have ht1 : 1 ≤ t := by linarith
    have ht_pos : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos ht_pos _)]
    calc |PringsheimPsiAtom.genFun C α σ_sign t| * t ^ (-(σ₀ + 1))
        ≤ D * t * t ^ (-(σ₀ + 1)) := by
          exact mul_le_mul_of_nonneg_right (hle t ht1) (rpow_nonneg (by linarith) _)
      _ = D * (t ^ (1 : ℝ) * t ^ (-(σ₀ + 1))) := by
          rw [rpow_one]; ring
      _ = D * t ^ (1 + (-(σ₀ + 1))) := by
          rw [← rpow_add ht_pos]
      _ = D * t ^ (-σ₀) := by ring_nf

/-! ## Real integrability for α < σ ≤ 1 via Pringsheim

This is the heart of the proof. The power series expansion of the Dirichlet
integral around σ₁ > 1 has non-negative Taylor coefficients. The corrected
formula (ZetaPoleCancellation) provides an analytic continuation past σ = 1.
Pringsheim's theorem forces the radius of convergence ≥ σ₁ - α.

The hard case is parameterized as `RealIntegrabilityHyp` and supplied as sorry
by `DeepSorries.combined_atoms`. -/

/-- The hard real integrability hypothesis: the Dirichlet integral of the generating
function converges for α < σ₀ ≤ 1. This is Landau's Satz 15 (1905). -/
def RealIntegrabilityHyp : Prop :=
  ∀ (C : ℝ), 0 < C → ∀ (α : ℝ), 1 / 2 < α →
  ∀ (σ_sign : ℝ), σ_sign = 1 ∨ σ_sign = -1 →
  (∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α) →
  ∀ (σ₀ : ℝ), α < σ₀ → σ₀ ≤ 1 →
  IntegrableOn (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
    (Ioi 1)

/-! ## Main theorem -/

/-- **Landau's abscissa of convergence theorem** (`LandauAbscissaHyp`).
Parameterized on `RealIntegrabilityHyp` (the Pringsheim argument for α < σ ≤ 1). -/
theorem landau_abscissa_hyp (h_hard : RealIntegrabilityHyp) :
    PringsheimPsiAtom.LandauAbscissaHyp := by
  intro C hC α hα σ_sign hσ hbound s hs hs1
  apply complex_integrableOn_of_real
  by_cases hα1 : α ≤ 1
  · exact h_hard C hC α hα σ_sign hσ hbound s.re hs hs1
  · push_neg at hα1
    exact real_integrableOn_gt_one C hC α hα (by linarith) σ_sign hσ s.re (by linarith)

end Aristotle.LandauAbscissaConvergence
