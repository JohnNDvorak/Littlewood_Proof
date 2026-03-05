import Littlewood.Aristotle.ZetaMeanSquare
import Littlewood.Aristotle.MeanSquare

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra

open Filter Asymptotics MeasureTheory Set Real

/-- Critical-line zeta mean-square integrand. -/
def zetaMsIntegrand (t : ℝ) : ℝ :=
  ‖riemannZeta (↑(1 / 2 : ℝ) + Complex.I * ↑t)‖ ^ 2

/-- Partial-zeta mean-square integrand. -/
def partialMsIntegrand (t : ℝ) : ℝ :=
  Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1 / 2 + Complex.I * t))

/-- Signed AFE mean-square gap integrand:
`|ζ(1/2+it)|² - 2|S_N(1/2+it)|²`. -/
def afeGapIntegrand (t : ℝ) : ℝ :=
  zetaMsIntegrand t - 2 * partialMsIntegrand t

/-- Continuity of the critical-line zeta mean-square integrand. -/
lemma continuous_zetaMsIntegrand : Continuous zetaMsIntegrand := by
  have h_ne_one : ∀ t : ℝ, ↑(1 / 2 : ℝ) + Complex.I * ↑t ≠ (1 : ℂ) := by
    intro t h
    have h_re := congr_arg Complex.re h
    simp at h_re
  have h_cont : Continuous (fun t : ℝ => riemannZeta (↑(1 / 2 : ℝ) + Complex.I * ↑t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp
      (g := riemannZeta)
      (f := fun t : ℝ => (↑(1 / 2 : ℝ) : ℂ) + Complex.I * (↑t : ℂ))
      (differentiableAt_riemannZeta (h_ne_one t)).continuousAt
      (by fun_prop)
  unfold zetaMsIntegrand
  exact h_cont.norm.pow 2

lemma intervalIntegrable_zetaMsIntegrand (T : ℝ) :
    IntervalIntegrable zetaMsIntegrand volume 1 T := by
  exact continuous_zetaMsIntegrand.intervalIntegrable (a := 1) (b := T)

lemma intervalIntegrable_zetaMsIntegrand_any (a b : ℝ) :
    IntervalIntegrable zetaMsIntegrand volume a b := by
  exact continuous_zetaMsIntegrand.intervalIntegrable (a := a) (b := b)

lemma intervalIntegrable_partialMsIntegrand (T : ℝ) :
    IntervalIntegrable partialMsIntegrand volume 1 T := by
  have h_eq : partialMsIntegrand =
      (fun t => (∑ n ∈ Finset.Icc 1 (N_t t), (1 : ℝ) / n) + (offDiagSsq t).re) := by
    funext t
    unfold partialMsIntegrand
    exact normSq_partialZeta_eq t
  rw [h_eq]
  have h_diag : IntervalIntegrable
      (fun t => ∑ n ∈ Finset.Icc 1 (N_t t), (1 : ℝ) / n) volume 1 T := by
    have h_diag_sum : IntervalIntegrable
        (fun t => ∑ n ∈ Finset.Icc 1 (N_t t), (1 : ℝ) / n) volume 1 T := by
      apply MonotoneOn.intervalIntegrable
      intro t _ u _ htu
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (Nat.floor_mono (Real.sqrt_le_sqrt
          (div_le_div_of_nonneg_right htu (by positivity)))))
        (fun _ _ _ => by positivity)
    exact h_diag_sum
  have h_offdiag : IntervalIntegrable (fun t => (offDiagSsq t).re) volume 1 T := by
    exact
      ⟨Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).1,
       Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).2⟩
  exact h_diag.add h_offdiag

theorem signed_remainder_isBigO_of_abs_remainder_isBigO
    (h_abs :
      (fun T => ∫ t in (1 : ℝ)..T, ‖afeGapIntegrand t‖) =O[atTop] (fun T => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t) =O[atTop] (fun T => T) := by
  refine IsBigO.trans ?_ h_abs
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  simp only [one_mul]
  have h_nonneg : 0 ≤ ∫ t in (1 : ℝ)..T, ‖afeGapIntegrand t‖ :=
    intervalIntegral.integral_nonneg_of_forall hT (fun t => norm_nonneg _)
  calc
    ‖∫ t in (1 : ℝ)..T, afeGapIntegrand t‖
        ≤ ∫ t in (1 : ℝ)..T, ‖afeGapIntegrand t‖ := by
          exact intervalIntegral.norm_integral_le_integral_norm
            (f := afeGapIntegrand) hT
    _ = ‖∫ t in (1 : ℝ)..T, ‖afeGapIntegrand t‖‖ := by
      symm
      exact Real.norm_of_nonneg h_nonneg

theorem mean_square_bridge_of_signed_remainder
    (h_signed :
      (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t) =O[atTop] (fun T => T)) :
    (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) -
      2 * (∫ t in (1 : ℝ)..T, partialMsIntegrand t))
    =O[atTop] (fun T => T) := by
  obtain ⟨C, hC_nonneg, hC⟩ := h_signed.exists_nonneg
  rw [IsBigOWith] at hC
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with T hT
  have hz : IntervalIntegrable zetaMsIntegrand volume 1 T :=
    intervalIntegrable_zetaMsIntegrand T
  have hp : IntervalIntegrable partialMsIntegrand volume 1 T :=
    intervalIntegrable_partialMsIntegrand T
  have h_eq :
      (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) -
          2 * (∫ t in (1 : ℝ)..T, partialMsIntegrand t) =
        ∫ t in (1 : ℝ)..T, afeGapIntegrand t := by
    unfold afeGapIntegrand
    rw [← intervalIntegral.integral_const_mul 2]
    rw [← intervalIntegral.integral_sub hz (hp.const_mul 2)]
  rw [h_eq]
  exact hT

end Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
