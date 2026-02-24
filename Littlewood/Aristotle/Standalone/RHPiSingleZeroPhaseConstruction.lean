import Littlewood.Aristotle.Standalone.RHPiTargetPhaseArgReduction

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiSingleZeroPhaseConstruction

open Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiTargetPhaseArgReduction

private theorem exists_large_x_log_arg_exact_of_pos
    {γ φ X : ℝ} (hγ : 0 < γ) :
    ∃ x : ℝ, X < x ∧ 1 < x ∧ ∃ k : ℤ,
      Real.log x * γ - φ - k • (2 * Real.pi) = 0 := by
  let L : ℝ := Real.log (max X 1)
  let B : ℝ := max ((γ * L - φ) / (2 * Real.pi)) ((-φ) / (2 * Real.pi))
  obtain ⟨k, hk⟩ := exists_int_gt B
  let t : ℝ := (φ + (k : ℝ) * (2 * Real.pi)) / γ
  let x : ℝ := Real.exp t
  have hboundL : (γ * L - φ) / (2 * Real.pi) < (k : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hk
  have hbound0 : (-φ) / (2 * Real.pi) < (k : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hk
  have htwoPiPos : 0 < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have htmpL : γ * L - φ < (k : ℝ) * (2 * Real.pi) := by
    exact (div_lt_iff₀ htwoPiPos).1 hboundL
  have htmp0 : -φ < (k : ℝ) * (2 * Real.pi) := by
    exact (div_lt_iff₀ htwoPiPos).1 hbound0
  have hnumL : γ * L < φ + (k : ℝ) * (2 * Real.pi) := by
    linarith
  have hnum0 : 0 < φ + (k : ℝ) * (2 * Real.pi) := by
    linarith
  have htL : L < t := by
    dsimp [t]
    exact (lt_div_iff₀ hγ).2 (by simpa [mul_comm] using hnumL)
  have ht0 : 0 < t := by
    dsimp [t]
    exact div_pos hnum0 hγ
  have hmaxPos : 0 < max X 1 := lt_of_lt_of_le zero_lt_one (le_max_right X 1)
  have hmaxx : max X 1 < x := by
    dsimp [x, L] at *
    exact (Real.log_lt_iff_lt_exp hmaxPos).1 htL
  have hXx : X < x := lt_of_le_of_lt (le_max_left X 1) hmaxx
  have hx1 : 1 < x := lt_of_le_of_lt (le_max_right X 1) hmaxx
  refine ⟨x, hXx, hx1, k, ?_⟩
  have hcalc :
      ((φ + (k : ℝ) * (2 * Real.pi)) / γ) * γ - φ - (k : ℝ) * (2 * Real.pi) = 0 := by
    have hγne : γ ≠ 0 := hγ.ne'
    calc
      ((φ + (k : ℝ) * (2 * Real.pi)) / γ) * γ - φ - (k : ℝ) * (2 * Real.pi)
          = (φ + (k : ℝ) * (2 * Real.pi)) * γ / γ - φ - (k : ℝ) * (2 * Real.pi) := by
              ring
      _ = (φ + (k : ℝ) * (2 * Real.pi)) - φ - (k : ℝ) * (2 * Real.pi) := by
            simp [hγne]
      _ = 0 := by ring
  simpa [x, t, smul_eq_mul] using hcalc

private theorem exists_large_x_log_arg_exact_of_neg
    {γ φ X : ℝ} (hγ : γ < 0) :
    ∃ x : ℝ, X < x ∧ 1 < x ∧ ∃ k : ℤ,
      Real.log x * γ - φ - k • (2 * Real.pi) = 0 := by
  let L : ℝ := Real.log (max X 1)
  let B : ℝ := min ((γ * L - φ) / (2 * Real.pi)) ((-φ) / (2 * Real.pi))
  obtain ⟨k, hk⟩ := exists_int_lt B
  let t : ℝ := (φ + (k : ℝ) * (2 * Real.pi)) / γ
  let x : ℝ := Real.exp t
  have hboundL : (k : ℝ) < (γ * L - φ) / (2 * Real.pi) :=
    lt_of_lt_of_le hk (min_le_left _ _)
  have hbound0 : (k : ℝ) < (-φ) / (2 * Real.pi) :=
    lt_of_lt_of_le hk (min_le_right _ _)
  have htwoPiPos : 0 < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have htmpL : (k : ℝ) * (2 * Real.pi) < γ * L - φ := by
    exact (lt_div_iff₀ htwoPiPos).1 hboundL
  have htmp0 : (k : ℝ) * (2 * Real.pi) < -φ := by
    exact (lt_div_iff₀ htwoPiPos).1 hbound0
  have hnumL : φ + (k : ℝ) * (2 * Real.pi) < γ * L := by
    linarith
  have hnum0 : φ + (k : ℝ) * (2 * Real.pi) < 0 := by
    linarith
  have htL : L < t := by
    dsimp [t]
    exact (lt_div_iff_of_neg hγ).2 (by simpa [mul_comm] using hnumL)
  have ht0 : 0 < t := by
    dsimp [t]
    exact div_pos_of_neg_of_neg hnum0 hγ
  have hmaxPos : 0 < max X 1 := lt_of_lt_of_le zero_lt_one (le_max_right X 1)
  have hmaxx : max X 1 < x := by
    dsimp [x, L] at *
    exact (Real.log_lt_iff_lt_exp hmaxPos).1 htL
  have hXx : X < x := lt_of_le_of_lt (le_max_left X 1) hmaxx
  have hx1 : 1 < x := lt_of_le_of_lt (le_max_right X 1) hmaxx
  refine ⟨x, hXx, hx1, k, ?_⟩
  have hcalc :
      ((φ + (k : ℝ) * (2 * Real.pi)) / γ) * γ - φ - (k : ℝ) * (2 * Real.pi) = 0 := by
    have hγne : γ ≠ 0 := ne_of_lt hγ
    calc
      ((φ + (k : ℝ) * (2 * Real.pi)) / γ) * γ - φ - (k : ℝ) * (2 * Real.pi)
          = (φ + (k : ℝ) * (2 * Real.pi)) * γ / γ - φ - (k : ℝ) * (2 * Real.pi) := by
              ring
      _ = (φ + (k : ℝ) * (2 * Real.pi)) - φ - (k : ℝ) * (2 * Real.pi) := by
            simp [hγne]
      _ = 0 := by ring
  simpa [x, t, smul_eq_mul] using hcalc

/-- For nonzero frequency `γ`, one can hit the target phase `φ` exactly modulo
`2π` at arbitrarily large `x`. -/
theorem exists_large_x_log_arg_exact
    {γ φ X : ℝ} (hγ : γ ≠ 0) :
    ∃ x : ℝ, X < x ∧ 1 < x ∧ ∃ k : ℤ,
      Real.log x * γ - φ - k • (2 * Real.pi) = 0 := by
  rcases lt_or_gt_of_ne hγ with hneg | hpos
  · exact exists_large_x_log_arg_exact_of_neg hneg
  · exact exists_large_x_log_arg_exact_of_pos hpos

/-- Target-argument approximation for one frequency with arbitrarily small
error and arbitrarily large `x`. -/
theorem exists_large_x_log_arg_target_single
    {ρ : ℂ} (hρ_im_ne : ρ.im ≠ 0)
    {ε X : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, X < x ∧ 1 < x ∧ ∃ k : ℤ,
      ‖Real.log x * ρ.im - Complex.arg ρ - k • (2 * Real.pi)‖ ≤ ε := by
  rcases exists_large_x_log_arg_exact (γ := ρ.im) (φ := Complex.arg ρ) (X := X) hρ_im_ne with
    ⟨x, hXx, hx1, k, hk⟩
  refine ⟨x, hXx, hx1, k, ?_⟩
  rw [hk, norm_zero]
  exact le_of_lt hε

/-- Anti-target-argument approximation for one frequency with arbitrarily
small error and arbitrarily large `x`. -/
theorem exists_large_x_log_arg_antitarget_single
    {ρ : ℂ} (hρ_im_ne : ρ.im ≠ 0)
    {ε X : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, X < x ∧ 1 < x ∧ ∃ k : ℤ,
      ‖Real.log x * ρ.im - (Complex.arg ρ + Real.pi) - k • (2 * Real.pi)‖ ≤ ε := by
  rcases exists_large_x_log_arg_exact
      (γ := ρ.im) (φ := Complex.arg ρ + Real.pi) (X := X) hρ_im_ne with
    ⟨x, hXx, hx1, k, hk⟩
  refine ⟨x, hXx, hx1, k, ?_⟩
  rw [hk, norm_zero]
  exact le_of_lt hε

/-- Target-phase closeness for one zero from an explicit large-`x` argument
construction. -/
theorem exists_large_x_phase_target_single
    {ρ : ℂ} (hρ_im_ne : ρ.im ≠ 0)
    {ε X : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, X < x ∧ 1 < x ∧
      ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε := by
  rcases exists_large_x_log_arg_target_single (ρ := ρ) hρ_im_ne (ε := ε) (X := X) hε with
    ⟨x, hXx, hx1, k, hk⟩
  have hρne : ρ ≠ 0 := by
    intro h0
    apply hρ_im_ne
    simpa [h0]
  have hphase :
      ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε :=
    target_phase_close_of_log_arg_approx (lt_trans zero_lt_one hx1) hρne hk
  exact ⟨x, hXx, hx1, hphase⟩

/-- Anti-target-phase closeness for one zero from an explicit large-`x`
argument construction. -/
theorem exists_large_x_phase_antitarget_single
    {ρ : ℂ} (hρ_im_ne : ρ.im ≠ 0)
    {ε X : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, X < x ∧ 1 < x ∧
      ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε := by
  rcases exists_large_x_log_arg_antitarget_single (ρ := ρ) hρ_im_ne (ε := ε) (X := X) hε with
    ⟨x, hXx, hx1, k, hk⟩
  have hρne : ρ ≠ 0 := by
    intro h0
    apply hρ_im_ne
    simpa [h0]
  have hphase :
      ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε :=
    antitarget_phase_close_of_log_arg_approx (lt_trans zero_lt_one hx1) hρne hk
  exact ⟨x, hXx, hx1, hphase⟩

end Aristotle.Standalone.RHPiSingleZeroPhaseConstruction
