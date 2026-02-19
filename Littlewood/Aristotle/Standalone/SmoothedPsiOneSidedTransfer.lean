import Mathlib
import Littlewood.Basic.ChebyshevFunctions
import Littlewood.Basic.LogarithmicIntegral

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.SmoothedPsiOneSidedTransfer

open Filter

/-- Smoothed `ψ-x` error after the change of variables `x = exp u`. -/
def smoothedPsiError (u : ℝ) : ℝ :=
  (chebyshevPsi (Real.exp u) - Real.exp u) / Real.exp u

private lemma sqrt_exp_div_exp (u : ℝ) :
    Real.sqrt (Real.exp u) / Real.exp u = Real.exp (-u / 2) := by
  have hpos : 0 < Real.exp u := Real.exp_pos u
  have hinv : (Real.exp u)⁻¹ = Real.exp u ^ (-1 : ℝ) := by
    have hneg := Real.rpow_neg (le_of_lt hpos) (1 : ℝ)
    simpa using hneg.symm
  calc
    Real.sqrt (Real.exp u) / Real.exp u
        = (Real.exp u) ^ (1 / 2 : ℝ) * (Real.exp u) ^ (-1 : ℝ) := by
            rw [Real.sqrt_eq_rpow, div_eq_mul_inv, hinv]
    _ = (Real.exp u) ^ ((1 / 2 : ℝ) + (-1 : ℝ)) := by
            rw [← Real.rpow_add hpos]
    _ = (Real.exp u) ^ (-(1 / 2 : ℝ)) := by ring_nf
    _ = Real.exp (u * (-(1 / 2 : ℝ))) := by
            rw [← Real.exp_mul]
    _ = Real.exp (-u / 2) := by ring_nf

/--
Transfer one-sided `o(√x)`-style control to the smoothed variable.

If `σ * (ψ(x)-x) < c * √x` eventually for every `c > 0`, then after `x = exp u`:
`σ * smoothedPsiError(u) < c * exp(-u/2)` eventually for every `c > 0`.
-/
theorem smoothed_psi_eventually_lt_exp_half_scale
    (σ : ℝ)
    (h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) < c * Real.sqrt x) :
    ∀ c : ℝ, c > 0 →
      ∀ᶠ u in atTop, σ * smoothedPsiError u < c * Real.exp (-u / 2) := by
  intro c hc
  have hx : ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) < c * Real.sqrt x :=
    h_side c hc
  have hu : ∀ᶠ u in atTop,
      σ * (chebyshevPsi (Real.exp u) - Real.exp u) < c * Real.sqrt (Real.exp u) :=
    Real.tendsto_exp_atTop.eventually hx
  refine hu.mono ?_
  intro u huu
  have hpos : 0 < Real.exp u := Real.exp_pos u
  have hdiv :
      (σ * (chebyshevPsi (Real.exp u) - Real.exp u)) / Real.exp u
        < (c * Real.sqrt (Real.exp u)) / Real.exp u := by
    rw [div_lt_iff₀ hpos]
    field_simp [ne_of_gt hpos]
    exact huu
  have hleft :
      σ * smoothedPsiError u
        = (σ * (chebyshevPsi (Real.exp u) - Real.exp u)) / Real.exp u := by
    unfold smoothedPsiError
    ring
  calc
    σ * smoothedPsiError u
        = (σ * (chebyshevPsi (Real.exp u) - Real.exp u)) / Real.exp u := hleft
    _ < (c * Real.sqrt (Real.exp u)) / Real.exp u := hdiv
    _ = c * Real.exp (-u / 2) := by
          rw [mul_div_assoc, sqrt_exp_div_exp]

/-- `≤`-version of `smoothed_psi_eventually_lt_exp_half_scale`. -/
theorem smoothed_psi_eventually_le_exp_half_scale
    (σ : ℝ)
    (h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) < c * Real.sqrt x) :
    ∀ c : ℝ, c > 0 →
      ∀ᶠ u in atTop, σ * smoothedPsiError u ≤ c * Real.exp (-u / 2) := by
  intro c hc
  exact (smoothed_psi_eventually_lt_exp_half_scale σ h_side c hc).mono
    (fun _ h => le_of_lt h)

/-- Positive-part version of `smoothed_psi_eventually_le_exp_half_scale`. -/
theorem smoothed_psi_positivePart_eventually_le_exp_half_scale
    (σ : ℝ)
    (h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) < c * Real.sqrt x) :
    ∀ c : ℝ, c > 0 →
      ∀ᶠ u in atTop, max (σ * smoothedPsiError u) 0 ≤ c * Real.exp (-u / 2) := by
  intro c hc
  exact (smoothed_psi_eventually_lt_exp_half_scale σ h_side c hc).mono
    (fun u hu =>
      (max_le_iff.mpr ⟨le_of_lt hu, by
        have hnonneg : 0 ≤ c * Real.exp (-u / 2) := by
          exact mul_nonneg (le_of_lt hc) (le_of_lt (Real.exp_pos _))
        exact hnonneg⟩))

/-- `π-li` error function in real-variable form. -/
def piLiError (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) - LogarithmicIntegral.logarithmicIntegral x

/-- Smoothed `π-li` error after the change of variables `x = exp u`. -/
def smoothedPiLiError (u : ℝ) : ℝ :=
  piLiError (Real.exp u) * (u / Real.exp (u / 2))

/--
Transfer one-sided `o(√x / log x)`-style control to the smoothed `π-li` variable.

If `σ * (π(x)-li(x)) < c * √x / log x` eventually for every `c > 0`, then after
`x = exp u`:
`σ * smoothedPiLiError(u) < c` eventually for every `c > 0`.
-/
theorem smoothed_pi_li_eventually_lt_const
    (σ : ℝ)
    (h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * piLiError x < c * (Real.sqrt x / Real.log x)) :
    ∀ c : ℝ, c > 0 →
      ∀ᶠ u in atTop, σ * smoothedPiLiError u < c := by
  intro c hc
  have hx : ∀ᶠ x in atTop, σ * piLiError x < c * (Real.sqrt x / Real.log x) :=
    h_side c hc
  have hu_base : ∀ᶠ u in atTop,
      σ * piLiError (Real.exp u)
        < c * (Real.sqrt (Real.exp u) / Real.log (Real.exp u)) :=
    Real.tendsto_exp_atTop.eventually hx
  have hu_ge_one : ∀ᶠ u in atTop, (1 : ℝ) ≤ u :=
    Filter.eventually_atTop.mpr ⟨1, fun u hu => hu⟩
  filter_upwards [hu_base, hu_ge_one] with u hbase hu1
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hfac_pos : 0 < u / Real.exp (u / 2) := by
    exact div_pos hu_pos (Real.exp_pos _)
  have hmul :
      (σ * piLiError (Real.exp u)) * (u / Real.exp (u / 2))
        < (c * (Real.sqrt (Real.exp u) / Real.log (Real.exp u))) * (u / Real.exp (u / 2)) :=
    mul_lt_mul_of_pos_right hbase hfac_pos
  have hleft :
      σ * smoothedPiLiError u
        = (σ * piLiError (Real.exp u)) * (u / Real.exp (u / 2)) := by
    unfold smoothedPiLiError
    ring
  have hright :
      (c * (Real.sqrt (Real.exp u) / Real.log (Real.exp u))) * (u / Real.exp (u / 2)) = c := by
    have hu0 : u ≠ 0 := ne_of_gt hu_pos
    rw [Real.log_exp, Real.sqrt_eq_rpow, ← Real.exp_mul]
    ring_nf
    field_simp [hu0, Real.exp_ne_zero]
  calc
    σ * smoothedPiLiError u
        = (σ * piLiError (Real.exp u)) * (u / Real.exp (u / 2)) := hleft
    _ < (c * (Real.sqrt (Real.exp u) / Real.log (Real.exp u))) * (u / Real.exp (u / 2)) := hmul
    _ = c := hright

/-- `≤`-version of `smoothed_pi_li_eventually_lt_const`. -/
theorem smoothed_pi_li_eventually_le_const
    (σ : ℝ)
    (h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * piLiError x < c * (Real.sqrt x / Real.log x)) :
    ∀ c : ℝ, c > 0 →
      ∀ᶠ u in atTop, σ * smoothedPiLiError u ≤ c := by
  intro c hc
  exact (smoothed_pi_li_eventually_lt_const σ h_side c hc).mono
    (fun _ h => le_of_lt h)

/-- Positive-part version of `smoothed_pi_li_eventually_le_const`. -/
theorem smoothed_pi_li_positivePart_eventually_le_const
    (σ : ℝ)
    (h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * piLiError x < c * (Real.sqrt x / Real.log x)) :
    ∀ c : ℝ, c > 0 →
      ∀ᶠ u in atTop, max (σ * smoothedPiLiError u) 0 ≤ c := by
  intro c hc
  exact (smoothed_pi_li_eventually_lt_const σ h_side c hc).mono
    (fun _ hu => (max_le_iff.mpr ⟨le_of_lt hu, le_of_lt hc⟩))

end Aristotle.Standalone.SmoothedPsiOneSidedTransfer
