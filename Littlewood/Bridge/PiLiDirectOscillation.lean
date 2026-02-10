/-
Bridge: Extract π(x) - li(x) = Ω±(√x / log x) from critical-line zeros
using a truncated explicit formula input tailored to π.

This bridge isolates the oscillation-extraction argument (phase alignment +
anti-alignment) from the analytic Perron-contour work needed to produce the
truncated π explicit formula itself.

Dependencies:
- `HardyCriticalLineZerosHyp`
- `TruncatedExplicitFormulaPiHyp`

Output:
- `PiLiOscillationSqrtHyp`
-/

import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.Aristotle.DirichletPhaseAlignment

noncomputable section

open Schmidt Asymptotics
open Filter ZetaZeros
open scoped BigOperators

namespace PiLiDirectOscillationBridge

private def piLiError (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x

/-- Input hypothesis for extracting π-li oscillation from critical-line zeros. -/
class TruncatedExplicitFormulaPiHyp : Prop where
  /-- Truncated explicit formula for `π(x) - li(x)` at `√x/log x` scale. -/
  pi_approx :
    ∀ (S : Finset ℂ),
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop,
        |piLiError x + ((∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ).re) / Real.log x|
          ≤ ε * (Real.sqrt x / Real.log x)

  /-- Anti-alignment for singleton critical-line zeros, scaled by `1/log x`. -/
  zero_sum_neg_frequently :
    ∀ (ρ₀ : ℂ), ρ₀ ∈ zetaNontrivialZeros →
      ρ₀.re = 1 / 2 → ρ₀.im ≠ 0 →
      ∃ c > 0, ∀ X : ℝ, ∃ x > X,
        1 < x ∧
          ((∑ ρ ∈ ({ρ₀} : Finset ℂ), ((x : ℂ) ^ ρ / ρ)).re) / Real.log x
            ≤ -(c * (Real.sqrt x / Real.log x))

/-- Ω₋ direction for `π(x) - li(x)` from aligned phases. -/
private theorem omega_minus_from_zeros
    [TruncatedExplicitFormulaPiHyp]
    (h_zeros : Set.Infinite {ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2}) :
    IsOmegaMinus (fun x => piLiError x) (fun x => Real.sqrt x / Real.log x) := by
  obtain ⟨ρ₀, hρ₀_mem, hρ₀_re⟩ := h_zeros.nonempty

  have hρ₀_re_pos : (0 : ℝ) < ρ₀.re := by rw [hρ₀_re]; norm_num
  have hρ₀_ne : ρ₀ ≠ 0 := by
    intro h
    simp [h] at hρ₀_re_pos

  have h_re_inv_pos : 0 < (1 / ρ₀).re := by
    simp only [one_div]
    rw [Complex.inv_re]
    exact div_pos hρ₀_re_pos (Complex.normSq_pos.mpr hρ₀_ne)

  set c₀ := (1 / ρ₀).re with hc₀_def

  have hS_re : ∀ ρ ∈ ({ρ₀} : Finset ℂ), ρ.re = 1 / 2 := by
    intro ρ hρ
    simp only [Finset.mem_singleton] at hρ
    subst hρ
    exact hρ₀_re

  have hS_in : ∀ ρ ∈ ({ρ₀} : Finset ℂ), ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    simp only [Finset.mem_singleton] at hρ
    subst hρ
    exact ⟨hρ₀_mem, hρ₀_re⟩

  have hρ₀_norm_pos : (0 : ℝ) < ‖ρ₀‖ := norm_pos_iff.mpr hρ₀_ne
  set ε_a := c₀ * ‖ρ₀‖ / 2 with hε_a_def
  have hε_a_pos : (0 : ℝ) < ε_a := by positivity

  have h_ef :=
    TruncatedExplicitFormulaPiHyp.pi_approx {ρ₀} hS_in (c₀ / 4) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp h_ef

  refine ⟨c₀ / 4, by positivity, ?_⟩
  rw [Filter.frequently_atTop]
  intro a

  obtain ⟨x, hx_gt, hx_align⟩ :=
    Aristotle.DirichletPhaseAlignment.exists_large_x_phases_aligned_finset
      {ρ₀} hS_re ε_a hε_a_pos (max (max a x₀) 2)

  have hx_pos : (0 : ℝ) < x := by linarith [le_max_right (max a x₀) (2 : ℝ)]
  have hx_gt_two : (2 : ℝ) < x := by
    exact lt_of_le_of_lt (le_max_right (max a x₀) (2 : ℝ)) hx_gt
  have hx_ge_a : a ≤ x := by
    linarith [le_max_left a x₀, le_max_left (max a x₀) (2 : ℝ)]
  have hx_ge_x₀ : x₀ ≤ x := by
    linarith [le_max_right a x₀, le_max_left (max a x₀) (2 : ℝ)]

  have h_bound :=
    Aristotle.DirichletPhaseAlignment.bound_real_part_of_sum_aligned
      hS_re hx_pos hε_a_pos hx_align

  have h_ef_x := hx₀ x hx_ge_x₀
  simp only [Finset.sum_singleton] at h_bound h_ef_x

  have h_upper := (abs_le.mp h_ef_x).2

  have h_eps_cancel : ε_a * (1 / ‖ρ₀‖) = c₀ / 2 := by
    rw [hε_a_def]
    field_simp

  have h_re_lower : ((x : ℂ) ^ ρ₀ / ρ₀).re ≥ Real.sqrt x * (c₀ / 2) := by
    calc
      ((x : ℂ) ^ ρ₀ / ρ₀).re
          ≥ Real.sqrt x * ((1 / ρ₀).re - ε_a * (1 / ‖ρ₀‖)) := h_bound
      _ = Real.sqrt x * (c₀ / 2) := by
          rw [← hc₀_def, h_eps_cancel]
          ring

  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)

  have h_re_lower_scaled :
      (c₀ / 2) * (Real.sqrt x / Real.log x)
        ≤ (((x : ℂ) ^ ρ₀ / ρ₀).re) / Real.log x := by
    have htmp :
        (Real.sqrt x * (c₀ / 2)) / Real.log x
          ≤ (((x : ℂ) ^ ρ₀ / ρ₀).re) / Real.log x := by
      rw [div_le_div_iff₀ hlog_pos hlog_pos]
      nlinarith [h_re_lower]
    have hrewrite :
        (c₀ / 2) * (Real.sqrt x / Real.log x)
          = (Real.sqrt x * (c₀ / 2)) / Real.log x := by ring
    simpa [hrewrite] using htmp

  refine ⟨x, hx_ge_a, ?_⟩
  nlinarith [h_upper, h_re_lower_scaled]

/-- Ω₊ direction for `π(x) - li(x)` from anti-aligned singleton phases. -/
private theorem omega_plus_from_zeros
    [TruncatedExplicitFormulaPiHyp]
    (h_zeros : Set.Infinite {ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2}) :
    IsOmegaPlus (fun x => piLiError x) (fun x => Real.sqrt x / Real.log x) := by
  have h_inf := h_zeros.diff (Set.finite_singleton ((1 / 2 : ℝ) : ℂ))
  obtain ⟨ρ₀, ⟨hρ₀_mem, hρ₀_re⟩, hρ₀_notin⟩ := h_inf.nonempty

  have hρ₀_im_ne : ρ₀.im ≠ 0 := by
    intro him
    exact hρ₀_notin
      (Set.mem_singleton_iff.mpr
        (Complex.ext (by simp [hρ₀_re]) (by simp [him])))

  have hS_in : ∀ ρ ∈ ({ρ₀} : Finset ℂ), ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    simp only [Finset.mem_singleton] at hρ
    subst hρ
    exact ⟨hρ₀_mem, hρ₀_re⟩

  obtain ⟨c, hc_pos, h_neg⟩ :=
    TruncatedExplicitFormulaPiHyp.zero_sum_neg_frequently ρ₀ hρ₀_mem hρ₀_re hρ₀_im_ne

  have h_ef := TruncatedExplicitFormulaPiHyp.pi_approx {ρ₀} hS_in (c / 2) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp h_ef

  refine ⟨c / 2, by positivity, ?_⟩
  rw [Filter.frequently_atTop]
  intro a

  obtain ⟨x, hx_gt, hx_one, hx_neg⟩ := h_neg (max a x₀)
  have hx_ge_a : a ≤ x := by linarith [le_max_left a x₀]
  have hx_ge_x₀ : x₀ ≤ x := by linarith [le_max_right a x₀]

  have h_ef_x := hx₀ x hx_ge_x₀
  simp only [Finset.sum_singleton] at h_ef_x hx_neg

  have h_lower := (abs_le.mp h_ef_x).1

  refine ⟨x, hx_ge_a, ?_⟩
  nlinarith [h_lower, hx_neg]

/-- π(x) - li(x) = Ω±(√x / log x) from critical-line zeros plus a truncated
explicit formula input for π. -/
instance [HardyCriticalLineZerosHyp] [TruncatedExplicitFormulaPiHyp] :
    PiLiOscillationSqrtHyp where
  oscillation := by
    have h_zeros := HardyCriticalLineZerosHyp.infinite
    exact ⟨omega_plus_from_zeros h_zeros, omega_minus_from_zeros h_zeros⟩

end PiLiDirectOscillationBridge
