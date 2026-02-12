/-
Lower-bound infrastructure for phase derivatives of Hardy cosine modes.

For the mode phase `phi_n(t) = theta(t) - t * log(n+1)`, this file builds a
quantitative lower bound for `thetaDeriv t - log(n+1)` away from the stationary
point scale `hardyStart n = 2*pi*(n+1)^2`, under a local one-point asymptotic
control hypothesis on `thetaDeriv`.
-/

import Mathlib
import Littlewood.Aristotle.ThetaDerivAsymptotic
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.HardyZMeasurability

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.PhaseDerivBounds

open HardyEstimatesPartial
open ThetaDerivAsymptotic

private lemma ratio_lower_from_offset (n : ℕ) (t δ : ℝ) (hδ : 0 ≤ δ)
    (ht : t ≥ hardyStart n + δ * ((↑n : ℝ) + 1)) :
    1 + δ / (2 * Real.pi * ((↑n : ℝ) + 1))
      ≤ t / (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2) := by
  have hn1_pos : 0 < ((↑n : ℝ) + 1) := by positivity
  have hden_pos : 0 < 2 * Real.pi * ((↑n : ℝ) + 1) ^ 2 := by positivity
  have ht' : 2 * Real.pi * ((↑n : ℝ) + 1) ^ 2 + δ * ((↑n : ℝ) + 1) ≤ t := by
    simpa [Aristotle.HardyNProperties.hardyStart_formula, add_comm, add_left_comm, add_assoc] using ht
  have hdiv :
      (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2 + δ * ((↑n : ℝ) + 1)) /
          (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2)
      ≤ t / (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2) :=
    div_le_div_of_nonneg_right ht' (le_of_lt hden_pos)
  have hleft :
      (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2 + δ * ((↑n : ℝ) + 1)) /
          (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2)
      = 1 + δ / (2 * Real.pi * ((↑n : ℝ) + 1)) := by
    have hn1_ne : ((↑n : ℝ) + 1) ≠ 0 := ne_of_gt hn1_pos
    have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp [hn1_ne, h2pi_ne]
  calc
    1 + δ / (2 * Real.pi * ((↑n : ℝ) + 1))
        = (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2 + δ * ((↑n : ℝ) + 1)) /
            (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2) := by simp [hleft]
    _ ≤ t / (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2) := hdiv

private lemma main_phase_log_rewrite (n : ℕ) (t : ℝ) (ht : 0 < t) :
    (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log ((↑n : ℝ) + 1)
      = (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2)) := by
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hn1_ne : ((↑n : ℝ) + 1) ≠ 0 := by positivity
  have ht_div_ne : t / (2 * Real.pi) ≠ 0 := div_ne_zero (ne_of_gt ht) h2pi_ne
  have hratio :
      (t / (2 * Real.pi)) / (((↑n : ℝ) + 1) ^ 2)
        = t / (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2) := by
    field_simp [h2pi_ne, pow_ne_zero 2 hn1_ne]
  calc
    (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - Real.log ((↑n : ℝ) + 1)
        = (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - (1 / 2 : ℝ) * (2 * Real.log ((↑n : ℝ) + 1)) := by
            ring
    _ = (1 / 2 : ℝ) * (Real.log (t / (2 * Real.pi)) - Real.log (((↑n : ℝ) + 1) ^ 2)) := by
          rw [Real.log_pow]
          ring
    _ = (1 / 2 : ℝ) * Real.log ((t / (2 * Real.pi)) / (((↑n : ℝ) + 1) ^ 2)) := by
          rw [Real.log_div ht_div_ne (pow_ne_zero 2 hn1_ne)]
    _ = (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2)) := by
          rw [hratio]

private lemma log_gain_lower (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    δ / ((δ + 4 * Real.pi) * ((↑n : ℝ) + 1))
      ≤ (1 / 2 : ℝ) * Real.log (1 + δ / (2 * Real.pi * ((↑n : ℝ) + 1))) := by
  set u : ℝ := δ / (2 * Real.pi * ((↑n : ℝ) + 1))
  have hu_nonneg : 0 ≤ u := by
    unfold u
    positivity
  have hlog : 2 * u / (u + 2) ≤ Real.log (1 + u) :=
    Real.le_log_one_add_of_nonneg hu_nonneg
  have hhalf : u / (u + 2) ≤ (1 / 2 : ℝ) * Real.log (1 + u) := by
    have hdiv : (2 * u / (u + 2)) / 2 ≤ Real.log (1 + u) / 2 := by
      exact div_le_div_of_nonneg_right hlog (by norm_num)
    have hleft : (2 * u / (u + 2)) / 2 = u / (u + 2) := by ring
    have hright : Real.log (1 + u) / 2 = (1 / 2 : ℝ) * Real.log (1 + u) := by ring
    linarith [hdiv, hleft, hright]
  have hu_rewrite : u / (u + 2) = δ / (δ + 4 * Real.pi * ((↑n : ℝ) + 1)) := by
    unfold u
    have hden : (2 * Real.pi * ((↑n : ℝ) + 1)) ≠ 0 := by
      nlinarith [Real.pi_pos]
    have hden2 : (δ + 4 * Real.pi * ((↑n : ℝ) + 1)) ≠ 0 := by
      have hpos : 0 < δ + 4 * Real.pi * ((↑n : ℝ) + 1) := by
        have : 0 < 4 * Real.pi * ((↑n : ℝ) + 1) := by positivity
        linarith
      exact ne_of_gt hpos
    field_simp [hden, hden2]
    ring
  have hN : (1 : ℝ) ≤ ((↑n : ℝ) + 1) := by
    have hnonneg : (0 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have hden_compare :
      δ + 4 * Real.pi * ((↑n : ℝ) + 1) ≤ (δ + 4 * Real.pi) * ((↑n : ℝ) + 1) := by
    nlinarith [hδ, hN, Real.pi_pos]
  have hden_pos_left : 0 < δ + 4 * Real.pi * ((↑n : ℝ) + 1) := by
    have : 0 < 4 * Real.pi * ((↑n : ℝ) + 1) := by positivity
    linarith
  have hrecip :
      1 / ((δ + 4 * Real.pi) * ((↑n : ℝ) + 1))
        ≤ 1 / (δ + 4 * Real.pi * ((↑n : ℝ) + 1)) := by
    simpa using (one_div_le_one_div_of_le hden_pos_left hden_compare)
  have hmain :
      δ / ((δ + 4 * Real.pi) * ((↑n : ℝ) + 1)) ≤ δ / (δ + 4 * Real.pi * ((↑n : ℝ) + 1)) := by
    calc
      δ / ((δ + 4 * Real.pi) * ((↑n : ℝ) + 1))
          = δ * (1 / ((δ + 4 * Real.pi) * ((↑n : ℝ) + 1))) := by ring
      _ ≤ δ * (1 / (δ + 4 * Real.pi * ((↑n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hrecip hδ
      _ = δ / (δ + 4 * Real.pi * ((↑n : ℝ) + 1)) := by ring
  calc
    δ / ((δ + 4 * Real.pi) * ((↑n : ℝ) + 1))
        ≤ δ / (δ + 4 * Real.pi * ((↑n : ℝ) + 1)) := hmain
    _ = u / (u + 2) := by simp [hu_rewrite]
    _ ≤ (1 / 2 : ℝ) * Real.log (1 + u) := hhalf
    _ = (1 / 2 : ℝ) * Real.log (1 + δ / (2 * Real.pi * ((↑n : ℝ) + 1))) := by
      simp [u]

/--
Local lower bound away from the stationary point, under a one-point asymptotic
control hypothesis for `thetaDeriv`.
-/
theorem phase_deriv_lower_away_of_local_bound
    (n : ℕ) (t δ A : ℝ)
    (hδ : 0 ≤ δ)
    (hTheta : thetaDeriv t ≥ (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - A / t)
    (ht : t ≥ hardyStart n + δ * ((↑n : ℝ) + 1)) :
    thetaDeriv t - Real.log ((↑n : ℝ) + 1)
      ≥ δ / ((δ + 4 * Real.pi) * ((↑n : ℝ) + 1)) - A / t := by
  have hstart_pos : 0 < hardyStart n := by
    rw [Aristotle.HardyNProperties.hardyStart_formula]
    positivity
  have hδterm_nonneg : 0 ≤ δ * ((↑n : ℝ) + 1) := by positivity
  have ht_ge_start : hardyStart n ≤ t := by linarith
  have ht_pos : 0 < t := by linarith
  have hratio := ratio_lower_from_offset n t δ hδ ht
  have hlog_rhs :
      (1 / 2 : ℝ) * Real.log (1 + δ / (2 * Real.pi * ((↑n : ℝ) + 1)))
        ≤ (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2)) := by
    have hone_pos : 0 < 1 + δ / (2 * Real.pi * ((↑n : ℝ) + 1)) := by
      have : 0 ≤ δ / (2 * Real.pi * ((↑n : ℝ) + 1)) := by positivity
      linarith
    have hlog : Real.log (1 + δ / (2 * Real.pi * ((↑n : ℝ) + 1)))
        ≤ Real.log (t / (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2)) :=
      Real.log_le_log hone_pos hratio
    nlinarith
  have hgain :
      δ / ((δ + 4 * Real.pi) * ((↑n : ℝ) + 1))
        ≤ (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2)) := by
    exact le_trans (log_gain_lower n δ hδ) hlog_rhs
  have htheta_shift :
      thetaDeriv t - Real.log ((↑n : ℝ) + 1)
        ≥ (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi * ((↑n : ℝ) + 1) ^ 2)) - A / t := by
    have hrew := main_phase_log_rewrite n t ht_pos
    linarith [hTheta, hrew]
  linarith [hgain, htheta_shift]

/--
Same lower bound written with an explicit coefficient
`c(δ) = δ / (δ + 4π)`, i.e. `c(δ)/(n+1) - A/t`.
-/
theorem phase_deriv_lower_away
    (n : ℕ) (t δ A : ℝ)
    (hδ : 0 ≤ δ)
    (hTheta : thetaDeriv t ≥ (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - A / t)
    (ht : t ≥ hardyStart n + δ * ((↑n : ℝ) + 1)) :
    thetaDeriv t - Real.log ((↑n : ℝ) + 1)
      ≥ (δ / (δ + 4 * Real.pi)) / ((↑n : ℝ) + 1) - A / t := by
  have hbase := phase_deriv_lower_away_of_local_bound n t δ A hδ hTheta ht
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbase

/--
Error-absorbed variant: if the local asymptotic error term `A/t` is at most half
of the main coefficient contribution, we get a clean positive lower bound.
-/
theorem phase_deriv_lower_away_no_error
    (n : ℕ) (t δ A : ℝ)
    (hδ : 0 ≤ δ)
    (hTheta : thetaDeriv t ≥ (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) - A / t)
    (ht : t ≥ hardyStart n + δ * ((↑n : ℝ) + 1))
    (hErr : A / t ≤ (δ / (2 * (δ + 4 * Real.pi))) / ((↑n : ℝ) + 1)) :
    thetaDeriv t - Real.log ((↑n : ℝ) + 1)
      ≥ (δ / (2 * (δ + 4 * Real.pi))) / ((↑n : ℝ) + 1) := by
  have hbase := phase_deriv_lower_away n t δ A hδ hTheta ht
  have hstep :
      δ / (δ + 4 * Real.pi) / ((↑n : ℝ) + 1) - A / t
        ≥ δ / (δ + 4 * Real.pi) / ((↑n : ℝ) + 1)
          - (δ / (2 * (δ + 4 * Real.pi))) / ((↑n : ℝ) + 1) := by
    linarith [hErr]
  have hhalf :
      δ / (δ + 4 * Real.pi) / ((↑n : ℝ) + 1)
        - (δ / (2 * (δ + 4 * Real.pi))) / ((↑n : ℝ) + 1)
      = (δ / (2 * (δ + 4 * Real.pi))) / ((↑n : ℝ) + 1) := by
    have hden1 : (δ + 4 * Real.pi) ≠ 0 := by nlinarith [Real.pi_pos]
    have hden2 : ((↑n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hden1, hden2]
    ring
  linarith [hbase, hstep, hhalf]

end Aristotle.PhaseDerivBounds
