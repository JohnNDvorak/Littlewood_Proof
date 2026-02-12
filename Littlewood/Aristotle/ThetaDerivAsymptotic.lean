/-
Asymptotic formula for θ'(t) = (1/2)·log(t/(2π)) + O(1/t).

The Riemann-Siegel theta function is θ(t) = Im(log Γ(1/4 + it/2)) - (t/2)·log π.
Its derivative (defined via the digamma function to avoid branch cuts) satisfies:

  θ'(t) = (1/2)·Re(digamma(1/4+it/2)) - (1/2)·log π

Using the asymptotic digamma(s) = log(s) - 1/(2s) + O(1/|s|²) and the
log(1/4+it/2) expansion from BinetStirling, we get:

  θ'(t) = (1/2)·log(t/(2π)) + O(1/t)

KEY RESULTS:
  re_log_quarter_plus_it_half_asymptotic:
    Re(log(1/4+it/2)) = log(t/2) + O(1/t²)
  theta_deriv_asymptotic:
    thetaDeriv(t) - (1/2)·log(t/(2π)) = O(1/t)
  theta_deriv_at_stationary_point:
    |thetaDeriv(2π(n+1)²) - log(n+1)| ≤ C/(n+1)²

DEPENDENCIES: BinetStirling.lean, GammaHalfPlane.lean
Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.BinetStirling
import Littlewood.Aristotle.GammaHalfPlane
import Littlewood.Aristotle.DigammaAsymptotic

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ThetaDerivAsymptotic

open Complex Asymptotics Filter Topology

/-
## Part 1: The effective phase derivative θ'(t)

We define θ'(t) via the digamma function to avoid branch-cut issues.
The digamma function ψ(s) = Γ'(s)/Γ(s) is meromorphic with poles only at
non-positive integers. At s = 1/4 + it/2 (which has Re(s) = 1/4 > 0),
both Γ(s) ≠ 0 and Γ is differentiable, so digamma(s) is well-defined.

θ'(t) = Im(d/dt[log Γ(1/4+it/2)]) - (1/2)·log π
       = Im((i/2)·digamma(1/4+it/2)) - (1/2)·log π
       = (1/2)·Re(digamma(1/4+it/2)) - (1/2)·log π

since Im(z·i/2) = (1/2)·Re(z) for any z.
-/

/-- The effective phase derivative θ'(t), defined as
    (1/2) · Re(Γ'/Γ(1/4+it/2)) - (1/2) · log π.
    This equals the derivative of Im(log Γ(1/4+it/2)) - (t/2)·log π
    at points where the latter is differentiable (i.e., away from branch cuts). -/
noncomputable def thetaDeriv (t : ℝ) : ℝ :=
  (1/2) * (deriv Gamma (1/4 + I * (↑t/2)) / Gamma (1/4 + I * (↑t/2))).re
  - (1/2) * Real.log Real.pi

/-
## Part 2: Re(log(1/4 + it/2)) asymptotic from BinetStirling

The existing log_quarter_plus_it_half_asymptotic gives:
  log(1/4+it/2) = log(t/2) + iπ/2 - i/(2t) + O(1/t²)

Taking real parts:
  Re(log(1/4+it/2)) = log(t/2) + O(1/t²)
-/

/-- The pure imaginary correction I·(π/2) has zero real part. -/
private lemma re_I_mul_pi_half : (I * (↑Real.pi / 2 : ℂ)).re = 0 := by
  simp [mul_re, I_re, I_im, ofReal_re, ofReal_im]

/-- The pure imaginary correction I/(2t) has zero real part. -/
private lemma re_I_div_two_t (t : ℝ) : (I / (2 * (↑t : ℂ))).re = 0 := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [show I / (2 * (↑t : ℂ)) = ↑(0 : ℝ) + ↑(1/(2*t)) * I from by push_cast; field_simp; ring]
    simp [ofReal_re, mul_re, ofReal_im, I_re, I_im]

/-- The real part of log(1/4+it/2) is asymptotically log(t/2) + O(1/t²).
    This follows from taking the real part of log_quarter_plus_it_half_asymptotic. -/
theorem re_log_quarter_plus_it_half_asymptotic :
    (fun t : ℝ => (Complex.log (1/4 + I * ↑t / 2)).re - Real.log (t / 2))
    =O[atTop] (fun t => 1 / t ^ 2) := by
  have h_main := log_quarter_plus_it_half_asymptotic
  rw [Asymptotics.isBigO_iff] at h_main ⊢
  obtain ⟨C, hC⟩ := h_main
  refine ⟨C, ?_⟩
  filter_upwards [hC, Filter.eventually_ge_atTop (1 : ℝ)] with t ht ht1
  have ht_pos : (0 : ℝ) < t := by linarith
  -- The difference is the real part of the complex error
  -- Re(log(s) - (log(t/2) + iπ/2 - i/(2t))) = Re(log(s)) - Re(log(t/2))
  -- since the imaginary corrections have Re = 0
  have h_re_eq :
      (Complex.log (1/4 + I * ↑t / 2)).re - Real.log (t / 2) =
      (Complex.log (1/4 + I * ↑t / 2) -
        (Complex.log (↑t / 2) + I * (↑Real.pi / 2) - I / (2 * ↑t))).re := by
    -- Re(log(↑t/2)) = Real.log(t/2)
    have h_log_re : (Complex.log ((↑t : ℂ) / 2)).re = Real.log (t / 2) := by
      have : (↑t : ℂ) / 2 = (↑(t / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.log_ofReal_re]
    -- Compute Re of the compound expression directly
    have h_compound_re :
        (Complex.log ((↑t : ℂ) / 2) + I * (↑Real.pi / 2) - I / (2 * ↑t)).re =
        Real.log (t / 2) := by
      have h1 : (Complex.log ((↑t : ℂ) / 2) + I * (↑Real.pi / 2)).re = Real.log (t / 2) := by
        rw [add_re, re_I_mul_pi_half, add_zero, h_log_re]
      rw [sub_re, h1, re_I_div_two_t, sub_zero]
    rw [sub_re, h_compound_re]
  rw [h_re_eq]
  calc ‖(Complex.log (1/4 + I * ↑t / 2) -
      (Complex.log (↑t / 2) + I * (↑Real.pi / 2) - I / (2 * ↑t))).re‖
      = |(Complex.log (1/4 + I * ↑t / 2) -
          (Complex.log (↑t / 2) + I * (↑Real.pi / 2) - I / (2 * ↑t))).re| :=
        Real.norm_eq_abs _
    _ ≤ ‖Complex.log (1/4 + I * ↑t / 2) -
          (Complex.log (↑t / 2) + I * (↑Real.pi / 2) - I / (2 * ↑t))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ C * ‖(1 : ℝ) / t ^ 2‖ := ht

/-
## Part 3: Re(1/(2s)) asymptotic

For s = 1/4 + it/2, Re(1/(2s)) = O(1/t²).
-/

/-- Re(1/(2·(1/4+it/2))) is O(1/t²). -/
lemma re_inv_two_s_isBigO :
    (fun t : ℝ => (1 / (2 * (1/4 + I * (↑t / 2) : ℂ))).re)
    =O[atTop] (fun t => 1 / t ^ 2) := by
  -- Strategy: 1/(2s) = 1/w where w = 1/2 + t*I.
  -- Re(1/w) = Re(w̄)/|w|² = Re(w)/|w|² = (1/2)/(1/4+t²) ≤ (1/2)/t² ≤ 1/t²
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
  have ht_pos : (0 : ℝ) < t := by linarith
  -- Compute directly using Complex.inv_re
  set w : ℂ := 2 * (1/4 + I * (↑t / 2)) with hw_def
  have hw_eq : w = ↑(1/2 : ℝ) + ↑t * I := by rw [hw_def]; push_cast; ring
  -- normSq(w) = (1/2)² + t² = 1/4 + t²
  have hw_normSq : Complex.normSq w = 1/4 + t^2 := by
    rw [hw_eq, Complex.normSq_add_mul_I]; simp; ring
  have hw_normSq_pos : (0 : ℝ) < Complex.normSq w := by rw [hw_normSq]; positivity
  -- Re(1/w) = Re(w)/normSq(w) = (1/2)/(1/4+t²)
  have h_re_val : (1 / w).re = (1/2) / (1/4 + t^2) := by
    rw [one_div, Complex.inv_re, hw_eq]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
               mul_one, add_zero]
    rw [show Complex.normSq (↑(1 / 2 : ℝ) + ↑t * I) = 1/4 + t^2 from by
      rw [Complex.normSq_add_mul_I]; simp; ring]
  -- Bound: (1/2)/(1/4+t²) ≤ 1/t² ≤ 1 * ‖1/t²‖
  rw [h_re_val, one_mul]
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num : (0:ℝ) < 1/2) (by positivity))]
  rw [Real.norm_eq_abs, abs_of_pos (div_pos one_pos (pow_pos ht_pos 2))]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 1/4 + t^2) (pow_pos ht_pos 2)]
  nlinarith [sq_nonneg t]

/-
## Part 4: Re(digamma(s)) asymptotic

digamma(s) = log(s) - 1/(2s) + O(1/|s|²)

We state the key step as sorry because the full proof requires
bounding the Binet integral derivative, which is substantial analysis.
The downstream theta_deriv_asymptotic theorem is conditional on this.
-/

/-- The digamma function Γ'/Γ at 1/4 + it/2 satisfies:
    Re(Γ'/Γ(s)) = Re(log(s)) + O(1/t).

    This is a consequence of the Stirling series for digamma:
    ψ(s) = log(s) - 1/(2s) + Σ B_{2k}/(2k·s^{2k})

    The proof requires bounding the Binet integral derivative. -/
theorem re_digamma_asymptotic :
    (fun t : ℝ => (deriv Gamma (1/4 + I * (↑t/2)) /
        Gamma (1/4 + I * (↑t/2))).re -
        (Complex.log (1/4 + I * ↑t / 2)).re)
    =O[atTop] (fun t => 1 / t) :=
  DigammaAsymptotic.re_digamma_asymptotic

/-
## Part 5: Main theorem — θ'(t) = (1/2)·log(t/(2π)) + O(1/t)
-/

/-- The key algebraic identity: log(t/2) - log π = log(t/(2π)) for t > 0. -/
lemma log_half_sub_log_pi (t : ℝ) (ht : 0 < t) :
    Real.log (t / 2) - Real.log Real.pi = Real.log (t / (2 * Real.pi)) := by
  rw [show t / (2 * Real.pi) = (t / 2) / Real.pi from by ring]
  rw [Real.log_div (ne_of_gt (by positivity : (0:ℝ) < t / 2)) (ne_of_gt Real.pi_pos)]

/-- **Main theorem**: The effective phase derivative satisfies
    θ'(t) = (1/2)·log(t/(2π)) + O(1/t) as t → ∞.

    This is the KEY RESULT needed for stationary phase analysis.

    Proof outline:
    θ'(t) = (1/2)·Re(Γ'/Γ(s)) - (1/2)·log π
           = (1/2)·(Re(log(s)) + O(1/t)) - (1/2)·log π    [by re_digamma_asymptotic]
           = (1/2)·(log(t/2) + O(1/t²) + O(1/t)) - (1/2)·log π  [by re_log_... asymptotic]
           = (1/2)·log(t/2) - (1/2)·log π + O(1/t)
           = (1/2)·log(t/(2π)) + O(1/t)                    [by log_half_sub_log_pi] -/
theorem theta_deriv_asymptotic :
    (fun t : ℝ => thetaDeriv t - (1/2) * Real.log (t / (2 * Real.pi)))
    =O[atTop] (fun t => 1 / t) := by
  have h_digamma := re_digamma_asymptotic
  have h_log := re_log_quarter_plus_it_half_asymptotic
  -- The key decomposition: θ'(t) - (1/2)·log(t/(2π)) can be split into
  -- (1/2) * (Re(ψ(s)) - Re(log(s))) + (1/2) * (Re(log(s)) - log(t/2))
  -- because (1/2)·log(t/2) - (1/2)·log π = (1/2)·log(t/(2π)).
  -- First, show the sum of two O(1/t) terms is O(1/t)
  have h_sum : (fun t : ℝ =>
      (1/2) * ((deriv Gamma (1/4 + I * (↑t/2)) /
        Gamma (1/4 + I * (↑t/2))).re -
        (Complex.log (1/4 + I * ↑t / 2)).re) +
      (1/2) * ((Complex.log (1/4 + I * ↑t / 2)).re - Real.log (t / 2)))
    =O[atTop] (fun t => 1 / t) := by
    apply IsBigO.add
    · exact h_digamma.const_mul_left (1/2)
    · apply IsBigO.trans (h_log.const_mul_left (1/2))
      -- 1/t² = O(1/t) as t → ∞
      rw [Asymptotics.isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
      have ht_pos : (0 : ℝ) < t := by linarith
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (div_pos one_pos (pow_pos ht_pos 2)),
          abs_of_pos (div_pos one_pos ht_pos)]
      rw [div_le_div_iff₀ (pow_pos ht_pos 2) ht_pos]
      nlinarith [sq_nonneg t]
  -- Now show that our function is eventually equal to this sum
  refine IsBigO.congr' h_sum ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have h_logid := log_half_sub_log_pi t ht
  show (1/2) * ((deriv Gamma (1/4 + I * (↑t/2)) /
      Gamma (1/4 + I * (↑t/2))).re -
      (Complex.log (1/4 + I * ↑t / 2)).re) +
    (1/2) * ((Complex.log (1/4 + I * ↑t / 2)).re - Real.log (t / 2)) =
    thetaDeriv t - (1/2) * Real.log (t / (2 * Real.pi))
  unfold thetaDeriv
  linarith

/-
## Part 6: Corollary — Stationary point analysis

At t₀ = 2π(n+1)², we have:
  θ'(t₀) = (1/2)·log(t₀/(2π)) + O(1/t₀)
          = (1/2)·log((n+1)²) + O(1/n²)
          = log(n+1) + O(1/n²)

This identifies the stationary points of the Hardy cosine modes.
-/

/-- At t₀ = 2π(n+1)², we have log(t₀/(2π)) = 2·log(n+1). -/
lemma log_at_stationary_point (n : ℕ) :
    Real.log (2 * Real.pi * (↑n + 1) ^ 2 / (2 * Real.pi)) =
    2 * Real.log (↑n + 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hn : (0 : ℝ) < (↑n + 1) := by positivity
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  rw [mul_div_cancel_left₀ _ h2pi_ne]
  have hsq : (↑n + 1 : ℝ) ^ 2 = (↑n + 1) * (↑n + 1) := by ring
  rw [hsq, Real.log_mul (ne_of_gt hn) (ne_of_gt hn)]
  ring

/-- **Stationary point corollary**: At t₀ = 2π(n+1)², the effective phase derivative
    is approximately log(n+1), with error O(1/(n+1)²).

    This is the key input for identifying stationary points of the Hardy cosine modes:
    the phase φ_n(t) = θ(t) - t·log(n+1) has φ'_n(t₀) ≈ log(n+1) - log(n+1) = 0
    when t₀ = 2π(n+1)². -/
theorem theta_deriv_at_stationary_point :
    ∃ C > 0, ∀ n : ℕ,
    |thetaDeriv (2 * Real.pi * (↑n + 1) ^ 2) - Real.log (↑n + 1)| ≤
      C / (↑n + 1) ^ 2 := by
  -- Extract bound from theta_deriv_asymptotic: ∃ C₀, ∀ᶠ t, |f(t)| ≤ C₀ · |1/t|
  have h_asymp := theta_deriv_asymptotic
  rw [Asymptotics.isBigO_iff] at h_asymp
  obtain ⟨C₀, hC₀⟩ := h_asymp
  -- Extract T₀ from the eventually
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ, ∀ t ≥ T₀,
      ‖thetaDeriv t - 1 / 2 * Real.log (t / (2 * Real.pi))‖ ≤ C₀ * ‖1 / t‖ := by
    rw [Filter.eventually_atTop] at hC₀
    exact hC₀
  -- For n with t₀ = 2π(n+1)² ≥ T₀, the bound holds with constant |C₀|/(2π)
  -- For finitely many small n, we can bound by a finite max
  -- Key: thetaDeriv is continuous (as a composition of continuous functions)
  -- We use a uniform bound that works for ALL n
  -- Step 1: For large n, use the asymptotic
  set f : ℕ → ℝ := fun n => |thetaDeriv (2 * Real.pi * (↑n + 1) ^ 2) - Real.log (↑n + 1)| with hf_def
  -- Step 2: Find N₀ such that for n ≥ N₀, the asymptotic applies
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, 2 * Real.pi * (↑n + 1) ^ 2 ≥ T₀ := by
    obtain ⟨M, hM⟩ := exists_nat_ge (max T₀ 0 / (2 * Real.pi))
    refine ⟨M, fun n hn => ?_⟩
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hn1 : (0 : ℝ) < ↑n + 1 := by positivity
    calc T₀ ≤ max T₀ 0 := le_max_left _ _
      _ = 2 * Real.pi * (max T₀ 0 / (2 * Real.pi)) := by
          rw [mul_div_cancel₀ (max T₀ 0) (ne_of_gt hpi)]
      _ ≤ 2 * Real.pi * ↑M := by gcongr
      _ ≤ 2 * Real.pi * (↑n + 1) ^ 2 := by
          gcongr; calc (↑M : ℝ) ≤ ↑n := Nat.cast_le.mpr hn
            _ ≤ (↑n + 1) ^ 2 := by nlinarith
  -- Step 3: For n ≥ N₀, bound the difference
  have h_large_bound : ∀ n ≥ N₀,
      f n ≤ (|C₀| + 1) / (2 * Real.pi) / (↑n + 1) ^ 2 := by
    intro n hn
    have hn1 : (0 : ℝ) < ↑n + 1 := by positivity
    have ht₀_pos : (0 : ℝ) < 2 * Real.pi * (↑n + 1) ^ 2 := by positivity
    have h_bd := hT₀ _ (hN₀ n hn)
    -- Use the log identity: (1/2)·log(t₀/(2π)) = log(n+1)
    have h_log := log_at_stationary_point n
    have h_eq : thetaDeriv (2 * Real.pi * (↑n + 1) ^ 2) - Real.log (↑n + 1) =
        thetaDeriv (2 * Real.pi * (↑n + 1) ^ 2) -
        1 / 2 * Real.log (2 * Real.pi * (↑n + 1) ^ 2 / (2 * Real.pi)) := by
      congr 1; rw [h_log]; ring
    simp only [hf_def]
    rw [h_eq]
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h_bd
    calc |thetaDeriv (2 * Real.pi * (↑n + 1) ^ 2) -
            1 / 2 * Real.log (2 * Real.pi * (↑n + 1) ^ 2 / (2 * Real.pi))|
        ≤ C₀ * |1 / (2 * Real.pi * (↑n + 1) ^ 2)| := h_bd
      _ ≤ |C₀| * |1 / (2 * Real.pi * (↑n + 1) ^ 2)| := by
          gcongr; exact le_abs_self C₀
      _ = |C₀| / (2 * Real.pi * (↑n + 1) ^ 2) := by
          rw [abs_of_pos (div_pos one_pos ht₀_pos)]; ring
      _ ≤ (|C₀| + 1) / (2 * Real.pi) / (↑n + 1) ^ 2 := by
          rw [div_div]; gcongr; linarith
  -- Step 4: Bound for small n (n < N₀) via existence of a uniform constant
  set C_large := (|C₀| + 1) / (2 * Real.pi)
  have h_fin_bound : ∃ C_s : ℝ, ∀ n : ℕ, n < N₀ → f n * (↑n + 1) ^ 2 ≤ C_s := by
    by_cases hN : N₀ = 0
    · exact ⟨0, fun n hn => absurd hn (by omega)⟩
    · set g : ℕ → ℝ := fun n => f n * (↑n + 1) ^ 2
      exact ⟨(Finset.range N₀).sup' (Finset.nonempty_range_iff.mpr hN) g,
          fun n hn => Finset.le_sup' g (Finset.mem_range.mpr hn)⟩
  obtain ⟨C_s, hC_s⟩ := h_fin_bound
  -- Take C = max(C_large, C_s) + 1 > 0
  refine ⟨max C_large C_s + 1, by positivity, fun n => ?_⟩
  have hn1_pos : (0 : ℝ) < (↑n + 1) ^ 2 := by positivity
  by_cases hn : n ≥ N₀
  · calc f n ≤ C_large / (↑n + 1) ^ 2 := h_large_bound n hn
      _ ≤ (max C_large C_s + 1) / (↑n + 1) ^ 2 := by
          gcongr; linarith [le_max_left C_large C_s]
  · push_neg at hn
    calc f n = f n * (↑n + 1) ^ 2 / (↑n + 1) ^ 2 := by
            rw [mul_div_cancel_right₀ _ (ne_of_gt hn1_pos)]
      _ ≤ C_s / (↑n + 1) ^ 2 := by gcongr; exact hC_s n hn
      _ ≤ (max C_large C_s + 1) / (↑n + 1) ^ 2 := by
          gcongr; linarith [le_max_right C_large C_s]

/-
## Part 7: Useful intermediate results for downstream consumers
-/

/-- θ'(t) is eventually positive (since log(t/(2π)) → ∞). -/
theorem thetaDeriv_eventually_pos :
    ∀ᶠ (t : ℝ) in atTop, 0 < thetaDeriv t := by
  -- θ'(t) = (1/2)·log(t/(2π)) + O(1/t), and log(t/(2π)) → ∞
  have h_asymp := theta_deriv_asymptotic
  rw [Asymptotics.isBigO_iff] at h_asymp
  obtain ⟨C, hC⟩ := h_asymp
  rw [Filter.eventually_atTop] at hC
  obtain ⟨T₀, hT₀⟩ := hC
  -- Choose T₁ = max(T₀, 2π·e^(2(|C|+1)), 1)
  set T₁ := max T₀ (max (2 * Real.pi * Real.exp (2 * (|C| + 1))) 1)
  rw [Filter.eventually_atTop]
  refine ⟨T₁, fun t ht => ?_⟩
  have ht_ge_T₀ : t ≥ T₀ := le_trans (le_max_left _ _) ht
  have ht_ge_exp : t ≥ 2 * Real.pi * Real.exp (2 * (|C| + 1)) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have ht_ge_1 : t ≥ 1 :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht_pos : (0 : ℝ) < t := by linarith
  have hpi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  -- Get the bound from asymptotic
  have h_bd := hT₀ t ht_ge_T₀
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h_bd
  -- The error is at most |C|/t in absolute value
  -- So thetaDeriv t ≥ (1/2)·log(t/(2π)) - |C|/t
  have h_lower : thetaDeriv t ≥ 1 / 2 * Real.log (t / (2 * Real.pi)) - |C| / t := by
    -- |x - y| ≤ B implies x ≥ y - B
    have h1 : thetaDeriv t - 1 / 2 * Real.log (t / (2 * Real.pi)) ≥
        -(C * |1 / t|) := by linarith [neg_abs_le (thetaDeriv t - 1 / 2 * Real.log (t / (2 * Real.pi)))]
    have h2 : C * |1 / t| ≤ |C| / t := by
      rw [abs_of_pos (div_pos one_pos ht_pos), one_div]
      calc C * t⁻¹ ≤ |C| * t⁻¹ := by
            exact mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr (le_of_lt ht_pos))
        _ = |C| / t := by rw [div_eq_mul_inv]
    linarith
  -- The main term: (1/2)·log(t/(2π)) ≥ |C|+1 (from our choice of T₁)
  have h_log_large : 1 / 2 * Real.log (t / (2 * Real.pi)) ≥ |C| + 1 := by
    have h_ratio : t / (2 * Real.pi) ≥ Real.exp (2 * (|C| + 1)) := by
      rw [ge_iff_le, le_div_iff₀ hpi_pos]; linarith
    have h_log : Real.log (t / (2 * Real.pi)) ≥ 2 * (|C| + 1) := by
      calc 2 * (|C| + 1) = Real.log (Real.exp (2 * (|C| + 1))) := (Real.log_exp _).symm
        _ ≤ Real.log (t / (2 * Real.pi)) :=
            Real.log_le_log (Real.exp_pos _) h_ratio
    linarith
  -- |C|/t ≤ |C| since t ≥ 1
  have h_Ct : |C| / t ≤ |C| := by
    rw [div_le_iff₀ ht_pos]
    calc |C| = |C| * 1 := (mul_one _).symm
      _ ≤ |C| * t := by gcongr
  -- Combine: thetaDeriv t ≥ (|C|+1) - |C| = 1 > 0
  linarith

end ThetaDerivAsymptotic
