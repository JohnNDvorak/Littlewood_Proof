import Mathlib
import Littlewood.Aristotle.MeanSquarePartialSumAsymptotic

open scoped BigOperators

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.DirichletPolynomialMVT

open Complex Finset MeasureTheory

/-- Finite Dirichlet polynomial with frequencies `log (n+1)`. -/
def dirPoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range N) (fun n => a n * ((↑(n + 1) : ℂ) ^ (-(Complex.I * (t : ℂ)))))

/-- Real-valued off-diagonal term used in the Dirichlet-polynomial mean-square decomposition. -/
def offDiagTerm (a : ℕ → ℂ) (T : ℝ) (m n : ℕ) : ℝ :=
  if m = n then 0 else
    (a m * star (a n) *
      (∫ t in (1 : ℝ)..T, ((↑(m + 1) : ℂ) / (↑(n + 1) : ℂ)) ^ (-(Complex.I * (t : ℂ))))).re

/-- Pointwise bound used for off-diagonal terms in the Dirichlet-polynomial mean-square decomposition. -/
def offDiagBoundTerm (a : ℕ → ℂ) (m n : ℕ) : ℝ :=
  if m = n then 0 else
    2 * ‖a m‖ * ‖a n‖ / |Real.log ((↑(m + 1) : ℝ) / (↑(n + 1) : ℝ))|

/-- Rewrite `((m/n)^(-it))` as a complex exponential with real frequency. -/
lemma ratio_cpow_negI_eq_exp (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    ((m : ℂ) / (n : ℂ)) ^ (-(Complex.I * (t : ℂ))) =
      Complex.exp (Complex.I * (t : ℂ) * Real.log ((n : ℝ) / (m : ℝ))) := by
  have hmn0 : ((m : ℂ) / (n : ℂ)) ≠ 0 := by
    exact div_ne_zero (Nat.cast_ne_zero.mpr hm.ne') (Nat.cast_ne_zero.mpr hn.ne')
  rw [Complex.cpow_def_of_ne_zero hmn0]
  have hlog : Complex.log ((m : ℂ) / (n : ℂ)) = (Real.log ((m : ℝ) / (n : ℝ)) : ℂ) := by
    change Complex.log (((m : ℝ) / (n : ℝ)) : ℂ) = (Real.log ((m : ℝ) / (n : ℝ)) : ℂ)
    have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast (Nat.zero_le m)
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
    simpa using (Complex.ofReal_log (div_nonneg hm0 hn0)).symm
  rw [hlog]
  have hlog_inv : (Real.log ((n : ℝ) / (m : ℝ)) : ℂ) =
      -(Real.log ((m : ℝ) / (n : ℝ)) : ℂ) := by
    norm_cast
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity)]
    ring
  have hlog_inv_real : Real.log ((n : ℝ) / (m : ℝ)) = -Real.log ((m : ℝ) / (n : ℝ)) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity)]
    ring
  calc
    Complex.exp ((Real.log ((m : ℝ) / (n : ℝ)) : ℂ) * (-(Complex.I * (t : ℂ))))
      = Complex.exp ((-(Real.log ((m : ℝ) / (n : ℝ)) : ℂ)) * (Complex.I * (t : ℂ))) := by
          congr 1
          ring
    _ = Complex.exp ((Real.log ((n : ℝ) / (m : ℝ)) : ℂ) * (Complex.I * (t : ℂ))) := by
          simp [hlog_inv_real]
    _ = Complex.exp (Complex.I * (t : ℂ) * Real.log ((n : ℝ) / (m : ℝ))) := by
          congr 1
          ring

/-- Off-diagonal integral bound: the oscillatory kernel is bounded by `2/|log(m/n)|`. -/
theorem off_diagonal_integral_bound (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmn : m ≠ n) (T : ℝ) (hT : T ≥ 1) :
    ‖∫ t in (1 : ℝ)..T, ((m : ℂ) / (n : ℂ)) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 2 / |Real.log ((m : ℝ) / (n : ℝ))| := by
  calc
    ‖∫ t in (1 : ℝ)..T, ((m : ℂ) / (n : ℂ)) ^ (-(Complex.I * (t : ℂ)))‖
      = ‖∫ t in (1 : ℝ)..T,
          Complex.exp (Complex.I * (t : ℂ) * Real.log ((n : ℝ) / (m : ℝ)))‖ := by
          refine congrArg norm ?_
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun t ht => ratio_cpow_negI_eq_exp m n hm hn t)
    _ = ‖∫ t in Set.Ioc 1 T,
          Complex.exp (Complex.I * (t : ℂ) * Real.log ((n : ℝ) / (m : ℝ)))‖ := by
          rw [intervalIntegral.integral_of_le hT]
    _ ≤ 2 / |Real.log ((n : ℝ) / (m : ℝ))| := by
          exact MeanSquarePartialSumAsymptotic.integral_exp_log_bound m n hm hn hmn T hT
    _ = 2 / |Real.log ((m : ℝ) / (n : ℝ))| := by
          have hlog_swap : Real.log ((n : ℝ) / (m : ℝ)) = -Real.log ((m : ℝ) / (n : ℝ)) := by
            rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity)]
            ring
          rw [hlog_swap, abs_neg]

/-- Diagonal integral: `‖n^{-it}‖ = 1`, hence the integral equals `T - 1`. -/
theorem diagonal_integral (n : ℕ) (hn : 0 < n) (T : ℝ) (_hT : T ≥ 1) :
    ∫ t in (1 : ℝ)..T, ‖((n : ℂ) ^ (-(Complex.I * (t : ℂ))))‖^2 = T - 1 := by
  have hconst :
      (fun t : ℝ => ‖((n : ℂ) ^ (-(Complex.I * (t : ℂ))))‖^2) = fun _ : ℝ => (1 : ℝ) := by
    funext t
    have hnorm :
        ‖((n : ℂ) ^ (-(Complex.I * (t : ℂ))))‖
          = (n : ℝ) ^ (Complex.re (-(Complex.I * (t : ℂ)))) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < n by exact_mod_cast hn)
        (-(Complex.I * (t : ℂ)))
    rw [hnorm]
    simp
  calc
    ∫ t in (1 : ℝ)..T, ‖((n : ℂ) ^ (-(Complex.I * (t : ℂ))))‖^2
      = ∫ t in (1 : ℝ)..T, (1 : ℝ) := by simpa [hconst]
    _ = T - 1 := by simp

/--
Mean-square decomposition for finite Dirichlet polynomials, assuming a finite-sum expansion into diagonal and
off-diagonal terms.

This keeps the oscillatory kernel bounds proved in this file reusable while separating out the algebraic
expansion step.
-/
theorem dirichlet_poly_mean_square
    (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : T ≥ 1)
    (h_expand :
      (∫ t in (1 : ℝ)..T, ‖dirPoly N a t‖^2) =
        (T - 1) * (Finset.sum (Finset.range N) (fun n => ‖a n‖^2)) +
          Finset.sum (Finset.range N) (fun m =>
            Finset.sum (Finset.range N) (fun n => offDiagTerm a T m n)) ) :
    ∃ E : ℝ,
      |E| ≤ Finset.sum (Finset.range N) (fun m =>
        Finset.sum (Finset.range N) (fun n => offDiagBoundTerm a m n)) ∧
      (∫ t in (1 : ℝ)..T, ‖dirPoly N a t‖^2) =
        (T - 1) * (Finset.sum (Finset.range N) (fun n => ‖a n‖^2)) + E := by
  let E : ℝ :=
    Finset.sum (Finset.range N) (fun m =>
      Finset.sum (Finset.range N) (fun n => offDiagTerm a T m n))
  refine ⟨E, ?_, ?_⟩
  · have h_abs_sum₁ :
      |E| ≤ Finset.sum (Finset.range N) (fun m =>
        |Finset.sum (Finset.range N) (fun n => offDiagTerm a T m n)|) := by
      simpa [E] using
        (abs_sum_le_sum_abs
          (s := Finset.range N)
          (f := fun m : ℕ =>
            Finset.sum (Finset.range N) (fun n => offDiagTerm a T m n)))
    have h_abs_sum₂ :
      Finset.sum (Finset.range N) (fun m =>
          |Finset.sum (Finset.range N) (fun n => offDiagTerm a T m n)|)
        ≤ Finset.sum (Finset.range N) (fun m =>
            Finset.sum (Finset.range N) (fun n => |offDiagTerm a T m n|)) := by
      refine sum_le_sum (fun m hm => ?_)
      exact abs_sum_le_sum_abs (s := Finset.range N) (f := fun n : ℕ => offDiagTerm a T m n)
    refine le_trans h_abs_sum₁ ?_
    refine le_trans h_abs_sum₂ ?_
    refine sum_le_sum (fun m hm => ?_)
    refine sum_le_sum (fun n hn => ?_)
    by_cases hmn : m = n
    · simp [offDiagTerm, offDiagBoundTerm, hmn]
    · have hkernel :
        ‖∫ t in (1 : ℝ)..T,
            ((↑(m + 1) : ℂ) / (↑(n + 1) : ℂ)) ^ (-(Complex.I * (t : ℂ)))‖
          ≤ 2 / |Real.log ((↑(m + 1) : ℝ) / (↑(n + 1) : ℝ))| := by
        exact off_diagonal_integral_bound (m + 1) (n + 1) (Nat.succ_pos _) (Nat.succ_pos _)
          (Nat.succ_ne_succ_iff.mpr hmn) T hT
      have hnorm_mul :
        ‖a m * star (a n) *
            (∫ t in (1 : ℝ)..T,
              ((↑(m + 1) : ℂ) / (↑(n + 1) : ℂ)) ^ (-(Complex.I * (t : ℂ))))‖
          ≤ ‖a m‖ * ‖a n‖ *
              (2 / |Real.log ((↑(m + 1) : ℝ) / (↑(n + 1) : ℝ))|) := by
        calc
          ‖a m * star (a n) *
              (∫ t in (1 : ℝ)..T,
                ((↑(m + 1) : ℂ) / (↑(n + 1) : ℂ)) ^ (-(Complex.I * (t : ℂ))))‖
            = ‖a m‖ * ‖a n‖ *
                ‖∫ t in (1 : ℝ)..T,
                    ((↑(m + 1) : ℂ) / (↑(n + 1) : ℂ)) ^ (-(Complex.I * (t : ℂ)))‖ := by
                simp [norm_mul, mul_assoc, mul_left_comm, mul_comm]
          _ ≤ ‖a m‖ * ‖a n‖ *
                (2 / |Real.log ((↑(m + 1) : ℝ) / (↑(n + 1) : ℝ))|) := by
                gcongr
      have h_re :
        |(a m * star (a n) *
            (∫ t in (1 : ℝ)..T,
              ((↑(m + 1) : ℂ) / (↑(n + 1) : ℂ)) ^ (-(Complex.I * (t : ℂ))))).re|
          ≤ ‖a m * star (a n) *
              (∫ t in (1 : ℝ)..T,
                ((↑(m + 1) : ℂ) / (↑(n + 1) : ℂ)) ^ (-(Complex.I * (t : ℂ))))‖ := by
        exact Complex.abs_re_le_norm _
      calc
        |offDiagTerm a T m n|
            = |(a m * star (a n) *
                (∫ t in (1 : ℝ)..T,
                  ((↑(m + 1) : ℂ) / (↑(n + 1) : ℂ)) ^ (-(Complex.I * (t : ℂ))))).re| := by
                simp [offDiagTerm, hmn]
        _ ≤ ‖a m * star (a n) *
              (∫ t in (1 : ℝ)..T,
                ((↑(m + 1) : ℂ) / (↑(n + 1) : ℂ)) ^ (-(Complex.I * (t : ℂ))))‖ := h_re
        _ ≤ ‖a m‖ * ‖a n‖ *
              (2 / |Real.log ((↑(m + 1) : ℝ) / (↑(n + 1) : ℝ))|) := hnorm_mul
        _ = 2 * ‖a m‖ * ‖a n‖ / |Real.log ((↑(m + 1) : ℝ) / (↑(n + 1) : ℝ))| := by ring
        _ = offDiagBoundTerm a m n := by
              simp [offDiagBoundTerm, hmn]
  · simpa [E] using h_expand

end Aristotle.DirichletPolynomialMVT
