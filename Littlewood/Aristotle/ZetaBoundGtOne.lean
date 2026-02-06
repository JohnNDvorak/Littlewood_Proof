import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 3200000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.ZetaBoundGtOne

/-
Bound for the Riemann Zeta function to the right of the critical strip.
-/
theorem zeta_bound_gt_one (δ : ℝ) (hδ : 0 < δ) :
    ∀ t : ℝ, ‖riemannZeta (1 + δ + t * Complex.I)‖ ≤ ‖riemannZeta (1 + δ)‖ := by
      intro t
      have h_sum : ‖riemannZeta (1 + δ + t * Complex.I)‖ ≤ ∑' n : ℕ, (1 : ℝ) / (n + 1 : ℝ) ^ (1 + δ) := by
        -- By definition of the Riemann zeta function, we know that
        have h_zeta_def : riemannZeta (1 + δ + t * Complex.I) = ∑' n : ℕ, (1 : ℂ) / (n + 1 : ℂ) ^ (1 + δ + t * Complex.I) := by
          have := @zeta_eq_tsum_one_div_nat_add_one_cpow ( 1 + δ + t * Complex.I );
          exact this ( by norm_num; linarith );
        refine' h_zeta_def ▸ le_trans ( norm_tsum_le_tsum_norm _ ) _;
        · -- We'll use the fact that |(n + 1 : ℂ) ^ (1 + δ + t * Complex.I)| = (n + 1) ^ (1 + δ).
          have h_abs : ∀ n : ℕ, ‖(n + 1 : ℂ) ^ (1 + δ + t * Complex.I)‖ = (n + 1 : ℝ) ^ (1 + δ) := by
            intro n; rw [ Complex.norm_cpow_of_ne_zero ] <;> norm_cast ; norm_num;
          simpa [ h_abs ] using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_rpow.2 <| by linarith;
        · norm_num [ Complex.norm_cpow_of_ne_zero, Nat.cast_add_one_ne_zero ];
          norm_cast ; norm_num [ Complex.arg ]
      have h_sum_eq : ∑' n : ℕ, (1 : ℝ) / (n + 1 : ℝ) ^ (1 + δ) = ‖riemannZeta (1 + δ)‖ := by
        have h_sum_eq : ∑' n : ℕ, (1 : ℝ) / (n + 1 : ℝ) ^ (1 + δ) = riemannZeta (1 + δ) := by
          have h_eq : ∀ s : ℝ, 1 < s → ∑' n : ℕ, (1 : ℝ) / (n + 1 : ℝ) ^ s = riemannZeta s := by
            intro s hs; rw [ zeta_eq_tsum_one_div_nat_add_one_cpow ] ; norm_cast;
            · convert Complex.ofReal_tsum _ ; norm_num [ Complex.ofReal_cpow ( add_nonneg ( Nat.cast_nonneg _ ) zero_le_one ) ];
            · exact_mod_cast hs
          simpa using h_eq ( 1 + δ ) ( by linarith );
        rw [ ← h_sum_eq, Complex.norm_of_nonneg ( tsum_nonneg fun _ => by positivity ) ]
      aesop

end Aristotle.ZetaBoundGtOne

end
