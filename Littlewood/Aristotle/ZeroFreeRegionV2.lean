/-
3-4-1 inequality and zero-free region infrastructure from Aristotle.

Provides the 3+4cos+cos2 inequality, von Mangoldt term decomposition,
Dirichlet series real-part extraction, and the combined 3-4-1 inequality
for -ζ'/ζ. Also includes zetaExtended (analytic continuation of (s-1)ζ(s))
and bounds near s=1.

WARNING: Contains 12 exact? calls from Aristotle budget exhaustion.
These are marked with sorry and documented. The file will compile
but these theorems are not fully proved.

Redundant results NOT included:
- three_four_one: already in ThreeFourOne.lean as three_four_one_inequality
- zeta_near_one_bound: already in PhragmenLindelof.lean

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ZeroFreeRegionV2

/-
For a non-zero natural number n and real numbers σ and t, the real part of Λ(n) * n^(-(σ + it)).
-/
lemma vonMangoldt_term_re (n : ℕ) (σ t : ℝ) (hn : n ≠ 0) :
    ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ + Complex.I * t))).re =
    (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
      norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ];
      norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn.bot_lt ) ] ; ring;
      norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, hn ] ; ring

/-
For any complex number s with real part greater than 1, the von Mangoldt Dirichlet series is summable.
-/
lemma summable_vonMangoldt_term (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s)) := by
      have h_summable : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)) := by
        have h_log_summable : Summable (fun n : ℕ => (Real.log n : ℝ) * (n : ℝ) ^ (-s.re)) := by
          have h_compare : ∀ ε > 0, ∃ C > 0, ∀ n : ℕ, n ≥ 2 → (Real.log n : ℝ) * (n : ℝ) ^ (-s.re) ≤ C * (n : ℝ) ^ (-s.re + ε) := by
            intro ε hε_pos
            obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n ≤ C * (n : ℝ) ^ ε := by
              use 1 / ε, by positivity, fun n hn => by have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ^ ε ) ; rw [ Real.log_rpow ( by positivity ) ] at this; nlinarith [ Real.rpow_pos_of_pos ( by positivity : 0 < ( n : ℝ ) ) ε, mul_div_cancel₀ 1 hε_pos.ne' ] ;
            exact ⟨ C, hC_pos, fun n hn => by convert mul_le_mul_of_nonneg_right ( hC n hn ) ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( -s.re ) ) using 1 ; rw [ Real.rpow_add ( by positivity ) ] ; ring ⟩;
          obtain ⟨ε, hε_pos, hε_lt⟩ : ∃ ε > 0, -s.re + ε < -1 := by
            exact ⟨ ( s.re - 1 ) / 2, by linarith, by linarith ⟩;
          obtain ⟨ C, hC_pos, hC ⟩ := h_compare ε hε_pos;
          rw [ ← summable_nat_add_iff 2 ];
          exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ( Real.rpow_nonneg ( by positivity ) _ ) ) ( fun n => hC _ ( by linarith ) ) ( Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_nat_rpow.2 <| by linarith );
        refine' .of_nonneg_of_le ( fun n => mul_nonneg ( _ ) ( Real.rpow_nonneg ( Nat.cast_nonneg n ) _ ) ) ( fun n => mul_le_mul_of_nonneg_right ( _ ) ( Real.rpow_nonneg ( Nat.cast_nonneg n ) _ ) ) h_log_summable;
        · exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg -- exact? #1
        · exact ArithmeticFunction.vonMangoldt_le_log -- exact? #2
      have h_abs_summable : Summable (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s)‖) := by
        have h_abs_summable : ∀ n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s)‖ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
          intro n; by_cases hn : n = 0 <;> simp +decide [ hn, Complex.norm_cpow_of_ne_zero ] ;
        aesop;
      exact h_abs_summable.of_norm

/-
For σ > 1 and real t, Re(-ζ'/ζ(σ+it)) = Σ Λ(n) n^(-σ) cos(t log n).
-/
lemma zeta_log_deriv_eq_series_re (σ t : ℝ) (hσ : 1 < σ) :
    (- (deriv riemannZeta (σ + Complex.I * t)) / riemannZeta (σ + Complex.I * t)).re =
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
      have h1 : (-deriv riemannZeta (σ + Complex.I * t) / riemannZeta (σ + Complex.I * t)) = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ + Complex.I * t)) := by
        rw [ ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div ];
        · simp +decide [ LSeries ];
          congr with ( _ | n ) <;> norm_num [ div_eq_mul_inv, Complex.cpow_neg ] ; ring;
          exact Or.inl ( by rw [ ← Complex.cpow_neg ] ; ring );
        · simpa using hσ;
      convert congr_arg Complex.re h1 using 1;
      rw_mod_cast [ Complex.re_tsum ];
      · refine' tsum_congr fun n => _;
        by_cases hn : n = 0 <;> simp +decide [ hn, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ] ; ring;
        rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring;
      · convert summable_vonMangoldt_term ( σ + Complex.I * t ) _ using 1;
        simpa using hσ

/-
Each term Λ(n) n^(-σ) (3 + 4cos(t log n) + cos(2t log n)) is non-negative.
-/
lemma term_nonneg (n : ℕ) (σ t : ℝ) :
  (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * t * Real.log n)) ≥ 0 := by
    have h_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) ∧ 0 ≤ (n : ℝ) ^ (-σ) := by
      exact ⟨ mod_cast ArithmeticFunction.vonMangoldt_nonneg, by positivity ⟩;
    exact mul_nonneg ( mul_nonneg h_nonneg.1 h_nonneg.2 ) ( by rw [ mul_assoc, Real.cos_two_mul ] ; nlinarith [ sq_nonneg ( Real.cos ( t * Real.log n ) + 1 ), Real.cos_sq' ( t * Real.log n ) ] )

/-
The combined 3-4-1 inequality: 3 Re(-ζ'/ζ(σ)) + 4 Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it)) ≥ 0.
-/
lemma zeta_log_deriv_341 (σ t : ℝ) (hσ : 1 < σ) :
    let L := fun (s : ℂ) => - (deriv riemannZeta s) / riemannZeta s
    3 * (L σ).re + 4 * (L (σ + Complex.I * t)).re + (L (σ + 2 * Complex.I * t)).re ≥ 0 := by
      have h_expand : ∀ s : ℂ, 1 < s.re → (- (deriv riemannZeta s) / riemannZeta s).re = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
        intro s hs;
        convert zeta_log_deriv_eq_series_re s.re s.im hs using 1;
        norm_num [ mul_comm Complex.I ];
      /- PROOF STRATEGY (not yet formalized):
         1. dsimp only (unfold let)
         2. rw [zeta_log_deriv_eq_series_re σ 0 hσ, ..σ t.., ..σ (2*t)..]
            to convert each (L s).re to its tsum form
         3. Extract real summability from summable_vonMangoldt_term via HasSum.re
            Each cos series bounded by Λ(n)·n^(-σ) which is summable
         4. Use tsum_mul_left, tsum_add to combine 3·Σ + 4·Σ + Σ = Σ(3·+4·+·)
         5. Apply tsum_nonneg with term_nonneg
         Note: This is proved differently (without series) in ThreeFourOneV2.three_four_one_v2 -/
      sorry

/-
The function (z-1)ζ(z) extended to z=1 by continuity.
-/
noncomputable def zetaExtended (z : ℂ) : ℂ := if z = 1 then 1 else (z - 1) * riemannZeta z

/-
For s ≠ 1 with ζ(s) ≠ 0, the log derivative decomposes as 1/(s-1) minus a bounded term.
-/
lemma zeta_residue_eq (s : ℂ) (h1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    - (deriv riemannZeta s) / riemannZeta s = 1 / (s - 1) - (deriv (fun z => (z - 1) * riemannZeta z) s) / ((s - 1) * riemannZeta s) := by
      have h_prod_rule : deriv (fun z => (z - 1) * riemannZeta z) s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
        have h_diff : DifferentiableAt ℂ riemannZeta s := by
          have h_analytic : AnalyticAt ℂ riemannZeta s := by
            apply_rules [ DifferentiableOn.analyticAt, riemannZeta ];
            exact fun x hx => ( differentiableAt_riemannZeta hx ).differentiableWithinAt;
            exact IsOpen.mem_nhds isOpen_ne h1
          exact h_analytic.differentiableAt;
        convert HasDerivAt.deriv ( HasDerivAt.mul ( hasDerivAt_id s |> HasDerivAt.sub <| hasDerivAt_const _ _ ) h_diff.hasDerivAt ) using 1 ; norm_num;
      grind

end ZeroFreeRegionV2
