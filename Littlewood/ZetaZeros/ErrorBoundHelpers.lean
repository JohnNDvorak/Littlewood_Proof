/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.Chebyshev

/-!
# Helper lemmas for the Chebyshev error bound proof

Real analysis helper lemmas used in deriving the PNT error bound
|ψ(x) - x| ≤ C·x·exp(-c·√(log x)) from the zero-free region.
-/

open Real

namespace ChebyshevErrorBound

/-- For x ≥ 0, exp(x) ≥ x²/2. Follows from the Taylor series of exp. -/
lemma exp_ge_sq_div_two {x : ℝ} (hx : 0 ≤ x) : x ^ 2 / 2 ≤ Real.exp x := by
  have := Real.sum_le_exp_of_nonneg hx 3
  norm_num [Finset.sum_range_succ] at this
  nlinarith

/-- The function u ↦ u² · exp(-α·u) achieves max 4/(α²·e²) at u = 2/α. -/
lemma sq_mul_exp_neg_le {α : ℝ} (hα : 0 < α) (u : ℝ) (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-α * u) ≤ 4 / (α ^ 2 * Real.exp 2) := by
  suffices h_v : ∀ v : ℝ, 0 ≤ v → v ^ 2 * Real.exp (2 - v) ≤ 4 by
    field_simp
    convert h_v (u * α) (mul_nonneg hu hα.le) using 1
    rw [mul_assoc, ← Real.exp_add]; ring
  intro v hv
  have h_exp : Real.exp (v - 2) ≥ (v / 2) ^ 2 := by
    have h_exp : Real.exp (v - 2) = (Real.exp ((v - 2) / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring
    exact h_exp.symm ▸ pow_le_pow_left₀ (by positivity)
      (by linarith [Real.add_one_le_exp ((v - 2) / 2)]) _
  rw [show 2 - v = -(v - 2) by ring, Real.exp_neg]
  nlinarith [Real.exp_pos (v - 2), mul_inv_cancel₀ (ne_of_gt (Real.exp_pos (v - 2)))]

/-- The function u ↦ u⁴ · exp(-α·u) achieves max 256/(α⁴·e⁴) at u = 4/α. -/
lemma pow4_mul_exp_neg_le {α : ℝ} (hα : 0 < α) (u : ℝ) (hu : 0 ≤ u) :
    u ^ 4 * Real.exp (-α * u) ≤ 256 / (α ^ 4 * Real.exp 4) := by
  have h_unbounded : (α * u) ^ 4 * Real.exp (-α * u) ≤ 4 ^ 4 * Real.exp (-4) := by
    suffices h_div : (α * u) ^ 4 ≤ 4 ^ 4 * Real.exp (α * u - 4) by
      exact le_trans (mul_le_mul_of_nonneg_right h_div <| Real.exp_nonneg _) <|
        by rw [mul_assoc, ← Real.exp_add]; ring_nf; norm_num
    suffices h_root : (α * u) ≤ 4 * Real.exp ((α * u - 4) / 4) by
      exact le_trans (pow_le_pow_left₀ (by positivity) h_root 4)
        (by rw [mul_pow, ← Real.exp_nat_mul]; ring_nf; norm_num)
    linarith [Real.add_one_le_exp ((α * u - 4) / 4)]
  rw [le_div_iff₀ (by positivity)]
  convert mul_le_mul_of_nonneg_right h_unbounded (show 0 ≤ Real.exp 4 by positivity) using 1
    <;> ring
    <;> norm_num [← Real.exp_add]

/-- For u ≥ log 4, exp(u) - 2 ≥ exp(u)/2. -/
lemma exp_sub_two_ge_half_exp {u : ℝ} (hu : Real.log 4 ≤ u) :
    Real.exp u / 2 ≤ Real.exp u - 2 := by
  linarith [Real.log_le_iff_le_exp (by norm_num) |>.1 hu]

/-
PROBLEM
Crude bound: |ψ(x) - x| ≤ 3x for x ≥ 1.
Uses Chebyshev.psi_nonneg and Chebyshev.psi_le.

PROVIDED SOLUTION
Use abs_le and split into two parts. Left: -(3*x) ≤ ψ(x) - x iff 0 ≤ ψ(x) + 2*x, which holds since ψ(x) ≥ 0 (Chebyshev.psi_nonneg) and x ≥ 0. Right: ψ(x) - x ≤ 3*x iff ψ(x) ≤ 4*x. From Chebyshev.psi_le hx: ψ(x) ≤ log(4)*x + 2*√x*log(x). We need log(4)*x + 2*√x*log(x) ≤ 4*x, i.e., 2*√x*log(x) ≤ (4 - log 4)*x. Since log 4 < 2 (because 4 < e²), 4 - log 4 > 2. So need 2*√x*log(x) ≤ 2*x, i.e., log(x) ≤ √x. This follows from: for x ≥ 1, log(x) ≤ √x (since log_le_sqrt hx which we have as an axiom, or prove inline: exp(√x) ≥ 1 + √x ≥ 1 + log x... no. Use: for t ≥ 0, t ≤ exp(t) implies log(x) ≤ x^{1/2} by substituting t = (log x)/2... Actually just use log x ≤ x - 1 ≤ x ≤ x and √x · log x ≤ √x · √x = x since log x ≤ √x). Actually the easiest approach: use Chebyshev.psi_le to get ψ(x) ≤ log 4 * x + 2 * √x * log x, then bound √x * log x ≤ x (since log x ≤ √x for x ≥ 1, which follows from exp being super-linear: exp(√x) ≥ 1 + √x, and for x ≥ 1, log x ≤ 2*(√x - 1) ≤ 2*√x... hmm. Actually, for x ≥ 1: use Real.add_one_le_exp (√x): √x + 1 ≤ exp(√x). Taking log: log(√x + 1) ≤ √x. And log x = 2*log(√x) ≤ 2*√x (since log t ≤ t for all t > 0). Wait, log t ≤ t - 1 ≤ t for t ≥ 1. So log(√x) ≤ √x for √x ≥ 1, i.e., x ≥ 1. Then log x = 2 log(√x) ≤ 2√x. So √x * log x ≤ √x * 2√x = 2x. Therefore ψ(x) ≤ log 4 * x + 2 * 2x = (log 4 + 4)x. Since log 4 + 4 < 6, ψ(x) ≤ 6x. Then |ψ(x) - x| ≤ max(5x, x) = 5x ≤ 3x? No, 5x > 3x. I need a tighter bound. Let me reconsider. Actually √x * log x ≤ x. Proof: log x ≤ √x for x ≥ 1. For this: set u = √x ≥ 1. Need log(u²) ≤ u, i.e., 2 log u ≤ u. For u ≥ 1: log u ≤ u - 1 (since log t ≤ t - 1 for all t > 0, and u ≥ 1 implies log u ≥ 0). So 2 log u ≤ 2(u-1) ≤ 2u. But we need 2 log u ≤ u. Since log u ≤ u - 1 and u ≥ 1, 2 log u ≤ 2(u-1). For u ≥ 2: 2(u-1) ≤ u*2 - 2 ≤ 2u, but we need ≤ u. 2(u-1) = 2u - 2 ≤ u iff u ≤ 2. So for u > 2 (i.e., x > 4) this fails with 2 log u ≤ 2(u-1). Hmm. Actually for u ≥ 1: we want 2 log u ≤ u. At u=1: 0 ≤ 1 ✓. Derivative of u - 2 log u: 1 - 2/u, which is > 0 for u > 2 and < 0 for u < 2. Minimum at u=2: 2 - 2 log 2 ≈ 2 - 1.386 = 0.614 > 0. So u - 2 log u > 0 for all u ≥ 1. ✓. OK so log x = 2 log √x ≤ √x. Then √x * log x ≤ √x * √x = x. Then ψ(x) ≤ log 4 * x + 2x = (log 4 + 2)x ≈ 3.386x. And |ψ(x) - x| = max(ψ(x) - x, x - ψ(x)). If ψ(x) ≥ x: ψ(x) - x ≤ (log 4 + 2)x - x = (log 4 + 1)x < 3x (since log 4 < 2). If ψ(x) < x: x - ψ(x) ≤ x ≤ 3x. So |ψ(x) - x| ≤ 3x. ✓
-/
lemma chebyshev_psi_crude_bound {x : ℝ} (hx : 1 ≤ x) :
    |Chebyshev.psi x - x| ≤ 3 * x := by
      rw [ abs_le ];
      constructor <;> have := Chebyshev.psi_le hx <;> have := Chebyshev.psi_nonneg x <;> norm_num at *;
      · linarith;
      · -- We'll use that $\sqrt{x} \log x \leq x$ for $x \geq 1$.
        have h_sqrt_log : Real.sqrt x * Real.log x ≤ x := by
          have h_sqrt_log : Real.log x ≤ Real.sqrt x := by
            have := Real.log_le_sub_one_of_pos (by positivity : 0 < Real.sqrt x / 2)
            rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] at this ; linarith [ Real.log_le_sub_one_of_pos zero_lt_two ] ;
          nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by positivity ) ];
        rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] at * ; norm_num at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two ] ;

/-
PROBLEM
log x ≤ √x for x ≥ 1.

PROVIDED SOLUTION
Set u = √x, so u ≥ 1 (since x ≥ 1). We need log(u²) ≤ u, i.e., 2*log(u) ≤ u. Since u ≥ 1, we have log(u) ≤ u - 1 (from Real.log_le_sub_one_of_le). So 2*log(u) ≤ 2*(u-1) = 2u - 2. We need 2u - 2 ≤ u, i.e., u ≤ 2. This only works for u ≤ 2. For general u ≥ 1, use the fact that the function f(u) = u - 2*log(u) has f'(u) = 1 - 2/u which is 0 at u = 2, and f(2) = 2 - 2*log(2) > 0 (since log 2 < 1). Since f achieves its minimum at u = 2 with f(2) > 0, f(u) > 0 for all u > 0.

Alternative approach: use Real.add_one_le_exp applied to √x / 2: √x/2 + 1 ≤ exp(√x/2). Then (√x/2 + 1)² ≤ exp(√x). So exp(√x) ≥ x/4 + √x + 1 ≥ x/4. Hmm this doesn't directly give log x ≤ √x.

Cleaner: log x ≤ √x iff x ≤ exp(√x). Set t = √x ≥ 1. Need t² ≤ exp(t). From exp_ge_sq_div_two: t²/2 ≤ exp(t). So t² ≤ 2*exp(t). But we need t² ≤ exp(t), which is stronger. From add_one_le_exp: 1 + t ≤ exp(t). For t ≥ 1: t² ≤ t*t = t*(1+t-1) ≤ ... hmm. Actually use exp_ge_sq_div_two with x = t: t²/2 ≤ exp(t). For t ≥ 0, exp(t) ≥ 1 + t, and for t ≥ 2: exp(t) ≥ 1 + t + t²/2 ≥ t²/2. We need t² ≤ exp(t). Use: exp(t/2) ≥ 1 + t/2, so exp(t) = exp(t/2)² ≥ (1 + t/2)² = 1 + t + t²/4 ≥ t²/4. For t ≥ 2: t²/4 ≥ t²/t² * ... no. Actually we need t² ≤ exp(t). For t ≥ 0, exp(t) ≥ 1 + t + t²/2 + t³/6 (from sum_le_exp with n=4). For t ≥ 2: t³/6 ≥ t² * 2/6 = t²/3. So exp(t) ≥ t²/2 + t²/3 = 5t²/6 ≥ t² for t ≥ 2 (since 5/6 < 1, this isn't enough). Hmm. For t ≥ 5: exp(t) ≥ t⁵/120 ≥ t² * t³/120. For t ≥ 5: t³/120 ≥ 125/120 > 1, so exp(t) ≥ t². For 1 ≤ t ≤ 5: check numerically that t² ≤ exp(t). At t=1: 1 vs e ≈ 2.718 ✓. At t=2: 4 vs e² ≈ 7.389 ✓. At t=3: 9 vs e³ ≈ 20.09 ✓. At t=5: 25 vs e⁵ ≈ 148.4 ✓. So it's always true but proving it in Lean requires some care.

Actually, simplest approach: from Real.rpow_le_exp_mul_rpow or use log x = 2 * log(√x) and log(√x) ≤ √x - 1 ≤ √x/2 when √x ≥ 2. Hmm.

Try: since we proved exp_ge_sq_div_two (t²/2 ≤ exp t), for t = √x: x/2 ≤ exp(√x). Taking log: log(x/2) ≤ √x, i.e., log x - log 2 ≤ √x. So log x ≤ √x + log 2. Not quite enough (need ≤ √x not ≤ √x + log 2).

OK best approach for Lean: log x ≤ √x is equivalent to x ≤ exp(√x). From the Taylor bound with n=3: exp(√x) ≥ 1 + √x + x/2 ≥ x/2 + √x ≥ x for x ≥ 2√x, i.e., √x ≥ 2, i.e., x ≥ 4. For x ∈ [1, 4]: log x ≤ log 4 < 2 ≤ √4 = 2 ≤ √x... wait √1 = 1 and log 1 = 0 ≤ 1 ✓. √2 ≈ 1.414, log 2 ≈ 0.693 ✓. √3 ≈ 1.732, log 3 ≈ 1.099 ✓. √4 = 2, log 4 ≈ 1.386 ✓. So it works for [1,4] too. Formal proof for [1,4]: log x ≤ x - 1 ≤ x ≤ x. And √x ≥ 1 for x ≥ 1, log x ≤ x - 1 for x ≥ 1. For x ≤ 4: x - 1 ≤ 3 and √x ≥ 1... not sufficient. For x ∈ [1,4]: log x ≤ x - 1 and we need x - 1 ≤ √x. (x-1)² ≤ x iff x² - 3x + 1 ≤ 0 iff x ∈ [(3-√5)/2, (3+√5)/2] ≈ [0.382, 2.618]. So for x > 2.618, x - 1 > √x. So this approach fails for x ∈ (2.618, 4). We'd need a different bound for that range. This is getting complicated. Let me just have the subagent try.
-/
lemma log_le_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.sqrt x := by
  have := Real.log_le_sub_one_of_pos ( show 0 < Real.sqrt x / 2 by positivity );
  rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] at this ; linarith [ Real.log_le_sub_one_of_pos zero_lt_two ]

end ChebyshevErrorBound
