# Aristotle Prompt A (Ultra Self-Contained, No Repo Access)

You are solving one deep Lean sorry with **zero access to our repository**.
Everything you need is below: full target file context and full transitive local dependency closure.

## Task
Complete **`digamma_log_bound_atomic`** with no `axiom`, `admit`, or `sorry`, preserving the declaration signature exactly.

## Output Requirements
1. Return Lean code that replaces the `sorry` in `digamma_log_bound_atomic`.
2. If helper lemmas are needed, include complete Lean code for them in the same response.
3. Do not require any external files not present in this prompt.
4. Keep namespace/import assumptions consistent with provided code.

## Version Contract
- Lean 4 + Mathlib 4 environment.
- No project-local file access beyond the code pasted in this prompt.

## Target File
- `Littlewood/Aristotle/DigammaBinetBound.lean`

## Target Declaration Snippet (from target file)
```lean
    _ = ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := rfl

lemma tendsto_logDeriv_GammaSeq_of_locallyUniform
    {U : Set ℂ} (hU : IsOpen U) (x : U)
    (hconv : TendstoLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => Complex.GammaSeq z n) Gamma Filter.atTop U)
    (hdiff : ∀ᶠ n : ℕ in Filter.atTop,
      DifferentiableOn ℂ (fun z : ℂ => Complex.GammaSeq z n) U)
    (hGamma : Gamma x ≠ 0) :
    Filter.Tendsto
      (fun n : ℕ => deriv (fun z : ℂ => Complex.GammaSeq z n) x / Complex.GammaSeq x n)
      Filter.atTop (nhds (deriv Gamma x / Gamma x)) := by
  simpa [logDeriv] using
    (Complex.logDeriv_tendsto hU x hconv hdiff hGamma)

-- ============================================================
-- Main theorem
-- ============================================================

/-- **Atomic sorry**: Binet/digamma bound on a right half-strip away from the real axis. -/
theorem digamma_log_bound_atomic :
    ∃ C > 0, ∀ s : ℂ, s.re ≥ 1/4 → |s.im| ≥ 1 →
      Gamma s ≠ 0 →
      ‖deriv Gamma s / Gamma s - Complex.log s‖ ≤ C / ‖s‖ := by
  sorry

end Aristotle.DigammaBinetBound
```

## Local Dependency Closure Included
- File count: 1
- Total bytes: 13622

### Included Local Files (transitive `import Littlewood.*` closure)
- `Littlewood/Aristotle/DigammaBinetBound.lean`

## Full File: `Littlewood/Aristotle/DigammaBinetBound.lean`
```lean
/-
Atomic Binet-style digamma bound used by `DigammaAsymptotic`.

This file isolates the deep analytic step:
  ‖Γ'(s)/Γ(s) - log(s)‖ ≤ C / ‖s‖
on the half-strip `Re(s) ≥ 1/4`, `|Im(s)| ≥ 1`.

## Strategy (Gauss series)

The Gauss digamma series gives ψ(s) - log(s) = Σ_{j≥0} [log(1+1/(s+j)) - 1/(s+j)].
Each term is bounded by 1/‖s+j‖² (from `norm_log_one_add_sub_self_le`, proved below
as `gauss_term_bound`). The sum Σ 1/‖s+j‖² ≤ C/‖s‖ by AM-GM + comparison
(‖s+j‖² ≥ ‖s‖²+j² ≥ (‖s‖+j)²/2, proved below as `norm_sq_add_natCast_ge`).

The remaining sorry is the Gauss series identity itself, which requires connecting
`GammaSeq_tendsto_Gamma` to derivative convergence via
`TendstoLocallyUniformlyOn.deriv` (Mathlib/Analysis/Complex/LocallyUniformLimit.lean).

SORRY COUNT: 1 (digamma_log_bound_atomic)

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option maxHeartbeats 400000

noncomputable section

namespace Aristotle.DigammaBinetBound

open Complex

-- ============================================================
-- Infrastructure: Term bound for the Gauss series
-- ============================================================

/-- Each term in the Gauss series: ‖log(1+1/w) - 1/w‖ ≤ 1/‖w‖²
    for ‖w‖ ≥ 2. From `norm_log_one_add_sub_self_le` with z = 1/w. -/
lemma gauss_term_bound (w : ℂ) (hw : 2 ≤ ‖w‖) :
    ‖Complex.log (1 + 1/w) - 1/w‖ ≤ 1 / ‖w‖ ^ 2 := by
  have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
  set z : ℂ := 1 / w with hz_def
  have hz_norm : ‖z‖ = 1 / ‖w‖ := by rw [hz_def, norm_div, norm_one]
  have hz_le_half : ‖z‖ ≤ 1 / 2 := by
    rw [hz_norm, div_le_div_iff₀ hw_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hz_lt_one : ‖z‖ < 1 := by linarith
  have h_one_sub_ge : (1 : ℝ) / 2 ≤ 1 - ‖z‖ := by linarith
  have h_inv_le : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = ((1 : ℝ) / 2)⁻¹ from by norm_num]
    exact inv_anti₀ (by linarith) h_one_sub_ge
  calc ‖Complex.log (1 + z) - z‖
      ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := norm_log_one_add_sub_self_le hz_lt_one
    _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        apply div_le_div_of_nonneg_right _ two_pos.le
        exact mul_le_mul_of_nonneg_left h_inv_le (sq_nonneg _)
    _ = ‖z‖ ^ 2 := by ring
    _ = 1 / ‖w‖ ^ 2 := by rw [hz_norm]; ring

-- ============================================================
-- Infrastructure: Norm lower bound for s + j
-- ============================================================

/-- For Re(s) ≥ 0, ‖s + ↑j‖² ≥ ‖s‖² + j².
    Follows from ‖s+j‖² = ‖s‖² + 2j·Re(s) + j² and 2j·Re(s) ≥ 0. -/
lemma norm_sq_add_natCast_ge (s : ℂ) (hs : 0 ≤ s.re) (j : ℕ) :
    ‖s‖ ^ 2 + (j : ℝ) ^ 2 ≤ ‖s + (j : ℂ)‖ ^ 2 := by
  -- Express ‖z‖² = z.re² + z.im² for both sides
  have lhs_eq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply, sq]
  have rhs_eq : ‖s + (j : ℂ)‖ ^ 2 = (s.re + (j : ℝ)) ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, sq]
  rw [lhs_eq, rhs_eq]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith [mul_nonneg hs hj]

lemma two_le_norm_add_natCast_of_strip
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (j : ℕ) (hj : 2 ≤ j) :
    (2 : ℝ) ≤ ‖s + (j : ℂ)‖ := by
  have hsj : (2 : ℝ) ≤ s.re + (j : ℝ) := by
    have hj' : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have habs : (2 : ℝ) ≤ |s.re + (j : ℝ)| := by
    have hsj0 : 0 ≤ s.re + (j : ℝ) := by linarith
    simpa [abs_of_nonneg hsj0] using hsj
  have hnorm : |(s + (j : ℂ)).re| ≤ ‖s + (j : ℂ)‖ := Complex.abs_re_le_norm (s + (j : ℂ))
  simpa [Complex.add_re] using le_trans habs hnorm

lemma gauss_term_bound_add_natCast
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (j : ℕ) (hj : 2 ≤ j) :
    ‖Complex.log (1 + 1 / (s + (j : ℂ))) - 1 / (s + (j : ℂ))‖ ≤
      1 / ‖s + (j : ℂ)‖ ^ 2 := by
  have h2 : (2 : ℝ) ≤ ‖s + (j : ℂ)‖ :=
    two_le_norm_add_natCast_of_strip s hs j hj
  exact gauss_term_bound (s + (j : ℂ)) h2

lemma inv_norm_add_natCast_sq_le_inv_of_strip
    (s : ℂ) (hsre : 0 ≤ s.re) (hsim : 1 ≤ |s.im|) (j : ℕ) :
    1 / ‖s + (j : ℂ)‖ ^ 2 ≤ 1 / (‖s‖ ^ 2 + (j : ℝ) ^ 2) := by
  have hnorm : 1 ≤ ‖s‖ := le_trans hsim (Complex.abs_im_le_norm s)
  have hnorm_pos : (0 : ℝ) < ‖s‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hnorm
  have hden_pos : (0 : ℝ) < ‖s‖ ^ 2 + (j : ℝ) ^ 2 := by positivity
  exact one_div_le_one_div_of_le hden_pos (norm_sq_add_natCast_ge s hsre j)

lemma inv_norm_add_natCast_sq_le_inv_natCast_sq
    (s : ℂ) (hsre : 0 ≤ s.re) (hsim : 1 ≤ |s.im|) {j : ℕ} (hj : 1 ≤ j) :
    1 / ‖s + (j : ℂ)‖ ^ 2 ≤ 1 / (j : ℝ) ^ 2 := by
  have h_step1 : 1 / ‖s + (j : ℂ)‖ ^ 2 ≤ 1 / (‖s‖ ^ 2 + (j : ℝ) ^ 2) :=
    inv_norm_add_natCast_sq_le_inv_of_strip s hsre hsim j
  have hj_nat_pos : 0 < j := lt_of_lt_of_le (by decide : 0 < 1) hj
  have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj_nat_pos
  have hj_sq_pos : (0 : ℝ) < (j : ℝ) ^ 2 := sq_pos_of_pos hj_pos
  have hj_sq_le : (j : ℝ) ^ 2 ≤ ‖s‖ ^ 2 + (j : ℝ) ^ 2 := by
    have hnorm_sq_nonneg : (0 : ℝ) ≤ ‖s‖ ^ 2 := sq_nonneg ‖s‖
    linarith
  have h_step2 : 1 / (‖s‖ ^ 2 + (j : ℝ) ^ 2) ≤ 1 / (j : ℝ) ^ 2 :=
    one_div_le_one_div_of_le hj_sq_pos hj_sq_le
  exact le_trans h_step1 h_step2

lemma gauss_term_bound_by_inv_natCast_sq
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (hsim : 1 ≤ |s.im|) {j : ℕ} (hj : 2 ≤ j) :
    ‖Complex.log (1 + 1 / (s + (j : ℂ))) - 1 / (s + (j : ℂ))‖ ≤ 1 / (j : ℝ) ^ 2 := by
  have hsre : 0 ≤ s.re := by linarith
  have hj1 : 1 ≤ j := le_trans (by norm_num : (1 : ℕ) ≤ 2) hj
  exact le_trans
    (gauss_term_bound_add_natCast s hs j hj)
    (inv_norm_add_natCast_sq_le_inv_natCast_sq s hsre hsim hj1)

lemma summable_gauss_terms_shifted_two
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (hsim : 1 ≤ |s.im|) :
    Summable (fun n : ℕ =>
      ‖Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) -
        1 / (s + ((n + 2 : ℕ) : ℂ))‖) := by
  have hbound : ∀ n : ℕ,
      ‖Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) -
        1 / (s + ((n + 2 : ℕ) : ℂ))‖ ≤
      1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
    intro n
    exact gauss_term_bound_by_inv_natCast_sq s hs hsim (show 2 ≤ n + 2 by omega)
  have hsum : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ 2) := by
    exact (summable_nat_add_iff 2).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsum

lemma one_le_norm_of_abs_im_ge_one (s : ℂ) (hsim : 1 ≤ |s.im|) : 1 ≤ ‖s‖ := by
  exact le_trans hsim (Complex.abs_im_le_norm s)

lemma summable_gauss_terms
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (hsim : 1 ≤ |s.im|) :
    Summable (fun n : ℕ =>
      ‖Complex.log (1 + 1 / (s + (n : ℂ))) - 1 / (s + (n : ℂ))‖) := by
  let f : ℕ → ℝ := fun n =>
    ‖Complex.log (1 + 1 / (s + (n : ℂ))) - 1 / (s + (n : ℂ))‖
  have hshift : Summable (fun n : ℕ => f (n + 2)) := by
    simpa [f] using summable_gauss_terms_shifted_two s hs hsim
  exact (summable_nat_add_iff 2).1 hshift

lemma summable_gauss_complex_terms_shifted_two
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (hsim : 1 ≤ |s.im|) :
    Summable (fun n : ℕ =>
      Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) -
        1 / (s + ((n + 2 : ℕ) : ℂ))) := by
  refine Summable.of_norm_bounded (summable_gauss_terms_shifted_two s hs hsim) ?_
  intro n
  simpa using (le_rfl :
    ‖Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) - 1 / (s + ((n + 2 : ℕ) : ℂ))‖
      ≤ ‖Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) - 1 / (s + ((n + 2 : ℕ) : ℂ))‖)

lemma summable_gauss_complex_terms
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (hsim : 1 ≤ |s.im|) :
    Summable (fun n : ℕ =>
      Complex.log (1 + 1 / (s + (n : ℂ))) - 1 / (s + (n : ℂ))) := by
  let f : ℕ → ℂ := fun n =>
    Complex.log (1 + 1 / (s + (n : ℂ))) - 1 / (s + (n : ℂ))
  have hshift : Summable (fun n : ℕ => f (n + 2)) := by
    simpa [f] using summable_gauss_complex_terms_shifted_two s hs hsim
  exact (summable_nat_add_iff 2).1 hshift

lemma tsum_gauss_terms_eq_prefix_two_add_tail
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (hsim : 1 ≤ |s.im|) :
    (∑' n : ℕ, ‖Complex.log (1 + 1 / (s + (n : ℂ))) - 1 / (s + (n : ℂ))‖)
      = ‖Complex.log (1 + 1 / s) - 1 / s‖
        + ‖Complex.log (1 + 1 / (s + 1)) - 1 / (s + 1)‖
        + ∑' n : ℕ, ‖Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) -
          1 / (s + ((n + 2 : ℕ) : ℂ))‖ := by
  let f : ℕ → ℝ := fun n =>
    ‖Complex.log (1 + 1 / (s + (n : ℂ))) - 1 / (s + (n : ℂ))‖
  have hf : Summable f := by
    simpa [f] using summable_gauss_terms s hs hsim
  have hsplit :
      (∑ i ∈ Finset.range 2, f i) + ∑' i : ℕ, f (i + 2) = ∑' i : ℕ, f i :=
    hf.sum_add_tsum_nat_add 2
  have hsum2 : (∑ i ∈ Finset.range 2, f i) = f 0 + f 1 := by
    rw [show (2 : ℕ) = 1 + 1 by decide, Finset.sum_range_succ, Finset.sum_range_succ]
    simp
  calc
    (∑' n : ℕ, f n) = (∑ i ∈ Finset.range 2, f i) + ∑' i : ℕ, f (i + 2) := by
      simpa using hsplit.symm
    _ = f 0 + f 1 + ∑' i : ℕ, f (i + 2) := by
      simpa [hsum2, add_assoc]
    _ = ‖Complex.log (1 + 1 / s) - 1 / s‖
          + ‖Complex.log (1 + 1 / (s + 1)) - 1 / (s + 1)‖
          + ∑' n : ℕ, ‖Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) -
            1 / (s + ((n + 2 : ℕ) : ℂ))‖ := by
          simp [f, add_assoc]

lemma tsum_gauss_complex_terms_eq_prefix_two_add_tail
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (hsim : 1 ≤ |s.im|) :
    (∑' n : ℕ, (Complex.log (1 + 1 / (s + (n : ℂ))) - 1 / (s + (n : ℂ))))
      = (Complex.log (1 + 1 / s) - 1 / s)
        + (Complex.log (1 + 1 / (s + 1)) - 1 / (s + 1))
        + ∑' n : ℕ, (Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) -
          1 / (s + ((n + 2 : ℕ) : ℂ))) := by
  let f : ℕ → ℂ := fun n => Complex.log (1 + 1 / (s + (n : ℂ))) - 1 / (s + (n : ℂ))
  have hf : Summable f := by
    simpa [f] using summable_gauss_complex_terms s hs hsim
  have hsplit :
      (∑ i ∈ Finset.range 2, f i) + ∑' i : ℕ, f (i + 2) = ∑' i : ℕ, f i :=
    hf.sum_add_tsum_nat_add 2
  have hsum2 : (∑ i ∈ Finset.range 2, f i) = f 0 + f 1 := by
    rw [show (2 : ℕ) = 1 + 1 by decide, Finset.sum_range_succ, Finset.sum_range_succ]
    simp
  calc
    (∑' n : ℕ, f n) = (∑ i ∈ Finset.range 2, f i) + ∑' i : ℕ, f (i + 2) := by
      simpa using hsplit.symm
    _ = f 0 + f 1 + ∑' i : ℕ, f (i + 2) := by
      simpa [hsum2, add_assoc]
    _ = (Complex.log (1 + 1 / s) - 1 / s)
          + (Complex.log (1 + 1 / (s + 1)) - 1 / (s + 1))
          + ∑' n : ℕ, (Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) -
            1 / (s + ((n + 2 : ℕ) : ℂ))) := by
          simp [f, add_assoc]

lemma norm_tsum_gauss_complex_terms_shifted_two_le
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (hsim : 1 ≤ |s.im|) :
    ‖∑' n : ℕ,
        (Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) -
          1 / (s + ((n + 2 : ℕ) : ℂ)))‖
      ≤ ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
  let f : ℕ → ℂ := fun n =>
    Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) -
      1 / (s + ((n + 2 : ℕ) : ℂ))
  have hsum_norm : Summable (fun n : ℕ => ‖f n‖) := by
    simpa [f] using summable_gauss_terms_shifted_two s hs hsim
  have hbound : ∀ n : ℕ, ‖f n‖ ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
    intro n
    simpa [f] using gauss_term_bound_by_inv_natCast_sq s hs hsim (show 2 ≤ n + 2 by omega)
  have hmajor : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ 2) := by
    exact (summable_nat_add_iff 2).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
  calc
    ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := hsum_norm.tsum_le_tsum hbound hmajor
    _ = ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := rfl

lemma tendsto_logDeriv_GammaSeq_of_locallyUniform
    {U : Set ℂ} (hU : IsOpen U) (x : U)
    (hconv : TendstoLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => Complex.GammaSeq z n) Gamma Filter.atTop U)
    (hdiff : ∀ᶠ n : ℕ in Filter.atTop,
      DifferentiableOn ℂ (fun z : ℂ => Complex.GammaSeq z n) U)
    (hGamma : Gamma x ≠ 0) :
    Filter.Tendsto
      (fun n : ℕ => deriv (fun z : ℂ => Complex.GammaSeq z n) x / Complex.GammaSeq x n)
      Filter.atTop (nhds (deriv Gamma x / Gamma x)) := by
  simpa [logDeriv] using
    (Complex.logDeriv_tendsto hU x hconv hdiff hGamma)

-- ============================================================
-- Main theorem
-- ============================================================

/-- **Atomic sorry**: Binet/digamma bound on a right half-strip away from the real axis. -/
theorem digamma_log_bound_atomic :
    ∃ C > 0, ∀ s : ℂ, s.re ≥ 1/4 → |s.im| ≥ 1 →
      Gamma s ≠ 0 →
      ‖deriv Gamma s / Gamma s - Complex.log s‖ ≤ C / ‖s‖ := by
  sorry

end Aristotle.DigammaBinetBound
```

