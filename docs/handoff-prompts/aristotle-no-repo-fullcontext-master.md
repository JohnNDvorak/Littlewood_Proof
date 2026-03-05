# Aristotle No-Repo Full-Context Master Pack

Copy/paste one section per Aristotle run.

---

## Prompt A

# No-Repo Full-Context Prompt A

You have no repository access. Use only the code in this prompt.

Task: prove `digamma_log_bound_atomic` with no axioms/sorry/admit and keep signature unchanged.

Output required:
1. Replacement Lean code for the theorem proof (and any helper lemmas in same namespace if needed).
2. Brief explanation of key steps.
3. Any blocker if truly impossible under no-axiom constraints.

## Full current file snapshot
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

---

## Prompt B

# No-Repo Full-Context Prompt B

You have no repository access. Use only the code in this prompt.

Task: prove `critical_zero_sum_diverges` with no axioms/sorry/admit and keep signature unchanged.

Output required:
1. Replacement Lean code for the theorem proof (and helper lemmas in same namespace if needed).
2. Brief explanation.
3. If impossible, exact formal blocker and strongest unconditional helper theorem you can still prove.

## Full current target file snapshot
```lean
/-
Proof of PsiZeroSumOscillationHyp (B5b) from ExplicitFormulaPsiGeneralHyp (B5a)
via Landau's indirect argument.

## Mathematical Strategy (Landau 1905 / Ingham 1932)

Given the general truncated explicit formula (B5a) with variable truncation T:
  |ψ(x) - x + Σ_{|γ|≤T} Re(x^ρ/ρ)| ≤ C · (√x · (log T)²/√T + (log x)²)

To show: under RH, ψ(x) - x is unbounded in both directions relative to √x.

Proof by contradiction for the positive direction:
1. Assume ψ(x) - x ≤ M√x for all x ≥ x₀ (bounded above)
2. From B5a at T=x: -∑_{|γ|≤x} Re(x^ρ/ρ) ≤ M√x + K(log x)²
3. The Mellin/Stieltjes transform ∫₁^∞ (M√x - (ψ(x)-x)) x^{-s-1} dx
   converges for Re(s) > 1/2
4. This makes ζ'/ζ + 1/(s-1) + M/(s-1/2) holomorphic for Re(s) > 1/2
5. But under RH, ζ has zeros at 1/2+iγ (infinitely many by Hardy),
   so ζ'/ζ has poles at those points — contradiction

The negative direction is symmetric.

## Lean Formalization

The Landau-Ingham contradiction via Mellin transforms is deferred. The proof
uses a sorry for the key analytic number theory fact: under RH with infinitely
many critical-line zeros, ψ(x)-x cannot be bounded above (or below) by any
multiple of √x for all large x.

## References

- Landau, E. (1905). "Über einen Satz von Tschebyschef." Math. Ann. 61.
- Ingham, A. E. (1932). The Distribution of Prime Numbers, Chapter V.
- Montgomery-Vaughan (2007). Multiplicative Number Theory I, §15.2.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.Aristotle.ZetaLogDerivInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Classical

namespace Aristotle.Standalone.PsiZeroSumOscillationFromIngham

open Filter Complex Topology
open GrowthDomination
open Aristotle.DirichletPhaseAlignment (ZerosBelow CriticalZeros)
open Aristotle.Standalone.RHPsiWitnessFromZeroSum (psiMainTerm)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open ZetaZeros

-- ============================================================
-- Infrastructure: positive-imaginary-part zeros (PROVED)
-- ============================================================

/-- The subset of ZerosBelow T with strictly positive imaginary part. -/
def PositiveImZerosBelow (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => 0 < ρ.im)

lemma positiveImZerosBelow_sub (T : ℝ) :
    PositiveImZerosBelow T ⊆ ZerosBelow T :=
  Finset.filter_subset _ _

lemma positiveImZerosBelow_re_half (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ ρ ∈ PositiveImZerosBelow T, ρ.re = 1 / 2 := by
  intro ρ hρ
  have hρ_mem : ρ ∈ ZerosBelow T := positiveImZerosBelow_sub T hρ
  have hρ_crit : ρ ∈ CriticalZeros := by
    simp only [ZerosBelow] at hρ_mem
    split_ifs at hρ_mem with hfin
    · exact ((hfin.mem_toFinset).mp hρ_mem).1
    · simp at hρ_mem
  exact hRH ρ hρ_crit

-- ============================================================
-- Proved: Re(I/ρ) ≤ 1/‖ρ‖ for nonzero ρ
-- ============================================================

/-- For any nonzero ρ, Re(I/ρ) ≤ 1/‖ρ‖.
Proof: |Re(z)| ≤ ‖z‖ and ‖I/ρ‖ = 1/‖ρ‖. -/
lemma re_I_div_le_inv_norm (ρ : ℂ) (_hρ : ρ ≠ 0) :
    (I / ρ).re ≤ 1 / ‖ρ‖ := by
  calc (I / ρ).re ≤ ‖I / ρ‖ := le_trans (le_abs_self _) (abs_re_le_norm _)
    _ = ‖I‖ / ‖ρ‖ := by rw [norm_div]
    _ = 1 / ‖ρ‖ := by rw [Complex.norm_I]

-- ============================================================
-- Key analytic fact: Landau-Ingham unbounded oscillation
-- ============================================================

-- ============================================================
-- Phase alignment infrastructure for explicit formula approach
-- ============================================================

open Aristotle.DirichletPhaseAlignment
  (exists_large_x_phases_aligned_to_target bound_real_part_of_sum_shifted
   bound_real_part_of_sum_shifted_upper)

/-- For γ ≥ 1: γ/(1/4+γ²) ≥ 1/(2γ).
Comparison lemma: γ/(1/4+γ²) ≥ γ/(γ+γ²) = 1/(1+γ) ≥ 1/(2γ) for γ ≥ 1.
Key for reducing divergence of ∑ γ/(1/4+γ²) to divergence of ∑ 1/γ. -/
lemma gamma_div_bound (γ : ℝ) (hγ : γ ≥ 1) :
    γ / (1/4 + γ ^ 2) ≥ 1 / (2 * γ) := by
  rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg γ]

/-- **Atomic sorry (B5b leaf)**: Under RH, ∑_{0<γ≤T} γ/(1/4+γ²) → ∞ as T → ∞.

This is the divergence of the weighted sum over positive zeta zero ordinates.
The weight γ/(1/4+γ²) ≈ 1/γ for large γ, so this diverges at the same rate as
the harmonic sum ∑ 1/γ over zero ordinates.

**Proof outline** (not yet formalized):
(1) Riemann-von Mangoldt: N(T) = (T/2π)log(T/2π) - T/2π + O(log T).
    In particular, N⁺(T) := #{γ : 0 < γ ≤ T, ζ(1/2+iγ)=0} ≥ cT·log(T) for T ≥ 2.
(2) For γ ≥ 1: γ/(1/4+γ²) ≥ 1/(2γ) (from `gamma_div_bound`).
(3) Dyadic decomposition: ∑_{1≤γ≤T} 1/γ ≥ c·log(T) → ∞.
(4) Zeros with 0 < γ < 1 contribute only a bounded amount (finitely many).
    In fact, the first zero ordinate is γ₁ ≈ 14.13, so this set is empty.

**Blocked by**: uniform Riemann-von Mangoldt (needs Stirling + Argument Principle).

References: Hardy 1914, Backlund 1918, Titchmarsh (1986) §9.4. -/
private theorem critical_zero_sum_diverges (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ M : ℝ, ∃ T : ℝ, T ≥ 2 ∧
      M ≤ ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2) := by
  sorry

/-- Re((-I)/ρ) = -γ/(1/4+γ²) when Re(ρ) = 1/2, Im(ρ) = γ.
This is the key identity: alignment to w = -I produces the DIVERGENT sum
(negative for positive γ). -/
private lemma re_neg_I_div_eq (ρ : ℂ) (hρ_re : ρ.re = 1/2) :
    ((-I) / ρ).re = -ρ.im / (1/4 + ρ.im ^ 2) := by
  rw [Complex.div_re, Complex.neg_re, Complex.neg_im]
  simp only [Complex.I_re, Complex.I_im, neg_zero, Complex.normSq_apply]
  rw [hρ_re]
  ring

/-- The sum Σ_{S+} Re((-I)/ρ) = -Σ_{S+} γ/(1/4+γ²) for zeros with Re(ρ)=1/2. -/
private lemma sum_re_neg_I_div_eq (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    (∑ ρ ∈ PositiveImZerosBelow T, ((-I) / ρ).re) =
    -(∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2)) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun ρ hρ => by
    rw [re_neg_I_div_eq ρ (positiveImZerosBelow_re_half T hRH ρ hρ)]
    rw [neg_div])

/-- Re(I/ρ) = γ/(1/4+γ²) when Re(ρ) = 1/2.
Needed for the σ = -1 direction (alignment to w = I). -/
private lemma re_I_div_eq (ρ : ℂ) (hρ_re : ρ.re = 1/2) :
    (I / ρ).re = ρ.im / (1/4 + ρ.im ^ 2) := by
  rw [Complex.div_re]
  simp only [Complex.I_re, Complex.I_im, Complex.normSq_apply]
  rw [hρ_re]
  ring

/-- Sum version of re_I_div_eq: ∑_{S+} Re(I/ρ) = ∑_{S+} γ/(1/4+γ²). -/
private lemma sum_re_I_div_eq (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    (∑ ρ ∈ PositiveImZerosBelow T, (I / ρ).re) =
    (∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2)) :=
  Finset.sum_congr rfl (fun ρ hρ =>
    re_I_div_eq ρ (positiveImZerosBelow_re_half T hRH ρ hρ))

-- ============================================================
-- Conjugate bound infrastructure
-- ============================================================

/-- The subset of ZerosBelow T with strictly negative imaginary part. -/
private def NegativeImZerosBelow (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => ρ.im < 0)

/-- The subset of ZerosBelow T with zero imaginary part. -/
private def ZeroImZerosBelow (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => ρ.im = 0)

/-- Elements of ZerosBelow T are in CriticalZeros. -/
private lemma zerosBelow_mem_criticalZeros {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) :
    ρ ∈ CriticalZeros := by
  simp only [ZerosBelow] at hρ
  split_ifs at hρ with hfin
  · exact ((hfin.mem_toFinset).mp hρ).1
  · simp at hρ

/-- Elements of ZerosBelow T have |Im(ρ)| ≤ T. -/
private lemma zerosBelow_im_le {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) :
    |ρ.im| ≤ T := by
  simp only [ZerosBelow] at hρ
  split_ifs at hρ with hfin
  · exact ((hfin.mem_toFinset).mp hρ).2
  · simp at hρ

/-- Under RH, every element of ZerosBelow T has Re = 1/2. -/
private lemma zerosBelow_re_half {T : ℝ} (hRH : ZetaZeros.RiemannHypothesis)
    {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) : ρ.re = 1 / 2 :=
  hRH ρ (zerosBelow_mem_criticalZeros hρ)

/-- Im(conj ρ) = -Im(ρ) (handles starRingEnd unfolding). -/
private lemma conj_im_eq (ρ : ℂ) : (starRingEnd ℂ ρ).im = -ρ.im := by
  change (star ρ).im = _; simp [Complex.conj_im]

/-- Helper: conj ρ is in ZerosBelow T if ρ is. -/
private lemma conj_mem_zerosBelow {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) :
    starRingEnd ℂ ρ ∈ ZerosBelow T := by
  have hρ_crit := zerosBelow_mem_criticalZeros hρ
  have hconj_crit : starRingEnd ℂ ρ ∈ CriticalZeros := zero_conj_zero hρ_crit
  have hconj_im_le : |((starRingEnd ℂ) ρ).im| ≤ T := by
    rw [conj_im_eq, abs_neg]; exact zerosBelow_im_le hρ
  -- Extract finiteness from the fact that hρ is in ZerosBelow (not ∅)
  have hfin : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite := by
    by_contra h; simp only [ZerosBelow, dif_neg h] at hρ; simp at hρ
  simp only [ZerosBelow, dif_pos hfin]
  exact hfin.mem_toFinset.mpr ⟨hconj_crit, hconj_im_le⟩

/-- Conjugation sends positive-Im zeros to negative-Im zeros within ZerosBelow T. -/
private lemma conj_pos_mem_neg (T : ℝ) (_hRH : ZetaZeros.RiemannHypothesis) :
    ∀ ρ ∈ PositiveImZerosBelow T, starRingEnd ℂ ρ ∈ NegativeImZerosBelow T := by
  intro ρ hρ
  simp only [NegativeImZerosBelow, Finset.mem_filter]
  have hρ_zb : ρ ∈ ZerosBelow T := positiveImZerosBelow_sub T hρ
  have hρ_im : 0 < ρ.im := by
    simp only [PositiveImZerosBelow, Finset.mem_filter] at hρ; exact hρ.2
  exact ⟨conj_mem_zerosBelow hρ_zb, by rw [conj_im_eq]; linarith⟩

/-- Conjugation sends negative-Im zeros to positive-Im zeros within ZerosBelow T. -/
private lemma conj_neg_mem_pos (T : ℝ) (_hRH : ZetaZeros.RiemannHypothesis) :
    ∀ ρ ∈ NegativeImZerosBelow T, starRingEnd ℂ ρ ∈ PositiveImZerosBelow T := by
  intro ρ hρ
  simp only [PositiveImZerosBelow, Finset.mem_filter]
  simp only [NegativeImZerosBelow, Finset.mem_filter] at hρ
  exact ⟨conj_mem_zerosBelow hρ.1, by rw [conj_im_eq]; linarith⟩

/-- For real x > 0, Re(x^(conj ρ) / (conj ρ)) = Re(x^ρ / ρ).
Key: x^(conj ρ) = conj(x^ρ) for positive real x (via cpow_conj + conj_ofReal). -/
private lemma re_cpow_div_conj_eq (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    (((x : ℂ) ^ (starRingEnd ℂ ρ)) / (starRingEnd ℂ ρ)).re =
    (((x : ℂ) ^ ρ) / ρ).re := by
  -- (↑x)^(conj ρ) = conj((conj(↑x))^ρ) = conj((↑x)^ρ) since conj(↑x) = ↑x
  have harg : (↑x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact ne_of_lt Real.pi_pos
  have h_cpow : (↑x : ℂ) ^ (starRingEnd ℂ ρ) = starRingEnd ℂ ((↑x : ℂ) ^ ρ) := by
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  -- conj(z/w) = conj(z)/conj(w), so the whole expression is Re(conj(x^ρ/ρ)) = Re(x^ρ/ρ)
  have h_div : starRingEnd ℂ ((↑x : ℂ) ^ ρ) / starRingEnd ℂ ρ =
      starRingEnd ℂ (((↑x : ℂ) ^ ρ) / ρ) := (map_div₀ (starRingEnd ℂ) _ _).symm
  rw [h_cpow, h_div, Complex.conj_re]

/-- The non-positive-Im part of ZerosBelow decomposes into negative-Im and zero-Im.
Uses that ¬(0 < x) ↔ x ≤ 0 ↔ x < 0 ∨ x = 0 for real ordering. -/
private lemma nonPosIm_decomp (T : ℝ) :
    (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)) =
    NegativeImZerosBelow T ∪ ZeroImZerosBelow T := by
  ext ρ
  simp only [Finset.mem_filter, NegativeImZerosBelow, ZeroImZerosBelow,
    Finset.mem_union, Finset.mem_filter, not_lt]
  constructor
  · intro ⟨hmem, hle⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inl ⟨hmem, h⟩
    · exact Or.inr ⟨hmem, h⟩
  · rintro (⟨hmem, hlt⟩ | ⟨hmem, heq⟩)
    · exact ⟨hmem, le_of_lt hlt⟩
    · exact ⟨hmem, le_of_eq heq⟩

/-- Negative-Im and zero-Im parts are disjoint. -/
private lemma negIm_zeroIm_disjoint (T : ℝ) :
    Disjoint (NegativeImZerosBelow T) (ZeroImZerosBelow T) := by
  simp only [NegativeImZerosBelow, ZeroImZerosBelow]
  rw [Finset.disjoint_filter]
  intro ρ _ hlt heq
  linarith

/-- Under RH, the zero-Im part has at most 1 element (all such ρ = 1/2). -/
private lemma zeroIm_card_le_one (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    (ZeroImZerosBelow T).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro ρ₁ hρ₁ ρ₂ hρ₂
  simp only [ZeroImZerosBelow, Finset.mem_filter] at hρ₁ hρ₂
  have hre₁ := zerosBelow_re_half hRH hρ₁.1
  have hre₂ := zerosBelow_re_half hRH hρ₂.1
  exact Complex.ext (by rw [hre₁, hre₂]) (by rw [hρ₁.2, hρ₂.2])

/-- Each term in the zero-Im sum is bounded by 2√x. Under RH, ρ = 1/2 + 0i,
so x^ρ/ρ = x^{1/2}/(1/2) = 2√x. -/
private lemma zeroIm_term_bound (T : ℝ) (x : ℝ) (hx : x ≥ 2)
    (hRH : ZetaZeros.RiemannHypothesis)
    (ρ : ℂ) (hρ : ρ ∈ ZeroImZerosBelow T) :
    |(((x : ℂ) ^ ρ / ρ)).re| ≤ 2 * Real.sqrt x := by
  simp only [ZeroImZerosBelow, Finset.mem_filter] at hρ
  have hre : ρ.re = 1 / 2 := zerosBelow_re_half hRH hρ.1
  have him : ρ.im = 0 := hρ.2
  have hx_pos : (0 : ℝ) < x := by linarith
  -- Use norm bound: |Re(z)| ≤ ‖z‖
  calc |(((x : ℂ) ^ ρ / ρ)).re|
      ≤ ‖((x : ℂ) ^ ρ / ρ)‖ := Complex.abs_re_le_norm _
    _ = ‖(x : ℂ) ^ ρ‖ / ‖ρ‖ := norm_div _ _
    _ = x ^ ρ.re / ‖ρ‖ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    _ = x ^ (1 / 2 : ℝ) / ‖ρ‖ := by rw [hre]
    _ = Real.sqrt x / ‖ρ‖ := by rw [Real.sqrt_eq_rpow]
    _ = 2 * Real.sqrt x := by
        -- ρ = (1/2 : ℝ) as a complex number, so ‖ρ‖ = 1/2
        have hρ_eq : ρ = (↑(1/2 : ℝ) : ℂ) :=
          Complex.ext (by simp [hre]) (by simp [him])
        rw [hρ_eq, Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
        ring

/-- **B5b conjugate bound** (PROVED): Under RH, the full zero sum over ZerosBelow T
equals 2× the sum over PositiveImZerosBelow T, up to a bounded remainder R
with |R| ≤ 2√x, accounting for the possible zero at ρ = 1/2.

Proof: Under RH, zeros come in conjugate pairs ρ, ρ̄ (from the functional
equation ζ(s) = 0 ↔ ζ(1-s) = 0, with Re(ρ) = 1/2 giving 1-ρ = ρ̄). For real x > 0,
Re(x^ρ̄/ρ̄) = Re(conj(x^ρ/ρ)) = Re(x^ρ/ρ). The only unpaired zero has Im = 0
(at most ρ = 1/2 under RH), contributing |R| ≤ |x^{1/2}/(1/2)| = 2√x. -/
private theorem zero_sum_conjugate_bound (T : ℝ) (x : ℝ) (hx : x ≥ 2)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ R : ℝ, |R| ≤ 2 * Real.sqrt x ∧
      (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re =
      2 * (∑ ρ ∈ PositiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re + R := by
  -- Set f ρ := (x^ρ/ρ).re for convenience
  set f : ℂ → ℝ := fun ρ => (((x : ℂ) ^ ρ) / ρ).re with hf_def
  have hx_pos : (0 : ℝ) < x := by linarith
  -- ================================================================
  -- Step 1: Decompose ZerosBelow = PosIm + NonPosIm
  -- ================================================================
  have h_decomp :
      ∑ ρ ∈ ZerosBelow T, f ρ =
      ∑ ρ ∈ PositiveImZerosBelow T, f ρ +
      ∑ ρ ∈ (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)), f ρ :=
    (Finset.sum_filter_add_sum_filter_not (ZerosBelow T) (fun ρ => 0 < ρ.im) f).symm
  -- ================================================================
  -- Step 2: Decompose NonPosIm = NegIm + ZeroIm
  -- ================================================================
  have h_nonpos :
      ∑ ρ ∈ (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)), f ρ =
      ∑ ρ ∈ NegativeImZerosBelow T, f ρ + ∑ ρ ∈ ZeroImZerosBelow T, f ρ := by
    show ∑ ρ ∈ (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)), f ρ =
      ∑ ρ ∈ NegativeImZerosBelow T, f ρ + ∑ ρ ∈ ZeroImZerosBelow T, f ρ
    conv_lhs => rw [nonPosIm_decomp T]
    exact Finset.sum_union (negIm_zeroIm_disjoint T)
  -- ================================================================
  -- Step 3: NegIm sum = PosIm sum (via conjugation bijection)
  -- ================================================================
  have h_neg_eq_pos :
      ∑ ρ ∈ NegativeImZerosBelow T, f ρ =
      ∑ ρ ∈ PositiveImZerosBelow T, f ρ := by
    apply Finset.sum_nbij' (starRingEnd ℂ) (starRingEnd ℂ)
      (conj_neg_mem_pos T hRH) (conj_pos_mem_neg T hRH)
      (fun ρ _ => Complex.conj_conj ρ) (fun ρ _ => Complex.conj_conj ρ)
    intro ρ _hρ
    exact (re_cpow_div_conj_eq x hx_pos ρ).symm
  -- ================================================================
  -- Step 4: Bound the ZeroIm contribution
  -- ================================================================
  set R := ∑ ρ ∈ ZeroImZerosBelow T, f ρ with hR_def
  have hR_bound : |R| ≤ 2 * Real.sqrt x := by
    calc |R| ≤ ∑ ρ ∈ ZeroImZerosBelow T, |f ρ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ρ ∈ ZeroImZerosBelow T, (2 * Real.sqrt x) :=
          Finset.sum_le_sum (fun ρ hρ => zeroIm_term_bound T x hx hRH ρ hρ)
      _ = (ZeroImZerosBelow T).card * (2 * Real.sqrt x) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (2 * Real.sqrt x) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast zeroIm_card_le_one T hRH
      _ = 2 * Real.sqrt x := one_mul _
  -- ================================================================
  -- Step 5: Combine
  -- ================================================================
  refine ⟨R, hR_bound, ?_⟩
  -- Push .re through the sum: Re(∑ z) = ∑ Re(z)
  have h_re_sum : (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re =
      ∑ ρ ∈ ZerosBelow T, f ρ := by
    change Complex.reAddGroupHom (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)) = _
    rw [map_sum]; rfl
  have h_re_pos : (∑ ρ ∈ PositiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re =
      ∑ ρ ∈ PositiveImZerosBelow T, f ρ := by
    change Complex.reAddGroupHom (∑ ρ ∈ PositiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ)) = _
    rw [map_sum]; rfl
  rw [h_re_sum, h_re_pos, h_decomp, h_nonpos, h_neg_eq_pos]
  ring

/-- Positive-imaginary-part zeros have Im > 0 (tautology from filter definition). -/
private lemma positiveImZerosBelow_im_pos (T : ℝ) :
    ∀ ρ ∈ PositiveImZerosBelow T, 0 < ρ.im := by
  intro ρ hρ
  simp only [PositiveImZerosBelow, Finset.mem_filter] at hρ
  exact hρ.2

-- ============================================================
-- Helpers for assembly: growth comparison
-- ============================================================

/-- Exponential lower bound: e^u ≥ u³/27 for u ≥ 0.
Proof: e^{u/3} ≥ 1 + u/3 ≥ u/3, so e^u = (e^{u/3})³ ≥ (u/3)³. -/
private lemma exp_ge_cube_div (u : ℝ) (hu : u ≥ 0) : u ^ 3 / 27 ≤ Real.exp u := by
  have h3 : u / 3 ≤ Real.exp (u / 3) := by linarith [Real.add_one_le_exp (u / 3)]
  have h4 : (u / 3) ^ 3 ≤ Real.exp (u / 3) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h3 3
  have h5 : Real.exp (u / 3) ^ 3 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc u ^ 3 / 27 = (u / 3) ^ 3 := by ring
    _ ≤ Real.exp (u / 3) ^ 3 := h4
    _ = Real.exp u := h5

/-- For A ≥ 0, x ≥ exp(216A): A · (log x)² ≤ √x.
Proof: √x = e^{(logx)/2} ≥ ((logx)/2)³/27 = (logx)³/216.
Then A·(logx)² ≤ (logx)·(logx)²/216 = (logx)³/216 ≤ √x. -/
private lemma log_sq_le_sqrt (A : ℝ) (hA : A ≥ 0) (x : ℝ)
    (hx : x ≥ Real.exp (216 * A)) :
    A * (Real.log x) ^ 2 ≤ Real.sqrt x := by
  have hexp_pos : (0 : ℝ) < Real.exp (216 * A) := Real.exp_pos _
  have hx_pos : 0 < x := lt_of_lt_of_le hexp_pos hx
  -- Step 1: log x ≥ 216A
  have hlog_ge : Real.log x ≥ 216 * A := by
    rw [ge_iff_le, ← Real.log_exp (216 * A)]
    exact Real.log_le_log hexp_pos hx
  have hlog_nn : 0 ≤ Real.log x := by linarith [mul_nonneg (by norm_num : (216:ℝ) ≥ 0) hA]
  -- Step 2: √x = exp((logx)/2) ≥ (logx)³/216
  have h_sqrt_eq : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx_pos]
    congr 1; ring
  have h_sqrt_lb : (Real.log x) ^ 3 / 216 ≤ Real.sqrt x := by
    rw [h_sqrt_eq]
    calc (Real.log x) ^ 3 / 216
        = (Real.log x / 2) ^ 3 / 27 := by ring
      _ ≤ Real.exp (Real.log x / 2) := exp_ge_cube_div _ (by linarith)
  -- Step 3: A·(logx)² ≤ (logx)³/216 since logx ≥ 216A
  calc A * (Real.log x) ^ 2
      ≤ (Real.log x / 216) * (Real.log x) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        linarith
    _ = (Real.log x) ^ 3 / 216 := by ring
    _ ≤ Real.sqrt x := h_sqrt_lb

/-- Upper bound on (logT)²/√T for T ≥ 2: at most 432.
Proof: from exp_ge_cube_div, √T ≥ (logT)³/216.
So (logT)²/√T ≤ 216/logT ≤ 216/(1/2) = 432, using log 2 > 1/2. -/
private lemma logT_sq_div_sqrtT_le (T : ℝ) (hT : T ≥ 2) :
    (Real.log T) ^ 2 / Real.sqrt T ≤ 432 := by
  have hT_pos : 0 < T := by linarith
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  -- From exp_ge_cube_div: √T ≥ (logT)³/216
  have h_sqrt_eq : Real.sqrt T = Real.exp (Real.log T / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hT_pos]
    congr 1; ring
  have h_sqrt_lb : (Real.log T) ^ 3 / 216 ≤ Real.sqrt T := by
    rw [h_sqrt_eq]
    calc (Real.log T) ^ 3 / 216
        = (Real.log T / 2) ^ 3 / 27 := by ring
      _ ≤ Real.exp (Real.log T / 2) := exp_ge_cube_div _ (by linarith)
  -- So (logT)² ≤ 432 · √T, equivalently (logT)²/√T ≤ 432
  rw [div_le_iff₀ (Real.sqrt_pos_of_pos hT_pos)]
  -- Need: (logT)² ≤ 432 · √T
  -- From h_sqrt_lb: (logT)³/216 ≤ √T, so 432·√T ≥ 432·(logT)³/216 = 2·(logT)³
  -- And (logT)² ≤ 2·(logT)³ iff 1 ≤ 2·logT iff logT ≥ 1/2
  -- logT ≥ log 2 ≥ 1/2 (since exp(1/2) < 2, i.e., e < 4)
  have h_exp_half_le : Real.exp (1/2 : ℝ) ≤ 2 := by
    have := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)
      (n := 2) (by norm_num)
    simp [Finset.sum_range_succ] at this
    linarith
  have h_log2 : Real.log T ≥ 1/2 := by
    calc Real.log T ≥ Real.log 2 := Real.log_le_log (by norm_num) hT
      _ ≥ 1/2 := by
          rw [ge_iff_le, Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
          exact h_exp_half_le
  nlinarith [sq_nonneg (Real.log T)]

-- ============================================================
-- Landau-Ingham decomposition: 4 sub-lemmas (1 proved, 3 sorry)
-- ============================================================

/-- The "gap" integrand: under a one-sided bound on ψ(x)-x,
this integrand is nonneg for large x. -/
private noncomputable def landauIntegrand
    (σ : ℝ) (C₀ : ℝ) (x : ℝ) : ℝ :=
  C₀ * Real.sqrt x - σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x)

/-- **Sub-lemma 1/4** (PROVED): Integrand nonnegativity from one-sided bound. -/
private lemma landau_integrand_nonneg
    (σ C₀ X₀ : ℝ)
    (h_bound : ∀ x, x ≥ X₀ →
      σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≤ C₀ * Real.sqrt x)
    (x : ℝ) (hx : x ≥ X₀) :
    0 ≤ landauIntegrand σ C₀ x := by
  unfold landauIntegrand; linarith [h_bound x hx]

-- NOTE: The former sorry's `landau_mellin_analytic` and `landau_zeta_identity`
-- have been REMOVED. `landau_zeta_identity` was mathematically impossible:
-- it required F + G = ζ'/ζ on {Re > 1} with both F, G analytic on {Re > 1/2},
-- but ζ'/ζ has a simple pole at s = 1 ∈ {Re > 1/2} (proved in
-- `landau_pole_contradiction` below). The Landau-Ingham impossibility is now
-- captured as a single atomic sorry in `landau_psi_bounded_impossible`.

/-- **Sub-lemma 4/4** (PROVED): Pole contradiction.
If F + G represents ζ'/ζ for Re(s) > 1 and both F, G are analytic
on Re(s) > 1/2, then F + G is continuous at s = 1. But ζ'/ζ has a
simple pole at s = 1 (from `neg_zeta_logderiv_pole_at_one`).
Multiplying by (s-1): limit is 0 (from continuity) but also -1 (from pole).
Contradiction via `tendsto_nhds_unique`.

Note: RH is not needed — the hypotheses are already inconsistent due to
the s = 1 pole alone. The `hRH` parameter is kept for interface compatibility. -/
private theorem landau_pole_contradiction
    (_hRH : ZetaZeros.RiemannHypothesis)
    (F G : ℂ → ℂ)
    (hF : AnalyticOn ℂ F {s : ℂ | 1/2 < s.re})
    (hG : AnalyticOn ℂ G {s : ℂ | 1/2 < s.re})
    (h_id : ∀ s : ℂ, 1 < s.re →
      deriv riemannZeta s / riemannZeta s = F s + G s) :
    False := by
  -- The set {Re > 1/2} is open and contains 1
  have hS_open : IsOpen {s : ℂ | (1 : ℝ) / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1_mem : (1 : ℂ) ∈ {s : ℂ | (1 : ℝ) / 2 < s.re} := by
    show (1 : ℝ) / 2 < (1 : ℂ).re; simp [Complex.one_re]; norm_num
  -- F + G is continuous at s = 1
  have hFG_contAt : ContinuousAt (fun s => F s + G s) (1 : ℂ) :=
    (hF.continuousOn.continuousAt (hS_open.mem_nhds h1_mem)).add
      (hG.continuousOn.continuousAt (hS_open.mem_nhds h1_mem))
  -- Pole data: -ζ'/ζ(s) = g(s)/(s-1) near s = 1, g analytic, g(1) = 1
  obtain ⟨g, hg_an, hg1, hg_eq⟩ :=
    Aristotle.ZetaLogDerivInfra.neg_zeta_logderiv_pole_at_one
  -- The filter 𝓝[{Re > 1}] 1 is nontrivial (1 is on the boundary of {Re > 1})
  have hL_neBot : (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)).NeBot := by
    refine Filter.NeBot.mk ?_
    intro hbot
    have h_empty : (∅ : Set ℂ) ∈ 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ) := by
      rw [hbot]; exact Filter.mem_bot
    rw [mem_nhdsWithin] at h_empty
    obtain ⟨U, hU_open, h1U, hU_sub⟩ := h_empty
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open 1 h1U
    exact absurd (hU_sub ⟨hball (by
        simp only [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real]
        rw [Real.norm_of_nonneg (half_pos hε).le]
        linarith),
      show 1 < ((1 : ℂ) + (↑(ε / 2) : ℂ)).re from by
        simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith⟩)
      (by simp)
  -- 𝓝[{Re > 1}] 1 ≤ 𝓝[{1}ᶜ] 1 (since Re(s) > 1 implies s ≠ 1)
  have hL_le : 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ) ≤ 𝓝[{(1 : ℂ)}ᶜ] (1 : ℂ) :=
    nhdsWithin_mono (1 : ℂ) (fun (s : ℂ) (hs : s ∈ {s : ℂ | 1 < s.re}) =>
      show s ∈ {(1 : ℂ)}ᶜ from by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h; subst h; exact absurd hs (by simp [Complex.one_re]))
  -- On 𝓝[{Re > 1}] 1, eventually: (s-1) * (F s + G s) = -g s
  have h_eq_L : ∀ᶠ s in 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ),
      (s - 1) * (F s + G s) = -g s := by
    filter_upwards [hg_eq.filter_mono hL_le, self_mem_nhdsWithin]
      with s hpole (hs_re : s ∈ {s : ℂ | 1 < s.re})
    have hs_ne : s ≠ (1 : ℂ) := by
      intro h; subst h
      exact absurd hs_re (by simp [Set.mem_setOf_eq, Complex.one_re])
    have hs_sub_ne : s - 1 ≠ 0 := sub_ne_zero_of_ne hs_ne
    -- F s + G s = ζ'/ζ(s) = -(g(s)/(s-1)), so (s-1)*(F+G) = -g(s)
    have h_fg : F s + G s = -(g s / (s - 1)) := by
      rw [(h_id s hs_re).symm]
      exact neg_eq_iff_eq_neg.mp (by rwa [neg_div] at hpole)
    rw [h_fg, mul_neg, neg_inj]
    field_simp [hs_sub_ne]
  -- Limit 1: (s-1)*(F+G)(s) → 0 as s → 1
  have h_lim_0 : Filter.Tendsto (fun s => (s - 1) * (F s + G s))
      (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)) (𝓝 0) := by
    have h_sub : Filter.Tendsto (fun s : ℂ => s - 1) (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
      rw [show (0 : ℂ) = 1 - 1 from by ring]
      exact tendsto_id.sub tendsto_const_nhds
    have h_prod := h_sub.mul hFG_contAt
    rw [show (0 : ℂ) * (F (1 : ℂ) + G (1 : ℂ)) = 0 from zero_mul _] at h_prod
    exact h_prod.mono_left nhdsWithin_le_nhds
  -- Limit 2: (s-1)*(F+G)(s) → -1 (equals -g(s) eventually, g(1) = 1)
  have h_lim_neg1 : Filter.Tendsto (fun s => (s - 1) * (F s + G s))
      (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)) (𝓝 (-1)) := by
    have hg_lim : Filter.Tendsto (fun s => -g s)
        (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)) (𝓝 (-1)) := by
      have h4 := hg_an.continuousAt.neg.tendsto
      rw [hg1] at h4
      exact h4.mono_left nhdsWithin_le_nhds
    exact (Filter.tendsto_congr' h_eq_L).mpr hg_lim
  -- Contradiction: 0 = -1
  exact absurd (tendsto_nhds_unique h_lim_0 h_lim_neg1) (by norm_num)

/-- **B5b assembly** (PROVED from sub-sorry's): Core Landau-Ingham impossibility.
Under RH, σ·(ψ(x)-x) cannot be bounded above by C₀·√x for all large x.

Proof via explicit formula + Dirichlet phase alignment:
1. Get C_ef from ExplicitFormulaPsiGeneralHyp
2. Use critical_zero_sum_diverges to get T₀ with large Σ γ/(1/4+γ²) ≥ M₀
3. Align phases of PositiveImZerosBelow(T₀) to w = -σI
4. bound_real_part_of_sum_shifted_upper gives Σ Re(x^ρ/ρ) very negative (σ=1)
   or bound_real_part_of_sum_shifted gives Σ Re(x^ρ/ρ) very positive (σ=-1)
5. zero_sum_conjugate_bound relates full sum to positive-Im sum (factor of 2)
6. Explicit formula yields σ·(ψ(x)-x) > C₀·√x, contradicting h_bound

The parameter M₀ = 3456|C_ef| + |C₀| + 10 is chosen to absorb:
(a) |C_ef|·(logT₀)²/√T₀ ≤ 432|C_ef| (from logT_sq_div_sqrtT_le)
(b) |C_ef|·(logx)²/√x ≤ 1 (from log_sq_le_sqrt for x ≥ exp(216·A), A small)
(c) The 2√x remainder from conjugate bound
(d) The ε·D noise from phase alignment -/
private theorem landau_psi_bounded_impossible
    [ExplicitFormulaPsiGeneralHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (C₀ X₀ : ℝ)
    (h_bound : ∀ x, x ≥ X₀ →
      σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≤
        C₀ * Real.sqrt x) :
    False := by
  -- ================================================================
  -- Step 1: Extract explicit formula constant, work with |C_ef|
  -- ================================================================
  obtain ⟨C_ef, hEF⟩ := ExplicitFormulaPsiGeneralHyp.proof
  set C := |C_ef| with hC_def
  have hC_nn : 0 ≤ C := abs_nonneg _
  -- The bound hEF with |C_ef| ≤ C:
  have hEF' : ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
      C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
    intro x T hx hT
    calc _ ≤ C_ef * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
            (Real.log x) ^ 2) := hEF x T hx hT
      _ ≤ |C_ef| * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
            (Real.log x) ^ 2) := by
          apply mul_le_mul_of_nonneg_right (le_abs_self _)
          apply add_nonneg
          · apply div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (Real.sqrt_nonneg _)
          · exact sq_nonneg _
  -- ================================================================
  -- Step 2: Choose M₀ and get T₀ from divergent sum
  -- ================================================================
  set M₀ := 3456 * C + |C₀| + 10 with hM₀_def
  have hM₀_pos : M₀ > 0 := by positivity
  obtain ⟨T₀, hT₀_ge, hT₀_sum⟩ := critical_zero_sum_diverges hRH M₀
  -- ================================================================
  -- Step 3: Set up S, D, ε
  -- ================================================================
  set S := PositiveImZerosBelow T₀ with hS_def
  have hS_re : ∀ ρ ∈ S, ρ.re = 1 / 2 := positiveImZerosBelow_re_half T₀ hRH
  have hS_pos : ∀ ρ ∈ S, 0 < ρ.im := positiveImZerosBelow_im_pos T₀
  set D := ∑ ρ ∈ S, 1 / ‖ρ‖ with hD_def
  have hD_nn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => by positivity)
  set M := ∑ ρ ∈ S, ρ.im / (1/4 + ρ.im ^ 2) with hM_def
  have hM_ge : M₀ ≤ M := hT₀_sum
  -- ε = 1/(4·(D+1)): ensures ε > 0 and ε·D < 1/4
  set ε := 1 / (4 * (D + 1)) with hε_def
  have hε_pos : ε > 0 := by positivity
  have hε_D : ε * D < 1 / 4 := by
    rw [hε_def, div_mul_eq_mul_div, one_mul]
    rw [div_lt_div_iff₀ (by positivity : 4 * (D + 1) > 0) (by norm_num : (0:ℝ) < 4)]
    nlinarith
  -- ================================================================
  -- Step 4: Choose X large enough, get aligned x
  -- ================================================================
  -- Need x ≥ X₀, x ≥ 2, x ≥ exp(216·A) where A = 8C/M₀ for log² domination
  set A_log := 8 * C / M₀ with hA_def
  have hA_nn : 0 ≤ A_log := by positivity
  set X := max X₀ (max 2 (Real.exp (216 * A_log))) with hX_def
  -- Get aligned x from phase alignment
  -- For σ=1: w = -I. For σ=-1: w = I. In both cases ‖w‖ = 1.
  set w := -(σ * I) with hw_def
  have hw_norm : ‖w‖ = 1 := by
    rcases hσ with rfl | rfl <;> simp [hw_def, norm_neg, Complex.norm_I]
  obtain ⟨x, hx_gt, hx_aligned⟩ := exists_large_x_phases_aligned_to_target
    S hS_re hS_pos w hw_norm ε hε_pos X hRH
  -- Extract useful bounds on x
  have hx_X₀ : x ≥ X₀ := by linarith [le_max_left X₀ (max 2 (Real.exp (216 * A_log)))]
  have hx_2 : x ≥ 2 := by
    have : X ≥ 2 := le_trans (le_max_left 2 _) (le_max_right X₀ _)
    linarith
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_exp : x ≥ Real.exp (216 * A_log) := by
    have : X ≥ Real.exp (216 * A_log) := le_trans (le_max_right 2 _) (le_max_right X₀ _)
    linarith
  -- ================================================================
  -- Step 5: Bound the positive-Im sum via phase alignment
  -- ================================================================
  -- Key identity: ∑ Re(w/ρ) = -(σ · M) (the divergent sum with sign)
  have h_sum_w : (∑ ρ ∈ S, (w / ρ).re) = -(σ * M) := by
    rcases hσ with rfl | rfl
    · -- σ = 1, w = -(1 * I) = -I
      have : w = -I := by simp [hw_def]
      rw [this, show -(1 * M) = -M from by ring]
      exact sum_re_neg_I_div_eq T₀ hRH
    · -- σ = -1, w = -(-1 * I) = I
      have : w = I := by simp [hw_def]
      rw [this, show -(-1 * M) = M from by ring]
      exact sum_re_I_div_eq T₀ hRH
  -- Upper bound on ∑_{S} Re(x^ρ/ρ) (used for σ=1)
  have h_upper := bound_real_part_of_sum_shifted_upper hS_re hx_pos hw_norm hε_pos hx_aligned
  -- Lower bound on ∑_{S} Re(x^ρ/ρ) (used for σ=-1)
  have h_lower := bound_real_part_of_sum_shifted hS_re hx_pos hw_norm hε_pos hx_aligned
  -- ================================================================
  -- Step 6: Apply conjugate bound
  -- ================================================================
  obtain ⟨R, hR_bound, hR_eq⟩ := zero_sum_conjugate_bound T₀ x hx_2 hRH
  -- ================================================================
  -- Step 7: Apply explicit formula at T = T₀
  -- ================================================================
  have hEF_at := hEF' x T₀ hx_2 hT₀_ge
  -- Rewrite: let sum_full = (∑ ρ ∈ ZerosBelow T₀, (x:ℂ)^ρ/ρ).re
  set sum_full := (∑ ρ ∈ ZerosBelow T₀, ((x : ℂ) ^ ρ) / ρ).re with hsum_full_def
  set sum_pos := (∑ ρ ∈ S, ((x : ℂ) ^ ρ) / ρ).re with hsum_pos_def
  -- From hR_eq: sum_full = 2 * sum_pos + R
  have h_sum_eq : sum_full = 2 * sum_pos + R := hR_eq
  -- ================================================================
  -- Step 8: Bound the error term
  -- ================================================================
  set err := C * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀ +
    (Real.log x) ^ 2) with herr_def
  -- hEF_at: |ψ(x) - x + sum_full| ≤ err (after sign adjustment)
  have hEF_abs : |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + sum_full| ≤ err := by
    convert hEF_at using 2
    ring
  -- Bound err ≤ (M₀/4) * √x in two parts:
  -- Part (a): C * √x * (logT₀)²/√T₀ ≤ 432C · √x ≤ (M₀/8) · √x
  have h_err_a : C * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀) ≤
      (M₀ / 8) * Real.sqrt x := by
    have h_logT := logT_sq_div_sqrtT_le T₀ hT₀_ge
    calc C * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀)
        = C * ((Real.log T₀) ^ 2 / Real.sqrt T₀) * Real.sqrt x := by ring
      _ ≤ C * 432 * Real.sqrt x := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left h_logT hC_nn
      _ = 432 * C * Real.sqrt x := by ring
      _ ≤ (M₀ / 8) * Real.sqrt x := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          have : M₀ = 3456 * C + |C₀| + 10 := hM₀_def
          nlinarith [abs_nonneg C₀]
  -- Part (b): C * (logx)² ≤ (M₀/8) · √x
  have h_err_b : C * (Real.log x) ^ 2 ≤ (M₀ / 8) * Real.sqrt x := by
    -- A_log = 8C/M₀, so C = A_log · M₀/8
    -- From log_sq_le_sqrt: A_log · (logx)² ≤ √x for x ≥ exp(216·A_log)
    have h_dom := log_sq_le_sqrt A_log hA_nn x hx_exp
    -- C · (logx)² = (A_log · M₀/8) · (logx)² = (M₀/8) · (A_log · (logx)²)
    --              ≤ (M₀/8) · √x
    calc C * (Real.log x) ^ 2
        = (M₀ / 8) * (A_log * (Real.log x) ^ 2) := by
          rw [hA_def]; field_simp
      _ ≤ (M₀ / 8) * Real.sqrt x := by
          apply mul_le_mul_of_nonneg_left h_dom
          positivity
  -- Combined: err ≤ (M₀/4) · √x
  have h_err_total : err ≤ (M₀ / 4) * Real.sqrt x := by
    calc err = C * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀) +
            C * (Real.log x) ^ 2 := by rw [herr_def]; ring
      _ ≤ (M₀ / 8) * Real.sqrt x + (M₀ / 8) * Real.sqrt x := add_le_add h_err_a h_err_b
      _ = (M₀ / 4) * Real.sqrt x := by ring
  -- ================================================================
  -- Step 9: Chain inequalities to contradiction
  -- ================================================================
  have h_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx_pos
  have h_sqrt_nn : 0 ≤ Real.sqrt x := le_of_lt h_sqrt_pos
  -- |a| ≤ b means -b ≤ a ≤ b
  have h_abs := abs_le.mp hEF_abs
  have h_psi_ge : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + sum_full ≥ -err :=
    h_abs.1
  have h_psi_le : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + sum_full ≤ err :=
    h_abs.2
  -- Case split on σ
  rcases hσ with rfl | rfl
  · -- ================================================================
    -- Case σ = 1: Show ψ(x) - x > C₀·√x (contradicts h_bound)
    -- ================================================================
    -- From h_upper: sum_pos ≤ √x · (∑ Re(w/ρ) + ε·D) = √x · (-M + ε·D)
    have h_pos_bound : sum_pos ≤ Real.sqrt x * (-M + ε * D) := by
      have h1 := h_upper
      rw [h_sum_w] at h1
      linarith
    -- From h_sum_eq: sum_full = 2·sum_pos + R ≤ 2√x(-M + εD) + 2√x
    have h_full_bound : sum_full ≤ 2 * Real.sqrt x * (-M + ε * D) + 2 * Real.sqrt x := by
      have hR_le : R ≤ 2 * Real.sqrt x := le_trans (le_abs_self R) hR_bound
      nlinarith [h_sum_eq, h_pos_bound]
    -- From h_psi_ge: ψ-x ≥ -sum_full - err
    -- So: ψ-x ≥ -(2√x(-M+εD) + 2√x) - (M₀/4)√x
    --        = √x · (2M - 2εD - 2 - M₀/4)
    have h_coeff : 2 * M - 2 * (ε * D) - 2 - M₀ / 4 > C₀ := by
      -- 2M - M₀/4 ≥ 2M₀ - M₀/4 = 7M₀/4
      have h1 : 2 * M - M₀ / 4 ≥ 7 * M₀ / 4 := by linarith [hM_ge]
      -- 7M₀/4 ≥ 7*(|C₀|+10)/4 > |C₀| + 5
      have h2 : 7 * M₀ / 4 ≥ 7 * (|C₀| + 10) / 4 := by
        have : M₀ ≥ |C₀| + 10 := by rw [hM₀_def]; linarith [hC_nn]
        linarith
      -- 2εD < 1/2
      have h3 : 2 * (ε * D) < 1 / 2 := by linarith [hε_D]
      -- Combine: coeff > 7(|C₀|+10)/4 - 1/2 - 2 ≥ |C₀| + 15 > |C₀| ≥ C₀
      have h4 : C₀ ≤ |C₀| := le_abs_self C₀
      nlinarith [abs_nonneg C₀]
    -- Get the contradiction: ψ(x) - x > C₀·√x
    -- From h_psi_ge: ψ-x ≥ -sum_full - err
    -- -sum_full ≥ -(2√x(-M+εD) + 2√x) = (2M-2εD-2)√x (from ring)
    -- err ≤ (M₀/4)√x, so ψ-x ≥ (2M-2εD-2-M₀/4)√x > C₀√x
    have h_key : -(2 * Real.sqrt x * (-M + ε * D) + 2 * Real.sqrt x) -
        (M₀ / 4) * Real.sqrt x =
        (2 * M - 2 * (ε * D) - 2 - M₀ / 4) * Real.sqrt x := by ring
    have h_psi_lb : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≥
        (2 * M - 2 * (ε * D) - 2 - M₀ / 4) * Real.sqrt x := by
      have h5 : -sum_full - err ≥
          -(2 * Real.sqrt x * (-M + ε * D) + 2 * Real.sqrt x) -
          (M₀ / 4) * Real.sqrt x := by linarith [h_full_bound, h_err_total]
      linarith [h_psi_ge, h_key]
    -- Contradiction with h_bound
    have := h_bound x hx_X₀
    simp only [one_mul] at this
    nlinarith [h_sqrt_nn]
  · -- ================================================================
    -- Case σ = -1: Show -(ψ(x) - x) > C₀·√x (contradicts h_bound)
    -- ================================================================
    -- From h_lower: sum_pos ≥ √x · (∑ Re(w/ρ) - ε·D) = √x · (M - ε·D)
    have h_pos_bound : sum_pos ≥ Real.sqrt x * (M - ε * D) := by
      have h1 := h_lower
      rw [h_sum_w] at h1
      linarith
    -- From h_sum_eq: sum_full = 2·sum_pos + R ≥ 2√x(M - εD) - 2√x
    have h_full_bound : sum_full ≥ 2 * Real.sqrt x * (M - ε * D) - 2 * Real.sqrt x := by
      have hR_ge : -(2 * Real.sqrt x) ≤ R := by linarith [neg_abs_le R, hR_bound]
      nlinarith [h_sum_eq, h_pos_bound]
    -- From h_psi_le: ψ-x ≤ -sum_full + err
    -- So: -(ψ-x) ≥ sum_full - err ≥ 2√x(M-εD) - 2√x - (M₀/4)√x
    -- Derive coeff > C₀ (same as σ=1 case)
    have hM₀_ge_abs : M₀ ≥ |C₀| + 10 := by rw [hM₀_def]; linarith [hC_nn]
    have h_2M_bound : 2 * M ≥ 2 * M₀ := by linarith [hM_ge]
    have h_M₀_quarter : M₀ / 4 ≤ M₀ := by linarith [hM₀_pos.le]
    have h_coeff_lb : 2 * M - 2 * (ε * D) - 2 - M₀ / 4 ≥ |C₀| + 5 := by linarith [hε_D]
    have h_coeff : 2 * M - 2 * (ε * D) - 2 - M₀ / 4 > C₀ := by linarith [le_abs_self C₀]
    -- Get the contradiction: -(ψ(x) - x) > C₀·√x
    have h_key : (2 * Real.sqrt x * (M - ε * D) - 2 * Real.sqrt x) -
        (M₀ / 4) * Real.sqrt x =
        (2 * M - 2 * (ε * D) - 2 - M₀ / 4) * Real.sqrt x := by ring
    have h_neg_psi_lb : -(Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≥
        (2 * M - 2 * (ε * D) - 2 - M₀ / 4) * Real.sqrt x := by
      have h5 : sum_full - err ≥
          (2 * Real.sqrt x * (M - ε * D) - 2 * Real.sqrt x) -
          (M₀ / 4) * Real.sqrt x := by linarith [h_full_bound, h_err_total]
      linarith [h_psi_le, h_key]
    -- Contradiction with h_bound
    have h_bd := h_bound x hx_X₀
    simp only [neg_one_mul, neg_le] at h_bd
    -- h_bd : -(C₀ * √x) ≤ ψ(x) - x, i.e., -(ψ-x) ≤ C₀√x
    -- h_neg_psi_lb : -(ψ-x) ≥ coeff * √x where coeff > C₀
    -- So: C₀√x ≥ -(ψ-x) ≥ coeff * √x > C₀ * √x (for √x > 0)
    have : C₀ * Real.sqrt x < (2 * M - 2 * (ε * D) - 2 - M₀ / 4) * Real.sqrt x :=
      mul_lt_mul_of_pos_right h_coeff h_sqrt_pos
    linarith

/-- **Landau-Ingham fact** (Landau 1905, Ingham 1932):
Under RH, ψ(x) - x is unbounded above relative to √x.
Proved from `landau_psi_bounded_impossible` via `by_contra` + `push_neg`. -/
private theorem landau_ingham_unbounded_above
    [ExplicitFormulaPsiGeneralHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≥ C * Real.sqrt x := by
  by_contra h; push_neg at h
  obtain ⟨C₀, X₀, hbound⟩ := h
  exact landau_psi_bounded_impossible hRH 1 (Or.inl rfl) C₀ (X₀ + 1)
    (fun x hx => by simp only [one_mul]; exact (hbound x (by linarith)).le)

/-- Symmetric Landau-Ingham fact for the negative direction.
Proved from `landau_psi_bounded_impossible` via `by_contra` + `push_neg`. -/
private theorem landau_ingham_unbounded_below
    [ExplicitFormulaPsiGeneralHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≤ -(C * Real.sqrt x) := by
  by_contra h; push_neg at h
  obtain ⟨C₀, X₀, hbound⟩ := h
  exact landau_psi_bounded_impossible hRH (-1) (Or.inr rfl) C₀ (X₀ + 1)
    (fun x hx => by
      simp only [neg_one_mul, neg_le]
      exact (hbound x (by linarith)).le)

-- ============================================================
-- Main theorem: PsiZeroSumOscillationHyp from Landau indirect argument
-- ============================================================

/-- **B5b proved from B5a** via Landau's indirect argument (Landau 1905, Ingham 1932):

Under RH, ψ(x) - x is unbounded in both directions relative to √x.

The top-level assembly is proved from `landau_psi_bounded_impossible`; inside that
proof, the remaining atomic leaves are:
- `critical_zero_sum_diverges` (in this file),
- `exists_large_x_phases_aligned_to_target` (in DirichletPhaseAlignment).
Both directions (above and below) are then proved via `by_contra` + `push_neg`. -/
theorem psiZeroSumOscillation_proved
    [ExplicitFormulaPsiGeneralHyp] :
    PsiZeroSumOscillationHyp where
  proof := by
    intro hRH
    exact ⟨landau_ingham_unbounded_above hRH, landau_ingham_unbounded_below hRH⟩

end Aristotle.Standalone.PsiZeroSumOscillationFromIngham
```

## Additional dependency snapshot used directly by this file (phase-alignment lemmas)
```lean
import Mathlib
import Littlewood.ZetaZeros.SupremumRealPart

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

namespace Aristotle.DirichletPhaseAlignment

/-
Definition of Chebyshev functions psi and theta.
-/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.floor x + 1), ArithmeticFunction.vonMangoldt n

noncomputable def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime, Real.log p

/-
Definitions of hypotheses and oscillation property.
-/
open Real Complex Filter Asymptotics Set

/-- The set of non-trivial zeros of the Riemann Zeta function. -/
def CriticalZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- The set of critical zeros with imaginary part bounded by T. -/
def ZerosBelow (T : ℝ) : Finset ℂ :=
  if h : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite then h.toFinset else ∅

/-- Hypothesis: There are infinitely many zeros on the critical line, and the number of zeros up to T is finite. -/
class HardyCriticalLineZerosHyp : Prop where
  infinite_critical_zeros : {ρ ∈ CriticalZeros | ρ.re = 1/2}.Infinite
  zeros_finite (T : ℝ) : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite

/-- Hypothesis: The explicit formula for ψ(x) holds with a specific error bound. -/
class ExplicitFormulaPsiHyp : Type where
  C : ℝ
  psi_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevPsi x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Hypothesis: The explicit formula for θ(x) holds with a specific error bound. -/
class ExplicitFormulaThetaHyp : Type where
  C : ℝ
  theta_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevTheta x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Definition of Ω± oscillation: The function takes arbitrarily large positive and negative values relative to g. -/
def IsOmegaOscillation (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ M, ∃ x, f x ≥ M * g x) ∧ (∀ M, ∃ x, f x ≤ -M * g x)

/-- The conclusion for ψ. -/
class PsiOscillationFromCriticalZerosHyp : Prop where
  psi_osc : IsOmegaOscillation (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ. -/
class ThetaOscillationSqrtHyp : Prop where
  theta_osc : IsOmegaOscillation (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

/-
Explicit formula + infinitely many critical zeros implies Ω±(√x) oscillation for ψ(x).
-/
instance [HardyCriticalLineZerosHyp] [ExplicitFormulaPsiHyp] : PsiOscillationFromCriticalZerosHyp := by
  -- By definition of `PsiOscillationFromCriticalZerosHyp`, we need to show that `chebyshevPsi x - x` oscillates like `sqrt x`.
  constructor;
  constructor <;> intro M <;> have := ‹ExplicitFormulaPsiHyp›.psi_approx 2 2 ( by norm_num ) ( by norm_num ) <;> norm_num at *;
  · use 0 ; norm_num [ chebyshevPsi ];
  · use 0; norm_num [ chebyshevPsi ] ;

/-
Explicit formula + infinitely many critical zeros implies Ω±(√x) oscillation for θ(x).
-/
instance [HardyCriticalLineZerosHyp] [ExplicitFormulaThetaHyp] : ThetaOscillationSqrtHyp := by
  by_contra h_contra;
  obtain ⟨h_pos, h_neg⟩ : (∀ M : ℝ, ∃ x, chebyshevTheta x - x ≥ M * Real.sqrt x) ∧ (∀ M : ℝ, ∃ x, chebyshevTheta x - x ≤ -M * Real.sqrt x) := by
    constructor <;> intro M <;> have := ‹ExplicitFormulaThetaHyp›.theta_approx 2 2 ( by norm_num ) ( by norm_num ) <;> norm_num at this;
    · use 0; norm_num;
      exact Finset.sum_nonneg fun _ _ => by positivity;
    · use 0; norm_num [ chebyshevTheta ] ;
      norm_num [ Finset.sum_filter ];
  exact h_contra ⟨ h_pos, h_neg ⟩

/-
Redefinition of oscillation at infinity and new theorem classes.
-/
open Real Complex Filter Asymptotics Set

/-- Definition of Ω± oscillation at infinity: The function takes arbitrarily large positive and negative values relative to g, for arbitrarily large inputs. -/
def IsOmegaOscillationAtTop (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ M, ∃ x, x > M ∧ f x ≥ M * g x) ∧ (∀ M, ∃ x, x > M ∧ f x ≤ -M * g x)

/-- The conclusion for ψ using the correct oscillation definition. -/
class PsiOscillationFromCriticalZerosHypAtTop : Prop where
  psi_osc : IsOmegaOscillationAtTop (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ using the correct oscillation definition. -/
class ThetaOscillationSqrtHypAtTop : Prop where
  theta_osc : IsOmegaOscillationAtTop (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

/-
Simultaneous Dirichlet Approximation Theorem: Given n real numbers and an integer N, there exists a small integer multiple that is close to an integer for all of them.
-/
lemma simultaneous_dirichlet_approximation {n : ℕ} (ξ : Fin n → ℝ) (N : ℕ) (hN : N > 0) :
  ∃ t : ℕ, 0 < t ∧ t ≤ N ^ n ∧ ∀ i, ∃ p : ℤ, |↑t * ξ i - p| ≤ 1 / N := by
    -- By the pigeonhole principle, since there are $N^n + 1$ vectors and only $N^n$ subcubes, at least two of these vectors must fall into the same subcube.
    obtain ⟨t1, t2, ht1t2, h_subcube⟩ : ∃ t1 t2 : ℕ, t1 < t2 ∧ t1 ≤ N^n ∧ t2 ≤ N^n ∧ ∀ i : Fin n, ⌊(t1 * ξ i - ⌊t1 * ξ i⌋ : ℝ) * N⌋ = ⌊(t2 * ξ i - ⌊t2 * ξ i⌋ : ℝ) * N⌋ := by
      by_contra h_contra;
      -- By the pigeonhole principle, since there are $N^n + 1$ vectors and only $N^n$ subcubes, at least two of these vectors must fall into the same subcube. Hence, we can find such $t1$ and $t2$.
      have h_pigeonhole : Finset.card (Finset.image (fun t : ℕ => fun i => ⌊((t : ℝ) * (ξ i) - ⌊(t : ℝ) * (ξ i)⌋) * N⌋) (Finset.range (N^n + 1))) ≤ N^n := by
        refine' le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _;
        exact Finset.Icc ( 0 : Fin n → ℤ ) ( fun _ => N - 1 );
        · exact fun x hx => Finset.mem_Icc.mpr ⟨ fun i => Int.floor_nonneg.mpr ( mul_nonneg ( Int.fract_nonneg _ ) ( Nat.cast_nonneg _ ) ), fun i => Int.le_sub_one_of_lt ( Int.floor_lt.mpr ( by norm_num; nlinarith [ Int.fract_nonneg ( ( x : ℝ ) * ξ i ), Int.fract_lt_one ( ( x : ℝ ) * ξ i ), show ( N : ℝ ) ≥ 1 by norm_cast ] ) ) ⟩;
        · erw [ Finset.card_map, Finset.card_pi ] ; aesop;
      exact (not_lt.2 h_pigeonhole) ( by rw [ Finset.card_image_of_injOn fun t ht t' ht' h => le_antisymm ( not_lt.mp fun contra => h_contra ⟨ t', t, contra, by linarith [ Finset.mem_range.mp ht', Finset.mem_range.mp ht ], by linarith [ Finset.mem_range.mp ht', Finset.mem_range.mp ht ], fun i => by simpa using congr_fun h.symm i ⟩ ) ( not_lt.mp fun contra => h_contra ⟨ t, t', contra, by linarith [ Finset.mem_range.mp ht, Finset.mem_range.mp ht' ], by linarith [ Finset.mem_range.mp ht, Finset.mem_range.mp ht' ], fun i => by simpa using congr_fun h i ⟩ ) ] ; simp +arith +decide );
    refine' ⟨ t2 - t1, tsub_pos_of_lt ht1t2, _, _ ⟩;
    · exact Nat.sub_le_of_le_add <| by linarith;
    · intro i; specialize h_subcube; have := h_subcube.2.2 i; rw [ Int.floor_eq_iff ] at this; norm_num at *;
      refine' ⟨ ⌊ ( t2 : ℝ ) * ξ i⌋ - ⌊ ( t1 : ℝ ) * ξ i⌋, _ ⟩ ; rw [ Nat.cast_sub ht1t2.le ] ; rw [ abs_le ] ; constructor <;> push_cast <;> nlinarith [ Int.fract_add_floor ( ( t2 : ℝ ) * ξ i ), Int.fract_add_floor ( ( t1 : ℝ ) * ξ i ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ), Int.floor_le ( Int.fract ( ( t2 : ℝ ) * ξ i ) * N ), Int.lt_floor_add_one ( Int.fract ( ( t2 : ℝ ) * ξ i ) * N ) ]

/-
For any finite set of frequencies and any epsilon, there exists an arbitrarily large x such that all phases align near 1.
-/
lemma exists_large_x_phases_aligned {n : ℕ} (γ : Fin n → ℝ) (ε : ℝ) (hε : ε > 0) (X : ℝ) :
  ∃ x > X, ∀ i, ‖(x : ℂ) ^ (I * γ i) - 1‖ < ε := by
    -- Define the frequencies $\gamma_i$.
    set γ_vals : Fin n → ℝ := fun i => γ i / (2 * Real.pi) with hγ_vals_def;
    -- Choose a large integer $N$ such that $N \delta > L + 1$, where $\delta = \epsilon / (2\pi)$ and $L = \log X$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 < N ∧ N * (ε / (4 * Real.pi)) > Real.log (max X 1) + 1 := by
      exact ⟨ ⌊ ( Real.log ( Max.max X 1 ) + 1 ) / ( ε / ( 4 * Real.pi ) ) ⌋₊ + 1, Nat.succ_pos _, by push_cast; nlinarith [ Nat.lt_floor_add_one ( ( Real.log ( Max.max X 1 ) + 1 ) / ( ε / ( 4 * Real.pi ) ) ), show 0 < ε / ( 4 * Real.pi ) by positivity, mul_div_cancel₀ ( Real.log ( Max.max X 1 ) + 1 ) ( show ε / ( 4 * Real.pi ) ≠ 0 by positivity ) ] ⟩;
    -- Apply Dirichlet approximation with a large integer $N$.
    obtain ⟨t₀, ht₀_pos, ht₀_le, ht₀_approx⟩ : ∃ t₀ : ℕ, 0 < t₀ ∧ t₀ ≤ N ^ n ∧ ∀ i, ∃ p : ℤ, |↑t₀ * γ_vals i - p| ≤ 1 / N := by
      convert simultaneous_dirichlet_approximation γ_vals N hN.1 using 1;
    -- Choose $k$ such that $k t₀ > L$ and $k/N < \delta$.
    obtain ⟨k, hk_pos, hk_gt_L, hk_lt_delta⟩ : ∃ k : ℕ, 0 < k ∧ k * t₀ > Real.log (max X 1) ∧ k / (N : ℝ) < ε / (4 * Real.pi) := by
      refine' ⟨ ⌊Real.log ( Max.max X 1 ) ⌋₊ + 1, _, _, _ ⟩ <;> norm_num;
      · nlinarith [ Nat.lt_floor_add_one ( Real.log ( Max.max X 1 ) ), show ( t₀ : ℝ ) ≥ 1 by norm_cast ];
      · rw [ div_lt_iff₀ ] <;> nlinarith [ Nat.floor_le ( Real.log_nonneg ( show 1 ≤ Max.max X 1 by norm_num ) ), Real.pi_gt_three, mul_div_cancel₀ ε ( by positivity : ( 4 * Real.pi ) ≠ 0 ), show ( N : ℝ ) ≥ 1 by norm_cast; linarith ];
    -- Let $t = k t₀$. Then $t \ge k > L$, so $e^t > X$.
    set t : ℝ := k * t₀ with ht_def
    have ht_gt_L : t > Real.log (max X 1) := by
      exact hk_gt_L
    have hx_gt_X : Real.exp t > max X 1 := by
      rwa [ gt_iff_lt, Real.log_lt_iff_lt_exp ( by positivity ) ] at ht_gt_L;
    -- And $|t \gamma_i - 2\pi (k p_i)| = k |t₀ \gamma_i - p_i| \le k/N < \delta$.
    have h_phase_approx : ∀ i, ∃ p : ℤ, |t * γ i - 2 * Real.pi * k * p| < ε / 2 := by
      intro i
      obtain ⟨p, hp⟩ := ht₀_approx i
      use p
      have h_phase_approx_i : |t * γ i - 2 * Real.pi * k * p| ≤ k / N * 2 * Real.pi := by
        convert mul_le_mul_of_nonneg_left hp ( show ( 0 : ℝ ) ≤ 2 * Real.pi * k by positivity ) using 1 <;> ring;
        rw [ show t * γ i - Real.pi * k * p * 2 = Real.pi * k * ( -p + t₀ * γ_vals i ) * 2 by push_cast [ ht_def, hγ_vals_def ] ; ring_nf; norm_num [ Real.pi_ne_zero ] ] ; rw [ abs_mul, abs_mul, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ Real.pi * k ) ] ; ring;
      exact h_phase_approx_i.trans_lt ( by nlinarith [ Real.pi_pos, mul_div_cancel₀ ( k : ℝ ) ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ), mul_div_cancel₀ ε ( by positivity : ( 4 * Real.pi ) ≠ 0 ) ] );
    -- This implies $|e^{i t \gamma_i} - 1| < \epsilon$ (roughly, using Lipschitz of exp).
    have h_exp_approx : ∀ i, ‖Complex.exp (Complex.I * (t * γ i)) - 1‖ < ε := by
      intro i
      obtain ⟨p, hp⟩ := h_phase_approx i
      have h_exp_approx_i : ‖Complex.exp (Complex.I * (t * γ i)) - 1‖ ≤ |t * γ i - 2 * Real.pi * k * p| := by
        have h_exp_approx_i : ‖Complex.exp (Complex.I * (t * γ i)) - 1‖ = ‖Complex.exp (Complex.I * (t * γ i - 2 * Real.pi * k * p)) - 1‖ := by
          norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
          norm_num [ mul_assoc, mul_comm Real.pi _, mul_left_comm ];
          norm_num [ show Real.cos ( t * γ i - p * ( k * ( 2 * Real.pi ) ) ) = Real.cos ( t * γ i ) by convert Real.cos_periodic.int_mul ( -p * k ) _ using 2; push_cast; ring, show Real.sin ( t * γ i - p * ( k * ( 2 * Real.pi ) ) ) = Real.sin ( t * γ i ) by convert Real.sin_periodic.int_mul ( -p * k ) _ using 2; push_cast; ring ];
        -- Using the fact that $|e^{i\theta} - 1| \leq |\theta|$ for any real $\theta$, we get:
        have h_exp_approx_i : ∀ θ : ℝ, ‖Complex.exp (Complex.I * θ) - 1‖ ≤ |θ| := by
          intros θ
          have h_exp_approx_i : ‖Complex.exp (Complex.I * θ) - 1‖ = 2 * |Real.sin (θ / 2)| := by
            norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
            rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring <;> norm_num [ Real.sin_sq, Real.cos_sq ] <;> ring;
            nlinarith [ Real.cos_sq' θ ];
          -- Using the fact that $|\sin(x)| \leq |x|$ for any real $x$, we get:
          have h_sin_approx : ∀ x : ℝ, |Real.sin x| ≤ |x| := fun x => abs_sin_le_abs;
          exact h_exp_approx_i.symm ▸ by simpa [ abs_div, mul_div_cancel₀ ] using mul_le_mul_of_nonneg_left ( h_sin_approx ( θ / 2 ) ) zero_le_two;
        convert h_exp_approx_i ( t * γ i - 2 * Real.pi * k * p ) using 1 ; norm_cast;
        aesop;
      linarith;
    use Real.exp t;
    simp_all +decide [ Complex.cpow_def_of_ne_zero, Complex.exp_ne_zero ];
    convert h_exp_approx using 3 ; rw [ Complex.log_exp ] <;> ring ; norm_num [ Real.pi_pos.ne' ];
    · positivity;
    · norm_cast ; linarith [ Real.pi_pos ]

/-
Redefinition of hypotheses with V2 suffix.
-/
open Real Complex Filter Asymptotics Set

/-- Hypothesis: There are infinitely many zeros on the critical line, and the sum of their reciprocals diverges. -/
class HardyCriticalLineZerosHyp_V2 : Prop where
  infinite_critical_zeros : {ρ ∈ CriticalZeros | ρ.re = 1/2}.Infinite
  zeros_finite (T : ℝ) : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite
  sum_inv_rho_diverges : ∀ B : ℝ, ∃ T : ℝ, ∑ ρ ∈ ZerosBelow T, 1 / ‖ρ‖ > B

/-- Hypothesis: The explicit formula for ψ(x) holds with a specific error bound. -/
class ExplicitFormulaPsiHyp_V2 : Type where
  C : ℝ
  psi_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevPsi x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Hypothesis: The explicit formula for θ(x) holds with a specific error bound. -/
class ExplicitFormulaThetaHyp_V2 : Type where
  C : ℝ
  theta_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevTheta x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- The conclusion for ψ using the correct oscillation definition. -/
class PsiOscillationFromCriticalZerosHypAtTop_V2 : Prop where
  psi_osc : IsOmegaOscillationAtTop (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ using the correct oscillation definition. -/
class ThetaOscillationSqrtHypAtTop_V2 : Prop where
  theta_osc : IsOmegaOscillationAtTop (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

/-
Redefinition of hypotheses with V3 suffix and helper lemma for Finset.
-/
open Real Complex Filter Asymptotics Set

/-- Hypothesis: There are infinitely many zeros on the critical line, and the sum of the real parts of their reciprocals diverges. -/
class HardyCriticalLineZerosHyp_V3 : Prop where
  infinite_critical_zeros : {ρ ∈ CriticalZeros | ρ.re = 1/2}.Infinite
  zeros_finite (T : ℝ) : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite
  sum_re_inv_rho_diverges : ∀ B : ℝ, ∃ T : ℝ, ∑ ρ ∈ ZerosBelow T, (1 / ρ).re > B

/-- Hypothesis: The explicit formula for ψ(x) holds with a specific error bound. -/
class ExplicitFormulaPsiHyp_V3 : Type where
  C : ℝ
  psi_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevPsi x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Hypothesis: The explicit formula for θ(x) holds with a specific error bound. -/
class ExplicitFormulaThetaHyp_V3 : Type where
  C : ℝ
  theta_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevTheta x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- The conclusion for ψ using the correct oscillation definition. -/
class PsiOscillationFromCriticalZerosHypAtTop_V3 : Prop where
  psi_osc : IsOmegaOscillationAtTop (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ using the correct oscillation definition. -/
class ThetaOscillationSqrtHypAtTop_V3 : Prop where
  theta_osc : IsOmegaOscillationAtTop (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

lemma exists_large_x_phases_aligned_finset (S : Finset ℂ) (_hS : ∀ ρ ∈ S, ρ.re = 1/2) (ε : ℝ) (hε : ε > 0) (X : ℝ) :
  ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - 1‖ < ε := by
    -- Apply the simultaneous Dirichlet approximation theorem to the frequencies γ_i = ρ.im for ρ in S.
    have h_dirichlet : ∀ (γ : Fin (Finset.card S) → ℝ) (ε : ℝ) (hε : ε > 0) (X : ℝ), ∃ x > X, ∀ i, ‖(x : ℂ) ^ (I * γ i) - 1‖ < ε :=
      fun γ' ε' hε' X' => exists_large_x_phases_aligned γ' ε' hε' X';
    -- By definition of $S$, we can create a bijection between $S$ and $\{0, 1, ..., S.card - 1\}$.
    obtain ⟨f, hf⟩ : ∃ f : S ≃ Fin (Finset.card S), True := by
      exact ⟨ Fintype.equivOfCardEq <| by simp +decide, trivial ⟩;
    obtain ⟨ x, hx₁, hx₂ ⟩ := h_dirichlet ( fun i => ( f.symm i |> Subtype.val |> Complex.im ) ) ε hε X;
    exact ⟨ x, hx₁, fun ρ hρ => by simpa using hx₂ ( f ⟨ ρ, hρ ⟩ ) ⟩

/-
Lower bound on the real part of the sum when phases are aligned.
-/
lemma bound_real_part_of_sum_aligned {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re = 1/2) {x : ℝ} (hx : x > 0) {ε : ℝ} (_hε : ε > 0)
  (h_phases : ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - 1‖ < ε) :
  (∑ ρ ∈ S, (x : ℂ)^ρ / ρ).re ≥ Real.sqrt x * ((∑ ρ ∈ S, (1/ρ).re) - ε * (∑ ρ ∈ S, 1/‖ρ‖)) := by
    -- For each $\rho \in S$, we have $\text{Re}(x^\rho/\rho) = \sqrt{x} \text{Re}(u_\rho/\rho)$ where $u_\rho = x^{i \text{Im}(\rho)}$.
    have h_re_expr (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re ((x : ℂ) ^ ρ / ρ) = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
      rw [ show ρ = 1 / 2 + Complex.I * ρ.im by simp +decide [ Complex.ext_iff, hS ρ hρ ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero, hx.ne' ] ; ring;
      norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring;
      norm_num [ Complex.arg_ofReal_of_nonneg hx.le, Real.sin_add, Real.cos_add, mul_assoc, ← Real.exp_add ] ; ring;
    -- Using the bound on $\|u_\rho - 1\|$, we get $\text{Re}((u_\rho - 1)/\rho) \ge -|(u_\rho - 1)/\rho| = -|u_\rho - 1|/|\rho| > -\epsilon/|\rho|$.
    have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - 1) / ρ) ≥ -ε / ‖ρ‖ := by
      have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - 1) / ρ) ≥ -‖((x : ℂ) ^ (Complex.I * ρ.im) - 1) / ρ‖ := by
        exact neg_le_of_abs_le ( Complex.abs_re_le_norm _ ) |> le_trans <| by norm_num;
      exact le_trans ( by simpa [ neg_div ] using div_le_div_of_nonneg_right ( neg_le_neg ( le_of_lt ( h_phases ρ hρ ) ) ) ( norm_nonneg ρ ) ) ( h_re_bound ρ hρ );
    simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
    rw [ ← Finset.sum_sub_distrib ];
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_re_bound i hi, Real.sqrt_nonneg x ] ;

/-
Generalized lower bound on Re(∑ x^ρ/ρ) when phases are aligned to an arbitrary
target w on the unit circle (not just w = 1).

When w = I (imaginary unit), the main term ∑ Re(I/ρ) = ∑ γ/(1/4+γ²) ≈ ∑ 1/γ
which DIVERGES — this is the key to proving Littlewood's oscillation theorem.
Contrast with w = 1 where ∑ Re(1/ρ) = ∑ (1/2)/(1/4+γ²) CONVERGES.
-/
lemma bound_real_part_of_sum_shifted {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    {x : ℝ} (hx : x > 0) {w : ℂ} (_hw : ‖w‖ = 1) {ε : ℝ} (_hε : ε > 0)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε) :
    (∑ ρ ∈ S, (x : ℂ)^ρ / ρ).re ≥ Real.sqrt x * ((∑ ρ ∈ S, (w/ρ).re) - ε * (∑ ρ ∈ S, 1/‖ρ‖)) := by
  -- Decompose x^ρ/ρ = √x · u_ρ/ρ where u_ρ = x^{iγ}
  have h_re_expr (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re ((x : ℂ) ^ ρ / ρ) = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
    rw [ show ρ = 1 / 2 + Complex.I * ρ.im by simp +decide [ Complex.ext_iff, hS ρ hρ ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero, hx.ne' ] ; ring;
    norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring;
    norm_num [ Complex.arg_ofReal_of_nonneg hx.le, Real.sin_add, Real.cos_add, mul_assoc, ← Real.exp_add ] ; ring;
  -- Bound: Re((u_ρ - w)/ρ) ≥ -ε/‖ρ‖
  have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ) ≥ -ε / ‖ρ‖ := by
    have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ) ≥ -‖((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ‖ := by
      exact neg_le_of_abs_le ( Complex.abs_re_le_norm _ ) |> le_trans <| by norm_num;
    exact le_trans ( by simpa [ neg_div ] using div_le_div_of_nonneg_right ( neg_le_neg ( le_of_lt ( h_phases ρ hρ ) ) ) ( norm_nonneg ρ ) ) ( h_re_bound ρ hρ );
  simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
  rw [ ← Finset.sum_sub_distrib ];
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_re_bound i hi, Real.sqrt_nonneg x ] ;

/-
Upper bound companion: when phases are aligned to w, the real part of ∑ x^ρ/ρ
is at most √x · (∑ Re(w/ρ) + ε · ∑ 1/‖ρ‖).
Needed for the NEGATIVE oscillation direction.
-/
lemma bound_real_part_of_sum_shifted_upper {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    {x : ℝ} (hx : x > 0) {w : ℂ} (_hw : ‖w‖ = 1) {ε : ℝ} (_hε : ε > 0)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε) :
    (∑ ρ ∈ S, (x : ℂ)^ρ / ρ).re ≤ Real.sqrt x * ((∑ ρ ∈ S, (w/ρ).re) + ε * (∑ ρ ∈ S, 1/‖ρ‖)) := by
  -- Decompose x^ρ/ρ = √x · u_ρ/ρ where u_ρ = x^{iγ}
  have h_re_expr (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re ((x : ℂ) ^ ρ / ρ) = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
    rw [ show ρ = 1 / 2 + Complex.I * ρ.im by simp +decide [ Complex.ext_iff, hS ρ hρ ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero, hx.ne' ] ; ring;
    norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring;
    norm_num [ Complex.arg_ofReal_of_nonneg hx.le, Real.sin_add, Real.cos_add, mul_assoc, ← Real.exp_add ] ; ring;
  -- Bound: Re((u_ρ - w)/ρ) ≤ ε/‖ρ‖
  have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ) ≤ ε / ‖ρ‖ := by
    calc Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ)
        ≤ ‖((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ‖ :=
          le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
      _ = ‖(x : ℂ) ^ (Complex.I * ρ.im) - w‖ / ‖ρ‖ := by
          rw [norm_div]
      _ ≤ ε / ‖ρ‖ := by
          exact div_le_div_of_nonneg_right (le_of_lt (h_phases ρ hρ)) (norm_nonneg ρ)
  simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
  rw [ ← Finset.sum_add_distrib ];
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_re_bound i hi, Real.sqrt_nonneg x ] ;

/-- **B5b-infra sorry**: Phase alignment to an arbitrary target w on S¹.

Given RH, a finite set S of zeros with Re(ρ) = 1/2 and Im(ρ) > 0, a target w
with ‖w‖ = 1, ε > 0, and X, there exists x > X such that all phases
x^{iγ} are within ε of w.

This is the inhomogeneous simultaneous Dirichlet approximation with equal
targets. The lemma is FALSE for arbitrary frequency sets (counterexample:
γ₁=1, γ₂=2, w=e^{iπ/3}). For zeta zeros, it holds because:

(1) Zeta zero ordinates are NOT all commensurate: if ∃c>0 with all γ_k ∈ c·ℤ,
    then N⁺(T) ≤ T/c + O(1), contradicting N⁺(T) ~ (T/2π)logT from RvM.
(2) Not-commensurate frequencies generate a dense subgroup G ⊆ ℝ/2πℤ via
    the map t ↦ (tγ₁ mod 2π, ..., tγₙ mod 2π).
(3) Density of G implies G ⊇ Δ (the diagonal), giving equal-target approximation.

The homogeneous case (w = 1) is proved in `exists_large_x_phases_aligned_finset`.
The gap is extending to arbitrary w via Kronecker's theorem (1884).

Now takes RH as a parameter, since the proof uses properties specific to
zeta zero ordinates (superlinear growth of N(T)).

**Blocked by**: Kronecker's theorem formalization + uniform Riemann-von Mangoldt.

References: Kronecker 1884, Hardy-Wright (2008) §23.8, Titchmarsh (1986) §9.4. -/
lemma exists_large_x_phases_aligned_to_target
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    (hS_pos : ∀ ρ ∈ S, 0 < ρ.im)
    (w : ℂ) (hw : ‖w‖ = 1) (ε : ℝ) (hε : ε > 0) (X : ℝ)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε := by
  sorry

end Aristotle.DirichletPhaseAlignment

end
```

---

## Prompt C

# No-Repo Full-Context Prompt C

You have no repository access. Use only the code in this prompt.

Task: prove `exists_large_x_phases_aligned_to_target` with no axioms/sorry/admit and keep signature unchanged.

Output required:
1. Replacement Lean code for the theorem proof (and helper lemmas in same namespace if needed).
2. Brief explanation.
3. If impossible, exact formal blocker and strongest unconditional helper theorem you can still prove.

## Full current file snapshot
```lean
import Mathlib
import Littlewood.ZetaZeros.SupremumRealPart

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

namespace Aristotle.DirichletPhaseAlignment

/-
Definition of Chebyshev functions psi and theta.
-/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.floor x + 1), ArithmeticFunction.vonMangoldt n

noncomputable def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime, Real.log p

/-
Definitions of hypotheses and oscillation property.
-/
open Real Complex Filter Asymptotics Set

/-- The set of non-trivial zeros of the Riemann Zeta function. -/
def CriticalZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- The set of critical zeros with imaginary part bounded by T. -/
def ZerosBelow (T : ℝ) : Finset ℂ :=
  if h : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite then h.toFinset else ∅

/-- Hypothesis: There are infinitely many zeros on the critical line, and the number of zeros up to T is finite. -/
class HardyCriticalLineZerosHyp : Prop where
  infinite_critical_zeros : {ρ ∈ CriticalZeros | ρ.re = 1/2}.Infinite
  zeros_finite (T : ℝ) : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite

/-- Hypothesis: The explicit formula for ψ(x) holds with a specific error bound. -/
class ExplicitFormulaPsiHyp : Type where
  C : ℝ
  psi_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevPsi x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Hypothesis: The explicit formula for θ(x) holds with a specific error bound. -/
class ExplicitFormulaThetaHyp : Type where
  C : ℝ
  theta_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevTheta x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Definition of Ω± oscillation: The function takes arbitrarily large positive and negative values relative to g. -/
def IsOmegaOscillation (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ M, ∃ x, f x ≥ M * g x) ∧ (∀ M, ∃ x, f x ≤ -M * g x)

/-- The conclusion for ψ. -/
class PsiOscillationFromCriticalZerosHyp : Prop where
  psi_osc : IsOmegaOscillation (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ. -/
class ThetaOscillationSqrtHyp : Prop where
  theta_osc : IsOmegaOscillation (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

/-
Explicit formula + infinitely many critical zeros implies Ω±(√x) oscillation for ψ(x).
-/
instance [HardyCriticalLineZerosHyp] [ExplicitFormulaPsiHyp] : PsiOscillationFromCriticalZerosHyp := by
  -- By definition of `PsiOscillationFromCriticalZerosHyp`, we need to show that `chebyshevPsi x - x` oscillates like `sqrt x`.
  constructor;
  constructor <;> intro M <;> have := ‹ExplicitFormulaPsiHyp›.psi_approx 2 2 ( by norm_num ) ( by norm_num ) <;> norm_num at *;
  · use 0 ; norm_num [ chebyshevPsi ];
  · use 0; norm_num [ chebyshevPsi ] ;

/-
Explicit formula + infinitely many critical zeros implies Ω±(√x) oscillation for θ(x).
-/
instance [HardyCriticalLineZerosHyp] [ExplicitFormulaThetaHyp] : ThetaOscillationSqrtHyp := by
  by_contra h_contra;
  obtain ⟨h_pos, h_neg⟩ : (∀ M : ℝ, ∃ x, chebyshevTheta x - x ≥ M * Real.sqrt x) ∧ (∀ M : ℝ, ∃ x, chebyshevTheta x - x ≤ -M * Real.sqrt x) := by
    constructor <;> intro M <;> have := ‹ExplicitFormulaThetaHyp›.theta_approx 2 2 ( by norm_num ) ( by norm_num ) <;> norm_num at this;
    · use 0; norm_num;
      exact Finset.sum_nonneg fun _ _ => by positivity;
    · use 0; norm_num [ chebyshevTheta ] ;
      norm_num [ Finset.sum_filter ];
  exact h_contra ⟨ h_pos, h_neg ⟩

/-
Redefinition of oscillation at infinity and new theorem classes.
-/
open Real Complex Filter Asymptotics Set

/-- Definition of Ω± oscillation at infinity: The function takes arbitrarily large positive and negative values relative to g, for arbitrarily large inputs. -/
def IsOmegaOscillationAtTop (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ M, ∃ x, x > M ∧ f x ≥ M * g x) ∧ (∀ M, ∃ x, x > M ∧ f x ≤ -M * g x)

/-- The conclusion for ψ using the correct oscillation definition. -/
class PsiOscillationFromCriticalZerosHypAtTop : Prop where
  psi_osc : IsOmegaOscillationAtTop (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ using the correct oscillation definition. -/
class ThetaOscillationSqrtHypAtTop : Prop where
  theta_osc : IsOmegaOscillationAtTop (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

/-
Simultaneous Dirichlet Approximation Theorem: Given n real numbers and an integer N, there exists a small integer multiple that is close to an integer for all of them.
-/
lemma simultaneous_dirichlet_approximation {n : ℕ} (ξ : Fin n → ℝ) (N : ℕ) (hN : N > 0) :
  ∃ t : ℕ, 0 < t ∧ t ≤ N ^ n ∧ ∀ i, ∃ p : ℤ, |↑t * ξ i - p| ≤ 1 / N := by
    -- By the pigeonhole principle, since there are $N^n + 1$ vectors and only $N^n$ subcubes, at least two of these vectors must fall into the same subcube.
    obtain ⟨t1, t2, ht1t2, h_subcube⟩ : ∃ t1 t2 : ℕ, t1 < t2 ∧ t1 ≤ N^n ∧ t2 ≤ N^n ∧ ∀ i : Fin n, ⌊(t1 * ξ i - ⌊t1 * ξ i⌋ : ℝ) * N⌋ = ⌊(t2 * ξ i - ⌊t2 * ξ i⌋ : ℝ) * N⌋ := by
      by_contra h_contra;
      -- By the pigeonhole principle, since there are $N^n + 1$ vectors and only $N^n$ subcubes, at least two of these vectors must fall into the same subcube. Hence, we can find such $t1$ and $t2$.
      have h_pigeonhole : Finset.card (Finset.image (fun t : ℕ => fun i => ⌊((t : ℝ) * (ξ i) - ⌊(t : ℝ) * (ξ i)⌋) * N⌋) (Finset.range (N^n + 1))) ≤ N^n := by
        refine' le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _;
        exact Finset.Icc ( 0 : Fin n → ℤ ) ( fun _ => N - 1 );
        · exact fun x hx => Finset.mem_Icc.mpr ⟨ fun i => Int.floor_nonneg.mpr ( mul_nonneg ( Int.fract_nonneg _ ) ( Nat.cast_nonneg _ ) ), fun i => Int.le_sub_one_of_lt ( Int.floor_lt.mpr ( by norm_num; nlinarith [ Int.fract_nonneg ( ( x : ℝ ) * ξ i ), Int.fract_lt_one ( ( x : ℝ ) * ξ i ), show ( N : ℝ ) ≥ 1 by norm_cast ] ) ) ⟩;
        · erw [ Finset.card_map, Finset.card_pi ] ; aesop;
      exact (not_lt.2 h_pigeonhole) ( by rw [ Finset.card_image_of_injOn fun t ht t' ht' h => le_antisymm ( not_lt.mp fun contra => h_contra ⟨ t', t, contra, by linarith [ Finset.mem_range.mp ht', Finset.mem_range.mp ht ], by linarith [ Finset.mem_range.mp ht', Finset.mem_range.mp ht ], fun i => by simpa using congr_fun h.symm i ⟩ ) ( not_lt.mp fun contra => h_contra ⟨ t, t', contra, by linarith [ Finset.mem_range.mp ht, Finset.mem_range.mp ht' ], by linarith [ Finset.mem_range.mp ht, Finset.mem_range.mp ht' ], fun i => by simpa using congr_fun h i ⟩ ) ] ; simp +arith +decide );
    refine' ⟨ t2 - t1, tsub_pos_of_lt ht1t2, _, _ ⟩;
    · exact Nat.sub_le_of_le_add <| by linarith;
    · intro i; specialize h_subcube; have := h_subcube.2.2 i; rw [ Int.floor_eq_iff ] at this; norm_num at *;
      refine' ⟨ ⌊ ( t2 : ℝ ) * ξ i⌋ - ⌊ ( t1 : ℝ ) * ξ i⌋, _ ⟩ ; rw [ Nat.cast_sub ht1t2.le ] ; rw [ abs_le ] ; constructor <;> push_cast <;> nlinarith [ Int.fract_add_floor ( ( t2 : ℝ ) * ξ i ), Int.fract_add_floor ( ( t1 : ℝ ) * ξ i ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ), Int.floor_le ( Int.fract ( ( t2 : ℝ ) * ξ i ) * N ), Int.lt_floor_add_one ( Int.fract ( ( t2 : ℝ ) * ξ i ) * N ) ]

/-
For any finite set of frequencies and any epsilon, there exists an arbitrarily large x such that all phases align near 1.
-/
lemma exists_large_x_phases_aligned {n : ℕ} (γ : Fin n → ℝ) (ε : ℝ) (hε : ε > 0) (X : ℝ) :
  ∃ x > X, ∀ i, ‖(x : ℂ) ^ (I * γ i) - 1‖ < ε := by
    -- Define the frequencies $\gamma_i$.
    set γ_vals : Fin n → ℝ := fun i => γ i / (2 * Real.pi) with hγ_vals_def;
    -- Choose a large integer $N$ such that $N \delta > L + 1$, where $\delta = \epsilon / (2\pi)$ and $L = \log X$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 < N ∧ N * (ε / (4 * Real.pi)) > Real.log (max X 1) + 1 := by
      exact ⟨ ⌊ ( Real.log ( Max.max X 1 ) + 1 ) / ( ε / ( 4 * Real.pi ) ) ⌋₊ + 1, Nat.succ_pos _, by push_cast; nlinarith [ Nat.lt_floor_add_one ( ( Real.log ( Max.max X 1 ) + 1 ) / ( ε / ( 4 * Real.pi ) ) ), show 0 < ε / ( 4 * Real.pi ) by positivity, mul_div_cancel₀ ( Real.log ( Max.max X 1 ) + 1 ) ( show ε / ( 4 * Real.pi ) ≠ 0 by positivity ) ] ⟩;
    -- Apply Dirichlet approximation with a large integer $N$.
    obtain ⟨t₀, ht₀_pos, ht₀_le, ht₀_approx⟩ : ∃ t₀ : ℕ, 0 < t₀ ∧ t₀ ≤ N ^ n ∧ ∀ i, ∃ p : ℤ, |↑t₀ * γ_vals i - p| ≤ 1 / N := by
      convert simultaneous_dirichlet_approximation γ_vals N hN.1 using 1;
    -- Choose $k$ such that $k t₀ > L$ and $k/N < \delta$.
    obtain ⟨k, hk_pos, hk_gt_L, hk_lt_delta⟩ : ∃ k : ℕ, 0 < k ∧ k * t₀ > Real.log (max X 1) ∧ k / (N : ℝ) < ε / (4 * Real.pi) := by
      refine' ⟨ ⌊Real.log ( Max.max X 1 ) ⌋₊ + 1, _, _, _ ⟩ <;> norm_num;
      · nlinarith [ Nat.lt_floor_add_one ( Real.log ( Max.max X 1 ) ), show ( t₀ : ℝ ) ≥ 1 by norm_cast ];
      · rw [ div_lt_iff₀ ] <;> nlinarith [ Nat.floor_le ( Real.log_nonneg ( show 1 ≤ Max.max X 1 by norm_num ) ), Real.pi_gt_three, mul_div_cancel₀ ε ( by positivity : ( 4 * Real.pi ) ≠ 0 ), show ( N : ℝ ) ≥ 1 by norm_cast; linarith ];
    -- Let $t = k t₀$. Then $t \ge k > L$, so $e^t > X$.
    set t : ℝ := k * t₀ with ht_def
    have ht_gt_L : t > Real.log (max X 1) := by
      exact hk_gt_L
    have hx_gt_X : Real.exp t > max X 1 := by
      rwa [ gt_iff_lt, Real.log_lt_iff_lt_exp ( by positivity ) ] at ht_gt_L;
    -- And $|t \gamma_i - 2\pi (k p_i)| = k |t₀ \gamma_i - p_i| \le k/N < \delta$.
    have h_phase_approx : ∀ i, ∃ p : ℤ, |t * γ i - 2 * Real.pi * k * p| < ε / 2 := by
      intro i
      obtain ⟨p, hp⟩ := ht₀_approx i
      use p
      have h_phase_approx_i : |t * γ i - 2 * Real.pi * k * p| ≤ k / N * 2 * Real.pi := by
        convert mul_le_mul_of_nonneg_left hp ( show ( 0 : ℝ ) ≤ 2 * Real.pi * k by positivity ) using 1 <;> ring;
        rw [ show t * γ i - Real.pi * k * p * 2 = Real.pi * k * ( -p + t₀ * γ_vals i ) * 2 by push_cast [ ht_def, hγ_vals_def ] ; ring_nf; norm_num [ Real.pi_ne_zero ] ] ; rw [ abs_mul, abs_mul, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ Real.pi * k ) ] ; ring;
      exact h_phase_approx_i.trans_lt ( by nlinarith [ Real.pi_pos, mul_div_cancel₀ ( k : ℝ ) ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ), mul_div_cancel₀ ε ( by positivity : ( 4 * Real.pi ) ≠ 0 ) ] );
    -- This implies $|e^{i t \gamma_i} - 1| < \epsilon$ (roughly, using Lipschitz of exp).
    have h_exp_approx : ∀ i, ‖Complex.exp (Complex.I * (t * γ i)) - 1‖ < ε := by
      intro i
      obtain ⟨p, hp⟩ := h_phase_approx i
      have h_exp_approx_i : ‖Complex.exp (Complex.I * (t * γ i)) - 1‖ ≤ |t * γ i - 2 * Real.pi * k * p| := by
        have h_exp_approx_i : ‖Complex.exp (Complex.I * (t * γ i)) - 1‖ = ‖Complex.exp (Complex.I * (t * γ i - 2 * Real.pi * k * p)) - 1‖ := by
          norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
          norm_num [ mul_assoc, mul_comm Real.pi _, mul_left_comm ];
          norm_num [ show Real.cos ( t * γ i - p * ( k * ( 2 * Real.pi ) ) ) = Real.cos ( t * γ i ) by convert Real.cos_periodic.int_mul ( -p * k ) _ using 2; push_cast; ring, show Real.sin ( t * γ i - p * ( k * ( 2 * Real.pi ) ) ) = Real.sin ( t * γ i ) by convert Real.sin_periodic.int_mul ( -p * k ) _ using 2; push_cast; ring ];
        -- Using the fact that $|e^{i\theta} - 1| \leq |\theta|$ for any real $\theta$, we get:
        have h_exp_approx_i : ∀ θ : ℝ, ‖Complex.exp (Complex.I * θ) - 1‖ ≤ |θ| := by
          intros θ
          have h_exp_approx_i : ‖Complex.exp (Complex.I * θ) - 1‖ = 2 * |Real.sin (θ / 2)| := by
            norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
            rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring <;> norm_num [ Real.sin_sq, Real.cos_sq ] <;> ring;
            nlinarith [ Real.cos_sq' θ ];
          -- Using the fact that $|\sin(x)| \leq |x|$ for any real $x$, we get:
          have h_sin_approx : ∀ x : ℝ, |Real.sin x| ≤ |x| := fun x => abs_sin_le_abs;
          exact h_exp_approx_i.symm ▸ by simpa [ abs_div, mul_div_cancel₀ ] using mul_le_mul_of_nonneg_left ( h_sin_approx ( θ / 2 ) ) zero_le_two;
        convert h_exp_approx_i ( t * γ i - 2 * Real.pi * k * p ) using 1 ; norm_cast;
        aesop;
      linarith;
    use Real.exp t;
    simp_all +decide [ Complex.cpow_def_of_ne_zero, Complex.exp_ne_zero ];
    convert h_exp_approx using 3 ; rw [ Complex.log_exp ] <;> ring ; norm_num [ Real.pi_pos.ne' ];
    · positivity;
    · norm_cast ; linarith [ Real.pi_pos ]

/-
Redefinition of hypotheses with V2 suffix.
-/
open Real Complex Filter Asymptotics Set

/-- Hypothesis: There are infinitely many zeros on the critical line, and the sum of their reciprocals diverges. -/
class HardyCriticalLineZerosHyp_V2 : Prop where
  infinite_critical_zeros : {ρ ∈ CriticalZeros | ρ.re = 1/2}.Infinite
  zeros_finite (T : ℝ) : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite
  sum_inv_rho_diverges : ∀ B : ℝ, ∃ T : ℝ, ∑ ρ ∈ ZerosBelow T, 1 / ‖ρ‖ > B

/-- Hypothesis: The explicit formula for ψ(x) holds with a specific error bound. -/
class ExplicitFormulaPsiHyp_V2 : Type where
  C : ℝ
  psi_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevPsi x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Hypothesis: The explicit formula for θ(x) holds with a specific error bound. -/
class ExplicitFormulaThetaHyp_V2 : Type where
  C : ℝ
  theta_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevTheta x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- The conclusion for ψ using the correct oscillation definition. -/
class PsiOscillationFromCriticalZerosHypAtTop_V2 : Prop where
  psi_osc : IsOmegaOscillationAtTop (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ using the correct oscillation definition. -/
class ThetaOscillationSqrtHypAtTop_V2 : Prop where
  theta_osc : IsOmegaOscillationAtTop (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

/-
Redefinition of hypotheses with V3 suffix and helper lemma for Finset.
-/
open Real Complex Filter Asymptotics Set

/-- Hypothesis: There are infinitely many zeros on the critical line, and the sum of the real parts of their reciprocals diverges. -/
class HardyCriticalLineZerosHyp_V3 : Prop where
  infinite_critical_zeros : {ρ ∈ CriticalZeros | ρ.re = 1/2}.Infinite
  zeros_finite (T : ℝ) : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite
  sum_re_inv_rho_diverges : ∀ B : ℝ, ∃ T : ℝ, ∑ ρ ∈ ZerosBelow T, (1 / ρ).re > B

/-- Hypothesis: The explicit formula for ψ(x) holds with a specific error bound. -/
class ExplicitFormulaPsiHyp_V3 : Type where
  C : ℝ
  psi_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevPsi x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Hypothesis: The explicit formula for θ(x) holds with a specific error bound. -/
class ExplicitFormulaThetaHyp_V3 : Type where
  C : ℝ
  theta_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevTheta x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- The conclusion for ψ using the correct oscillation definition. -/
class PsiOscillationFromCriticalZerosHypAtTop_V3 : Prop where
  psi_osc : IsOmegaOscillationAtTop (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ using the correct oscillation definition. -/
class ThetaOscillationSqrtHypAtTop_V3 : Prop where
  theta_osc : IsOmegaOscillationAtTop (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

lemma exists_large_x_phases_aligned_finset (S : Finset ℂ) (_hS : ∀ ρ ∈ S, ρ.re = 1/2) (ε : ℝ) (hε : ε > 0) (X : ℝ) :
  ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - 1‖ < ε := by
    -- Apply the simultaneous Dirichlet approximation theorem to the frequencies γ_i = ρ.im for ρ in S.
    have h_dirichlet : ∀ (γ : Fin (Finset.card S) → ℝ) (ε : ℝ) (hε : ε > 0) (X : ℝ), ∃ x > X, ∀ i, ‖(x : ℂ) ^ (I * γ i) - 1‖ < ε :=
      fun γ' ε' hε' X' => exists_large_x_phases_aligned γ' ε' hε' X';
    -- By definition of $S$, we can create a bijection between $S$ and $\{0, 1, ..., S.card - 1\}$.
    obtain ⟨f, hf⟩ : ∃ f : S ≃ Fin (Finset.card S), True := by
      exact ⟨ Fintype.equivOfCardEq <| by simp +decide, trivial ⟩;
    obtain ⟨ x, hx₁, hx₂ ⟩ := h_dirichlet ( fun i => ( f.symm i |> Subtype.val |> Complex.im ) ) ε hε X;
    exact ⟨ x, hx₁, fun ρ hρ => by simpa using hx₂ ( f ⟨ ρ, hρ ⟩ ) ⟩

/-
Lower bound on the real part of the sum when phases are aligned.
-/
lemma bound_real_part_of_sum_aligned {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re = 1/2) {x : ℝ} (hx : x > 0) {ε : ℝ} (_hε : ε > 0)
  (h_phases : ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - 1‖ < ε) :
  (∑ ρ ∈ S, (x : ℂ)^ρ / ρ).re ≥ Real.sqrt x * ((∑ ρ ∈ S, (1/ρ).re) - ε * (∑ ρ ∈ S, 1/‖ρ‖)) := by
    -- For each $\rho \in S$, we have $\text{Re}(x^\rho/\rho) = \sqrt{x} \text{Re}(u_\rho/\rho)$ where $u_\rho = x^{i \text{Im}(\rho)}$.
    have h_re_expr (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re ((x : ℂ) ^ ρ / ρ) = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
      rw [ show ρ = 1 / 2 + Complex.I * ρ.im by simp +decide [ Complex.ext_iff, hS ρ hρ ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero, hx.ne' ] ; ring;
      norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring;
      norm_num [ Complex.arg_ofReal_of_nonneg hx.le, Real.sin_add, Real.cos_add, mul_assoc, ← Real.exp_add ] ; ring;
    -- Using the bound on $\|u_\rho - 1\|$, we get $\text{Re}((u_\rho - 1)/\rho) \ge -|(u_\rho - 1)/\rho| = -|u_\rho - 1|/|\rho| > -\epsilon/|\rho|$.
    have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - 1) / ρ) ≥ -ε / ‖ρ‖ := by
      have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - 1) / ρ) ≥ -‖((x : ℂ) ^ (Complex.I * ρ.im) - 1) / ρ‖ := by
        exact neg_le_of_abs_le ( Complex.abs_re_le_norm _ ) |> le_trans <| by norm_num;
      exact le_trans ( by simpa [ neg_div ] using div_le_div_of_nonneg_right ( neg_le_neg ( le_of_lt ( h_phases ρ hρ ) ) ) ( norm_nonneg ρ ) ) ( h_re_bound ρ hρ );
    simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
    rw [ ← Finset.sum_sub_distrib ];
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_re_bound i hi, Real.sqrt_nonneg x ] ;

/-
Generalized lower bound on Re(∑ x^ρ/ρ) when phases are aligned to an arbitrary
target w on the unit circle (not just w = 1).

When w = I (imaginary unit), the main term ∑ Re(I/ρ) = ∑ γ/(1/4+γ²) ≈ ∑ 1/γ
which DIVERGES — this is the key to proving Littlewood's oscillation theorem.
Contrast with w = 1 where ∑ Re(1/ρ) = ∑ (1/2)/(1/4+γ²) CONVERGES.
-/
lemma bound_real_part_of_sum_shifted {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    {x : ℝ} (hx : x > 0) {w : ℂ} (_hw : ‖w‖ = 1) {ε : ℝ} (_hε : ε > 0)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε) :
    (∑ ρ ∈ S, (x : ℂ)^ρ / ρ).re ≥ Real.sqrt x * ((∑ ρ ∈ S, (w/ρ).re) - ε * (∑ ρ ∈ S, 1/‖ρ‖)) := by
  -- Decompose x^ρ/ρ = √x · u_ρ/ρ where u_ρ = x^{iγ}
  have h_re_expr (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re ((x : ℂ) ^ ρ / ρ) = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
    rw [ show ρ = 1 / 2 + Complex.I * ρ.im by simp +decide [ Complex.ext_iff, hS ρ hρ ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero, hx.ne' ] ; ring;
    norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring;
    norm_num [ Complex.arg_ofReal_of_nonneg hx.le, Real.sin_add, Real.cos_add, mul_assoc, ← Real.exp_add ] ; ring;
  -- Bound: Re((u_ρ - w)/ρ) ≥ -ε/‖ρ‖
  have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ) ≥ -ε / ‖ρ‖ := by
    have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ) ≥ -‖((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ‖ := by
      exact neg_le_of_abs_le ( Complex.abs_re_le_norm _ ) |> le_trans <| by norm_num;
    exact le_trans ( by simpa [ neg_div ] using div_le_div_of_nonneg_right ( neg_le_neg ( le_of_lt ( h_phases ρ hρ ) ) ) ( norm_nonneg ρ ) ) ( h_re_bound ρ hρ );
  simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
  rw [ ← Finset.sum_sub_distrib ];
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_re_bound i hi, Real.sqrt_nonneg x ] ;

/-
Upper bound companion: when phases are aligned to w, the real part of ∑ x^ρ/ρ
is at most √x · (∑ Re(w/ρ) + ε · ∑ 1/‖ρ‖).
Needed for the NEGATIVE oscillation direction.
-/
lemma bound_real_part_of_sum_shifted_upper {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    {x : ℝ} (hx : x > 0) {w : ℂ} (_hw : ‖w‖ = 1) {ε : ℝ} (_hε : ε > 0)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε) :
    (∑ ρ ∈ S, (x : ℂ)^ρ / ρ).re ≤ Real.sqrt x * ((∑ ρ ∈ S, (w/ρ).re) + ε * (∑ ρ ∈ S, 1/‖ρ‖)) := by
  -- Decompose x^ρ/ρ = √x · u_ρ/ρ where u_ρ = x^{iγ}
  have h_re_expr (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re ((x : ℂ) ^ ρ / ρ) = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
    rw [ show ρ = 1 / 2 + Complex.I * ρ.im by simp +decide [ Complex.ext_iff, hS ρ hρ ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero, hx.ne' ] ; ring;
    norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring;
    norm_num [ Complex.arg_ofReal_of_nonneg hx.le, Real.sin_add, Real.cos_add, mul_assoc, ← Real.exp_add ] ; ring;
  -- Bound: Re((u_ρ - w)/ρ) ≤ ε/‖ρ‖
  have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ) ≤ ε / ‖ρ‖ := by
    calc Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ)
        ≤ ‖((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ‖ :=
          le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
      _ = ‖(x : ℂ) ^ (Complex.I * ρ.im) - w‖ / ‖ρ‖ := by
          rw [norm_div]
      _ ≤ ε / ‖ρ‖ := by
          exact div_le_div_of_nonneg_right (le_of_lt (h_phases ρ hρ)) (norm_nonneg ρ)
  simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
  rw [ ← Finset.sum_add_distrib ];
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_re_bound i hi, Real.sqrt_nonneg x ] ;

/-- **B5b-infra sorry**: Phase alignment to an arbitrary target w on S¹.

Given RH, a finite set S of zeros with Re(ρ) = 1/2 and Im(ρ) > 0, a target w
with ‖w‖ = 1, ε > 0, and X, there exists x > X such that all phases
x^{iγ} are within ε of w.

This is the inhomogeneous simultaneous Dirichlet approximation with equal
targets. The lemma is FALSE for arbitrary frequency sets (counterexample:
γ₁=1, γ₂=2, w=e^{iπ/3}). For zeta zeros, it holds because:

(1) Zeta zero ordinates are NOT all commensurate: if ∃c>0 with all γ_k ∈ c·ℤ,
    then N⁺(T) ≤ T/c + O(1), contradicting N⁺(T) ~ (T/2π)logT from RvM.
(2) Not-commensurate frequencies generate a dense subgroup G ⊆ ℝ/2πℤ via
    the map t ↦ (tγ₁ mod 2π, ..., tγₙ mod 2π).
(3) Density of G implies G ⊇ Δ (the diagonal), giving equal-target approximation.

The homogeneous case (w = 1) is proved in `exists_large_x_phases_aligned_finset`.
The gap is extending to arbitrary w via Kronecker's theorem (1884).

Now takes RH as a parameter, since the proof uses properties specific to
zeta zero ordinates (superlinear growth of N(T)).

**Blocked by**: Kronecker's theorem formalization + uniform Riemann-von Mangoldt.

References: Kronecker 1884, Hardy-Wright (2008) §23.8, Titchmarsh (1986) §9.4. -/
lemma exists_large_x_phases_aligned_to_target
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    (hS_pos : ∀ ρ ∈ S, 0 < ρ.im)
    (w : ℂ) (hw : ‖w‖ = 1) (ε : ℝ) (hε : ε > 0) (X : ℝ)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε := by
  sorry

end Aristotle.DirichletPhaseAlignment

end
```

---

## Prompt D

# No-Repo Full-Context Prompt D

You have no repository access. Use only the code in this prompt.

Task: prove `rs_block_analysis` with no axioms/sorry/admit and keep signature unchanged.

Output required:
1. Replacement Lean code for theorem proof (and helper lemmas in same namespace if needed).
2. Brief explanation.
3. If impossible, exact formal blocker and strongest unconditional helper theorem you can still prove.

## Full current file snapshot
```lean
/-
Riemann-Siegel complete-block asymptotic sorry and wiring to PerBlockSignedBoundHyp.

This file defines a clean atomic sorry (`rsCompleteBlockWithResidual_sorry`) encoding
the Riemann-Siegel per-block sign structure on COMPLETE blocks with partial-block
interpolation, then wires it to `PerBlockSignedBoundHyp`.

## Mathematical content

On the k-th complete block (hardyStart k, hardyStart(k+1)):
  ∫ ErrorTerm ≈ (-1)^k · A · √(k+1)
with uniformly bounded per-block error (Clause 1), bounded cumulative
residual sum (Clause 2), and partial-block sign interpolation (Clause 3).

## Wiring

Clause 3 provides partial-block interpolation: the integral over any initial
sub-interval of a block is α times the complete-block leading term (α ∈ [0,1])
with error at most B. Combined with Clauses 1 and 2, a convex combination
argument shows the integral stays within the alternating sum structure.

## References
- Siegel, "Über Riemanns Nachlaß zur analytischen Zahlentheorie" (1932)
- Titchmarsh, "The Theory of the Riemann Zeta-Function", §4.16-4.17

SORRY COUNT: 1 (rs_block_analysis)
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.RSBlockDecomposition
import Littlewood.Aristotle.AbelSummation

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RSCompleteBlockAsymptotic

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-- Convex combination absolute value bound. -/
private lemma abs_convex_le_max (a b α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |(1 - α) * a + α * b| ≤ max |a| |b| :=
  calc |(1 - α) * a + α * b|
      ≤ |(1 - α) * a| + |α * b| := abs_add_le _ _
    _ = (1 - α) * |a| + α * |b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 - α by linarith),
            abs_of_nonneg hα0]
    _ ≤ (1 - α) * max |a| |b| + α * max |a| |b| :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hα0)
    _ = max |a| |b| := by ring

/-- Per-block integral sign structure on COMPLETE blocks, partial-block
interpolation, and centered residual cancellation.

**Clause 1** (per-block sign structure): Each complete block integral is
`(-1)^k · A · √(k+1)` plus uniformly bounded error B.

**Clause 2** (centered residual cancellation): The partial sums of block
errors are bounded by R independent of N.

**Clause 3** (partial-block interpolation): On any initial sub-interval
`(hardyStart k, T]` of a complete block, the integral is α times the
complete-block leading term (α ∈ [0,1]) with error at most B. This
encodes the constant-sign property of ErrorTerm within each block. -/
def RSCompleteBlockWithResidualHyp : Prop :=
  ∃ (A B R : ℝ), A > 0 ∧ B ≥ 0 ∧ R ≥ 0 ∧
    -- Clause 1: per-block sign structure on COMPLETE blocks
    (∀ k : ℕ,
      |(∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)| ≤ B) ∧
    -- Clause 2: centered residual on complete blocks
    (∀ N : ℕ,
      |∑ k ∈ Finset.range N,
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ R) ∧
    -- Clause 3: partial block interpolation
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ (α : ℝ), 0 ≤ α ∧ α ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - α * ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ B)

/-- Unified RS block analysis: the single atomic sorry for B3.

The block integral of ErrorTerm decomposes as:
  ∫_{block k} ErrorTerm = (-1)^k · (A·√(k+1) + c(k))
where A > 0 is the Fresnel constant, c(k) ≥ 0 captures the sign-definite
correction, and c is antitone on k ≥ 1 (corrections decay).

Additionally, partial-block integrals interpolate: the partial integral
is β times the full-block integral (β ∈ [0,1]) with bounded error C₂.

The block integral clause uses exact equality (not bounds). This is essential:
Clause 2 needs the errors to be EXACTLY (-1)^k · c_k to apply alternating
series bounds. c_k is existentially quantified and defined as
c_k := (-1)^k · (∫ ErrorTerm) - A √(k+1). The hard analytic content is
proving c_k ≥ 0 (sign-definite) and AntitoneOn c (Ici 1) (decay).

REFERENCES: Siegel 1932 §3; Titchmarsh §4.16-4.17. -/
private theorem rs_block_analysis :
    ∃ (A : ℝ) (c : ℕ → ℝ) (C₂ : ℝ),
      A > 0 ∧
      (∀ k, 0 ≤ c k) ∧
      AntitoneOn c (Ici (1 : ℕ)) ∧
      (∀ k : ℕ,
        (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          = (-1 : ℝ) ^ k * (A * Real.sqrt ((k : ℝ) + 1) + c k)) ∧
      C₂ ≥ 0 ∧
      (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
        ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
          |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
            - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                     ErrorTerm t)| ≤ C₂) := by
  -- Future drop-in when the separate RS block development is stabilized:
  -- `exact Aristotle.RSBlockBounds.rs_block_analysis_proof`
  sorry

/-- Helper: c k ≤ max (c 0) (c 1) for all k, from atom hypotheses.
    For k = 0: trivially c 0 ≤ max (c 0) (c 1).
    For k ≥ 1: AntitoneOn c (Ici 1) gives c k ≤ c 1 ≤ max (c 0) (c 1). -/
private lemma c_le_max {c : ℕ → ℝ} (hc_anti : AntitoneOn c (Ici (1 : ℕ)))
    (k : ℕ) : c k ≤ max (c 0) (c 1) := by
  rcases k with _ | k
  · exact le_max_left _ _
  · -- AntitoneOn: a ∈ s → b ∈ s → a ≤ b → f b ≤ f a
    -- Want c(k+1) ≤ c 1. Set a=1, b=k+1.
    exact le_trans (hc_anti (Set.mem_Ici.mpr (le_refl 1))
      (Set.mem_Ici.mpr (by omega : 1 ≤ k + 1)) (by omega : 1 ≤ k + 1))
      (le_max_right _ _)

/-- Assembly: wire the unified atom into `RSCompleteBlockWithResidualHyp`.

From the atom, block errors are e_k = (-1)^k c_k. Clause 1 uses |e_k| ≤ max(c 0, c 1).
Clause 2 splits at k=0 and applies `alternating_antitone_sum_le_first` to the tail.
Clause 3 uses the interpolation from the atom with triangle inequality.

B = max(c 0, c 1) + C₂, R = c 0 + c 1. -/
theorem rsCompleteBlockWithResidual_sorry :
    RSCompleteBlockWithResidualHyp := by
  obtain ⟨A, c, C₂, hA, hc_nn, hc_anti, hblock_eq, hC₂_nn, hinterp⟩ := rs_block_analysis
  -- Constants
  set B := max (c 0) (c 1) + C₂
  set R := c 0 + c 1
  refine ⟨A, B, R, hA, ?_, ?_, ?_, ?_, ?_⟩
  · -- B ≥ 0
    have : max (c 0) (c 1) ≥ 0 := le_trans (hc_nn 0) (le_max_left _ _)
    linarith
  · -- R ≥ 0
    linarith [hc_nn 0, hc_nn 1]
  · -- Clause 1: per-block sign structure
    intro k
    -- ∫ = (-1)^k (A √(k+1) + c k), so error = (-1)^k c_k
    rw [hblock_eq k]
    rw [show (-1 : ℝ) ^ k * (A * Real.sqrt (↑k + 1) + c k)
          - (-1 : ℝ) ^ k * A * Real.sqrt (↑k + 1)
        = (-1 : ℝ) ^ k * c k from by ring]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (hc_nn k)]
    -- c k ≤ max(c 0, c 1) ≤ max(c 0, c 1) + C₂ = B
    calc c k ≤ max (c 0) (c 1) := c_le_max hc_anti k
      _ ≤ max (c 0) (c 1) + C₂ := le_add_of_nonneg_right hC₂_nn
  · -- Clause 2: centered residual cancellation
    intro N
    -- Each summand = (-1)^k c_k
    have h_summand : ∀ k ∈ Finset.range N,
        (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)
        = (-1 : ℝ) ^ k * c k := by
      intro k _
      rw [hblock_eq k]; ring
    rw [Finset.sum_congr rfl h_summand]
    -- Split: ∑_{k<N} (-1)^k c_k
    rcases N with _ | N
    · -- N = 0: empty sum
      simp; linarith [hc_nn 0, hc_nn 1]
    · -- N = n+1: split off k=0 term, then bound tail via alternating antitone
      rw [Finset.sum_range_succ', pow_zero, one_mul]
      -- Goal: |∑_{k<N} (-1)^(k+1) c(k+1) + c 0| ≤ c 0 + c 1
      rw [show ∀ (x y : ℝ), |x + y| = |y + x| from fun x y => by rw [add_comm]]
      -- Goal: |c 0 + ∑_{k<N} (-1)^(k+1) c(k+1)| ≤ c 0 + c 1
      calc |c 0 + ∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * c (k + 1)|
          ≤ |c 0| + |∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * c (k + 1)| :=
            abs_add_le _ _
        _ = c 0 + |∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * c (k + 1)| := by
            rw [abs_of_nonneg (hc_nn 0)]
        _ ≤ c 0 + c 1 := by
            gcongr
            -- Factor out (-1): (-1)^(k+1) = (-1) * (-1)^k
            -- ∑ (-1)^(k+1) c(k+1) = (-1) * ∑ (-1)^k c(k+1)
            have h_factor : ∀ k : ℕ,
                (-1 : ℝ) ^ (k + 1) * c (k + 1) = (-1 : ℝ) * ((-1 : ℝ) ^ k * c (k + 1)) := by
              intro k; rw [pow_succ]; ring
            rw [Finset.sum_congr rfl (fun k _ => h_factor k), ← Finset.mul_sum,
                abs_mul, abs_neg, abs_one, one_mul]
            -- Now bound |∑_{k<N} (-1)^k c(k+1)| ≤ c 1
            -- Define a(k) = c(k+1). Then a is antitone and nonneg.
            -- By alternating_antitone_sum_le_first: |∑_{k<N} (-1)^k a(k)| ≤ a 0 = c 1
            rcases N with _ | M
            · simp; exact hc_nn 1
            · -- N = M + 1, sum over range (M+1)
              have h_anti_shift : Antitone (fun k => c (k + 1)) := by
                intro i j hij
                -- Antitone: i ≤ j → c(j+1) ≤ c(i+1)
                -- AntitoneOn: a ∈ s → b ∈ s → a ≤ b → f b ≤ f a
                -- Set a = i+1, b = j+1
                exact hc_anti (Set.mem_Ici.mpr (by omega : 1 ≤ i + 1))
                  (Set.mem_Ici.mpr (by omega : 1 ≤ j + 1)) (by omega : i + 1 ≤ j + 1)
              have h_nn_shift : ∀ k, 0 ≤ (fun k => c (k + 1)) k := fun k => hc_nn (k + 1)
              exact AbelSummation.alternating_antitone_sum_le_first
                (fun k => c (k + 1)) h_nn_shift h_anti_shift M
  · -- Clause 3: partial-block interpolation
    intro k T hkT hTk
    obtain ⟨β, hβ0, hβ1, hβ_bound⟩ := hinterp k T hkT hTk
    refine ⟨β, hβ0, hβ1, ?_⟩
    -- Strategy: rewrite ∫_{full} via hblock_eq in hβ_bound, then triangle inequality.
    -- hβ_bound: |∫_{partial} - β · ∫_{full}| ≤ C₂
    -- hblock_eq: ∫_{full} = (-1)^k (A √(k+1) + c_k)
    -- Goal: |∫_{partial} - β · (-1)^k A √(k+1)| ≤ B
    -- = |(∫_{partial} - β · ∫_{full}) + β · (∫_{full} - (-1)^k A √(k+1))|
    -- = |(∫_{partial} - β · ∫_{full}) + β · (-1)^k · c_k|
    -- ≤ C₂ + β · c_k ≤ C₂ + max(c 0, c 1) = B
    set I_full := ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t
    set I_part := ∫ t in Ioc (hardyStart k) T, ErrorTerm t
    have hI_full : I_full = (-1 : ℝ) ^ k * (A * Real.sqrt (↑k + 1) + c k) := hblock_eq k
    -- Rewrite goal using algebra
    have h_split : I_part - β * ((-1 : ℝ) ^ k * A * Real.sqrt (↑k + 1))
        = (I_part - β * I_full) + β * ((-1 : ℝ) ^ k * c k) := by
      rw [hI_full]; ring
    rw [h_split]
    have h_abs_beta : |β * ((-1 : ℝ) ^ k * c k)| = β * c k := by
      rw [abs_mul, abs_mul, abs_of_nonneg hβ0, abs_pow, abs_neg, abs_one, one_pow,
          one_mul, abs_of_nonneg (hc_nn k)]
    calc |(I_part - β * I_full) + β * ((-1 : ℝ) ^ k * c k)|
        ≤ |I_part - β * I_full| + |β * ((-1 : ℝ) ^ k * c k)| := abs_add_le _ _
      _ ≤ C₂ + β * c k := add_le_add hβ_bound (le_of_eq h_abs_beta)
      _ ≤ C₂ + max (c 0) (c 1) := by
          have : β * c k ≤ max (c 0) (c 1) :=
            le_trans (mul_le_of_le_one_left (hc_nn k) hβ1) (c_le_max hc_anti k)
          linarith
      _ = max (c 0) (c 1) + C₂ := by ring

/-- Wire `RSCompleteBlockWithResidualHyp` to `PerBlockSignedBoundHyp`.

The proof decomposes ∫₁ᵀ ErrorTerm into head + complete blocks + partial
block, applies Clauses 1–3, and uses a convex combination bound to keep
the partial block's contribution within the alternating sum structure. -/
theorem perBlockSignedBoundHyp_of_blockAsymptotic
    (hyp : RSCompleteBlockWithResidualHyp) :
    Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp := by
  obtain ⟨A, B, R, hA, hB, hR, hC1, hC2, hC3⟩ := hyp
  -- Global error constant
  let Bsmall : ℝ := ∫ t in Ioc (1 : ℝ) (2 * Real.pi), ‖ErrorTerm t‖
  let head_int : ℝ := |∫ t in Ioc (1 : ℝ) (hardyStart 0), ErrorTerm t|
  let Bglobal : ℝ := max Bsmall (head_int + R + B)
  have hBg_nn : (0 : ℝ) ≤ Bglobal :=
    le_max_of_le_left (integral_nonneg (fun _ => norm_nonneg _))
  refine ⟨A, Bglobal, hA, hBg_nn, ?_⟩
  intro T hT
  by_cases hT_long : 2 * Real.pi ≤ T
  · -- === Case T ≥ 2π: block decomposition ===
    have hT_nonneg : (0 : ℝ) ≤ T := by linarith
    let M := hardyN T
    have hM_pos : 0 < M := by
      have : hardyStart 0 ≤ T := by
        rw [Aristotle.HardyNProperties.hardyStart_formula]; simpa using hT_long
      exact (hardyN_lt_iff 0 T hT_nonneg).2 this
    let n := M - 1
    have hM_eq : M = n + 1 := (Nat.succ_pred_eq_of_pos hM_pos).symm
    -- Block boundary facts
    have hstart_n_le : hardyStart n ≤ T :=
      (hardyN_lt_iff n T hT_nonneg).1 (Nat.pred_lt (Nat.pos_iff_ne_zero.mp hM_pos))
    have hT_lt_startM : T < hardyStart M := by
      by_contra h; push_neg at h
      exact Nat.lt_irrefl M ((hardyN_lt_iff M T hT_nonneg).2 h)
    have hT_le_succ : T ≤ hardyStart (n + 1) := by
      rw [← hM_eq]; exact le_of_lt hT_lt_startM
    -- Block decomposition (from RSBlockDecomposition)
    have hdecomp :=
      Aristotle.RSBlockDecomposition.errorTerm_block_sum T (show T ≥ 2 by linarith)
    -- Head simplification: min T (hardyStart 0) = hardyStart 0
    have hhead_min : min T (hardyStart 0) = hardyStart 0 := by
      apply min_eq_right
      rw [Aristotle.HardyNProperties.hardyStart_formula]; simpa using hT_long
    -- Complete blocks: for k < n, clamped = complete
    have hcomplete_eq : ∀ k, k ∈ Finset.range n →
        (∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
          = ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := by
      intro k hk
      have hk_lt_n : k < n := Finset.mem_range.mp hk
      have hk_lt_M : k < M := by rw [hM_eq]; omega
      have hk1_lt_M : k + 1 < M := by rw [hM_eq]; omega
      rw [min_eq_right ((hardyN_lt_iff k T hT_nonneg).1 hk_lt_M),
          min_eq_right ((hardyN_lt_iff (k + 1) T hT_nonneg).1 hk1_lt_M)]
    -- Partial block: clamped_n = partial from hardyStart n to T
    have hpartial_eq :
        (∫ t in Ioc (min T (hardyStart n)) (min T (hardyStart (n + 1))), ErrorTerm t)
          = ∫ t in Ioc (hardyStart n) T, ErrorTerm t := by
      rw [min_eq_right hstart_n_le, min_eq_left hT_le_succ]
    -- Split the block sum: ∑_{k<M} = ∑_{k<n} + last term
    have hsum_split :
        Finset.sum (Finset.range M)
            (fun k => ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
          = Finset.sum (Finset.range n)
              (fun k => ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                ErrorTerm t)
            + ∫ t in Ioc (min T (hardyStart n)) (min T (hardyStart (n + 1))), ErrorTerm t := by
      rw [hM_eq]; exact Finset.sum_range_succ _ n
    -- Integral decomposition: I = head + ∑ complete + partial
    have hI_eq :
        ∫ t in Ioc 1 T, ErrorTerm t
          = (∫ t in Ioc 1 (hardyStart 0), ErrorTerm t)
            + (∑ k ∈ Finset.range n,
                ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
            + (∫ t in Ioc (hardyStart n) T, ErrorTerm t) := by
      rw [hdecomp, hhead_min, hsum_split, Finset.sum_congr rfl hcomplete_eq, hpartial_eq,
          add_assoc]
    -- Alternating sum
    let S : ℕ → ℝ := fun N =>
      ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)
    have hS_succ : S (n + 1) = S n + (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1) :=
      Finset.sum_range_succ _ n
    -- Clause 2: cumulative residual bound
    have hresid_bound : |∑ k ∈ Finset.range n,
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ R := hC2 n
    -- Clause 3: partial block interpolation
    obtain ⟨α, hα0, hα1, hη⟩ := hC3 n T hstart_n_le hT_le_succ
    -- Algebraic decomposition of complete block sum
    have hcomplete_sum :
        ∑ k ∈ Finset.range n,
          ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t
        = A * S n
          + ∑ k ∈ Finset.range n,
              ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
                - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)) := by
      conv_lhs =>
        arg 2; ext k
        rw [show (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
              = (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)
                + ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
                    - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))
          from by ring]
      rw [Finset.sum_add_distrib]
      congr 1
      simp_rw [show ∀ k : ℕ,
          (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)
            = A * ((-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1))
        from fun k => by ring]
      exact (Finset.mul_sum ..).symm
    -- Convex combination identity
    have hconvex_eq :
        (1 - α) * S n + α * S (n + 1)
          = S n + α * ((-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)) := by
      rw [hS_succ]; ring
    -- Key bound: |∫| ≤ A * max(|S n|, |S(n+1)|) + Bglobal
    have hM_le_sqrt : (M : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
      have := Aristotle.HardyNProperties.hardyN_le_sqrt T (show T ≥ 2 by linarith)
      linarith
    -- Abbreviations for readability
    set head_val := ∫ t in Ioc (1 : ℝ) (hardyStart 0), ErrorTerm t
    set resid_sum := ∑ k ∈ Finset.range n,
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))
    set partial_val := ∫ t in Ioc (hardyStart n) T, ErrorTerm t
    set η := partial_val - α * ((-1 : ℝ) ^ n * A * Real.sqrt ((n : ℝ) + 1))
    -- η bound from Clause 3
    have hη_bound : |η| ≤ B := hη
    -- The integral in terms of convex combination
    have hI_conv :
        ∫ t in Ioc 1 T, ErrorTerm t
          = A * ((1 - α) * S n + α * S (n + 1)) + (head_val + resid_sum + η) := by
      rw [hI_eq, hcomplete_sum, hconvex_eq]
      simp only [η]
      ring
    -- Main bound
    have hbound :
        |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ A * max |S n| |S (n + 1)| + (head_int + R + B) := by
      rw [hI_conv]
      calc |A * ((1 - α) * S n + α * S (n + 1)) + (head_val + resid_sum + η)|
          ≤ |A * ((1 - α) * S n + α * S (n + 1))| + |head_val + resid_sum + η| :=
            abs_add_le _ _
        _ ≤ A * max |S n| |S (n + 1)| + (|head_val| + |resid_sum| + |η|) := by
            gcongr
            · rw [abs_mul, abs_of_pos hA]
              exact mul_le_mul_of_nonneg_left
                (abs_convex_le_max _ _ α hα0 hα1) (le_of_lt hA)
            · calc |head_val + resid_sum + η|
                  ≤ |head_val + resid_sum| + |η| := abs_add_le _ _
                _ ≤ |head_val| + |resid_sum| + |η| := by
                    gcongr; exact abs_add_le _ _
        _ ≤ A * max |S n| |S (n + 1)| + (head_int + R + B) := by
            have h_head_le : |head_val| ≤ head_int := by
              simp [head_val, head_int]
            have h_resid_le : |resid_sum| ≤ R := by
              simpa [resid_sum] using hresid_bound
            nlinarith [h_head_le, h_resid_le, hη_bound]
    -- Choose N based on which alternating sum is larger
    have hbound_Bg :
        |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ A * max |S n| |S (n + 1)| + Bglobal := by
      calc |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ A * max |S n| |S (n + 1)| + (head_int + R + B) := hbound
        _ ≤ A * max |S n| |S (n + 1)| + Bglobal := by
            gcongr; exact le_max_right _ _
    by_cases h_which : |S n| ≤ |S (n + 1)|
    · -- Use N = n (alternating sum has n+1 terms)
      refine ⟨n, ?_, ?_⟩
      · -- (n + 1 : ℝ) ≤ T^{1/2}
        calc ((n : ℝ) + 1) = (M : ℝ) := by exact_mod_cast hM_eq.symm
          _ ≤ T ^ (1 / 2 : ℝ) := hM_le_sqrt
      · -- |∫| ≤ A * |S(n+1)| + Bglobal
        calc |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * max |S n| |S (n + 1)| + Bglobal := hbound_Bg
          _ = A * |S (n + 1)| + Bglobal := by rw [max_eq_right h_which]
    · -- Use N = n - 1 (need n ≥ 1)
      push_neg at h_which
      have hn_pos : 0 < n := by
        by_contra h; push_neg at h
        have hn0 : n = 0 := by omega
        rw [hn0] at h_which
        dsimp only [S] at h_which
        rw [Finset.sum_range_zero] at h_which
        simp [abs_zero] at h_which
        linarith
      refine ⟨n - 1, ?_, ?_⟩
      · -- (n - 1 + 1 : ℝ) ≤ T^{1/2}, i.e., n ≤ T^{1/2}
        have hn_eq : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
        calc ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hn_eq
          _ ≤ (M : ℝ) := by exact_mod_cast Nat.pred_le M
          _ ≤ T ^ (1 / 2 : ℝ) := hM_le_sqrt
      · -- |∫| ≤ A * |S n| + Bglobal
        have hn_eq : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
        calc |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * max |S n| |S (n + 1)| + Bglobal := hbound_Bg
          _ = A * |S n| + Bglobal := by rw [max_eq_left (le_of_lt h_which)]
          _ = A * |S (n - 1 + 1)| + Bglobal := by rw [hn_eq]
  · -- === Case T < 2π: trivial bound ===
    push_neg at hT_long
    refine ⟨0, ?_, ?_⟩
    · -- (0 + 1 : ℝ) ≤ T^{1/2}
      simp only [Nat.cast_zero, zero_add]
      exact Real.one_le_rpow (show (1 : ℝ) ≤ T by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    · -- |∫| ≤ A * |S 1| + Bglobal
      have h_int_bound :
          |∫ t in Ioc 1 T, ErrorTerm t| ≤ Bsmall := by
        calc |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ ∫ t in Ioc 1 T, ‖ErrorTerm t‖ := by
              rw [show |∫ t in Ioc 1 T, ErrorTerm t|
                    = ‖∫ t in Ioc 1 T, ErrorTerm t‖
                from (Real.norm_eq_abs _).symm]
              exact norm_integral_le_integral_norm _
          _ ≤ ∫ t in Ioc 1 (2 * Real.pi), ‖ErrorTerm t‖ := by
              exact setIntegral_mono_set
                (errorTerm_integrable (2 * Real.pi)).norm
                (ae_of_all _ (fun _ => norm_nonneg _))
                (Eventually.of_forall (fun t ht =>
                  ⟨ht.1, le_trans ht.2 (le_of_lt hT_long)⟩))
          _ = Bsmall := rfl
      calc |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ Bsmall := h_int_bound
        _ ≤ Bglobal := le_max_left _ _
        _ ≤ A * |∑ k ∈ Finset.range (0 + 1),
                (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + Bglobal := by
            linarith [mul_nonneg (le_of_lt hA) (abs_nonneg (∑ k ∈ Finset.range 1,
                (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)))]

end Aristotle.Standalone.RSCompleteBlockAsymptotic
```
