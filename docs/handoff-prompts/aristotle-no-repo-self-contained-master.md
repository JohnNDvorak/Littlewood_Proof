# Aristotle No-Repo Self-Contained Prompt Pack

Use these when Aristotle has **no repository access**. Each prompt embeds the key code context, theorem signatures, and required wiring information.

---

## Prompt A (No-Repo): `digamma_log_bound_atomic`

You have no repo access. Work from this prompt only.

### Environment assumptions
- Lean 4: `v4.27.0-rc1`
- Mathlib rev: `fdddb3ea2c8c35de4455e033bc2a5df4d3a391ee`
- No axioms, no `sorry`, no `admit`.

### Target theorem (exact signature)
```lean
theorem digamma_log_bound_atomic :
    ∃ C > 0, ∀ s : ℂ, s.re ≥ 1/4 → |s.im| ≥ 1 →
      Gamma s ≠ 0 →
      ‖deriv Gamma s / Gamma s - Complex.log s‖ ≤ C / ‖s‖ := by
  sorry
```

### Available local code context (already proved)
```lean
import Mathlib

namespace Aristotle.DigammaBinetBound
open Complex

lemma gauss_term_bound (w : ℂ) (hw : 2 ≤ ‖w‖) :
    ‖Complex.log (1 + 1/w) - 1/w‖ ≤ 1 / ‖w‖ ^ 2 := by
  -- already proved
  ...

lemma norm_sq_add_natCast_ge (s : ℂ) (hs : 0 ≤ s.re) (j : ℕ) :
    ‖s‖ ^ 2 + (j : ℝ) ^ 2 ≤ ‖s + (j : ℂ)‖ ^ 2 := by
  -- already proved
  ...

lemma two_le_norm_add_natCast_of_strip
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (j : ℕ) (hj : 2 ≤ j) :
    (2 : ℝ) ≤ ‖s + (j : ℂ)‖ := by ...

lemma gauss_term_bound_add_natCast
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (j : ℕ) (hj : 2 ≤ j) :
    ‖Complex.log (1 + 1 / (s + (j : ℂ))) - 1 / (s + (j : ℂ))‖ ≤
      1 / ‖s + (j : ℂ)‖ ^ 2 := by ...

lemma inv_norm_add_natCast_sq_le_inv_of_strip
    (s : ℂ) (hsre : 0 ≤ s.re) (hsim : 1 ≤ |s.im|) (j : ℕ) :
    1 / ‖s + (j : ℂ)‖ ^ 2 ≤ 1 / (‖s‖ ^ 2 + (j : ℝ) ^ 2) := by ...

lemma inv_norm_add_natCast_sq_le_inv_natCast_sq
    (s : ℂ) (hsre : 0 ≤ s.re) (hsim : 1 ≤ |s.im|) {j : ℕ} (hj : 1 ≤ j) :
    1 / ‖s + (j : ℂ)‖ ^ 2 ≤ 1 / (j : ℝ) ^ 2 := by ...

lemma gauss_term_bound_by_inv_natCast_sq
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (hsim : 1 ≤ |s.im|) {j : ℕ} (hj : 2 ≤ j) :
    ‖Complex.log (1 + 1 / (s + (j : ℂ))) - 1 / (s + (j : ℂ))‖ ≤ 1 / (j : ℝ) ^ 2 := by ...

lemma summable_gauss_terms_shifted_two
    (s : ℂ) (hs : (1 / 4 : ℝ) ≤ s.re) (hsim : 1 ≤ |s.im|) :
    Summable (fun n : ℕ =>
      ‖Complex.log (1 + 1 / (s + ((n + 2 : ℕ) : ℂ))) -
        1 / (s + ((n + 2 : ℕ) : ℂ))‖) := by ...

lemma summable_gauss_terms ... := by ...
lemma summable_gauss_complex_terms_shifted_two ... := by ...
lemma summable_gauss_complex_terms ... := by ...

lemma tsum_gauss_terms_eq_prefix_two_add_tail ... := by ...
lemma tsum_gauss_complex_terms_eq_prefix_two_add_tail ... := by ...
lemma norm_tsum_gauss_complex_terms_shifted_two_le ... := by ...

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
  simpa [logDeriv] using (Complex.logDeriv_tendsto hU x hconv hdiff hGamma)
```

### Required deliverable
Return Lean code that **replaces only the proof of** `digamma_log_bound_atomic` and compiles in this context.

### Proof strategy requirement
- Use the Gauss-series route and existing summability/tail lemmas above.
- No outside axioms or extra assumptions.

---

## Prompt B (No-Repo): `critical_zero_sum_diverges`

You have no repo access. Work from this prompt only.

### Environment assumptions
- Lean 4 `v4.27.0-rc1`, Mathlib rev above.
- No axioms, no `sorry`, no `admit`.

### Target theorem (exact signature)
```lean
private theorem critical_zero_sum_diverges (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ M : ℝ, ∃ T : ℝ, T ≥ 2 ∧
      M ≤ ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2) := by
  sorry
```

### Available local code context (already proved)
```lean
import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.Aristotle.ZetaLogDerivInfra

namespace Aristotle.Standalone.PsiZeroSumOscillationFromIngham
open Filter Complex Topology GrowthDomination ZetaZeros

open Aristotle.DirichletPhaseAlignment (ZerosBelow CriticalZeros)

-- positive-imaginary zero subset
def PositiveImZerosBelow (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => 0 < ρ.im)

lemma positiveImZerosBelow_sub (T : ℝ) :
    PositiveImZerosBelow T ⊆ ZerosBelow T := Finset.filter_subset _ _

lemma positiveImZerosBelow_re_half (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ ρ ∈ PositiveImZerosBelow T, ρ.re = 1 / 2 := by
  ...

lemma re_I_div_le_inv_norm (ρ : ℂ) (_hρ : ρ ≠ 0) :
    (I / ρ).re ≤ 1 / ‖ρ‖ := by ...

lemma gamma_div_bound (γ : ℝ) (hγ : γ ≥ 1) :
    γ / (1/4 + γ ^ 2) ≥ 1 / (2 * γ) := by ...

private lemma re_neg_I_div_eq (ρ : ℂ) (hρ_re : ρ.re = 1/2) :
    ((-I) / ρ).re = -ρ.im / (1/4 + ρ.im ^ 2) := by ...

private lemma sum_re_neg_I_div_eq (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    (∑ ρ ∈ PositiveImZerosBelow T, ((-I) / ρ).re) =
    -(∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2)) := by ...

private lemma re_I_div_eq (ρ : ℂ) (hρ_re : ρ.re = 1/2) :
    (I / ρ).re = ρ.im / (1/4 + ρ.im ^ 2) := by ...

private lemma sum_re_I_div_eq (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    (∑ ρ ∈ PositiveImZerosBelow T, (I / ρ).re) =
    (∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2)) := by ...
```

### Required deliverable
Return Lean code replacing only the proof of `critical_zero_sum_diverges`.

### Important constraint
Do not rely on assumption bundles that are known to be axiom-backed (e.g. `Littlewood.Assumptions`).

### If impossible in this context
If a true unconditional proof cannot be completed from this context alone, provide:
1. a formal blocker statement (exact missing theorem), and
2. a best unconditional helper theorem that compiles and reduces the gap.

---

## Prompt C (No-Repo): `exists_large_x_phases_aligned_to_target`

You have no repo access. Work from this prompt only.

### Environment assumptions
- Lean 4 `v4.27.0-rc1`, Mathlib rev above.
- No axioms, no `sorry`, no `admit`.

### Target theorem (exact signature)
```lean
lemma exists_large_x_phases_aligned_to_target
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    (hS_pos : ∀ ρ ∈ S, 0 < ρ.im)
    (w : ℂ) (hw : ‖w‖ = 1) (ε : ℝ) (hε : ε > 0) (X : ℝ)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε := by
  sorry
```

### Available local code context (already proved)
```lean
import Mathlib
import Littlewood.ZetaZeros.SupremumRealPart

namespace Aristotle.DirichletPhaseAlignment
open Real Complex Filter Asymptotics Set

-- key definitions
def CriticalZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}
def ZerosBelow (T : ℝ) : Finset ℂ :=
  if h : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite then h.toFinset else ∅

-- proved simultaneous approximation infra
lemma simultaneous_dirichlet_approximation {n : ℕ} ... := by ...
lemma exists_large_x_phases_aligned {n : ℕ} ... := by ...
lemma exists_large_x_phases_aligned_finset
  (S : Finset ℂ) (_hS : ∀ ρ ∈ S, ρ.re = 1/2) (ε : ℝ) (hε : ε > 0) (X : ℝ) :
  ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - 1‖ < ε := by ...

-- proved shifted lower/upper bounds
lemma bound_real_part_of_sum_shifted ... := by ...
lemma bound_real_part_of_sum_shifted_upper ... := by ...
```

### Required deliverable
Return Lean code replacing only the proof of `exists_large_x_phases_aligned_to_target`.

### Important
- Keep theorem statement unchanged.
- Do not inject new hypotheses.

### If impossible in this context
Provide the exact obstruction theorem needed and a strongest unconditional replacement lemma that compiles.

---

## Prompt D (No-Repo): `rs_block_analysis`

You have no repo access. Work from this prompt only.

### Environment assumptions
- Lean 4 `v4.27.0-rc1`, Mathlib rev above.
- No axioms, no `sorry`, no `admit`.

### Target theorem (exact signature)
```lean
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
  sorry
```

### Available local code context (already proved)
```lean
import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.RSBlockDecomposition
import Littlewood.Aristotle.AbelSummation

namespace Aristotle.Standalone.RSCompleteBlockAsymptotic
open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

private lemma abs_convex_le_max (a b α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |(1 - α) * a + α * b| ≤ max |a| |b| := by ...

def RSCompleteBlockWithResidualHyp : Prop :=
  ∃ (A B R : ℝ), A > 0 ∧ B ≥ 0 ∧ R ≥ 0 ∧
    (∀ k : ℕ,
      |(∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)| ≤ B) ∧
    (∀ N : ℕ,
      |∑ k ∈ Finset.range N,
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ R) ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ (α : ℝ), 0 ≤ α ∧ α ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - α * ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ B)

-- downstream theorem uses rs_block_analysis exactly
 theorem rsCompleteBlockWithResidual_sorry : RSCompleteBlockWithResidualHyp := by
   obtain ⟨A, c, C₂, hA, hc_nn, hc_anti, hblock_eq, hC₂_nn, hinterp⟩ := rs_block_analysis
   ...
```

### Required deliverable
Return Lean code replacing only the proof of `rs_block_analysis`.

### Important
- Keep theorem statement unchanged.
- Preserve compatibility with downstream proof of `rsCompleteBlockWithResidual_sorry`.

### If impossible in this context
Provide exact missing theorem and strongest unconditional intermediate lemma package.

---

## Output format required from Aristotle
For each prompt, output:
1. The replacement Lean proof code (or helper lemmas + final proof code).
2. A short explanation of strategy.
3. Any explicit blocker statement if full closure is impossible under no-axiom constraints.
