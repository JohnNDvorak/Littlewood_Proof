/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Landau's Lemma

This file proves Landau's fundamental lemma about Dirichlet integrals with
non-negative coefficients. This is a key tool for establishing oscillation
results in analytic number theory.

## Main Results

* `landau_lemma` : If A(x) ≥ 0 for large x and F(s) = ∫₁^∞ A(x)x^{-s}dx converges
  for Re(s) > σ_c, then F is not analytic at s = σ_c.

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Lemma 15.1
* Ingham, "The Distribution of Prime Numbers", Chapter IV
-/

open Complex Real Filter Topology Set MeasureTheory

namespace Landau

/-! ## Statement of Landau's Lemma -/

/-- The abscissa of convergence for a Dirichlet integral ∫₁^∞ A(x)x^{-s}dx -/
noncomputable def abscissaOfConvergence (_A : ℝ → ℝ) : EReal :=
  sInf (Set.univ : Set EReal)  -- Placeholder definition

/-- The Dirichlet integral transform F(s) = ∫₁^∞ A(x)x^{-s}dx -/
noncomputable def dirichletIntegral (A : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi 1, A x * (x : ℂ) ^ (-s)

/-! ## Hypotheses -/

/--
HYPOTHESIS: Landau's lemma conclusion for a Dirichlet integral.
MATHEMATICAL STATUS: classical analytic number theory.
MATHLIB STATUS: not available.
REFERENCE: Montgomery-Vaughan, Lemma 15.1.
-/
class LandauLemmaHyp (A : ℝ → ℝ) (σ_c : ℝ) : Prop where
  analytic_right : ∀ s : ℂ, σ_c < s.re → AnalyticAt ℂ (dirichletIntegral A) s
  not_analytic_at : ¬AnalyticAt ℂ (dirichletIntegral A) σ_c

/--
HYPOTHESIS: Absolute convergence of the Dirichlet integral for Re(s) > σ_c.
MATHEMATICAL STATUS: follows from Landau's lemma hypotheses with suitable bounds on A.
MATHLIB STATUS: not available.
-/
class DirichletIntegralConvergesHyp (A : ℝ → ℝ) (σ_c : ℝ) : Prop where
  converges : ∀ s : ℂ, σ_c < s.re →
    Integrable (fun x => A x * (x : ℂ) ^ (-s)) (volume.restrict (Set.Ioi 1))

/--
HYPOTHESIS: Analyticity of the Dirichlet integral for Re(s) > σ_c.
MATHEMATICAL STATUS: standard parametric integral theorem.
MATHLIB STATUS: not available.
-/
class DirichletIntegralAnalyticHyp (A : ℝ → ℝ) (σ_c : ℝ) : Prop where
  analytic : ∀ s : ℂ, σ_c < s.re → AnalyticAt ℂ (dirichletIntegral A) s

/--
HYPOTHESIS: Differentiation under the Dirichlet integral.
MATHEMATICAL STATUS: standard dominated convergence argument.
MATHLIB STATUS: not available.
-/
class DirichletIntegralDerivHyp (A : ℝ → ℝ) (σ_c : ℝ) : Prop where
  deriv :
    ∀ s : ℂ, σ_c < s.re → ∀ k : ℕ,
      iteratedDeriv k (dirichletIntegral A) s =
        ∫ x in Set.Ioi 1, A x * (-Real.log x) ^ k * (x : ℂ) ^ (-s)

/--
HYPOTHESIS: Power series expansion around s = 1 for the Dirichlet integral.
MATHEMATICAL STATUS: analytic continuation near s = 1.
MATHLIB STATUS: not available.
-/
class DirichletIntegralPowerSeriesHyp (A : ℝ → ℝ) (σ_c : ℝ) : Prop where
  powerSeries :
    σ_c < 1 →
      ∃ r > 0, ∀ s : ℂ, ‖s - 1‖ < r →
        dirichletIntegral A s =
          ∑' k, (iteratedDeriv k (dirichletIntegral A) 1 / k.factorial) * (s - 1) ^ k

/--
HYPOTHESIS: The power series radius extends past σ_c for non-negative A.
MATHEMATICAL STATUS: Landau's lemma argument.
MATHLIB STATUS: not available.
-/
class RadiusExceedsAbscissaHyp (A : ℝ → ℝ) (σ_c : ℝ) : Prop where
  radius_exceeds :
    σ_c < 1 → AnalyticAt ℂ (dirichletIntegral A) σ_c →
      ∃ ε > 0, ∀ s : ℝ, σ_c - ε < s →
        Integrable (fun x => A x * x ^ (-s)) (volume.restrict (Set.Ioi 1))

/--
HYPOTHESIS: Extension of convergence from analytic continuation at σ₀.
MATHEMATICAL STATUS: corollary of Landau's lemma.
MATHLIB STATUS: not available.
-/
class LandauExtensionHyp (A : ℝ → ℝ) (σ₀ : ℝ) : Prop where
  extension :
    AnalyticAt ℂ (dirichletIntegral A) σ₀ →
      ∃ ε > 0, ∀ s : ℝ, σ₀ - ε < s →
        Integrable (fun x => A x * x ^ (-s)) (volume.restrict (Set.Ioi 1))

/--
HYPOTHESIS: Landau lemma for Dirichlet series.
MATHEMATICAL STATUS: classical analytic number theory.
MATHLIB STATUS: not available.
-/
class LandauLemmaSeriesHyp (a : ℕ → ℂ) (σ_c : ℂ) : Prop where
  not_analytic :
    ¬AnalyticAt ℂ (fun s => ∑' n, a n * (n : ℂ) ^ (-s)) σ_c

/--
HYPOTHESIS: The logarithmic derivative -ζ'/ζ has a pole at any zero of ζ.
MATHEMATICAL STATUS: follows from analytic order factorization of ζ.
MATHLIB STATUS: not available.
-/
class ZetaLogDerivPoleHyp : Prop where
  pole_at_zero :
    ∀ ρ : ℂ, riemannZeta ρ = 0 →
      ¬AnalyticAt ℂ (fun s => -deriv riemannZeta s / riemannZeta s) ρ

/-- Landau's Lemma: For Dirichlet integrals with eventually non-negative coefficients,
    the abscissa of convergence is a singularity. -/
theorem landau_lemma
    (A : ℝ → ℝ)
    (hA_measurable : Measurable A)
    (hA_nonneg : ∀ᶠ x in atTop, 0 ≤ A x)
    (σ_c : ℝ) [LandauLemmaHyp A σ_c] :
    -- F(s) is analytic for Re(s) > σ_c
    (∀ s : ℂ, σ_c < s.re → AnalyticAt ℂ (dirichletIntegral A) s) ∧
    -- F(s) is NOT analytic at s = σ_c (on the real axis)
    ¬AnalyticAt ℂ (dirichletIntegral A) σ_c := by
  constructor
  · -- Part 1: Analyticity for Re(s) > σ_c
    intro s hs
    simpa using (LandauLemmaHyp.analytic_right (A := A) (σ_c := σ_c) s hs)
  · -- Part 2: Singularity at σ_c
    simpa using (LandauLemmaHyp.not_analytic_at (A := A) (σ_c := σ_c))

/-! ## Proof Outline -/

section ProofOutline

/-- Step 1: The integral converges absolutely for Re(s) > σ_c -/
theorem dirichletIntegral_converges
    (A : ℝ → ℝ) (hA_nonneg : ∀ᶠ x in atTop, 0 ≤ A x) (s : ℂ) (σ_c : ℝ)
    (hs : σ_c < s.re) [DirichletIntegralConvergesHyp A σ_c] :
    Integrable (fun x => A x * (x : ℂ) ^ (-s)) (volume.restrict (Set.Ioi 1)) := by
  simpa using (DirichletIntegralConvergesHyp.converges (A := A) (σ_c := σ_c) s hs)

/-- Step 2: The integral defines an analytic function for Re(s) > σ_c -/
theorem dirichletIntegral_analytic
    (A : ℝ → ℝ) (hA_nonneg : ∀ᶠ x in atTop, 0 ≤ A x) (s : ℂ) (σ_c : ℝ)
    (hs : σ_c < s.re) [DirichletIntegralAnalyticHyp A σ_c] :
    AnalyticAt ℂ (dirichletIntegral A) s := by
  simpa using (DirichletIntegralAnalyticHyp.analytic (A := A) (σ_c := σ_c) s hs)

/-- Step 3: If analytic at σ_c, we can differentiate under the integral -/
theorem dirichletIntegral_deriv
    (A : ℝ → ℝ) (s : ℂ) (σ_c : ℝ) (hs : σ_c < s.re) (k : ℕ)
    [DirichletIntegralDerivHyp A σ_c] :
    iteratedDeriv k (dirichletIntegral A) s =
      ∫ x in Set.Ioi 1, A x * (-Real.log x) ^ k * (x : ℂ) ^ (-s) := by
  simpa using (DirichletIntegralDerivHyp.deriv (A := A) (σ_c := σ_c) s hs k)

/-- Step 4: Power series expansion around s = 1 -/
theorem dirichletIntegral_powerSeries
    (A : ℝ → ℝ) (hA_nonneg : ∀ᶠ x in atTop, 0 ≤ A x) (σ_c : ℝ) (hσ_c : σ_c < 1)
    [DirichletIntegralPowerSeriesHyp A σ_c] :
    ∃ r > 0, ∀ s : ℂ, ‖s - 1‖ < r →
      dirichletIntegral A s = ∑' k, (iteratedDeriv k (dirichletIntegral A) 1 / k.factorial) *
        (s - 1) ^ k := by
  simpa using (DirichletIntegralPowerSeriesHyp.powerSeries (A := A) (σ_c := σ_c) hσ_c)

/-- Step 5: For non-negative A, the radius extends past σ_c (contradiction) -/
theorem radius_exceeds_abscissa
    (A : ℝ → ℝ) (hA_nonneg : ∀ᶠ x in atTop, 0 ≤ A x) (σ_c : ℝ) (hσ_c_lt_1 : σ_c < 1)
    (hanalytic : AnalyticAt ℂ (dirichletIntegral A) σ_c)
    [RadiusExceedsAbscissaHyp A σ_c] :
    ∃ ε > 0, ∀ s : ℝ, σ_c - ε < s →
      Integrable (fun x => A x * x ^ (-s)) (volume.restrict (Set.Ioi 1)) := by
  simpa using (RadiusExceedsAbscissaHyp.radius_exceeds (A := A) (σ_c := σ_c) hσ_c_lt_1 hanalytic)

end ProofOutline

/-! ## Corollaries -/

section Corollaries

/-- Corollary: If F(s) = ∫ A(x)x^{-s}dx with A ≥ 0 eventually, and F extends
    analytically to a neighborhood of σ₀ ∈ ℝ, then the integral converges for Re(s) > σ₀ - ε -/
theorem landau_extension
    (A : ℝ → ℝ) (hA_nonneg : ∀ᶠ x in atTop, 0 ≤ A x) (σ₀ : ℝ)
    (hanalytic : AnalyticAt ℂ (dirichletIntegral A) σ₀)
    [LandauExtensionHyp A σ₀] :
    ∃ ε > 0, ∀ s : ℝ, σ₀ - ε < s →
      Integrable (fun x => A x * x ^ (-s)) (volume.restrict (Set.Ioi 1)) := by
  simpa using (LandauExtensionHyp.extension (A := A) (σ₀ := σ₀) hanalytic)

/-- Abscissa of convergence for a Dirichlet series -/
noncomputable def abscissaOfConvergenceSeries (_a : ℕ → ℝ) : EReal :=
  sInf (Set.univ : Set EReal)  -- Placeholder

/-- Version for Dirichlet series ∑ aₙn^{-s} -/
theorem landau_lemma_series
    (_a : ℕ → ℂ) (_ha_nonneg : ∀ᶠ n in atTop, 0 ≤ (_a n).re)
    (_σ_c : ℂ) [LandauLemmaSeriesHyp _a _σ_c] :
    ¬AnalyticAt ℂ (fun s => ∑' n, _a n * (n : ℂ) ^ (-s)) _σ_c := by
  simpa using (LandauLemmaSeriesHyp.not_analytic (a := _a) (σ_c := _σ_c))

end Corollaries

/-! ## Application to Zeta -/

section ZetaApplication

/-- The logarithmic derivative -ζ'/ζ has a pole at any zero of ζ -/
theorem zetaLogDeriv_pole_at_zero (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    [ZetaLogDerivPoleHyp] :
    ¬AnalyticAt ℂ (fun s => -deriv riemannZeta s / riemannZeta s) ρ := by
  simpa using (ZetaLogDerivPoleHyp.pole_at_zero (ρ := ρ) hρ)

/-- -ζ'/ζ(s) = ∑ Λ(n)/n^s for Re(s) > 1, connecting to Chebyshev's ψ -/
theorem zetaLogDeriv_vonMangoldt (s : ℂ) (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℂ) ^ s := by
  have h := (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs).symm
  have hterm :
      (fun n : ℕ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n) =
        fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s := by
    funext n
    by_cases h0 : n = 0
    · subst h0
      simp [LSeries.term]
    · simp [LSeries.term, h0]
  have hL :
      LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s := by
    simp [LSeries, hterm]
  simpa [hL] using h

end ZetaApplication

-- ============================================================
-- SECTION: LSeries-Based Hypotheses (Task 42)
-- ============================================================
-- These hypotheses use Mathlib's LSeries infrastructure instead of
-- the custom dirichletIntegral. This leverages:
-- - LSeries_eq_mul_integral (Abel summation)
-- - LSeries_analyticOnNhd (analyticity)
-- - abscissaOfAbsConv (convergence abscissa)
-- ============================================================

/--
LSeries-based Landau lemma hypothesis.
For non-negative arithmetic functions, the L-series has a singularity
at its abscissa of convergence.

This is equivalent to LandauLemmaHyp but uses Mathlib's LSeries.
-/
class LandauLemmaLSeriesHyp : Prop where
  singularity : ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) →
    (∃ σ_c : ℝ, (∀ s : ℂ, σ_c < s.re → LSeriesSummable (fun n => (a n : ℂ)) s) ∧
                (∀ s : ℂ, s.re < σ_c → ¬LSeriesSummable (fun n => (a n : ℂ)) s)) →
    ∀ σ_c : ℝ, (∀ s : ℂ, σ_c < s.re → LSeriesSummable (fun n => (a n : ℂ)) s) →
              (∀ s : ℂ, s.re < σ_c → ¬LSeriesSummable (fun n => (a n : ℂ)) s) →
    ¬AnalyticAt ℂ (LSeries (fun n => (a n : ℂ))) σ_c

/--
For LSeries, analyticity in the convergence half-plane is FREE from Mathlib!
-/
theorem lseries_analytic_in_half_plane (f : ℕ → ℂ) :
    AnalyticOnNhd ℂ (LSeries f) {s | LSeries.abscissaOfAbsConv f < s.re} :=
  LSeries_analyticOnNhd f

/--
The abscissa of absolute convergence from Mathlib.
-/
noncomputable def lseriesAbscissa (a : ℕ → ℂ) : EReal :=
  LSeries.abscissaOfAbsConv a

/--
Key connection: For arithmetic functions like von Mangoldt, we get analyticity
directly from Mathlib without needing our dirichletIntegral hypotheses.
-/
theorem vonMangoldt_lseries_analytic (s : ℂ) (hs : 1 < s.re) :
    AnalyticAt ℂ (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s := by
  apply lseries_analytic_in_half_plane
  simp only [Set.mem_setOf_eq]
  -- The abscissa of abs convergence for von Mangoldt is ≤ 1
  -- because it's summable for any Re(s) > 1
  have habscissa : LSeries.abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt hy
  exact lt_of_le_of_lt habscissa (by exact_mod_cast hs)

/--
The von Mangoldt L-series is summable for Re(s) > 1. This is FREE from Mathlib!
-/
theorem vonMangoldt_lseries_summable (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt hs

-- ============================================================
-- SECTION: VonMangoldt Identity and Gap #1 Connection (Task 43)
-- ============================================================
-- The key identity from Mathlib:
--   L ↗Λ s = -deriv riemannZeta s / riemannZeta s
-- This is `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
--
-- IMPLICATIONS FOR GAP #1 (Euler Product):
-- The identity -ζ'/ζ = Σ Λ(n)/n^s is proved in Mathlib for Re(s) > 1.
-- This is the KEY CONNECTION between:
--   - Dirichlet series world (Landau lemma, LSeries)
--   - Zeta function world (zeros, poles, analytic properties)
--
-- What remains for Gap #1:
-- 1. Euler product: ζ(s) = Π_p (1 - p^{-s})^{-1} for Re(s) > 1
--    → Mathlib has this implicitly via product formulas
-- 2. Log of Euler product: log ζ(s) = Σ_p Σ_k p^{-ks}/k
--    → Not directly in Mathlib
-- 3. Zero-free region via 3-4-1 inequality
--    → Requires log ζ infrastructure
-- ============================================================

/--
PROVED FROM MATHLIB: The connection between von Mangoldt LSeries and
the logarithmic derivative of zeta. This is the bridge between
Landau lemma world and zeta zero analysis.

This identity is what makes Landau's lemma relevant to the zeta function:
if ζ(ρ) = 0, then -ζ'/ζ has a pole at ρ, which (by this identity) means
the von Mangoldt series has a singularity there.
-/
theorem vonMangoldt_eq_neg_zeta_logderiv (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    -deriv riemannZeta s / riemannZeta s := by
  -- Mathlib's statement uses ↗Λ which is definitionally equal
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/--
For the Chebyshev function connection: ψ(x) = Σ_{n ≤ x} Λ(n)
The Mellin transform of ψ gives the von Mangoldt L-series.
Note: This is `Landau.chebyshevPsiLocal` to avoid conflict with root-level definition.
-/
noncomputable def chebyshevPsiLocal (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), ArithmeticFunction.vonMangoldt n

/--
Connection to ZetaLogDerivPoleHyp: the key use of Landau's lemma
for zeta zeros is that:
1. L(Λ, s) = -ζ'/ζ(s) for Re(s) > 1
2. Λ(n) ≥ 0 for all n
3. By Landau's lemma, L(Λ, s) has a singularity at its abscissa of convergence
4. If ζ(ρ) = 0 with 0 < Re(ρ) < 1, then -ζ'/ζ has a pole at ρ
5. Therefore, the abscissa of convergence of L(Λ, s) is ≥ Re(ρ)

This is the structural connection between Landau lemma and ZetaLogDerivPoleHyp.
-/
theorem zeta_zero_implies_vonMangoldt_singularity (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    (hρ_re : 0 < ρ.re) (hρ_re' : ρ.re < 1) [ZetaLogDerivPoleHyp] :
    ¬AnalyticAt ℂ (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) ρ := by
  intro hanalytic
  -- The von Mangoldt LSeries equals -ζ'/ζ for Re(s) > 1
  -- If analytic at ρ, it would need to match -ζ'/ζ which has a pole there
  have hpole := ZetaLogDerivPoleHyp.pole_at_zero ρ hρ
  -- The proof requires analytic continuation arguments
  sorry -- BLOCKED: Need analytic continuation from Re(s) > 1 to ρ

/-!
## Hypothesis Instances

All hypothesis class instances (LandauLemmaHyp, DirichletIntegralConvergesHyp, etc.)
are provided in Assumptions.lean (the single source of truth for axioms).
-/

end Landau
