/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), adapted for Lean 4.27 by Claude
-/
import Littlewood.CoreLemmas.LandauLemma

/-!
# Dirichlet Integral — Conditional Constructors

The sorry-backed instances in `Assumptions.lean` were deprecated because they
claimed properties for ALL `A : ℝ → ℝ` without hypotheses. This file provides
conditional constructors given appropriate assumptions on A.

## Main Results

* `Landau.analyticHyp_of_analyticOnNhd` — G2 from analyticity on a half-plane
* `Landau.convergesHyp_of_integrableOn` — G1 from integrability hypothesis
* `Landau.derivHyp_of_iteratedDeriv` — G3 from iterated derivative formula
-/

open Complex Real Filter Topology Set MeasureTheory

namespace Landau

/-- **G2 from half-plane analyticity**: If `dirichletIntegral A` is analytic on
`{s | σ_c < s.re}`, then `DirichletIntegralAnalyticHyp A σ_c` holds. -/
theorem analyticHyp_of_analyticOnNhd (A : ℝ → ℝ) (σ_c : ℝ)
    (hf : AnalyticOnNhd ℂ (dirichletIntegral A) {s | σ_c < s.re}) :
    DirichletIntegralAnalyticHyp A σ_c where
  analytic := fun s hs => hf s hs

/-- **G1**: Wraps an explicit integrability hypothesis into the class. -/
theorem convergesHyp_of_integrableOn (A : ℝ → ℝ) (σ_c : ℝ)
    (hint : ∀ s : ℂ, σ_c < s.re →
      Integrable (fun x => A x * (x : ℂ) ^ (-s)) (volume.restrict (Ioi 1))) :
    DirichletIntegralConvergesHyp A σ_c where
  converges := hint

/-- **G3**: Wraps an explicit iterated derivative formula into the class. -/
theorem derivHyp_of_iteratedDeriv (A : ℝ → ℝ) (σ_c : ℝ)
    (hderiv : ∀ s : ℂ, σ_c < s.re → ∀ k : ℕ,
      iteratedDeriv k (dirichletIntegral A) s =
        ∫ x in Ioi 1, A x * (-Real.log x) ^ k * (x : ℂ) ^ (-s)) :
    DirichletIntegralDerivHyp A σ_c where
  deriv := hderiv

end Landau
