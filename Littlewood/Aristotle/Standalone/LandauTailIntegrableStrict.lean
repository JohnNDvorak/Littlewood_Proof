import Littlewood.Aristotle.PringsheimPsiAtom

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauTailIntegrableStrict

open Filter MeasureTheory Set

/-- Restrict Landau's real integrand from `(1, ∞)` to `(T₀, ∞)` when `1 ≤ T₀`. -/
theorem tail_integrableOn_of_integrableOn_Ioi_one
    (C α σ_sign σ₀ : ℝ)
    (hIoi1 : IntegrableOn
      (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioi (1 : ℝ)))
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀) :
    IntegrableOn
      (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioi T₀) := by
  refine hIoi1.mono_set ?_
  intro t ht
  exact lt_of_le_of_lt hT₀ ht

/-- Standalone Landau tail blocker analogous to
`LandauAbscissaProof.tail_integrableOn_of_nonneg`.

This theorem is fully proved. The only non-local input is the explicit
`h_landau_real` hypothesis, which is exactly the missing hard theorem:
real-axis convergence for `α < σ₀ ≤ 1` on `(1, ∞)`. -/
theorem tail_integrableOn_of_nonneg_strict
    (h_landau_real :
      ∀ (C : ℝ), 0 < C → ∀ (α : ℝ), 1 / 2 < α →
      ∀ (σ_sign : ℝ), σ_sign = 1 ∨ σ_sign = -1 →
      (∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α) →
      ∀ (σ₀ : ℝ), α < σ₀ → σ₀ ≤ 1 →
      IntegrableOn (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
        (Ioi (1 : ℝ)))
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (_hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀1 : σ₀ ≤ 1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (_hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) :
    IntegrableOn
      (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioi T₀) := by
  have hIoi1 :
      IntegrableOn
        (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
        (Ioi (1 : ℝ)) :=
    h_landau_real C hC α hα σ_sign hσ hbound σ₀ hσ₀ hσ₀1
  exact tail_integrableOn_of_integrableOn_Ioi_one C α σ_sign σ₀ hIoi1 T₀ hT₀

end Aristotle.Standalone.LandauTailIntegrableStrict
