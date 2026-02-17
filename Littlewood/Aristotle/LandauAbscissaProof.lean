/-
Proof of LandauAbscissaHyp (Landau's abscissa of convergence theorem).

For g(t) = C·t^α + σ·(t - ψ(t)) ≥ 0 eventually, the Dirichlet integral
∫₁^∞ g(t)·t^{-(σ₀+1)} dt converges for α < σ₀ ≤ 1.

## Proof Strategy

Split the integral at T₀ where g becomes non-negative:
  ∫₁^∞ = ∫₁^{T₀} + ∫_{T₀}^∞

**Compact part** [1, T₀]: Bounded integrand on finite-measure set → trivially integrable.

**Tail** [T₀, ∞) where g ≥ 0: The corrected formula
  F(s) = s·C/(s-α) + σ·(1 + zrf'/zrf(s))
is analytic on {Re(s) > α} (including at s = 1 where poles cancel). For σ > 1,
the formula equals s times the Dirichlet integral. By MCT (σ ↘ 1), the tail
converges at σ = 1. For σ₀ < 1, the Tonelli/Cauchy argument extends convergence:
the Taylor "anti-coefficients" a_k = ∫ g·t^{-2}·(log t)^k are non-negative and
bounded by Cauchy estimates from the analyticity at σ = 1, giving a convergent
geometric bound for Σ a_k·(1-σ₀)^k/k! = ∫ g·t^{-(σ₀+1)}.

## References

* Landau, "Über einen Satz von Tschebyschef" (1905), Satz 15
* Hardy-Riesz, "The General Theory of Dirichlet's Series", Ch. 1

SORRY COUNT: 1 (tail_integrableOn_of_nonneg — Tonelli/Cauchy for σ₀ < 1)
NOTE: Not imported by DeepSorries (sorry consolidated there via LandauAbscissaConvergence).

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.LandauAbscissaConvergence
import Littlewood.Aristotle.PringsheimPsiAtom

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.LandauAbscissaProof

open Complex Real Filter Topology MeasureTheory Set

/-! ## Helper: compact part integrability

On the finite interval (1, T₀], the integrand is bounded (genFun ≤ D·t on [1,T₀]
and t^{-(σ₀+1)} ≤ 1), so IntegrableOn follows from finite measure + boundedness. -/

/-- genFun is measurable (chebyshevPsi is monotone hence measurable). -/
private theorem genFun_measurable (C α σ_sign : ℝ) :
    Measurable (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t) := by
  unfold PringsheimPsiAtom.genFun
  exact (measurable_id.pow_const α |>.const_mul C).add
    ((measurable_id.sub Chebyshev.psi_mono.measurable).const_mul σ_sign)

/-- The integrand is measurable on Ioi 1. -/
private theorem integrand_measurable (C α σ_sign σ₀ : ℝ) :
    Measurable (fun t : ℝ => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1))) := by
  exact (genFun_measurable C α σ_sign).mul (measurable_id.pow_const _)

/-- IntegrableOn on the compact part (1, T₀]. -/
private theorem compact_part_integrableOn (C : ℝ) (hC : 0 < C)
    (α : ℝ) (hα1 : α ≤ 1) (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (σ₀ : ℝ) (hσ₀_pos : 0 < σ₀) (T₀ : ℝ) (_hT₀ : 1 ≤ T₀) :
    IntegrableOn (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioc 1 T₀) := by
  -- Use: bounded AEStronglyMeasurable function on finite-measure set → integrable
  obtain ⟨D, _hD, hle⟩ := PringsheimPsiAtom.genFun_le_linear C hC α hα1 σ_sign hσ
  apply Measure.integrableOn_of_bounded (measure_Ioc_lt_top.ne)
    ((integrand_measurable C α σ_sign σ₀).aestronglyMeasurable) (M := D * T₀)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ⟨ht1, htT₀⟩
  have ht_pos : 0 < t := by linarith
  have ht1' : 1 ≤ t := by linarith
  rw [Real.norm_eq_abs, abs_mul]
  have h_rpow_le : |t ^ (-(σ₀ + 1))| ≤ 1 := by
    rw [abs_of_pos (rpow_pos_of_pos ht_pos _)]
    exact rpow_le_one_of_one_le_of_nonpos ht1' (by linarith)
  calc |PringsheimPsiAtom.genFun C α σ_sign t| * |t ^ (-(σ₀ + 1))|
      ≤ (D * t) * 1 :=
        mul_le_mul (hle t ht1') h_rpow_le (abs_nonneg _) (by positivity)
    _ = D * t := mul_one _
    _ ≤ D * T₀ := by nlinarith

/-! ## Helper: tail integrability

On [T₀, ∞) where g ≥ 0, the Dirichlet integral converges by the Landau
abscissa argument. This is the deep mathematical content.

**Proof sketch for the tail:**

For σ > 1 (known convergence), the real integral equals the corrected formula:
  ∫₁^∞ g(t) t^{-(σ+1)} = witnessG(σ)/σ

The corrected formula is analytic at σ = 1 (from ZetaPoleCancellation), so as
σ ↘ 1, the formula → finite limit L. By MCT on the tail (g ≥ 0, t > 1,
integrand increases as σ decreases), the tail integral at σ = 1 is finite.

For σ₀ ∈ (α, 1), the Taylor expansion at σ = 1 with non-negative "anti-coefficients"
  aₖ = ∫ g(t) t^{-2} (log t)^k dt ≥ 0
gives (by Tonelli for non-negative terms):
  ∫ g t^{-(σ₀+1)} = Σ aₖ (1-σ₀)^k / k!
The Taylor series of the corrected formula converges at σ₀ (radius ≥ 1-α),
and by Cauchy estimates aₖ ≤ k! M / r^k, so the sum is bounded by M·r/(r-(1-σ₀)) < ∞.
-/

/-- **Tail integrability**: the Dirichlet integral of g converges on the tail
[T₀, ∞) where g ≥ 0, for any σ₀ > α.

This is Landau's Satz 15 (1905) — the hard analytical content.
The proof uses: MCT from σ > 1 to σ = 1, then Pringsheim's theorem
(non-negative Taylor coefficients cannot be analytically continued past
a singularity on the positive real axis) to extend below σ = 1.

SORRY: Tonelli/Cauchy argument extending convergence from σ=1 to σ₀ < 1.
MCT gives convergence at σ=1. For σ₀ < 1, expand t^{-(σ₀+1)} in Taylor
series around σ=1, get non-negative coefficients, swap sum/integral by Tonelli,
bound partial sums by Cauchy estimates from analyticity at σ=1. -/
private theorem tail_integrableOn_of_nonneg
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀1 : σ₀ ≤ 1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t) :
    IntegrableOn (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioi T₀) := by
  sorry

/-! ## Main theorem assembly -/

/-- **Core lemma**: If g ≥ 0 eventually and the corrected formula is analytic at
real σ₀ > α, then the Dirichlet integral converges at σ₀.

Splits the integral at T₀ into compact + tail:
- Compact (1, T₀]: bounded × finite measure → integrable
- Tail (T₀, ∞): g ≥ 0, use Landau's abscissa argument -/
theorem nonneg_dirichlet_integral_of_formula_analytic
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀1 : σ₀ ≤ 1) :
    IntegrableOn (fun t => PringsheimPsiAtom.genFun C α σ_sign t * t ^ (-(σ₀ + 1)))
      (Ioi 1) := by
  have hσ₀_pos : 0 < σ₀ := by linarith
  -- Extract T₀ from the eventual non-negativity
  have hnn := PringsheimPsiAtom.genFun_nonneg_eventually α C hC σ_sign hσ hbound
  rw [Filter.Eventually, Filter.mem_atTop_sets] at hnn
  obtain ⟨T₀_raw, hT₀_raw⟩ := hnn
  -- Ensure T₀ ≥ 1 (so Ioi 1 ⊇ Ioi T₀)
  set T₀ := max T₀_raw 1 with hT₀_def
  have hT₀ : 1 ≤ T₀ := le_max_right _ _
  have hg_nn : ∀ t : ℝ, T₀ ≤ t → 0 ≤ PringsheimPsiAtom.genFun C α σ_sign t := by
    intro t ht
    exact hT₀_raw t (le_trans (le_max_left _ _) ht)
  -- Split: Ioi 1 = Ioc 1 T₀ ∪ Ioi T₀
  have h_split : Ioi (1 : ℝ) = Ioc 1 T₀ ∪ Ioi T₀ := by
    ext x; simp only [mem_Ioi, mem_Ioc, mem_union, mem_Ioi]
    constructor
    · intro hx; by_cases hxT : x ≤ T₀
      · exact Or.inl ⟨hx, hxT⟩
      · exact Or.inr (by linarith)
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
  rw [h_split]
  apply IntegrableOn.union
  · -- Compact part: (1, T₀]
    exact compact_part_integrableOn C hC α hα1 σ_sign hσ σ₀ hσ₀_pos T₀ hT₀
  · -- Tail: (T₀, ∞) where g ≥ 0
    exact tail_integrableOn_of_nonneg C hC α hα hα1 σ_sign hσ hbound σ₀ hσ₀ hσ₀1
      T₀ hT₀ hg_nn

/-! ## Main theorems -/

/-- **Landau's abscissa of convergence theorem** — proves `RealIntegrabilityHyp`.

Combines the non-negative tail argument with the compact piece to get
full integrability on (1, ∞). -/
theorem real_integrability_hyp : LandauAbscissaConvergence.RealIntegrabilityHyp := by
  intro C hC α hα σ_sign hσ hbound σ₀ hσ₀ hσ₀1
  exact nonneg_dirichlet_integral_of_formula_analytic C hC α hα (by linarith) σ_sign hσ
    hbound σ₀ hσ₀ hσ₀1

/-- **LandauAbscissaHyp** — the main result, proved from RealIntegrabilityHyp. -/
theorem landau_abscissa_hyp_proved : PringsheimPsiAtom.LandauAbscissaHyp :=
  LandauAbscissaConvergence.landau_abscissa_hyp real_integrability_hyp

end Aristotle.LandauAbscissaProof
