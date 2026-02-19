import Littlewood.Aristotle.Standalone.RHWitnessConstructiveStrict
import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.ZetaZeros.SupremumRealPart

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.RHZeroSumAlignmentBridge

open Filter Complex
open GrowthDomination

/-- Explicit finite-zero main term used in the RH explicit-formula branch:
`psiMain(x) = 2 * Σ_{ρ∈S} Re(x^ρ/ρ)`. -/
def psiMainFromZeros (S : Finset ℂ) (x : ℝ) : ℝ :=
  2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)

/-- Deterministic lower bound for `psiMainFromZeros` from phase alignment and
critical-line real-part data. -/
theorem psiMain_from_alignment_lower
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ.re = 1 / 2)
    {x : ℝ} (hx : 0 < x)
    {ε : ℝ} (hε : 0 < ε)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε)
    (h_coeff : lll x ≤
      (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    2 * (Real.sqrt x * lll x) ≤ psiMainFromZeros S x := by
  have hsum :=
    Aristotle.DirichletPhaseAlignment.bound_real_part_of_sum_aligned
      hS hx hε h_phases
  unfold psiMainFromZeros
  calc
    2 * (Real.sqrt x * lll x)
        ≤ 2 * (Real.sqrt x * ((∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖))) := by
          have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h_coeff hsqrt_nonneg) (by positivity)
    _ ≤ 2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) :=
          by
            have hsum_le :
                Real.sqrt x * ((∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖))
                  ≤ (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
              simpa using hsum
            exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = psiMainFromZeros S x := by rfl

/-- Pointwise minus witness extraction from:
1. explicit-formula error at `(x,S)`,
2. phase alignment at `(x,S)`,
3. coefficient lower bound at `(x,S)`. -/
theorem psi_minus_pointwise_from_explicit_error_alignment_coeff
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ.re = 1 / 2)
    {x : ℝ} (hx : 0 < x)
    {ε : ℝ} (hε : 0 < ε)
    (h_error_at_x :
      |(chebyshevPsi x - x) + psiMainFromZeros S x| ≤ Real.sqrt x * lll x)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε)
    (h_coeff : lll x ≤
      (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    chebyshevPsi x - x ≤ -(Real.sqrt x * lll x) := by
  have hmain :
      2 * (Real.sqrt x * lll x) ≤ psiMainFromZeros S x :=
    psiMain_from_alignment_lower S hS hx hε h_phases h_coeff
  have hupp : (chebyshevPsi x - x) + psiMainFromZeros S x ≤ Real.sqrt x * lll x :=
    (abs_le.mp h_error_at_x).2
  nlinarith

/-- Pointwise plus witness extraction from:
1. explicit-formula error at `(x,S)`,
2. a sufficiently negative finite-zero main term at `(x,S)`. -/
theorem psi_plus_pointwise_from_explicit_error_main_negative
    (S : Finset ℂ)
    {x : ℝ}
    (h_error_at_x :
      |(chebyshevPsi x - x) + psiMainFromZeros S x| ≤ Real.sqrt x * lll x)
    (h_main_negative : psiMainFromZeros S x ≤ -(2 * (Real.sqrt x * lll x))) :
    chebyshevPsi x - x ≥ Real.sqrt x * lll x := by
  have hlow : -(Real.sqrt x * lll x) ≤
      (chebyshevPsi x - x) + psiMainFromZeros S x :=
    (abs_le.mp h_error_at_x).1
  nlinarith

/-- RH-side frequent negative witness for `ψ-x` from:
1. eventual explicit-formula error control around `psiMainFromZeros`, and
2. cofinal phase-alignment + coefficient-lower-bound witnesses. -/
theorem rh_psi_frequent_minus_from_zero_sum_alignment
    (hRH : ZetaZeros.RiemannHypothesis)
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ.re = 1 / 2)
    (ε : ℝ) (hε : 0 < ε)
    (h_error : ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMainFromZeros S x| ≤ Real.sqrt x * lll x)
    (h_alignment_growth : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε) ∧
      lll x ≤ (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≤ -(Real.sqrt x * lll x) := by
  have h_main_minus :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧
        2 * (Real.sqrt x * lll x) ≤ psiMainFromZeros S x := by
    intro X
    obtain ⟨x, hxMax, hphases, hcoeff⟩ := h_alignment_growth (max X 1)
    have hxX : X < x := lt_of_le_of_lt (le_max_left X 1) hxMax
    have hx1 : 1 < x := lt_of_le_of_lt (le_max_right X 1) hxMax
    refine ⟨x, hxX, ?_⟩
    exact psiMain_from_alignment_lower S hS (lt_trans zero_lt_one hx1) hε hphases hcoeff
  exact Aristotle.Standalone.RHWitnessConstructiveStrict.rh_psi_frequent_minus_from_perron_explicit_alignment
      hRH (psiMainFromZeros S) h_error h_main_minus

/-- Pointwise RH-minus witness builder:
for each threshold `X`, if one can choose `x > X` and a finite critical-line
set `S` such that
1) the explicit-formula error at `(x,S)` is bounded by `√x · lll x`,
2) all phases in `S` align at `x`,
3) the coefficient lower bound dominates `lll x`,
then `ψ(x)-x ≤ -√x · lll x` occurs cofinally. -/
theorem rh_psi_frequent_minus_from_pointwise_zero_sum_witness
    (_hRH : ZetaZeros.RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε)
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ.re = 1 / 2) ∧
        |(chebyshevPsi x - x) + psiMainFromZeros S x| ≤ Real.sqrt x * lll x ∧
        (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε) ∧
        lll x ≤
          (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≤ -(Real.sqrt x * lll x) := by
  intro X
  obtain ⟨x, hxMax, S, hS, herr, hphases, hcoeff⟩ := h_witness (max X 1)
  have hxX : X < x := lt_of_le_of_lt (le_max_left X 1) hxMax
  have hx1 : 1 < x := lt_of_le_of_lt (le_max_right X 1) hxMax
  have hx_pos : 0 < x := lt_trans zero_lt_one hx1
  refine ⟨x, hxX, ?_⟩
  exact psi_minus_pointwise_from_explicit_error_alignment_coeff
    S hS hx_pos hε herr hphases hcoeff

/-- Pointwise RH-plus witness builder:
for each threshold `X`, if one can choose `x > X` and a finite critical-line
set `S` such that
1) the explicit-formula error at `(x,S)` is bounded by `√x · lll x`,
2) the main zero-sum is sufficiently negative,
then `ψ(x)-x ≥ √x · lll x` occurs cofinally. -/
theorem rh_psi_frequent_plus_from_pointwise_zero_sum_witness
    (_hRH : ZetaZeros.RiemannHypothesis)
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ.re = 1 / 2) ∧
        |(chebyshevPsi x - x) + psiMainFromZeros S x| ≤ Real.sqrt x * lll x ∧
        psiMainFromZeros S x ≤ -(2 * (Real.sqrt x * lll x))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≥ Real.sqrt x * lll x := by
  intro X
  obtain ⟨x, hx, S, _hS, herr, hmain⟩ := h_witness X
  refine ⟨x, hx, ?_⟩
  exact psi_plus_pointwise_from_explicit_error_main_negative S herr hmain

/-- Pointwise RH witness pair builder:
if both plus/minus pointwise witness families are available, then both
frequent branches follow in the exact shape consumed by `RHCaseOscillation`. -/
theorem rh_psi_frequent_pair_from_pointwise_zero_sum_witness
    (hRH : ZetaZeros.RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε)
    (h_witness_plus :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ.re = 1 / 2) ∧
        |(chebyshevPsi x - x) + psiMainFromZeros S x| ≤ Real.sqrt x * lll x ∧
        psiMainFromZeros S x ≤ -(2 * (Real.sqrt x * lll x)))
    (h_witness_minus :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ.re = 1 / 2) ∧
        |(chebyshevPsi x - x) + psiMainFromZeros S x| ≤ Real.sqrt x * lll x ∧
        (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε) ∧
        lll x ≤
          (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≥ Real.sqrt x * lll x)
    ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≤ -(Real.sqrt x * lll x)) := by
  refine ⟨?_, ?_⟩
  · exact rh_psi_frequent_plus_from_pointwise_zero_sum_witness hRH h_witness_plus
  · exact rh_psi_frequent_minus_from_pointwise_zero_sum_witness hRH ε hε h_witness_minus

/-- RH-case `ψ-x = Ω±(√x·lll x)` from pointwise witness families for both signs. -/
theorem rh_psi_oscillation_from_pointwise_zero_sum_witness_pair
    (hRH : ZetaZeros.RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε)
    (h_witness_plus :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ.re = 1 / 2) ∧
        |(chebyshevPsi x - x) + psiMainFromZeros S x| ≤ Real.sqrt x * lll x ∧
        psiMainFromZeros S x ≤ -(2 * (Real.sqrt x * lll x)))
    (h_witness_minus :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ.re = 1 / 2) ∧
        |(chebyshevPsi x - x) + psiMainFromZeros S x| ≤ Real.sqrt x * lll x ∧
        (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε) ∧
        lll x ≤
          (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] := by
  obtain ⟨hplus, hminus⟩ :=
    rh_psi_frequent_pair_from_pointwise_zero_sum_witness
      hRH ε hε h_witness_plus h_witness_minus
  exact Aristotle.RHCaseOscillation.rh_psi_oscillation_from_frequent hplus hminus

end Aristotle.Standalone.RHZeroSumAlignmentBridge
