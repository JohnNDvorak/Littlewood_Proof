import Littlewood.Aristotle.Standalone.RHWitnessConstructiveStrict
import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.ZetaZeros.SupremumRealPart

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.RHPiZeroSumAlignmentBridge

open Filter Complex
open GrowthDomination

/-- `π(x)-li(x)` in project notation. -/
def piLiErr (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x

/-- RH π-side comparison scale. -/
def piScale (x : ℝ) : ℝ :=
  Real.sqrt x / Real.log x * lll x

/-- Finite-zero main term used in RH π witness extraction:
`piMain(x) = 2 * Σ Re(x^ρ/ρ) / log x`. -/
def piMainFromZeros (S : Finset ℂ) (x : ℝ) : ℝ :=
  2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) / Real.log x

/-- Deterministic lower bound for `piMainFromZeros` from phase alignment and
critical-line real-part data, scaled by `1/log x`. -/
theorem piMain_from_alignment_lower
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ.re = 1 / 2)
    {x : ℝ} (hx : 1 < x)
    {ε : ℝ} (hε : 0 < ε)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε)
    (h_coeff : lll x ≤
      (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    2 * piScale x ≤ piMainFromZeros S x := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  have hsum :=
    Aristotle.DirichletPhaseAlignment.bound_real_part_of_sum_aligned
      hS hx_pos hε h_phases
  unfold piScale piMainFromZeros
  have hmul :
      2 * (Real.sqrt x * lll x)
        ≤ 2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
    calc
      2 * (Real.sqrt x * lll x)
          ≤ 2 * (Real.sqrt x * ((∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖))) := by
            have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h_coeff hsqrt_nonneg) (by positivity)
      _ ≤ 2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
            have hsum_le :
                Real.sqrt x * ((∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖))
                  ≤ (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
              simpa using hsum
            exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
  have hdiv :
      (2 * (Real.sqrt x * lll x)) / Real.log x
        ≤ (2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)) / Real.log x := by
    exact div_le_div_of_nonneg_right hmul (le_of_lt hlog_pos)
  have hscaled :
      2 * (Real.sqrt x / Real.log x * lll x)
        ≤ (2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)) / Real.log x := by
    calc
      2 * (Real.sqrt x / Real.log x * lll x)
          = (2 * (Real.sqrt x * lll x)) / Real.log x := by
              field_simp [hlog_pos.ne']
      _ ≤ (2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)) / Real.log x := hdiv
  simpa [piScale, piMainFromZeros, mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- Pointwise minus witness extraction from:
1. explicit-formula error at `(x,S)`,
2. phase alignment at `(x,S)`,
3. coefficient lower bound at `(x,S)`. -/
theorem pi_minus_pointwise_from_explicit_error_alignment_coeff
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ.re = 1 / 2)
    {x : ℝ} (hx : 1 < x)
    {ε : ℝ} (hε : 0 < ε)
    (h_error_at_x : |piLiErr x + piMainFromZeros S x| ≤ piScale x)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε)
    (h_coeff : lll x ≤
      (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    piLiErr x ≤ -piScale x := by
  have hmain : 2 * piScale x ≤ piMainFromZeros S x :=
    piMain_from_alignment_lower S hS hx hε h_phases h_coeff
  have hupp : piLiErr x + piMainFromZeros S x ≤ piScale x :=
    (abs_le.mp h_error_at_x).2
  nlinarith

/-- Pointwise plus witness extraction from:
1. explicit-formula error at `(x,S)`,
2. a sufficiently negative finite-zero main term at `(x,S)`. -/
theorem pi_plus_pointwise_from_explicit_error_main_negative
    (S : Finset ℂ)
    {x : ℝ}
    (h_error_at_x : |piLiErr x + piMainFromZeros S x| ≤ piScale x)
    (h_main_negative : piMainFromZeros S x ≤ -(2 * piScale x)) :
    piLiErr x ≥ piScale x := by
  have hlow : -piScale x ≤ piLiErr x + piMainFromZeros S x :=
    (abs_le.mp h_error_at_x).1
  nlinarith

/-- Pointwise RH-minus witness builder for `π-li`.
For each threshold `X`, if one can choose `x > X` and a finite critical-line set `S`
with bounded explicit-formula error, aligned phases, and coefficient domination,
then `π(x)-li(x) ≤ -((√x/log x)·lll x)` occurs cofinally. -/
theorem rh_pi_frequent_minus_from_pointwise_zero_sum_witness
    (_hRH : ZetaZeros.RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε)
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ.re = 1 / 2) ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε) ∧
        lll x ≤
          (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ piLiErr x ≤ -piScale x := by
  intro X
  obtain ⟨x, hxMax, S, hS, herr, hphases, hcoeff⟩ := h_witness (max X 2)
  have hxX : X < x := lt_of_le_of_lt (le_max_left X 2) hxMax
  have hx2 : 2 < x := lt_of_le_of_lt (le_max_right X 2) hxMax
  have hx1 : 1 < x := lt_trans one_lt_two hx2
  refine ⟨x, hxX, ?_⟩
  exact pi_minus_pointwise_from_explicit_error_alignment_coeff
    S hS hx1 hε herr hphases hcoeff

/-- Pointwise RH-plus witness builder for `π-li`.
For each threshold `X`, if one can choose `x > X` and a finite critical-line set `S`
with bounded explicit-formula error and sufficiently negative main term,
then `π(x)-li(x) ≥ (√x/log x)·lll x` occurs cofinally. -/
theorem rh_pi_frequent_plus_from_pointwise_zero_sum_witness
    (_hRH : ZetaZeros.RiemannHypothesis)
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ.re = 1 / 2) ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        piMainFromZeros S x ≤ -(2 * piScale x)) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ piLiErr x ≥ piScale x := by
  intro X
  obtain ⟨x, hx, S, _hS, herr, hmain⟩ := h_witness X
  refine ⟨x, hx, ?_⟩
  exact pi_plus_pointwise_from_explicit_error_main_negative S herr hmain

end Aristotle.Standalone.RHPiZeroSumAlignmentBridge
