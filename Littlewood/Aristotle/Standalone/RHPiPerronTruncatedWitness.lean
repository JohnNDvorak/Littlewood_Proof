import Littlewood.Aristotle.Standalone.RHPiZeroSumAlignmentBridge
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.ZetaZeros.ZeroCountingFunction

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiPerronTruncatedWitness

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge

/--
Perron/truncated explicit-formula witness family at the baseline `sqrt/log` scale.

This is the direct analytic payload expected from a RH truncated explicit formula
for `π(x)-li(x)` with a finite zero cutoff `T`.
-/
abbrev PerronSqrtErrorFamily : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis,
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
      4 ≤ T ∧
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ Real.sqrt x / Real.log x

/-- Pointwise scale comparison: `(sqrt x)/(log x) ≤ piScale x`
whenever `x > 1` and `lll x ≥ 1`. -/
lemma sqrt_over_log_le_piScale_of_lll_ge_one
    {x : ℝ}
    (hx1 : 1 < x)
    (hlll : 1 ≤ lll x) :
    Real.sqrt x / Real.log x ≤ piScale x := by
  have hlog_pos : 0 < Real.log x := Real.log_pos hx1
  have hdiv_nonneg : 0 ≤ Real.sqrt x / Real.log x :=
    div_nonneg (Real.sqrt_nonneg x) (le_of_lt hlog_pos)
  calc
    Real.sqrt x / Real.log x
        ≤ (Real.sqrt x / Real.log x) * lll x :=
          le_mul_of_one_le_right hdiv_nonneg hlll
    _ = piScale x := by
          simp [piScale, mul_assoc, mul_comm, mul_left_comm]

/-- Upgrade a pointwise `sqrt/log` explicit-formula error bound to the
Littlewood `piScale` bound. -/
lemma sqrt_error_le_piScale_of_lll_ge_one
    {x T : ℝ}
    (hx1 : 1 < x)
    (hlll : 1 ≤ lll x)
    (herr :
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ Real.sqrt x / Real.log x) :
    |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
      ≤ piScale x := by
  exact le_trans herr (sqrt_over_log_le_piScale_of_lll_ge_one hx1 hlll)

/-- Global upgrade: any Perron witness family at `sqrt/log` scale yields the
same witness family at `piScale`. -/
theorem perron_sqrt_family_to_piScale
    (hPerron : PerronSqrtErrorFamily) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis,
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
          ≤ piScale x := by
  intro _hRH X
  rcases (Filter.eventually_atTop.1 lll_eventually_ge_one) with ⟨B, hB⟩
  rcases hPerron _hRH (max X B) with ⟨x, hx, T, hT4, hx1, herr⟩
  have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
  have hlll : 1 ≤ lll x := hB x hBx
  refine ⟨x, hXx, T, hT4, hx1, ?_⟩
  exact sqrt_error_le_piScale_of_lll_ge_one hx1 hlll herr

end Aristotle.Standalone.RHPiPerronTruncatedWitness
