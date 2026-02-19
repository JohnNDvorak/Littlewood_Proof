import Littlewood.Aristotle.RHCaseOscillation
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.ZetaZeros.SupremumRealPart

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.RHWitnessConstructiveStrict

open Filter
open GrowthDomination

/-- RH-side constructive witness for the positive `ψ-x` branch from
eventual explicit-formula/Perron control and a cofinal aligned main term. -/
theorem rh_psi_frequent_plus_from_perron_explicit_alignment
    (_hRH : ZetaZeros.RiemannHypothesis)
    (psiMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x)
    (h_main_plus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMain x ≤ -(2 * (Real.sqrt x * lll x))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≥ Real.sqrt x * lll x := by
  intro X
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_error
  obtain ⟨x, hxgt, hmainx⟩ := h_main_plus (max X M)
  have hX : X < x := lt_of_le_of_lt (le_max_left X M) hxgt
  have hMle : M ≤ x := le_trans (le_max_right X M) (le_of_lt hxgt)
  have herr := hM x hMle
  have hlow : -(Real.sqrt x * lll x) ≤ (chebyshevPsi x - x) + psiMain x :=
    (abs_le.mp herr).1
  refine ⟨x, hX, ?_⟩
  nlinarith

/-- RH-side constructive witness for the negative `ψ-x` branch from
eventual explicit-formula/Perron control and a cofinal aligned main term. -/
theorem rh_psi_frequent_minus_from_perron_explicit_alignment
    (_hRH : ZetaZeros.RiemannHypothesis)
    (psiMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x)
    (h_main_minus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x * lll x) ≤ psiMain x) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≤ -(Real.sqrt x * lll x) := by
  intro X
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_error
  obtain ⟨x, hxgt, hmainx⟩ := h_main_minus (max X M)
  have hX : X < x := lt_of_le_of_lt (le_max_left X M) hxgt
  have hMle : M ≤ x := le_trans (le_max_right X M) (le_of_lt hxgt)
  have herr := hM x hMle
  have hupp : (chebyshevPsi x - x) + psiMain x ≤ Real.sqrt x * lll x :=
    (abs_le.mp herr).2
  refine ⟨x, hX, ?_⟩
  nlinarith

/-- RH-side constructive witness for the positive `π-li` branch from
eventual explicit-formula/Perron control and a cofinal aligned main term. -/
theorem rh_pi_li_frequent_plus_from_perron_explicit_alignment
    (_hRH : ZetaZeros.RiemannHypothesis)
    (piMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x) + piMain x|
        ≤ Real.sqrt x / Real.log x * lll x)
    (h_main_plus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piMain x ≤ -(2 * (Real.sqrt x / Real.log x * lll x))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≥
        Real.sqrt x / Real.log x * lll x := by
  intro X
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_error
  obtain ⟨x, hxgt, hmainx⟩ := h_main_plus (max X M)
  have hX : X < x := lt_of_le_of_lt (le_max_left X M) hxgt
  have hMle : M ≤ x := le_trans (le_max_right X M) (le_of_lt hxgt)
  have herr := hM x hMle
  have hlow : -(Real.sqrt x / Real.log x * lll x) ≤
      ((Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x) + piMain x :=
    (abs_le.mp herr).1
  refine ⟨x, hX, ?_⟩
  nlinarith

/-- RH-side constructive witness for the negative `π-li` branch from
eventual explicit-formula/Perron control and a cofinal aligned main term. -/
theorem rh_pi_li_frequent_minus_from_perron_explicit_alignment
    (_hRH : ZetaZeros.RiemannHypothesis)
    (piMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x) + piMain x|
        ≤ Real.sqrt x / Real.log x * lll x)
    (h_main_minus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x / Real.log x * lll x) ≤ piMain x) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≤
        -(Real.sqrt x / Real.log x * lll x) := by
  intro X
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_error
  obtain ⟨x, hxgt, hmainx⟩ := h_main_minus (max X M)
  have hX : X < x := lt_of_le_of_lt (le_max_left X M) hxgt
  have hMle : M ≤ x := le_trans (le_max_right X M) (le_of_lt hxgt)
  have herr := hM x hMle
  have hupp :
      ((Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x) + piMain x
        ≤ Real.sqrt x / Real.log x * lll x :=
    (abs_le.mp herr).2
  refine ⟨x, hX, ?_⟩
  nlinarith

/-- Combined RH witness pair for `ψ-x`. -/
theorem rh_psi_frequent_pair_from_perron_explicit_alignment
    (hRH : ZetaZeros.RiemannHypothesis)
    (psiMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x)
    (h_main_plus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMain x ≤ -(2 * (Real.sqrt x * lll x)))
    (h_main_minus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x * lll x) ≤ psiMain x) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≥ Real.sqrt x * lll x)
    ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≤ -(Real.sqrt x * lll x)) := by
  refine ⟨?_, ?_⟩
  · exact rh_psi_frequent_plus_from_perron_explicit_alignment
      hRH psiMain h_error h_main_plus
  · exact rh_psi_frequent_minus_from_perron_explicit_alignment
      hRH psiMain h_error h_main_minus

/-- Combined RH witness pair for `π-li`. -/
theorem rh_pi_li_frequent_pair_from_perron_explicit_alignment
    (hRH : ZetaZeros.RiemannHypothesis)
    (piMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x) + piMain x|
        ≤ Real.sqrt x / Real.log x * lll x)
    (h_main_plus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piMain x ≤ -(2 * (Real.sqrt x / Real.log x * lll x)))
    (h_main_minus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x / Real.log x * lll x) ≤ piMain x) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≥
        Real.sqrt x / Real.log x * lll x)
    ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≤
        -(Real.sqrt x / Real.log x * lll x)) := by
  refine ⟨?_, ?_⟩
  · exact rh_pi_li_frequent_plus_from_perron_explicit_alignment
      hRH piMain h_error h_main_plus
  · exact rh_pi_li_frequent_minus_from_perron_explicit_alignment
      hRH piMain h_error h_main_minus

/-- RH-case `ψ-x = Ω±(√x·lll x)` from constructive Perron/explicit/alignment
data, in the exact shape consumed by `DeepSorries` RH branch wiring. -/
theorem rh_psi_oscillation_from_perron_explicit_alignment
    (hRH : ZetaZeros.RiemannHypothesis)
    (psiMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x)
    (h_main_plus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMain x ≤ -(2 * (Real.sqrt x * lll x)))
    (h_main_minus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x * lll x) ≤ psiMain x) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] := by
  exact Aristotle.RHCaseOscillation.rh_psi_oscillation_from_frequent
    (rh_psi_frequent_plus_from_perron_explicit_alignment
      hRH psiMain h_error h_main_plus)
    (rh_psi_frequent_minus_from_perron_explicit_alignment
      hRH psiMain h_error h_main_minus)

/-- RH-case `π-li = Ω±((√x/log x)·lll x)` from constructive
Perron/explicit/alignment data, consumable by `DeepSorries` RH branch wiring. -/
theorem rh_pi_li_oscillation_from_perron_explicit_alignment
    (hRH : ZetaZeros.RiemannHypothesis)
    (piMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x) + piMain x|
        ≤ Real.sqrt x / Real.log x * lll x)
    (h_main_plus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piMain x ≤ -(2 * (Real.sqrt x / Real.log x * lll x)))
    (h_main_minus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x / Real.log x * lll x) ≤ piMain x) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  exact Aristotle.RHCaseOscillation.rh_pi_li_oscillation_from_frequent
    (rh_pi_li_frequent_plus_from_perron_explicit_alignment
      hRH piMain h_error h_main_plus)
    (rh_pi_li_frequent_minus_from_perron_explicit_alignment
      hRH piMain h_error h_main_minus)

end Aristotle.Standalone.RHWitnessConstructiveStrict
