import Littlewood.Aristotle.LandauSchmidtDirect
import Littlewood.Aristotle.ZetaLogDerivNonAnalytic
import Littlewood.Aristotle.HalfPlaneConnected
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.Basic.LogarithmicIntegral

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauPiPuncturedExtensionChain

open Filter Topology Asymptotics Complex Set
open ZetaZeros GrowthDomination

/-!
Standalone pi-li Landau chain using the mathematically correct hard-case input:
an analytic log-zeta branch on the punctured half-plane `{Re > α} \ {1}`.

This avoids the impossible stronger requirement of analyticity on all `{Re > α}`
for `α < 1`, while preserving the full oscillation contradiction route.
-/

/-- Punctured-half-plane version of the pi-li Landau extension hypothesis. -/
def PiIntegralHypPunctured : Prop :=
  ∀ (α : ℝ), 1 / 2 < α -> ∀ (C : ℝ), 0 < C ->
  ∀ (σ : ℝ), σ = 1 ∨ σ = -1 ->
  (∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) ->
  ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H ({s : ℂ | α < s.re} \ {(1 : ℂ)}) ∧
    ∀ s : ℂ, 1 < s.re -> exp (H s) = riemannZeta s

/-- Landau contradiction from the punctured extension hypothesis:
at a zero `ρ₀` with `Re(ρ₀) > α`, identity principle forces
`exp(H ρ₀) = ζ(ρ₀) = 0`, impossible. -/
theorem pi_landau_contradiction_of_punctured_extension
    (pi_integral_hyp_punctured : PiIntegralHypPunctured)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ zetaNontrivialZeros)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_re : α < ρ₀.re)
    (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_bound : ∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) :
    False := by
  obtain ⟨H, hH_anal, hH_eq⟩ := pi_integral_hyp_punctured α hα_half C hC σ hσ h_bound
  have hρ₀_ne := ZetaLogDerivNonAnalytic.nontrivial_zero_ne_one ρ₀ hρ₀
  have hρ₀_zero := ZetaLogDerivNonAnalytic.nontrivial_zero_vanishes ρ₀ hρ₀
  set Ω := {s : ℂ | α < s.re} \ {(1 : ℂ)} with hΩ_def
  have hExpH_anal : AnalyticOnNhd ℂ (exp ∘ H) Ω :=
    fun s hs => analyticAt_cexp.comp (hH_anal s hs)
  have hζ_anal : AnalyticOnNhd ℂ riemannZeta Ω :=
    fun s hs => ZetaLogDerivPole.zeta_analyticAt s
      (fun h => hs.2 (mem_singleton_iff.mpr h))
  have hΩ_pc := HalfPlaneConnected.halfPlane_diff_singleton_isPreconnected α 1
  set z₀ : ℂ := ⟨α + 1, 0⟩
  have hz₀_re_1 : 1 < z₀.re := by
    simp [z₀]
    linarith
  have hz₀_ne : z₀ ≠ 1 := by
    intro h
    have := congr_arg Complex.re h
    simp [z₀] at this
    linarith
  have hz₀_mem : z₀ ∈ Ω := by
    refine ⟨?_, ?_⟩
    · simp [z₀]
    · intro h
      exact hz₀_ne (mem_singleton_iff.mp h)
  have h_ev : (exp ∘ H) =ᶠ[𝓝 z₀] riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz₀_re_1]
      with s hs
    exact hH_eq s hs
  have h_eqOn := hExpH_anal.eqOn_of_preconnected_of_eventuallyEq
    hζ_anal hΩ_pc hz₀_mem h_ev
  have hρ₀_mem : ρ₀ ∈ Ω := by
    refine ⟨?_, ?_⟩
    · exact hα_re
    · intro h
      exact hρ₀_ne (mem_singleton_iff.mp h)
  exact absurd ((h_eqOn hρ₀_mem).trans hρ₀_zero) (exp_ne_zero (H ρ₀))

/-- Schmidt oscillation for `π-li` from the punctured extension hypothesis. -/
theorem pi_omega_rpow_of_zero_above_of_punctured_extension
    (pi_integral_hyp_punctured : PiIntegralHypPunctured)
    (α : ℝ) (hα : 1 / 2 < α)
    (hzero : ∃ ρ ∈ zetaNontrivialZeros, α < ρ.re) :
    (fun x => (↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) =Ω±[fun x => x ^ α] := by
  obtain ⟨ρ₀, hρ₀, hα_re⟩ := hzero
  constructor
  · by_contra h_not
    have h_not_freq : ¬ ∃ᶠ x in atTop,
        (↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≥ 1 * x ^ α := by
      intro hfreq
      exact h_not ⟨1, one_pos, hfreq⟩
    have h_upper : ∀ᶠ x in atTop,
        (↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≤ 1 * x ^ α :=
      (Filter.not_frequently.mp h_not_freq).mono fun _ hx => le_of_lt (not_le.mp hx)
    exact pi_landau_contradiction_of_punctured_extension pi_integral_hyp_punctured
      ρ₀ hρ₀ α hα hα_re 1 one_pos 1 (Or.inl rfl)
      (by simpa only [one_mul] using h_upper)
  · by_contra h_not
    have h_not_freq : ¬ ∃ᶠ x in atTop,
        (↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≤ -(1 * x ^ α) := by
      intro hfreq
      exact h_not ⟨1, one_pos, by simpa [neg_mul] using hfreq⟩
    have h_lower : ∀ᶠ x in atTop,
        -(1 * x ^ α) ≤ (↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x :=
      (Filter.not_frequently.mp h_not_freq).mono fun _ hx => le_of_lt (not_le.mp hx)
    exact pi_landau_contradiction_of_punctured_extension pi_integral_hyp_punctured
      ρ₀ hρ₀ α hα hα_re 1 one_pos (-1) (Or.inr rfl)
      (by filter_upwards [h_lower] with x hx; linarith)

/-- Full-strength not-RH pi-li oscillation from punctured extension input. -/
theorem pi_li_omega_lll_of_not_RH_of_punctured_extension
    (pi_integral_hyp_punctured : PiIntegralHypPunctured)
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  obtain ⟨ρ₀, hρ₀, hρ₀_re⟩ :=
    Aristotle.LandauSchmidtDirect.exists_zero_re_gt_half_of_not_RH hRH
  set α := (1 / 2 + ρ₀.re) / 2
  have hα_half : 1 / 2 < α := by
    simp [α]
    linarith
  have hα_re : α < ρ₀.re := by
    simp [α]
    linarith
  have hΩ := pi_omega_rpow_of_zero_above_of_punctured_extension
    pi_integral_hyp_punctured α hα_half ⟨ρ₀, hρ₀, hα_re⟩
  exact hΩ.of_eventually_ge (sqrt_div_log_mul_lll_le_rpow α hα_half)
    sqrt_div_log_mul_lll_eventually_nonneg

end Aristotle.Standalone.LandauPiPuncturedExtensionChain
