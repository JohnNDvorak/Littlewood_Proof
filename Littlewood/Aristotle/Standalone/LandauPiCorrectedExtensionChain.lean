import Littlewood.Aristotle.LandauSchmidtDirect
import Littlewood.Aristotle.ZetaLogDerivNonAnalytic
import Littlewood.Aristotle.ZetaLogDerivPole
import Littlewood.Aristotle.HalfPlaneConnected
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.Basic.LogarithmicIntegral

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LandauPiCorrectedExtensionChain

open Filter Topology Asymptotics Complex Set
open ZetaZeros GrowthDomination

/-!
# Corrected pi-li Landau chain using `(s-1)*ζ(s)` instead of `ζ(s)`

The original `PiAtomHardCasePuncturedCore` required `H` analytic on `{Re > α} \ {1}`
with `exp(H) = ζ` on `{Re > 1}`. This is **mathematically false** due to monodromy:
`ζ'/ζ` has residue −1 at `s = 1`, giving monodromy `−2πi` for any branch of `log ζ`
around `s = 1`. No single-valued analytic `H` exists on the punctured half-plane.

The corrected version uses `G` analytic on `{Re > α}` (full half-plane, no puncture)
with `exp(G) = (s-1)*ζ(s)` on `{Re > 1}`. This **is** constructively provable:
`(s-1)*ζ(s)` has zero monodromy around `s = 1` (the log-derivative residues cancel:
`1/(s-1)` contributes `+1` and `ζ'/ζ` contributes `−1`), so `log((s-1)ζ(s))` is
single-valued on `{Re > α}`.

The contradiction route is the same: identity theorem on the preconnected domain
`{Re > α} \ {1}` forces `exp(G(ρ₀)) = (ρ₀-1)*ζ(ρ₀) = 0` at a nontrivial zero,
but `exp ≠ 0`.
-/

/-- Corrected pi-li Landau extension hypothesis: `G` analytic on the full half-plane
`{Re > α}` with `exp(G s) = (s - 1) * ζ(s)` for `Re(s) > 1`.

Restricted to `1/2 < α < 1` because:
- `α > 1/2` is needed for the Landau argument
- `α < 1` is the only range where the hypothesis is nontrivial
  (for `α ≥ 1`, the domain `{Re > α} ⊂ {Re > 1}` and the construction is standard)
- Under `¬RH`, nontrivial zeros have `Re(ρ) < 1`, so `α < 1` suffices -/
def PiIntegralHypCorrected : Prop :=
  ∀ (α : ℝ), 1 / 2 < α → α < 1 →
  ∀ (C : ℝ), 0 < C →
  ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
  (∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) →
  ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
    ∀ s : ℂ, 1 < s.re → exp (G s) = (s - 1) * riemannZeta s

/-- Landau contradiction from the corrected extension hypothesis:
at a nontrivial zero `ρ₀` with `Re(ρ₀) > α`, the identity principle on
`{Re > α} \ {1}` forces `exp(G ρ₀) = (ρ₀ - 1) * ζ(ρ₀) = 0`, impossible. -/
theorem pi_landau_contradiction_of_corrected_extension
    (pi_integral_hyp : PiIntegralHypCorrected)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ zetaNontrivialZeros)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) (hα_re : α < ρ₀.re)
    (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_bound : ∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) :
    False := by
  obtain ⟨G, hG_anal, hG_eq⟩ := pi_integral_hyp α hα_half hα_lt_one C hC σ hσ h_bound
  have hρ₀_ne := ZetaLogDerivNonAnalytic.nontrivial_zero_ne_one ρ₀ hρ₀
  have hρ₀_zero := ZetaLogDerivNonAnalytic.nontrivial_zero_vanishes ρ₀ hρ₀
  -- Work on the punctured domain Ω = {Re > α} \ {1}, which is preconnected
  set Ω := {s : ℂ | α < s.re} \ {(1 : ℂ)} with hΩ_def
  -- exp ∘ G is analytic on Ω (G is analytic on the larger set {Re > α})
  have hExpG_anal : AnalyticOnNhd ℂ (exp ∘ G) Ω :=
    fun s hs => analyticAt_cexp.comp (hG_anal s hs.1)
  -- (· - 1) * riemannZeta is analytic on Ω (product of analytic functions)
  have hSZeta_anal : AnalyticOnNhd ℂ (fun s => (s - 1) * riemannZeta s) Ω :=
    fun s hs => by
      have hne : s ≠ 1 := fun h => hs.2 (mem_singleton_iff.mpr h)
      exact (analyticAt_id.sub analyticAt_const).mul
        (ZetaLogDerivPole.zeta_analyticAt s hne)
  -- {Re > α} \ {1} is preconnected (existing infrastructure)
  have hΩ_pc := HalfPlaneConnected.halfPlane_diff_singleton_isPreconnected α 1
  -- Pick a base point z₀ in {Re > 1} ∩ Ω
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
  -- exp(G s) = (s-1)*ζ(s) near z₀ (from hypothesis, since Re(z₀) > 1)
  have h_ev : (exp ∘ G) =ᶠ[𝓝 z₀] (fun s => (s - 1) * riemannZeta s) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz₀_re_1]
      with s hs
    simp only [Function.comp]
    exact hG_eq s hs
  -- Identity theorem: exp ∘ G = (· - 1) * ζ on all of Ω
  have h_eqOn := hExpG_anal.eqOn_of_preconnected_of_eventuallyEq
    hSZeta_anal hΩ_pc hz₀_mem h_ev
  -- ρ₀ ∈ Ω (since Re(ρ₀) > α and ρ₀ ≠ 1)
  have hρ₀_mem : ρ₀ ∈ Ω := by
    refine ⟨?_, ?_⟩
    · exact hα_re
    · intro h
      exact hρ₀_ne (mem_singleton_iff.mp h)
  -- At ρ₀: exp(G(ρ₀)) = (ρ₀-1)*ζ(ρ₀) = (ρ₀-1)*0 = 0, but exp ≠ 0
  have hval : (fun s => (s - 1) * riemannZeta s) ρ₀ = 0 := by
    simp only
    rw [hρ₀_zero, mul_zero]
  exact absurd ((h_eqOn hρ₀_mem).trans hval) (exp_ne_zero (G ρ₀))

/-- Schmidt oscillation for `π-li` from the corrected extension hypothesis. -/
theorem pi_omega_rpow_of_zero_above_of_corrected_extension
    (pi_integral_hyp : PiIntegralHypCorrected)
    (α : ℝ) (hα : 1 / 2 < α) (hα_lt_one : α < 1)
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
    exact pi_landau_contradiction_of_corrected_extension pi_integral_hyp
      ρ₀ hρ₀ α hα hα_lt_one hα_re 1 one_pos 1 (Or.inl rfl)
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
    exact pi_landau_contradiction_of_corrected_extension pi_integral_hyp
      ρ₀ hρ₀ α hα hα_lt_one hα_re 1 one_pos (-1) (Or.inr rfl)
      (by filter_upwards [h_lower] with x hx; linarith)

/-- Full-strength not-RH pi-li oscillation from corrected extension input. -/
theorem pi_li_omega_lll_of_not_RH_of_corrected_extension
    (pi_integral_hyp : PiIntegralHypCorrected)
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
  -- α < 1 because ρ₀ is a nontrivial zero, hence Re(ρ₀) < 1
  have hρ₀_re_lt_one : ρ₀.re < 1 := (mem_zetaNontrivialZeros.1 hρ₀).2.2
  have hα_lt_one : α < 1 := by
    simp [α]
    linarith
  have hα_re : α < ρ₀.re := by
    simp [α]
    linarith
  have hΩ := pi_omega_rpow_of_zero_above_of_corrected_extension
    pi_integral_hyp α hα_half hα_lt_one ⟨ρ₀, hρ₀, hα_re⟩
  exact hΩ.of_eventually_ge (sqrt_div_log_mul_lll_le_rpow α hα_half)
    sqrt_div_log_mul_lll_eventually_nonneg

end Aristotle.Standalone.LandauPiCorrectedExtensionChain
