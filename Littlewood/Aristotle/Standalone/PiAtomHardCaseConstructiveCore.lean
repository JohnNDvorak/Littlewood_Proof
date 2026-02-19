import Littlewood.Aristotle.LandauLogZetaObstruction
import Littlewood.Aristotle.CorrectionTermAnalyticity
import Littlewood.Aristotle.Standalone.LandauPiPuncturedExtensionChain
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.CoreLemmas.GrowthDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.PiAtomHardCaseConstructiveCore

open Complex Real Filter Topology Set
open ZetaZeros GrowthDomination

/-- One-sided hard-case `π-li` bound in the range `1/2 < α < 1`. -/
def PiLiHardBound (α C σ : ℝ) : Prop :=
  ∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α

/-- Constructive hard-case core: punctured-half-plane log-branch construction
in the genuinely hard range `1/2 < α < 1`. -/
def PiAtomHardCasePuncturedCore : Prop :=
  ∀ (α : ℝ), 1 / 2 < α → α < 1 →
  ∀ (C : ℝ), 0 < C →
  ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
  PiLiHardBound α C σ →
  ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H ({s : ℂ | α < s.re} \ {(1 : ℂ)}) ∧
    ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s

/-- A full hard-case branch is equivalent to a punctured branch plus continuity
at `s = 1`. This isolates the only extra requirement beyond punctured continuation. -/
theorem exists_full_log_branch_iff_punctured_with_continuous_at_one
    (α : ℝ) (hα1 : α < 1) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s) ↔
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H ({s : ℂ | α < s.re} \ {(1 : ℂ)}) ∧
      ContinuousAt H (1 : ℂ) ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s) := by
  constructor
  · rintro ⟨H, hH_anal, hH_eq⟩
    refine ⟨H, ?_, ?_, hH_eq⟩
    · intro s hs
      exact hH_anal s hs.1
    · have h1_mem : (1 : ℂ) ∈ {s : ℂ | α < s.re} := by
        simp [hα1]
      exact (hH_anal 1 h1_mem).continuousAt
  · rintro ⟨H, hH_anal_punct, hH_cont, hH_eq⟩
    have h_halfplane_nhds : {s : ℂ | α < s.re} ∈ 𝓝 (1 : ℂ) := by
      exact (isOpen_lt continuous_const continuous_re).mem_nhds (by simp [hα1])
    have h_re_eventually :
        ∀ᶠ z in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ), α < z.re :=
      nhdsWithin_le_nhds h_halfplane_nhds
    have h_diff_punct :
        ∀ᶠ z in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ), DifferentiableAt ℂ H z := by
      filter_upwards [eventually_mem_nhdsWithin, h_re_eventually] with z hz_ne hz_re
      have hz_mem : z ∈ ({s : ℂ | α < s.re} \ {(1 : ℂ)}) := by
        refine ⟨hz_re, ?_⟩
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz_ne
      exact (hH_anal_punct z hz_mem).differentiableAt
    have hH_anal_one : AnalyticAt ℂ H (1 : ℂ) :=
      Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        h_diff_punct hH_cont
    refine ⟨H, ?_, hH_eq⟩
    intro s hs
    by_cases hs1 : s = 1
    · subst hs1
      exact hH_anal_one
    · exact hH_anal_punct s ⟨hs, by simp [hs1]⟩

/-- No punctured branch can be continuous at `s = 1` for `α < 1`, because that
would force a full branch and contradict the pole obstruction. -/
theorem no_punctured_log_branch_continuous_at_one
    (α : ℝ) (hα1 : α < 1) :
    ¬∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H ({s : ℂ | α < s.re} \ {(1 : ℂ)}) ∧
      ContinuousAt H (1 : ℂ) ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s := by
  intro h
  have hFull :=
    (exists_full_log_branch_iff_punctured_with_continuous_at_one α hα1).2 h
  exact LandauLogZetaObstruction.zeta_has_no_analytic_log_at_one α hα1 hFull

/-- Wiring theorem: the hard-range punctured core is exactly enough to build the
global punctured Landau hypothesis used in the non-RH `π-li` chain. -/
theorem piIntegralHypPunctured_of_punctured_core
    (hCore : PiAtomHardCasePuncturedCore) :
    Aristotle.Standalone.LandauPiPuncturedExtensionChain.PiIntegralHypPunctured := by
  intro α hα C hC σ hσ hbound
  by_cases hα1 : α < 1
  · exact hCore α hα hα1 C hC σ hσ hbound
  · have hα_ge_one : 1 ≤ α := by linarith
    refine ⟨LandauLogZetaObstruction.H_zeta_log, ?_, ?_⟩
    · intro s hs
      have hs_re_gt_one : 1 < s.re := lt_of_le_of_lt hα_ge_one hs.1
      have hmid_gt_one : 1 < (1 + s.re) / 2 := by linarith
      have hmid_lt_re : (1 + s.re) / 2 < s.re := by linarith
      exact CorrectionTermAnalyticity.H_zeta_log_analyticOnNhd
        ((1 + s.re) / 2) hmid_gt_one s (by
          simp only [mem_setOf_eq]
          exact hmid_lt_re)
    · intro s hs
      exact LandauLogZetaObstruction.H_zeta_log_exp_eq hs

/-- Non-RH `π-li` oscillation from the punctured hard-range core. -/
theorem pi_li_omega_lll_of_not_RH_from_punctured_core
    (hCore : PiAtomHardCasePuncturedCore)
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  exact Aristotle.Standalone.LandauPiPuncturedExtensionChain.pi_li_omega_lll_of_not_RH_of_punctured_extension
    (piIntegralHypPunctured_of_punctured_core hCore) hRH

end Aristotle.Standalone.PiAtomHardCaseConstructiveCore
