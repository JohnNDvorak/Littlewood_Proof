/-
# AnalyticOrderAtConj — analytic order of ζ is conjugation-invariant

Proves:
`analyticOrderAt riemannZeta (conj ρ) = analyticOrderAt riemannZeta ρ`
for any `ρ` with `ρ ≠ 1` and `conj ρ ≠ 1`.
-/

import Littlewood.ZetaZeros.ZeroCountingFunction

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Filter Topology

namespace Aristotle.AnalyticOrderAtConj

open ZetaZeros

/-- ζ is analytic at any `s ≠ 1`. -/
private lemma zeta_analyticAt (s : ℂ) (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt
    (fun z (hz : z ∈ {w : ℂ | w ≠ 1}) => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_ne.mem_nhds hs)

/-- ζ is not identically zero near any `s ≠ 1`. -/
private lemma zeta_not_eventually_zero (s : ℂ) (hs : s ≠ 1) :
    ¬(∀ᶠ z in 𝓝 s, riemannZeta z = 0) := by
  intro h_zero
  have h_aon : AnalyticOnNhd ℂ riemannZeta {w : ℂ | w ≠ 1} :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      isOpen_ne
  have h_conn : IsPreconnected {w : ℂ | w ≠ 1} := by
    have : IsConnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
      isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)
    simpa using this.isPreconnected
  have h2_ne : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re)
  have h2_mem : (2 : ℂ) ∈ {w : ℂ | w ≠ 1} := by norm_num
  exact h2_ne (h_aon.eqOn_zero_of_preconnected_of_eventuallyEq_zero h_conn hs h_zero h2_mem)

/-- The analytic order of ζ at any `s ≠ 1` is finite. -/
private lemma zeta_analyticOrder_ne_top (s : ℂ) (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ :=
  fun h_top => zeta_not_eventually_zero s hs (analyticOrderAt_eq_top.mp h_top)

/-- Conjugation of zeta: `g(w) = conj (ζ (conj w))` agrees with ζ near `ρ`. -/
private lemma riemannZeta_eq_conj_zeta_conj_near
    (ρ : ℂ) (hρ : ρ ≠ 1) (hρc : starRingEnd ℂ ρ ≠ 1) :
    (fun w => starRingEnd ℂ (riemannZeta (starRingEnd ℂ w))) =ᶠ[𝓝 ρ] riemannZeta := by
  have h_open : IsOpen {w : ℂ | w ≠ 1 ∧ starRingEnd ℂ w ≠ 1} :=
    IsOpen.inter isOpen_ne (isOpen_ne.preimage continuous_star)
  refine eventually_of_mem (h_open.mem_nhds ⟨hρ, hρc⟩) ?_
  intro w ⟨hw, _⟩
  show starRingEnd ℂ (riemannZeta (starRingEnd ℂ w)) = riemannZeta w
  rw [riemannZeta_conj hw, starRingEnd_self_apply]

/-- `conj ∘ h ∘ conj` is analytic at `ρ` when `h` is analytic at `conj ρ`. -/
private lemma conj_comp_analyticAt_conj (h : ℂ → ℂ) (ρ : ℂ)
    (hh_anal : AnalyticAt ℂ h (starRingEnd ℂ ρ)) :
    AnalyticAt ℂ (fun w => starRingEnd ℂ (h (starRingEnd ℂ w))) ρ := by
  have hh_diff_ev : ∀ᶠ z in 𝓝 (starRingEnd ℂ ρ), DifferentiableAt ℂ h z :=
    analyticAt_iff_eventually_differentiableAt.mp hh_anal
  have hk_diff_ev : ∀ᶠ w in 𝓝 ρ,
      DifferentiableAt ℂ (fun w => starRingEnd ℂ (h (starRingEnd ℂ w))) w := by
    have h_pullback : ∀ᶠ w in 𝓝 ρ, DifferentiableAt ℂ h (starRingEnd ℂ w) :=
      continuous_star.continuousAt.eventually hh_diff_ev
    filter_upwards [h_pullback] with w hw
    have := DifferentiableAt.conj_conj hw
    simp only [starRingEnd_self_apply] at this
    exact this
  exact analyticAt_iff_eventually_differentiableAt.mpr hk_diff_ev

/-- The analytic order of ζ at `conj ρ` equals the analytic order at `ρ`. -/
theorem analyticOrderAt_riemannZeta_conj
    (ρ : ℂ) (hρ : ρ ≠ 1) (hρc : starRingEnd ℂ ρ ≠ 1) :
    analyticOrderAt riemannZeta (starRingEnd ℂ ρ) = analyticOrderAt riemannZeta ρ := by
  set g : ℂ → ℂ := fun w => starRingEnd ℂ (riemannZeta (starRingEnd ℂ w)) with hg_def
  have hg_eq : g =ᶠ[𝓝 ρ] riemannZeta := riemannZeta_eq_conj_zeta_conj_near ρ hρ hρc
  have hord_g_eq_zeta : analyticOrderAt g ρ = analyticOrderAt riemannZeta ρ :=
    analyticOrderAt_congr hg_eq
  suffices hsuff : analyticOrderAt riemannZeta (starRingEnd ℂ ρ) = analyticOrderAt g ρ by
    rw [hsuff, hord_g_eq_zeta]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (zeta_analyticOrder_ne_top (starRingEnd ℂ ρ) hρc)
  rw [← hn]
  symm
  have hζ_anal_conj := zeta_analyticAt (starRingEnd ℂ ρ) hρc
  obtain ⟨h, hh_anal, hh_ne, hh_eq⟩ := hζ_anal_conj.analyticOrderAt_eq_natCast.mp hn.symm
  have hg_anal : AnalyticAt ℂ g ρ := (zeta_analyticAt ρ hρ).congr hg_eq.symm
  rw [hg_anal.analyticOrderAt_eq_natCast]
  refine ⟨fun w => starRingEnd ℂ (h (starRingEnd ℂ w)), ?_, ?_, ?_⟩
  · exact conj_comp_analyticAt_conj h ρ hh_anal
  · show starRingEnd ℂ (h (starRingEnd ℂ ρ)) ≠ 0
    simp only [ne_eq, map_eq_zero]
    exact hh_ne
  · have h_preimage : ∀ᶠ w in 𝓝 ρ, riemannZeta (starRingEnd ℂ w) =
        (starRingEnd ℂ w - starRingEnd ℂ ρ) ^ n • h (starRingEnd ℂ w) :=
      continuous_star.continuousAt.eventually hh_eq
    filter_upwards [h_preimage] with w hw
    show starRingEnd ℂ (riemannZeta (starRingEnd ℂ w)) =
      (w - ρ) ^ n • starRingEnd ℂ (h (starRingEnd ℂ w))
    rw [hw]
    simp only [smul_eq_mul, map_mul, map_pow, map_sub, starRingEnd_self_apply]

end Aristotle.AnalyticOrderAtConj
