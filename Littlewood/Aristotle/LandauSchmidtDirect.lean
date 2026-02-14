/-
Direct proof infrastructure for the Landau-Schmidt oscillation theorem.

Under ¬RH, there exists a nontrivial zero ρ₀ with Re(ρ₀) > 1/2.
By the functional equation symmetry (zero_one_sub_zero), we can always
find such a zero. The Landau non-negative Dirichlet integral argument
then gives ψ(x) - x = Ω±(x^α) for any α ∈ (1/2, Re(ρ₀)).

## Main Results

* `exists_zero_re_gt_half_of_not_RH` : ¬RH → ∃ zero with Re > 1/2
* `landau_dirichlet_extension` : One-sided bound → ζ'/ζ has analytic extension
    PROVED from `landau_nonneg_integral` (sorry) + h(s) trick + identity principle
* `psi_omega_rpw_of_zero_above` : Zero with Re > α → ψ-x = Ω±(x^α) (PROVED)
* `psi_omega_lll_of_not_RH` : ¬RH → ψ-x = Ω±(√x · lll x) (PROVED)
* `pi_omega_rpow_of_zero_above` : Zero with Re > α → π-li = Ω±(x^α) (PROVED)
* `pi_li_omega_lll_of_not_RH` : ¬RH → π-li = Ω±(√x/log x · lll x) (PROVED)

## Architecture

The Landau contradiction is cleanly decomposed:
  1. `landau_nonneg_integral` (SORRY): Pure analysis — non-negative Dirichlet
     integral converges and gives analytic G on {Re > α} with explicit formula
     on {Re > 1}.
  2. `extract_analytic_extension` (PROVED): h(s) trick — from G, construct F
     analytic at s₀ agreeing with ζ'/ζ in punctured neighborhood. Uses identity
     principle on preconnected {Re > α} \ {1} and isolated zeros of ζ.
  3. `landau_dirichlet_extension` (PROVED): Combines 1 and 2.
  4. `zeta_logDeriv_no_analytic_extension` (PROVED, ZetaLogDerivNonAnalytic.lean):
     Any analytic F agreeing with ζ'/ζ near a zero → False.
  5. The contradiction follows in 2 lines (steps 3+4).

## Mathematical References

* Landau, "Über einen Satz von Tschebyschef" (1905)
* Schmidt, "Über die Anzahl der Primzahlen unter gegebener Grenze" (1903)
* Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1
-/

import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.Basic.OmegaNotation
import Littlewood.Basic.LogarithmicIntegral
import Littlewood.Aristotle.ZetaLogDerivNonAnalytic
import Littlewood.Aristotle.HalfPlaneConnected

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.LandauSchmidtDirect

open Filter Topology Asymptotics Complex Set
open ZetaZeros GrowthDomination

/-- Under ¬RH, there exists a nontrivial zero with Re > 1/2.
Proof: ¬RH gives ρ with Re(ρ) ≠ 1/2. If Re(ρ) > 1/2, done.
If Re(ρ) < 1/2, then 1-ρ is also a zero (functional equation)
and Re(1-ρ) = 1 - Re(ρ) > 1/2. -/
theorem exists_zero_re_gt_half_of_not_RH
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    ∃ ρ ∈ zetaNontrivialZeros, (1 : ℝ) / 2 < ρ.re := by
  unfold ZetaZeros.RiemannHypothesis at hRH
  push_neg at hRH
  obtain ⟨ρ, hρ, hne⟩ := hRH
  by_cases h : (1 : ℝ) / 2 < ρ.re
  · exact ⟨ρ, hρ, h⟩
  · push_neg at h
    have hlt : ρ.re < 1 / 2 := lt_of_le_of_ne h hne
    refine ⟨1 - ρ, zero_one_sub_zero hρ, ?_⟩
    simp only [Complex.sub_re, Complex.one_re]
    linarith

/-! ## Landau non-negative Dirichlet integral -/

/-- **Landau's non-negative Dirichlet integral theorem**: Under a one-sided bound
σ*(ψ(x)-x) ≤ C*x^α, the non-negative function g(t) = C*t^α + σ*(t - ψ(t)) ≥ 0
has convergent Dirichlet integral G(s) = s·∫₁^∞ g(t)·t^{-(s+1)} dt for Re(s) > α,
and G is analytic there.

On {Re > 1}, G satisfies:
  G(s) = s*C/(s-α) + σ*s/(s-1) + σ*ζ'/ζ(s)

SORRY: Requires non-negative Dirichlet integral convergence (Landau 1905),
analyticity of parametric integrals, and evaluation of closed-form integrals.
The identity principle and pole obstruction arguments are PROVED separately. -/
private theorem landau_nonneg_integral
    (α : ℝ) (hα : 1 / 2 < α) (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_bound : ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
              (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s) := by
  sorry

/-! ## The h(s) trick: identity principle + isolated zeros -/

/-- **h(s) trick**: From the Dirichlet integral function G, construct an analytic
function F at s₀ that agrees with ζ'/ζ in a punctured neighborhood.

**Construction**: F(s) = σ·G(s) - σ·s·C/(s-α) - s/(s-1).
Since σ² = 1, F = ζ'/ζ on {Re > 1} (algebraic simplification).
Setting h = F·ζ - ζ', we get h analytic on {Re > α}\{1} with h = 0 on {Re > 1}.
By the identity principle (preconnected domain), h = 0 everywhere.
Since ζ has isolated zeros, F = ζ'/ζ in a punctured neighborhood of s₀. -/
private theorem extract_analytic_extension
    (α : ℝ) (hα : 1 / 2 < α)
    (G : ℂ → ℂ) (hG_anal : AnalyticOnNhd ℂ G {s : ℂ | α < s.re})
    (σ : ℝ) (hσ_cases : σ = 1 ∨ σ = -1) (C : ℝ)
    (hG_eq : ∀ s : ℂ, 1 < s.re →
      G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
            (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s))
    (s₀ : ℂ) (hs₀_re : α < s₀.re) (hs₀_ne : s₀ ≠ 1) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, F s = deriv riemannZeta s / riemannZeta s := by
  -- σ² = 1
  have hσ_sq : (↑σ : ℂ) * (↑σ : ℂ) = 1 := by
    rcases hσ_cases with rfl | rfl <;> push_cast <;> norm_num
  -- Helper: s - ↑α ≠ 0 when α < s.re
  have h_ne_α : ∀ s : ℂ, α < s.re → s - (↑α : ℂ) ≠ 0 := by
    intro s hs h
    have : s.re = α := by
      have := congr_arg Complex.re h; simp at this; linarith
    linarith
  -- Define F(s) = σ·G(s) - σ·s·C/(s-α) - s/(s-1)
  set F : ℂ → ℂ := fun s =>
    (↑σ : ℂ) * G s - (↑σ : ℂ) * (s * (↑C : ℂ) / (s - (↑α : ℂ))) - s / (s - 1) with hF_def
  -- Helper: F is AnalyticAt at any point of {Re > α} \ {1}
  have hF_analyticAt : ∀ s : ℂ, α < s.re → s ≠ 1 → AnalyticAt ℂ F s := by
    intro s hs_re hs_ne
    exact ((analyticAt_const.mul (hG_anal s hs_re)).sub
      (analyticAt_const.mul ((analyticAt_id.mul analyticAt_const).div
        (analyticAt_id.sub analyticAt_const) (h_ne_α s hs_re)))).sub
      (analyticAt_id.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs_ne))
  refine ⟨F, hF_analyticAt s₀ hs₀_re hs₀_ne, ?_⟩
  -- Domain Ω = {Re > α} \ {1}: preconnected and open
  set Ω := {s : ℂ | α < s.re} \ {(1 : ℂ)} with hΩ_def
  have hΩ_pc := HalfPlaneConnected.halfPlane_diff_singleton_isPreconnected α 1
  have hΩ_open : IsOpen Ω :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  -- Base point z₀ with Re > α and Re > 1
  set z₀ : ℂ := ⟨α + 1, 0⟩ with hz₀_def
  have hz₀_re_α : α < z₀.re := by simp [z₀]
  have hz₀_re_1 : 1 < z₀.re := by simp [z₀]; linarith
  have hz₀_ne : z₀ ≠ 1 := by
    intro h; have := congr_arg Complex.re h; simp [z₀] at this; linarith
  have hz₀_mem : z₀ ∈ Ω :=
    ⟨hz₀_re_α, fun h => hz₀_ne (mem_singleton_iff.mp h)⟩
  -- Step 1: F = ζ'/ζ when both Re > α and Re > 1
  have hF_eq_zeta : ∀ s : ℂ, α < s.re → 1 < s.re →
      F s = deriv riemannZeta s / riemannZeta s := by
    intro s hsα hs1
    simp only [hF_def]
    rw [hG_eq s hs1]
    -- Abbreviate for ring manipulation
    set A := s * (↑C : ℂ) / (s - (↑α : ℂ))
    set B := s / (s - 1)
    set D := deriv riemannZeta s / riemannZeta s
    -- Goal: ↑σ * (A + ↑σ * B + ↑σ * D) - ↑σ * A - B = D
    have : ↑σ * (A + ↑σ * B + ↑σ * D) - ↑σ * A - B =
        ↑σ * ↑σ * B + ↑σ * ↑σ * D - B := by ring
    rw [this, hσ_sq, one_mul, one_mul]; ring
  -- Step 2: h(s) = F(s)·ζ(s) - ζ'(s) is AnalyticOnNhd on Ω
  set h : ℂ → ℂ := fun s => F s * riemannZeta s - deriv riemannZeta s with hh_def
  have hh_anal : AnalyticOnNhd ℂ h Ω := by
    intro s hs
    have hs_ne : s ≠ 1 := fun heq => hs.2 (mem_singleton_iff.mpr heq)
    have hζ := ZetaLogDerivPole.zeta_analyticAt s hs_ne
    exact (hF_analyticAt s hs.1 hs_ne).mul hζ |>.sub hζ.deriv
  -- Step 3: h = 0 near z₀ (since h = 0 on {Re > α} ∩ {Re > 1})
  have hh_ev : h =ᶠ[𝓝 z₀] 0 := by
    have ho1 := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show z₀ ∈ {s : ℂ | (1 : ℝ) < s.re} from hz₀_re_1)
    have ho2 := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show z₀ ∈ {s : ℂ | α < s.re} from hz₀_re_α)
    filter_upwards [ho1, ho2] with s hs1 hsα
    simp only [hh_def, Pi.zero_apply]
    have h_zeta_ne := riemannZeta_ne_zero_of_one_le_re (show (1 : ℝ) ≤ s.re by linarith)
    rw [hF_eq_zeta s hsα hs1, div_mul_cancel₀ _ h_zeta_ne, sub_self]
  -- Step 4: Identity principle: h = 0 on all of Ω
  have hh_eq_zero := hh_anal.eqOn_of_preconnected_of_eventuallyEq
    (fun _ _ => analyticAt_const) hΩ_pc hz₀_mem hh_ev
  -- Step 5: Extract F = ζ'/ζ from h = 0 and isolated zeros of ζ
  have hs₀_mem : s₀ ∈ Ω :=
    ⟨hs₀_re, fun h => hs₀_ne (mem_singleton_iff.mp h)⟩
  -- ζ has isolated zeros: eventually ζ(s) ≠ 0 in punctured nhd of s₀
  have h_zeta_ev : ∀ᶠ s in 𝓝[≠] s₀, riemannZeta s ≠ 0 := by
    rcases eq_or_ne (riemannZeta s₀) 0 with hz | hnz
    · exact ZetaLogDerivPole.zeta_eventually_ne_zero_of_zero s₀ hs₀_ne hz
    · exact nhdsWithin_le_nhds
        ((ZetaLogDerivPole.zeta_analyticAt s₀ hs₀_ne).continuousAt.preimage_mem_nhds
          (isOpen_ne.mem_nhds hnz))
  -- Combine: in punctured nhd, ζ(s) ≠ 0 and s ∈ Ω, giving F = ζ'/ζ
  filter_upwards [h_zeta_ev,
    nhdsWithin_le_nhds (hΩ_open.mem_nhds hs₀_mem)] with s h_ne h_Ω
  -- h(s) = 0 from identity principle
  have h_zero := hh_eq_zero h_Ω
  -- h(s) = F(s)·ζ(s) - ζ'(s) = 0, so F(s)·ζ(s) = ζ'(s)
  simp only [hh_def] at h_zero
  exact (eq_div_iff h_ne).mpr (sub_eq_zero.mp h_zero)

/-! ## Landau Dirichlet integral extension — PROVED from sorry + h(s) trick -/

/-- **Landau's Dirichlet integral extension**: Under a one-sided bound on ψ,
there exists an analytic function at any point s₀ in the extended half-plane
that agrees with ζ'/ζ in a punctured neighborhood.

PROVED from `landau_nonneg_integral` (sorry, pure analysis) combined with
`extract_analytic_extension` (proved, h(s) trick + identity principle). -/
private theorem landau_dirichlet_extension
    (α : ℝ) (hα : 1 / 2 < α) (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (_hσ : σ = 1 ∨ σ = -1)
    (h_bound : ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α)
    (s₀ : ℂ) (hs₀_re : α < s₀.re) (hs₀_ne : s₀ ≠ 1) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, F s = deriv riemannZeta s / riemannZeta s := by
  obtain ⟨G, hG_anal, hG_eq⟩ := landau_nonneg_integral α hα C hC σ _hσ h_bound
  exact extract_analytic_extension α hα G hG_anal σ _hσ C hG_eq s₀ hs₀_re hs₀_ne

/-! ## Landau contradictions — PROVED from the extension + pole obstruction -/

/-- **Landau upper contradiction**: If there exists a zero with Re > α and
ψ(x) - x is eventually bounded above by C·x^α, we get a contradiction.

PROVED: 2-line derivation from `landau_dirichlet_extension` (sorry, analytical core)
and `zeta_logDeriv_no_analytic_extension` (proved, pole obstruction). -/
private theorem landau_upper_contradiction
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ zetaNontrivialZeros)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_re : α < ρ₀.re)
    (C : ℝ) (hC : 0 < C)
    (h_bound : ∀ᶠ x in atTop, chebyshevPsi x - x ≤ C * x ^ α) :
    False := by
  -- Convert the bound to signed form (σ = 1)
  have h_signed : ∀ᶠ x in atTop, 1 * (chebyshevPsi x - x) ≤ C * x ^ α := by
    simpa only [one_mul] using h_bound
  -- Get the analytic extension at ρ₀
  obtain ⟨F, hF_anal, hF_eq⟩ := landau_dirichlet_extension α hα_half C hC 1
    (Or.inl rfl) h_signed ρ₀ hα_re
    (ZetaLogDerivNonAnalytic.nontrivial_zero_ne_one ρ₀ hρ₀)
  -- F is analytic at ρ₀ but agrees with ζ'/ζ which has a pole — contradiction
  exact ZetaLogDerivNonAnalytic.zeta_logDeriv_no_analytic_extension ρ₀ hρ₀ F hF_anal hF_eq

/-- **Landau lower contradiction**: If there exists a zero with Re > α and
ψ(x) - x is eventually bounded below by -C·x^α, we get a contradiction.

PROVED: Same structure as the upper case with σ = -1. -/
private theorem landau_lower_contradiction
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ zetaNontrivialZeros)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_re : α < ρ₀.re)
    (C : ℝ) (hC : 0 < C)
    (h_bound : ∀ᶠ x in atTop, -(C * x ^ α) ≤ chebyshevPsi x - x) :
    False := by
  -- Convert: -(C·x^α) ≤ ψ-x means (-1)·(ψ-x) ≤ C·x^α
  have h_signed : ∀ᶠ x in atTop, (-1) * (chebyshevPsi x - x) ≤ C * x ^ α := by
    filter_upwards [h_bound] with x hx
    linarith
  -- Get the analytic extension at ρ₀
  obtain ⟨F, hF_anal, hF_eq⟩ := landau_dirichlet_extension α hα_half C hC (-1)
    (Or.inr rfl) h_signed ρ₀ hα_re
    (ZetaLogDerivNonAnalytic.nontrivial_zero_ne_one ρ₀ hρ₀)
  -- F is analytic at ρ₀ but agrees with ζ'/ζ which has a pole — contradiction
  exact ZetaLogDerivNonAnalytic.zeta_logDeriv_no_analytic_extension ρ₀ hρ₀ F hF_anal hF_eq

/-! ## Schmidt oscillation — PROVED from Landau contradictions -/

/-- Schmidt's oscillation theorem (for ψ): If there exists a nontrivial zero ρ₀
with Re(ρ₀) > α > 1/2, then ψ(x) - x = Ω±(x^α).
PROVED from the two Landau contradictions above. -/
theorem psi_omega_rpow_of_zero_above
    (α : ℝ) (hα : 1 / 2 < α)
    (hzero : ∃ ρ ∈ zetaNontrivialZeros, α < ρ.re) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => x ^ α] := by
  obtain ⟨ρ₀, hρ₀, hα_re⟩ := hzero
  constructor
  -- Ω₊: ψ(x) - x ≥ c · x^α infinitely often
  · by_contra h_not
    have h_not_freq : ¬ ∃ᶠ x in atTop, chebyshevPsi x - x ≥ 1 * x ^ α := by
      intro hfreq; exact h_not ⟨1, one_pos, hfreq⟩
    have h_upper : ∀ᶠ x in atTop, chebyshevPsi x - x ≤ 1 * x ^ α :=
      (Filter.not_frequently.mp h_not_freq).mono fun _ hx => le_of_lt (not_le.mp hx)
    exact landau_upper_contradiction ρ₀ hρ₀ α hα hα_re 1 one_pos h_upper
  -- Ω₋: ψ(x) - x ≤ -c · x^α infinitely often
  · by_contra h_not
    have h_not_freq : ¬ ∃ᶠ x in atTop, chebyshevPsi x - x ≤ -(1 * x ^ α) := by
      intro hfreq; exact h_not ⟨1, one_pos, by simpa [neg_mul] using hfreq⟩
    have h_lower : ∀ᶠ x in atTop, -(1 * x ^ α) ≤ chebyshevPsi x - x :=
      (Filter.not_frequently.mp h_not_freq).mono fun _ hx => le_of_lt (not_le.mp hx)
    exact landau_lower_contradiction ρ₀ hρ₀ α hα hα_re 1 one_pos h_lower

/-- Under ¬RH, ψ(x) - x = Ω±(√x · lll x).
PROVED from Schmidt oscillation + growth domination. -/
theorem psi_omega_lll_of_not_RH (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] := by
  obtain ⟨ρ₀, hρ₀, hρ₀_re⟩ := exists_zero_re_gt_half_of_not_RH hRH
  -- Choose α = (1/2 + Re(ρ₀))/2, so 1/2 < α < Re(ρ₀)
  set α := (1 / 2 + ρ₀.re) / 2 with hα_def
  have hα_half : 1 / 2 < α := by rw [hα_def]; linarith
  have hα_re : α < ρ₀.re := by rw [hα_def]; linarith
  -- ψ-x = Ω±(x^α) by Schmidt
  have hΩ := psi_omega_rpow_of_zero_above α hα_half ⟨ρ₀, hρ₀, hα_re⟩
  -- √x · lll x ≤ x^α eventually (growth domination)
  have h_dom := sqrt_mul_lll_le_rpow α hα_half
  -- √x · lll x ≥ 0 eventually
  have h_nn := sqrt_mul_lll_eventually_nonneg
  -- Transfer: Ω±(x^α) → Ω±(√x · lll x)
  exact hΩ.of_eventually_ge h_dom h_nn

/-! ## π-li Landau argument — log ζ obstruction -/

/-- **Non-negative Dirichlet integral for π**: Under a one-sided bound
σ*(π(x)-li(x)) ≤ C*x^α, there exists H analytic on {Re > α} with
exp(H(s)) = ζ(s) for Re(s) > 1.

SORRY: Requires Dirichlet integral convergence for the prime counting function,
the relation log ζ(s) = ∑ Λ(n)/(n^s·log n) for Re(s) > 1, and construction
of an analytic branch of log ζ from the convergent integral. -/
private theorem pi_landau_log_extension
    (α : ℝ) (hα : 1 / 2 < α) (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_bound : ∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s := by
  sorry

/-- **π-li Landau contradiction**: Under a one-sided bound on π(x)-li(x),
any nontrivial zero with Re > α gives a contradiction.

The proof uses the identity principle: exp(H) and ζ are both analytic on
{Re > α}\{1}, agree on {Re > 1}, hence agree on {Re > α}\{1}.
At a zero ρ₀: exp(H(ρ₀)) = ζ(ρ₀) = 0, contradicting exp_ne_zero. -/
private theorem pi_landau_contradiction
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ zetaNontrivialZeros)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_re : α < ρ₀.re)
    (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_bound : ∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) :
    False := by
  obtain ⟨H, hH_anal, hH_eq⟩ := pi_landau_log_extension α hα_half C hC σ hσ h_bound
  have hρ₀_ne := ZetaLogDerivNonAnalytic.nontrivial_zero_ne_one ρ₀ hρ₀
  have hρ₀_zero := ZetaLogDerivNonAnalytic.nontrivial_zero_vanishes ρ₀ hρ₀
  -- Domain Ω = {Re > α} \ {1}
  set Ω := {s : ℂ | α < s.re} \ {(1 : ℂ)} with hΩ_def
  -- exp ∘ H is analytic on Ω (restriction of analytic on {Re > α})
  have hExpH_anal : AnalyticOnNhd ℂ (exp ∘ H) Ω :=
    fun s hs => analyticAt_cexp.comp (hH_anal s hs.1)
  -- ζ is analytic on Ω
  have hζ_anal : AnalyticOnNhd ℂ riemannZeta Ω :=
    fun s hs => ZetaLogDerivPole.zeta_analyticAt s
      (fun h => hs.2 (mem_singleton_iff.mpr h))
  -- Ω is preconnected
  have hΩ_pc := HalfPlaneConnected.halfPlane_diff_singleton_isPreconnected α 1
  -- Base point z₀ ∈ Ω with Re > 1
  set z₀ : ℂ := ⟨α + 1, 0⟩
  have hz₀_re_1 : 1 < z₀.re := by simp [z₀]; linarith
  have hz₀_ne : z₀ ≠ 1 := by
    intro h; have := congr_arg re h; simp [z₀] at this; linarith
  have hz₀_mem : z₀ ∈ Ω :=
    ⟨by simp [z₀], fun h => hz₀_ne (mem_singleton_iff.mp h)⟩
  -- exp(H) = ζ near z₀
  have h_ev : (exp ∘ H) =ᶠ[𝓝 z₀] riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz₀_re_1]
      with s hs
    exact hH_eq s hs
  -- Identity principle: exp(H) = ζ on Ω
  have h_eqOn := hExpH_anal.eqOn_of_preconnected_of_eventuallyEq
    hζ_anal hΩ_pc hz₀_mem h_ev
  -- At ρ₀ ∈ Ω: exp(H(ρ₀)) = ζ(ρ₀) = 0 contradicts exp_ne_zero
  have hρ₀_mem : ρ₀ ∈ Ω :=
    ⟨show α < ρ₀.re by linarith, fun h => hρ₀_ne (mem_singleton_iff.mp h)⟩
  exact absurd ((h_eqOn hρ₀_mem).trans hρ₀_zero) (exp_ne_zero (H ρ₀))

/-! ## π-li Schmidt oscillation — PROVED from π-li Landau contradictions -/

/-- Schmidt's oscillation theorem (for π-li): If there exists a nontrivial zero ρ₀
with Re(ρ₀) > α > 1/2, then π(x) - li(x) = Ω±(x^α).
PROVED from the π-li Landau contradiction above. -/
theorem pi_omega_rpow_of_zero_above
    (α : ℝ) (hα : 1 / 2 < α)
    (hzero : ∃ ρ ∈ zetaNontrivialZeros, α < ρ.re) :
    (fun x => (↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) =Ω±[fun x => x ^ α] := by
  obtain ⟨ρ₀, hρ₀, hα_re⟩ := hzero
  constructor
  -- Ω₊: π(x)-li(x) ≥ c · x^α infinitely often
  · by_contra h_not
    have h_not_freq : ¬ ∃ᶠ x in atTop,
        (↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≥ 1 * x ^ α := by
      intro hfreq; exact h_not ⟨1, one_pos, hfreq⟩
    have h_upper : ∀ᶠ x in atTop,
        (↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≤ 1 * x ^ α :=
      (Filter.not_frequently.mp h_not_freq).mono fun _ hx => le_of_lt (not_le.mp hx)
    exact pi_landau_contradiction ρ₀ hρ₀ α hα hα_re 1 one_pos 1 (Or.inl rfl)
      (by simpa only [one_mul] using h_upper)
  -- Ω₋: π(x)-li(x) ≤ -c · x^α infinitely often
  · by_contra h_not
    have h_not_freq : ¬ ∃ᶠ x in atTop,
        (↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≤ -(1 * x ^ α) := by
      intro hfreq; exact h_not ⟨1, one_pos, by simpa [neg_mul] using hfreq⟩
    have h_lower : ∀ᶠ x in atTop,
        -(1 * x ^ α) ≤ (↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x :=
      (Filter.not_frequently.mp h_not_freq).mono fun _ hx => le_of_lt (not_le.mp hx)
    exact pi_landau_contradiction ρ₀ hρ₀ α hα hα_re 1 one_pos (-1) (Or.inr rfl)
      (by filter_upwards [h_lower] with x hx; linarith)

/-- **π-li Landau oscillation under ¬RH**: π(x) - li(x) = Ω±(√x/log x · lll x).

PROVED from Schmidt oscillation + growth domination.
Uses the independent Landau argument for π via log ζ (not derivable from ψ
oscillation by partial summation). -/
theorem pi_li_omega_lll_of_not_RH (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  obtain ⟨ρ₀, hρ₀, hρ₀_re⟩ := exists_zero_re_gt_half_of_not_RH hRH
  set α := (1 / 2 + ρ₀.re) / 2
  have hα_half : 1 / 2 < α := by simp [α]; linarith
  have hα_re : α < ρ₀.re := by simp [α]; linarith
  have hΩ := pi_omega_rpow_of_zero_above α hα_half ⟨ρ₀, hρ₀, hα_re⟩
  exact hΩ.of_eventually_ge (sqrt_div_log_mul_lll_le_rpow α hα_half)
    sqrt_div_log_mul_lll_eventually_nonneg

end Aristotle.LandauSchmidtDirect
