/-
Infrastructure for the Landau oscillation argument: logarithmic derivative
of ζ has a simple pole at nontrivial zeros.

If ζ(ρ₀) = 0 and ρ₀ ≠ 1, then deriv(ζ)/ζ has a simple pole at ρ₀.
In particular, ‖ζ'/ζ(s)‖ → ∞ as s → ρ₀.

This is a key building block for the Landau argument: if the integral
F(s) = s∫(ψ(t)-t)/t^{s+1} defines an analytic function, and
-ζ'/ζ(s) = F(s) + s/(s-1) on Re(s) > 1, then by analytic continuation
-ζ'/ζ is analytic in Re(s) > α. But -ζ'/ζ has a pole at any zero ρ₀ with
Re(ρ₀) > α — contradiction.

## Main Results

* `zeta_analyticAt` : ζ is analytic at s ≠ 1
* `zeta_not_eventually_zero` : ζ is not identically zero near any s ≠ 1
* `zeta_analyticOrder_ne_top` : order of ζ at a zero is finite
* `zeta_logDeriv_meromorphicAt` : ζ'/ζ is meromorphic at zeros
* `zeta_logDeriv_tendsto_cobounded` : ‖ζ'/ζ‖ → ∞ at nontrivial zeros

SORRY COUNT: 0

REFERENCES:
  - Standard complex analysis (Ahlfors, Conway)
  - Titchmarsh, "The Theory of the Riemann Zeta-Function", §3

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.ZetaLogDerivPole

open Complex Filter Topology

/-! ## Analyticity of ζ -/

/-- riemannZeta is analytic at any s ≠ 1.
Proved via DifferentiableOn on the open set {s | s ≠ 1}. -/
theorem zeta_analyticAt (s : ℂ) (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt
    (fun z (hz : z ∈ {w : ℂ | w ≠ 1}) =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_ne.mem_nhds hs)

/-- riemannZeta is meromorphic at any s ≠ 1 (trivially, from analyticity). -/
theorem zeta_meromorphicAt (s : ℂ) (hs : s ≠ 1) : MeromorphicAt riemannZeta s :=
  (zeta_analyticAt s hs).meromorphicAt

/-! ## ζ is not identically zero

This uses the identity principle: ζ is analytic on the connected set ℂ\{1},
and ζ(2) = π²/6 ≠ 0. Therefore ζ cannot vanish on any open subset of ℂ\{1}. -/

/-- ζ is not identically zero near any point s ≠ 1.
Proved via the identity principle on the connected set ℂ\{1}. -/
theorem zeta_not_eventually_zero (s : ℂ) (hs : s ≠ 1) :
    ¬(∀ᶠ z in 𝓝 s, riemannZeta z = 0) := by
  intro h_zero
  -- ζ is analytic on ℂ \ {1}
  have h_anal : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    fun z hz => zeta_analyticAt z hz
  -- 0 is analytic on ℂ \ {1}
  have h_zero_anal : AnalyticOnNhd ℂ (0 : ℂ → ℂ) ({1}ᶜ : Set ℂ) :=
    fun _ _ => analyticAt_const
  -- ℂ \ {1} is preconnected (dim_ℝ(ℂ) = 2 > 1)
  have h_conn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  -- s ∈ ℂ \ {1}
  have hs_mem : s ∈ ({1}ᶜ : Set ℂ) := hs
  -- By identity principle, ζ = 0 on all of ℂ \ {1}
  have h_eq_on := h_anal.eqOn_of_preconnected_of_eventuallyEq h_zero_anal h_conn hs_mem h_zero
  -- Evaluate at 2: ζ(2) = 0
  have h2_mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  -- But ζ(2) ≠ 0 (Re(2) = 2 ≥ 1)
  exact absurd (h_eq_on h2_mem) (riemannZeta_ne_zero_of_one_le_re (by norm_num : (1:ℝ) ≤ (2:ℂ).re))

/-- At a zero, riemannZeta is not identically zero in a punctured neighborhood.
This is the "isolated zeros" conclusion. -/
theorem zeta_eventually_ne_zero_of_zero (ρ₀ : ℂ) (hne : ρ₀ ≠ 1) (hz : riemannZeta ρ₀ = 0) :
    ∀ᶠ z in 𝓝[≠] ρ₀, riemannZeta z ≠ 0 := by
  rcases (zeta_analyticAt ρ₀ hne).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd h (zeta_not_eventually_zero ρ₀ hne)
  · exact h

/-! ## Analytic order at zeros -/

/-- The analytic order of ζ at any s ≠ 1 is finite (not ⊤). -/
theorem zeta_analyticOrder_ne_top (s : ℂ) (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  intro h_top
  exact zeta_not_eventually_zero s hs (analyticOrderAt_eq_top.mp h_top)

/-- The analytic order of ζ at a zero ρ₀ is positive (at least 1). -/
theorem zeta_analyticOrder_pos (ρ₀ : ℂ) (hne : ρ₀ ≠ 1) (hz : riemannZeta ρ₀ = 0) :
    0 < analyticOrderAt riemannZeta ρ₀ := by
  rw [pos_iff_ne_zero]
  exact ((zeta_analyticAt ρ₀ hne).analyticOrderAt_ne_zero).mpr hz

/-! ## Meromorphic order of ζ'/ζ at zeros -/

/-- The logarithmic derivative ζ'/ζ is meromorphic at any s ≠ 1. -/
theorem zeta_logDeriv_meromorphicAt (ρ₀ : ℂ) (hne : ρ₀ ≠ 1) :
    MeromorphicAt (fun s => deriv riemannZeta s / riemannZeta s) ρ₀ :=
  MeromorphicAt.div
    ((zeta_analyticAt ρ₀ hne).meromorphicAt.deriv)
    (zeta_meromorphicAt ρ₀ hne)

/-- The meromorphic order of ζ'/ζ at a zero ρ₀ is negative (pole).

The order is -1 (simple pole), since if ζ has a zero of order m ≥ 1 at ρ₀,
then ζ' has a zero of order m-1, so ζ'/ζ has order (m-1) - m = -1. -/
theorem zeta_logDeriv_meromorphicOrder_neg (ρ₀ : ℂ) (hne : ρ₀ ≠ 1) (hz : riemannZeta ρ₀ = 0) :
    meromorphicOrderAt (fun s => deriv riemannZeta s / riemannZeta s) ρ₀ < 0 := by
  have h_anal := zeta_analyticAt ρ₀ hne
  -- Express div as mul * inv
  have h_eq : (fun s => deriv riemannZeta s / riemannZeta s) =
              deriv riemannZeta * riemannZeta⁻¹ := by
    ext s; simp [div_eq_mul_inv]
  rw [h_eq, meromorphicOrderAt_mul h_anal.meromorphicAt.deriv (zeta_meromorphicAt ρ₀ hne).inv,
      meromorphicOrderAt_inv]
  -- Cast analytic orders to meromorphic orders
  rw [h_anal.meromorphicOrderAt_eq, h_anal.deriv.meromorphicOrderAt_eq]
  -- Use derivative order relation: order(f') + 1 = order(f · - f(x))
  have h_ord := h_anal.analyticOrderAt_deriv_add_one
  -- Since ζ(ρ₀) = 0: (riemannZeta · - riemannZeta ρ₀) = riemannZeta
  have h_sub_eq : (riemannZeta · - riemannZeta ρ₀) = riemannZeta := by
    ext z; simp [hz]
  rw [h_sub_eq] at h_ord
  -- h_ord : analyticOrderAt (deriv riemannZeta) ρ₀ + 1 = analyticOrderAt riemannZeta ρ₀
  -- Extract ℕ values from ℕ∞
  have h_ne_top := zeta_analyticOrder_ne_top ρ₀ hne
  have h_deriv_ne_top : analyticOrderAt (deriv riemannZeta) ρ₀ ≠ ⊤ := by
    intro h_top; rw [h_top] at h_ord; exact absurd h_ord.symm h_ne_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_ne_top
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h_deriv_ne_top
  -- Rewrite using extracted values
  rw [← hn, ← hm] at h_ord ⊢
  -- h_ord : (↑m : ℕ∞) + 1 = ↑n
  -- Goal: (↑m : ℕ∞).map ↑ + -((↑n : ℕ∞).map ↑) < 0  in WithTop ℤ
  simp only [ENat.map_coe]
  -- Goal: (↑(↑m : ℤ) : WithTop ℤ) + -(↑(↑n : ℤ) : WithTop ℤ) < 0
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
  -- Goal: ↑((↑m : ℤ) + -(↑n : ℤ)) < 0
  norm_cast at h_ord ⊢
  omega

/-- ‖ζ'/ζ(s)‖ → ∞ as s → ρ₀ for any nontrivial zero ρ₀.

This is the key fact for the Landau argument: if -ζ'/ζ extends analytically
past Re(s) = α for some α < Re(ρ₀), then it must be bounded near ρ₀,
contradicting this unboundedness. -/
theorem zeta_logDeriv_tendsto_cobounded (ρ₀ : ℂ) (hne : ρ₀ ≠ 1) (hz : riemannZeta ρ₀ = 0) :
    Tendsto (fun s => deriv riemannZeta s / riemannZeta s)
      (𝓝[≠] ρ₀) (Bornology.cobounded ℂ) :=
  tendsto_cobounded_of_meromorphicOrderAt_neg
    (zeta_logDeriv_meromorphicOrder_neg ρ₀ hne hz)

end Aristotle.ZetaLogDerivPole
