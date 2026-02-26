/-
Holomorphic logarithm on a convex domain.

If f is analytic and non-vanishing on {Re > α}, then there exists an analytic
function g on {Re > α} with exp(g) = f.

**Proof strategy**:
1. The half-plane {Re > α} is convex → contractible → simply connected.
2. exp : ℂ → ℂ\{0} is a covering map (Mathlib: `isCoveringMapOn_exp`).
3. By the lifting theorem for simply connected spaces, there exists a
   continuous lift g with exp ∘ g = f.
4. The lift is analytic: at each point, exp is a local biholomorphism,
   and the lift locally equals (local inverse of exp) ∘ f.

Reference: Conway, Functions of One Complex Variable, §IV.6, Theorem 6.13.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Complex Filter Topology Set

namespace Aristotle.Standalone.HolomorphicLogOnHalfPlane

variable (α : ℝ)

/-! ## Step 1: Domain setup -/

private abbrev U := {s : ℂ | α < s.re}

private lemma isOpen_U : IsOpen (U α) :=
  isOpen_lt continuous_const continuous_re

private lemma convex_U : Convex ℝ (U α) :=
  convex_halfSpace_re_gt α

private lemma nonempty_U : (U α).Nonempty :=
  ⟨(↑(α + 1) : ℂ), by simp [U, Complex.ofReal_re]⟩

/-! ## Step 2: Topological instances -/

private instance : ContractibleSpace ↥(U α) :=
  (convex_U α).contractibleSpace (nonempty_U α)

private instance : LocPathConnectedSpace ↥(U α) :=
  (isOpen_U α).locPathConnectedSpace

/-! ## Step 3: Continuous lift via covering map -/

/-- Given a non-vanishing continuous function on the half-plane subtype,
the covering map lift provides a continuous logarithm. -/
private lemma continuous_lift (f : ℂ → ℂ)
    (hf_cont : ContinuousOn f (U α))
    (hf_ne : ∀ s : ℂ, s ∈ U α → f s ≠ 0) :
    ∃ F : C(↥(U α), ℂ), ∀ z : ↥(U α), exp (F z) = f z.val := by
  -- Wrap f as a ContinuousMap on the subtype
  let f_sub : C(↥(U α), ℂ) := ⟨fun z => f z.val, hf_cont.restrict⟩
  -- Base point
  have h_base : (↑(α + 1) : ℂ) ∈ U α := by
    simp [U, Complex.ofReal_re]
  let a₀ : ↥(U α) := ⟨↑(α + 1), h_base⟩
  -- Lift value at base point
  have h_ne : f (↑(α + 1) : ℂ) ≠ 0 := hf_ne _ h_base
  let e₀ := Complex.log (f (↑(α + 1) : ℂ))
  have he₀ : exp e₀ = f_sub a₀ := exp_log h_ne
  -- Non-vanishing condition for covering map lift
  have hs : ∀ a : ↥(U α), f_sub a ∈ ({0}ᶜ : Set ℂ) := by
    intro ⟨z, hz⟩; exact hf_ne z hz
  -- Apply the covering map lifting theorem
  obtain ⟨F, ⟨_, hF_lift⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f_sub he₀ hs
  exact ⟨F, fun z => by
    have := congr_fun hF_lift z
    simp only [Function.comp] at this
    exact this⟩

/-! ## Step 4: Upgrade continuous lift to analytic

At each point z₀, we show the lift F is locally equal to ψ ∘ f where
ψ is the analytic local inverse of exp. -/

/-- The continuous lift from a covering map is analytic when the base map is analytic. -/
private lemma lift_is_analytic (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (U α))
    (hf_ne : ∀ s : ℂ, s ∈ U α → f s ≠ 0)
    (F : C(↥(U α), ℂ))
    (hF : ∀ z : ↥(U α), exp (F z) = f z.val) :
    AnalyticOnNhd ℂ (fun z => if hz : z ∈ U α then F ⟨z, hz⟩ else 0) (U α) := by
  intro z₀ hz₀
  let g : ℂ → ℂ := fun z => if hz : z ∈ U α then F ⟨z, hz⟩ else 0
  -- The local inverse of exp at F(z₀) is analytic
  let w₀ := F ⟨z₀, hz₀⟩
  have h_exp_an : AnalyticAt ℂ exp w₀ := analyticAt_cexp
  have h_exp_ne : deriv exp w₀ ≠ 0 := by
    rw [Complex.deriv_exp]; exact exp_ne_zero _
  -- ψ is the local inverse of exp at w₀
  let ψ := h_exp_an.hasStrictDerivAt.localInverse exp (deriv exp w₀) w₀ h_exp_ne
  -- ψ is analytic at f(z₀)
  have hψ_an : AnalyticAt ℂ ψ (f z₀) := by
    have := h_exp_an.analyticAt_localInverse h_exp_ne
    rwa [hF ⟨z₀, hz₀⟩] at this
  -- ψ ∘ f is analytic at z₀
  have hψf_an : AnalyticAt ℂ (ψ ∘ f) z₀ := hψ_an.comp (hf z₀ hz₀)
  -- Key: g =ᶠ[𝓝 z₀] ψ ∘ f
  -- This follows from: ψ(exp(w)) = w near w₀, and g is continuous near z₀
  suffices h_eq : g =ᶠ[𝓝 z₀] ψ ∘ f from hψf_an.congr h_eq.symm
  -- The left inverse property: ψ(exp(w)) = w for w near w₀
  have h_left : ∀ᶠ w in 𝓝 w₀, ψ (exp w) = w :=
    h_exp_an.hasStrictDerivAt.eventually_left_inverse h_exp_ne
  -- g is continuous at z₀ (because F is continuous on ↥U and U is open at z₀)
  have hU_nhd : U α ∈ 𝓝 z₀ := (isOpen_U α).mem_nhds hz₀
  -- F pulled back to ℂ is continuous near z₀
  have h_cont_sub : ContinuousAt (fun (z : ↥(U α)) => F z) ⟨z₀, hz₀⟩ :=
    F.continuous.continuousAt
  -- Pull back through the subtype: F(z) near F(z₀) for z near z₀
  -- In the subtype topology: 𝓝 ⟨z₀, hz₀⟩ = comap Subtype.val (𝓝 z₀)
  have h_pre : ∀ᶠ z in 𝓝 (⟨z₀, hz₀⟩ : ↥(U α)), ψ (exp (F z)) = F z :=
    h_cont_sub.eventually h_left
  -- Convert from subtype filter to ambient filter
  -- Since U is open and z₀ ∈ U, the subtype nhds maps to nhds via the open embedding
  rw [nhds_subtype_eq_comap] at h_pre
  obtain ⟨V, hV_nhds, hV_sub⟩ := Filter.mem_comap.mp h_pre
  -- Now combine with U ∈ 𝓝 z₀
  filter_upwards [hU_nhd, hV_nhds] with z hz_in_U hz_in_V
  -- Goal: g z = (ψ ∘ f) z, i.e., g z = ψ (f z)
  show g z = ψ (f z)
  -- g(z) = F ⟨z, hz_in_U⟩ (since z ∈ U)
  -- Use split_ifs to handle the dite in g's definition
  change (if hz : z ∈ U α then F ⟨z, hz⟩ else 0) = ψ (f z)
  split_ifs with hzU
  · -- Positive branch: F ⟨z, hzU⟩ = ψ (f z)
    -- ψ(exp(F ⟨z, hzU⟩)) = F ⟨z, hzU⟩ (from the subtype filter)
    have h1 : ψ (exp (F ⟨z, hzU⟩)) = F ⟨z, hzU⟩ :=
      hV_sub (show (⟨z, hzU⟩ : ↥(U α)).val ∈ V from hz_in_V)
    -- exp(F ⟨z, hzU⟩) = f z (lift property)
    have h2 : exp (F ⟨z, hzU⟩) = f z := hF ⟨z, hzU⟩
    rw [← h2, h1]
  · -- Negative branch: z ∈ U but ¬ z ∈ U — contradiction
    exact absurd hz_in_U hzU

/-! ## Main theorem -/

/-- Every non-vanishing analytic function on a half-plane has an analytic logarithm. -/
theorem analytic_log_on_halfPlane_gen (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (U α))
    (hf_ne : ∀ s : ℂ, s ∈ U α → f s ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (U α) ∧
      ∀ s : ℂ, s ∈ U α → exp (g s) = f s := by
  -- Step 1: Get the continuous lift
  obtain ⟨F, hF⟩ := continuous_lift α f hf.continuousOn hf_ne
  -- Step 2: Define g and show it's analytic
  let g : ℂ → ℂ := fun z => if hz : z ∈ U α then F ⟨z, hz⟩ else 0
  refine ⟨g, lift_is_analytic α f hf hf_ne F hF, fun s hs => ?_⟩
  -- Step 3: exp(g(s)) = f(s)
  show exp (if hz : s ∈ U α then F ⟨s, hz⟩ else 0) = f s
  rw [dif_pos hs]
  exact hF ⟨s, hs⟩

end Aristotle.Standalone.HolomorphicLogOnHalfPlane

/-! ## Interface for PiAtomCoreFromZetaZeroFree -/

/-- Every non-vanishing analytic function on a half-plane {Re > α}
has an analytic logarithm. Interface matching `PiAtomCoreFromZetaZeroFree`. -/
theorem Aristotle.Standalone.analytic_log_on_halfPlane' (α : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f {s : ℂ | α < s.re})
    (hf_ne : ∀ s : ℂ, α < s.re → f s ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, α < s.re → exp (g s) = f s :=
  HolomorphicLogOnHalfPlane.analytic_log_on_halfPlane_gen α f hf hf_ne
