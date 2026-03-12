import Littlewood.Aristotle.ZetaLogDerivPole

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTLogDerivCompat

open Complex
open Aristotle.ZetaLogDerivPole

/-- External-port adapter for `strongpnt` zero-free-region log-derivative
meromorphicity shape. -/
theorem zeta_logDeriv_meromorphicAt_port
    (ρ₀ : ℂ) (hne : ρ₀ ≠ 1) :
    MeromorphicAt (fun s => deriv riemannZeta s / riemannZeta s) ρ₀ :=
  zeta_logDeriv_meromorphicAt ρ₀ hne

/-- External-port adapter for the negative meromorphic order at a zeta zero. -/
theorem zeta_logDeriv_meromorphicOrder_neg_port
    (ρ₀ : ℂ) (hne : ρ₀ ≠ 1) (hz : riemannZeta ρ₀ = 0) :
    meromorphicOrderAt (fun s => deriv riemannZeta s / riemannZeta s) ρ₀ < 0 :=
  zeta_logDeriv_meromorphicOrder_neg ρ₀ hne hz

/-- External-port adapter for `‖ζ'/ζ‖ → ∞` at a nontrivial zero. -/
theorem zeta_logDeriv_tendsto_cobounded_port
    (ρ₀ : ℂ) (hne : ρ₀ ≠ 1) (hz : riemannZeta ρ₀ = 0) :
    Filter.Tendsto (fun s => deriv riemannZeta s / riemannZeta s)
      (nhdsWithin ρ₀ (({ρ₀} : Set ℂ)ᶜ)) (Bornology.cobounded ℂ) := by
  simpa [nhdsWithin] using
  zeta_logDeriv_tendsto_cobounded ρ₀ hne hz

end Aristotle.Standalone.ExternalPort.StrongPNTLogDerivCompat
