import Littlewood.Bridge.PiLiDirectOscillation
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalSplitExactSeedPayloads

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.RHPiExternalTruncatedPiBuilder

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExternalPort.RHPiExternalSplitExactSeedPayloads

/-- Field-level bundle for constructing a concrete
`TruncatedExplicitFormulaPiHyp` witness from theorem terms. -/
structure TruncatedPiWitnessBundle : Prop where
  piApprox :
    ∀ (S : Finset ℂ),
      (∀ ρ ∈ S, ρ ∈ ZetaZeros.zetaNontrivialZeros ∧ ρ.re = 1 / 2) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x in Filter.atTop,
        |((Nat.primeCounting (Nat.floor x) : ℝ) -
            LogarithmicIntegral.logarithmicIntegral x) +
          ((∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ).re) / Real.log x|
          ≤ ε * (Real.sqrt x / Real.log x)
  zeroSumNegFrequently :
    ∀ (ρ₀ : ℂ), ρ₀ ∈ ZetaZeros.zetaNontrivialZeros →
      ρ₀.re = 1 / 2 → ρ₀.im ≠ 0 →
      ∃ c > 0, ∀ X : ℝ, ∃ x > X,
        1 < x ∧
          ((∑ ρ ∈ ({ρ₀} : Finset ℂ), ((x : ℂ) ^ ρ / ρ)).re) / Real.log x
            ≤ -(c * (Real.sqrt x / Real.log x))

/-- Build `TruncatedExplicitFormulaPiHyp` from a field-level theorem bundle. -/
def truncatedExplicitFormulaPiHyp_of_bundle
    (hBundle : TruncatedPiWitnessBundle) :
    TruncatedExplicitFormulaPiHyp where
  pi_approx := hBundle.piApprox
  zero_sum_neg_frequently := hBundle.zeroSumNegFrequently

/-- Consolidated external-provider class for a concrete truncated-`pi` witness. -/
class ExternalTruncatedPiWitnessPayload : Prop where
  bundle : TruncatedPiWitnessBundle

/-- Auto-wire `TruncatedExplicitFormulaPiHyp` from a concrete truncated-`pi`
provider payload. -/
instance (priority := 100)
    [ExternalTruncatedPiWitnessPayload] :
    TruncatedExplicitFormulaPiHyp :=
  truncatedExplicitFormulaPiHyp_of_bundle
    ExternalTruncatedPiWitnessPayload.bundle

/-- Auto-wire the split external truncated lane from the concrete truncated-`pi`
provider payload. -/
instance (priority := 90)
    [ExternalTruncatedPiWitnessPayload] :
    ExternalTruncatedPiPayload where
  witness := inferInstance

/-- Component endpoint from a concrete truncated-`pi` provider payload. -/
theorem truncatedExplicitFormulaPi_of_witness_payload
    [ExternalTruncatedPiWitnessPayload] :
    TruncatedExplicitFormulaPiHyp := by
  infer_instance

end Aristotle.Standalone.ExternalPort.RHPiExternalTruncatedPiBuilder
