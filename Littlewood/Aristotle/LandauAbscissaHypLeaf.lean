import Mathlib
import Littlewood.Aristotle.LandauAbscissaConvergence

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.LandauAbscissaHypLeaf

/-- Optional instance-style packaging of
`LandauAbscissaConvergence.RealIntegrabilityHyp`. -/
class LandauRealIntegrabilityHyp : Prop where
  proof : Aristotle.LandauAbscissaConvergence.RealIntegrabilityHyp

/-- Importable leaf for the `DeepSorries` Landau-abscissa placeholder.

It turns the real-integrability core theorem (`RealIntegrabilityHyp`) into the
exact `PringsheimPsiAtom.LandauAbscissaHyp` object required by
`PringsheimPsiAtom.pringsheim_psi_atom`. -/
theorem landau_abscissa_hyp_of_real_integrability
    (h_real : Aristotle.LandauAbscissaConvergence.RealIntegrabilityHyp) :
    Aristotle.PringsheimPsiAtom.LandauAbscissaHyp :=
  Aristotle.LandauAbscissaConvergence.landau_abscissa_hyp h_real

/-- Instance-driven convenience wrapper around
`landau_abscissa_hyp_of_real_integrability`. -/
theorem landau_abscissa_hyp_of_instance
    [LandauRealIntegrabilityHyp] :
    Aristotle.PringsheimPsiAtom.LandauAbscissaHyp :=
  landau_abscissa_hyp_of_real_integrability LandauRealIntegrabilityHyp.proof

end Aristotle.LandauAbscissaHypLeaf
