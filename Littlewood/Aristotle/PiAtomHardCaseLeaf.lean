import Mathlib
import Littlewood.Aristotle.PringsheimPiAtom

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.PiAtomHardCaseLeaf

/-- Optional instance-style packaging of the remaining π hard-case theorem. -/
class PiAtomHardCaseHyp : Prop where
  proof : Aristotle.PringsheimPiAtom.PiAtomHardCase

/-- Importable leaf for the `DeepSorries` π-atom hard-case placeholder.

Given a proof of `PringsheimPiAtom.PiAtomHardCase`, this produces the exact
`PringsheimAtoms.PiAtomType` object consumed by the non-RH π branch wiring. -/
theorem pringsheim_pi_atom_of_hard_case
    (h_hard : Aristotle.PringsheimPiAtom.PiAtomHardCase) :
    Aristotle.PringsheimAtoms.PiAtomType :=
  Aristotle.PringsheimPiAtom.pringsheim_pi_atom h_hard

/-- Instance-driven convenience wrapper around
`pringsheim_pi_atom_of_hard_case`. -/
theorem pringsheim_pi_atom_of_instance
    [PiAtomHardCaseHyp] :
    Aristotle.PringsheimAtoms.PiAtomType :=
  pringsheim_pi_atom_of_hard_case PiAtomHardCaseHyp.proof

end Aristotle.PiAtomHardCaseLeaf
