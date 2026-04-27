import Mathlib
import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.Aristotle.ZetaZerosFiniteBelowV2

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyDirichletPhaseAlignmentWiring

open Schmidt

/-- The Dirichlet-phase critical-zero set is definitionally the standard
nontrivial zeta-zero set. -/
lemma criticalZeros_eq_zetaNontrivialZeros :
    Aristotle.DirichletPhaseAlignment.CriticalZeros = ZetaZeros.zetaNontrivialZeros := by
  ext ρ
  simp [Aristotle.DirichletPhaseAlignment.CriticalZeros, ZetaZeros.zetaNontrivialZeros]

/-- Bounded critical-strip zeros are finite in the Dirichlet-phase shape. -/
lemma criticalZeros_finite_below (T : ℝ) :
    (Aristotle.DirichletPhaseAlignment.CriticalZeros ∩ {ρ : ℂ | |ρ.im| ≤ T}).Finite := by
  convert (ZetaZerosFiniteBelowV2.zetaZeros_finite_below T) using 1
  ext ρ
  constructor
  · intro h
    rcases h with ⟨hzero, him⟩
    rcases hzero with ⟨hzeta, hpos, hlt⟩
    exact ⟨hzeta, hpos, hlt, him⟩
  · intro h
    rcases h with ⟨hzeta, hpos, hlt, him⟩
    exact ⟨⟨hzeta, hpos, hlt⟩, him⟩

/-- Schmidt Hardy zeros provide the Dirichlet-phase Hardy class needed by the
RH zero-sum lane. -/
instance [Schmidt.HardyCriticalLineZerosHyp] :
    Aristotle.DirichletPhaseAlignment.HardyCriticalLineZerosHyp where
  infinite_critical_zeros := by
    simpa [criticalZeros_eq_zetaNontrivialZeros, Set.mem_setOf_eq, Set.mem_sep_iff]
      using (Schmidt.HardyCriticalLineZerosHyp.infinite)
  zeros_finite := criticalZeros_finite_below

end HardyDirichletPhaseAlignmentWiring
