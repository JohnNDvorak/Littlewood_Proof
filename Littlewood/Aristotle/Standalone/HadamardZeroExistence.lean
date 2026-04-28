import Littlewood.Aristotle.Standalone.HadamardFactorizationXi
import Littlewood.ZetaZeros.ZeroDensity

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ZetaZeros

/-- The Hadamard canonical-product zero data already packages a concrete
nontrivial zero. Taking the zeroth listed zero and, if needed, conjugating it
produces a zero with positive imaginary part. -/
theorem zetaHasNontrivialZeroHyp_of_hadamardCriticalZeros
    [h : HadamardXi.HadamardXiCanonicalProductCriticalZeros] :
    ZetaHasNontrivialZeroHyp := by
  let ρ : ℂ := h.zeros 0
  have hρ : ρ ∈ zetaNontrivialZeros := by
    simpa [ρ] using h.zeros_spec 0
  have him_ne : ρ.im ≠ 0 := ZetaZeros.Density.zetaNontrivialZero_im_ne_zero hρ
  by_cases him_pos : 0 < ρ.im
  · exact ⟨⟨ρ, (mem_zetaNontrivialZerosPos).2 ⟨hρ, him_pos⟩⟩⟩
  · have him_nonpos : ρ.im ≤ 0 := le_of_not_gt him_pos
    have him_neg : ρ.im < 0 := lt_of_le_of_ne him_nonpos him_ne
    have hconj : starRingEnd ℂ ρ ∈ zetaNontrivialZeros := zero_conj_zero hρ
    have hconj_pos : 0 < (starRingEnd ℂ ρ).im := by
      simpa using (neg_pos.mpr him_neg)
    exact ⟨⟨starRingEnd ℂ ρ, (mem_zetaNontrivialZerosPos).2 ⟨hconj, hconj_pos⟩⟩⟩

/-- Prefer the Hadamard-based zero witness when the canonical-product zero data
is already in scope. This avoids falling back to first-zero placeholders on the
active RH `π` path. -/
instance (priority := 1100)
    [HadamardXi.HadamardXiCanonicalProductCriticalZeros] :
    ZetaHasNontrivialZeroHyp :=
  zetaHasNontrivialZeroHyp_of_hadamardCriticalZeros

end ZetaZeros
