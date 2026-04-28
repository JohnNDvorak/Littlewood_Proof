import Littlewood.Aristotle.Standalone.HadamardFactorizationXi
import Littlewood.Development.ZetaLogDerivBound
import Littlewood.ZetaZeros.ZeroDensity

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Littlewood.Bridge.HadamardConcreteBridge

open Complex
open HadamardXi
open ZetaZeros

/-- Convert a Hadamard-enumerated critical-strip zero into a concrete positive-
ordinate zeta zero by conjugating when necessary. This is the basic bridge from
the abstract Hadamard sequence to the project's concrete zero-counting
infrastructure on `zetaNontrivialZerosPos`. -/
noncomputable def positiveRepresentative
    [h : HadamardXiCanonicalProductCriticalZeros] (n : ℕ) : zetaNontrivialZerosPos := by
  let ρ : ℂ := h.zeros n
  have hρ : ρ ∈ zetaNontrivialZeros := by
    simpa [ρ] using h.zeros_spec n
  have him_ne : ρ.im ≠ 0 := ZetaZeros.Density.zetaNontrivialZero_im_ne_zero hρ
  by_cases him_pos : 0 < ρ.im
  · exact ⟨ρ, (mem_zetaNontrivialZerosPos).2 ⟨hρ, him_pos⟩⟩
  · have him_nonpos : ρ.im ≤ 0 := le_of_not_gt him_pos
    have him_neg : ρ.im < 0 := lt_of_le_of_ne him_nonpos him_ne
    have hconj : starRingEnd ℂ ρ ∈ zetaNontrivialZeros := zero_conj_zero hρ
    have hconj_pos : 0 < (starRingEnd ℂ ρ).im := by
      simpa using (neg_pos.mpr him_neg)
    exact ⟨starRingEnd ℂ ρ, (mem_zetaNontrivialZerosPos).2 ⟨hconj, hconj_pos⟩⟩

/-- The positive representative has ordinate equal to the absolute value of the
original Hadamard zero's ordinate. -/
theorem positiveRepresentative_im_eq_abs
    [h : HadamardXiCanonicalProductCriticalZeros] (n : ℕ) :
    (positiveRepresentative n : ℂ).im = |(h.zeros n).im| := by
  let ρ : ℂ := h.zeros n
  have hρ : ρ ∈ zetaNontrivialZeros := by
    simpa [ρ] using h.zeros_spec n
  have him_ne : ρ.im ≠ 0 := ZetaZeros.Density.zetaNontrivialZero_im_ne_zero hρ
  dsimp [positiveRepresentative, ρ]
  by_cases him_pos : 0 < (h.zeros n).im
  · simp [him_pos, abs_of_pos him_pos]
  · have him_nonpos : (h.zeros n).im ≤ 0 := le_of_not_gt him_pos
    have him_neg : (h.zeros n).im < 0 := lt_of_le_of_ne him_nonpos him_ne
    simp [him_pos, abs_of_neg him_neg]

/-- If a Hadamard-enumerated zero lies within distance `1` of height `t`, then
its positive representative lies in the concrete positive zero set below
`|t| + 1`. This is the basic height-window bridge from the abstract Hadamard
enumeration to `zerosUpTo`. -/
theorem positiveRepresentative_mem_zerosUpTo_of_near
    [h : HadamardXiCanonicalProductCriticalZeros] {n : ℕ} {t : ℝ}
    (hnear : |(h.zeros n).im - t| ≤ 1) :
    (positiveRepresentative n : ℂ) ∈ zerosUpTo (|t| + 1) := by
  have hmem_pos : ((positiveRepresentative n : zetaNontrivialZerosPos) : ℂ) ∈ zetaNontrivialZerosPos :=
    (positiveRepresentative n).property
  rw [zerosUpTo]
  refine ⟨hmem_pos, ?_⟩
  have htri : |(h.zeros n).im| ≤ |(h.zeros n).im - t| + |t| := by
    have h := norm_add_le ((h.zeros n).im - t) t
    simpa [Real.norm_eq_abs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have him_le : |(h.zeros n).im| ≤ |t| + 1 := by
    linarith
  change (positiveRepresentative n : ℂ).im ≤ |t| + 1
  rw [positiveRepresentative_im_eq_abs]
  exact him_le

/-- Focused near-zero leaf after reducing the abstract Hadamard core to the
concrete critical-zero enumeration. The remaining missing content is the actual
near-packet estimate; the bridge from `h.zeros` to concrete zeta zeros lives in
the lemmas above. -/
class HadamardXiNearZeroSumCriticalZerosLeaf
    [h : HadamardXiCanonicalProductCriticalZeros] : Prop where
  bound :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (σ t : ℝ), 1 / 2 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
      (∀ n : ℕ, (↑σ + ↑t * I : ℂ) ≠ h.zeros n) →
        ‖∑' (n : {n : ℕ // |(h.zeros n).im - t| ≤ 1}),
          (1 / ((↑σ + ↑t * I : ℂ) - h.zeros ↑n) + 1 / h.zeros ↑n)‖ ≤
            C * Real.log |t|

/-- Focused far-zero leaf after reducing the abstract Hadamard core to the
concrete critical-zero enumeration. The bridge file isolates the enumeration
compatibility lemmas needed for the eventual constructive proof. -/
class HadamardXiFarZeroSumCriticalZerosLeaf
    [h : HadamardXiCanonicalProductCriticalZeros] : Prop where
  bound :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (σ t : ℝ), 1 / 2 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
      (∀ n : ℕ, (↑σ + ↑t * I : ℂ) ≠ h.zeros n) →
        ‖∑' (n : {n : ℕ // ¬ (|(h.zeros n).im - t| ≤ 1)}),
          (1 / ((↑σ + ↑t * I : ℂ) - h.zeros ↑n) + 1 / h.zeros ↑n)‖ ≤
            C * (Real.log |t|) ^ 2

instance (priority := 100)
    [h : HadamardXiCanonicalProductCriticalZeros]
    [HadamardXiNearZeroSumCriticalZerosLeaf] :
    Littlewood.Development.ZetaLogDerivBound.HadamardXiNearZeroSumBound where
  bound := HadamardXiNearZeroSumCriticalZerosLeaf.bound

instance (priority := 100)
    [h : HadamardXiCanonicalProductCriticalZeros]
    [HadamardXiFarZeroSumCriticalZerosLeaf] :
    Littlewood.Development.ZetaLogDerivBound.HadamardXiFarZeroSumBound where
  bound := HadamardXiFarZeroSumCriticalZerosLeaf.bound

/-!
No default providers are installed for the near/far concrete packet leaves.

These two classes remain available only as optional compatibility surfaces for
legacy experiments. The raw near-packet support surface is false as a default
pointwise route, and the far-packet tail estimate is still open on this
concrete enumeration. Active theorem paths should avoid depending on either
class by default.
-/

end Littlewood.Bridge.HadamardConcreteBridge
