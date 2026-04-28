/-
# Zero-sum convention bridge: ZerosBelow ↔ piMainFromZeros

Under RH, the ψ-level zero sum over ZerosBelow T (both ordinates)
equals piMainFromZeros over finite_zeros_le T (positive ordinates, factor 2)
times logx.

This is the conjugation pairing identity specialized to x^ρ/ρ.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.MultBridgeHelpers
import Littlewood.Aristotle.Standalone.MultConjugatePairing
import Littlewood.Aristotle.Standalone.RHPiZeroSumAlignmentBridge
import Littlewood.Aristotle.Standalone.CriticalZeroSumDiverges
import Littlewood.Aristotle.Standalone.LittlewoodKeyLemma
import Littlewood.Aristotle.PerronFormulaV2
import Littlewood.ZetaZeros.ZeroDensity

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiZeroSumConventionBridge

open Complex ZetaZeros Filter Real
open Aristotle.DirichletPhaseAlignment (ZerosBelow CriticalZeros)
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Littlewood.Classical.MultConjugatePairing
open Littlewood.Classical (positiveImZerosBelow)
open CriticalZeroSumDivergesProof (criticalZeros_eq)
open ZetaZeros.Density (zetaNontrivialZero_im_ne_zero)

private theorem criticalZeros_imBound_finite (T : ℝ) :
    (CriticalZeros ∩ {ρ : ℂ | |ρ.im| ≤ T}).Finite := by
  have hEq : (CriticalZeros ∩ {ρ : ℂ | |ρ.im| ≤ T}) = zetaZerosInStrip T := by
    ext ρ
    simp [Aristotle.DirichletPhaseAlignment.CriticalZeros, zetaZerosInStrip]
    tauto
  rw [hEq]
  exact zetaZerosInStrip_finite T

private theorem conj_mem_zerosBelow_unconditional {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ ZerosBelow T) : starRingEnd ℂ ρ ∈ ZerosBelow T := by
  have hfin : (CriticalZeros ∩ {ρ : ℂ | |ρ.im| ≤ T}).Finite :=
    criticalZeros_imBound_finite T
  rw [ZerosBelow, dif_pos hfin] at hρ ⊢
  have hρ' : ρ ∈ CriticalZeros ∩ {ρ : ℂ | |ρ.im| ≤ T} :=
    hfin.mem_toFinset.mp hρ
  rcases hρ' with ⟨hcrit, him⟩
  refine hfin.mem_toFinset.mpr ?_
  refine ⟨?_, ?_⟩
  · have hz : ρ ∈ zetaNontrivialZeros := by
      simpa [criticalZeros_eq] using hcrit
    have hconj : starRingEnd ℂ ρ ∈ zetaNontrivialZeros := zero_conj_zero hz
    simpa [criticalZeros_eq] using hconj
  · simpa [Complex.conj_im, abs_neg] using him

private theorem zerosBelow_filter_pos_im_eq_unconditional (T : ℝ) :
    (ZerosBelow T).filter (fun ρ => 0 < ρ.im) = positiveImZerosBelow T := by
  have hfin : (CriticalZeros ∩ {ρ : ℂ | |ρ.im| ≤ T}).Finite :=
    criticalZeros_imBound_finite T
  ext ρ
  simp only [Finset.mem_filter]
  constructor
  · intro h
    have hmem : ρ ∈ ZerosBelow T := h.1
    have him_pos : 0 < ρ.im := h.2
    rw [ZerosBelow, dif_pos hfin] at hmem
    have hρ' : ρ ∈ CriticalZeros ∩ {ρ : ℂ | |ρ.im| ≤ T} :=
      hfin.mem_toFinset.mp hmem
    rcases hρ' with ⟨hcrit, him_le⟩
    rw [Littlewood.Classical.mem_positiveImZerosBelow]
    refine ⟨?_, ?_⟩
    · exact mem_zetaNontrivialZerosPos.mpr
        ⟨by simpa [criticalZeros_eq] using hcrit, him_pos⟩
    · simpa [abs_of_pos him_pos] using him_le
  · intro h
    rw [Littlewood.Classical.mem_positiveImZerosBelow] at h
    rcases h with ⟨hpos, him_le⟩
    rcases mem_zetaNontrivialZerosPos.mp hpos with ⟨hzeta, him_pos⟩
    constructor
    · rw [ZerosBelow, dif_pos hfin]
      exact hfin.mem_toFinset.mpr ⟨by simpa [criticalZeros_eq] using hzeta,
        by simpa [abs_of_pos him_pos] using him_le⟩
    · exact him_pos

/-- The zero sum over ZerosBelow T (both ordinate signs) divided by
logx equals piMainFromZeros over (finite_zeros_le T).toFinset.

The proof applies conjugate_pairing_identity to split ZerosBelow into
positive-Im + Im=0 parts, observes that Im=0 is empty (no real-axis
nontrivial zeros), and identifies the positive-Im part with
positiveImZerosBelow T = (finite_zeros_le T).toFinset. -/
theorem zero_sum_convention_bridge
    (T : ℝ) (x : ℝ) (hx : 0 < x) :
    (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ).re) / Real.log x =
    piMainFromZeros ((finite_zeros_le T).toFinset) x := by
  -- Step 1: Apply conjugation pairing identity
  have hconj : ∀ ρ ∈ ZerosBelow T, starRingEnd ℂ ρ ∈ ZerosBelow T :=
    fun ρ hρ => conj_mem_zerosBelow_unconditional hρ
  have hf_conj : ∀ ρ ∈ ZerosBelow T,
      ((x : ℂ) ^ (starRingEnd ℂ ρ) / (starRingEnd ℂ ρ)).re =
      ((x : ℂ) ^ ρ / ρ).re :=
    fun ρ _hρ => Littlewood.Classical.MultBridgeHelpers.re_cpow_div_conj_eq x hx ρ
  -- Rewrite the sum to match conjugate_pairing_identity's form: Σ (1 * f ρ)
  have hsum_eq : ∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ).re =
      ∑ ρ ∈ ZerosBelow T, (1 : ℝ) * ((x : ℂ) ^ ρ / ρ).re := by
    congr 1; ext ρ; ring
  rw [hsum_eq]
  rw [conjugate_pairing_identity (ZerosBelow T)
    (fun _ => (1 : ℝ)) (fun ρ => ((x : ℂ) ^ ρ / ρ).re)
    hconj (fun _ _ => rfl) hf_conj]
  -- Step 2: The Im=0 sum is 0 (no real-axis nontrivial zeros)
  have hreal_zero : ∑ ρ ∈ (ZerosBelow T).filter (fun ρ => ρ.im = 0),
      1 * ((x : ℂ) ^ ρ / ρ).re = 0 := by
    apply Finset.sum_eq_zero
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    have hρz : ρ ∈ zetaNontrivialZeros := by
      have hmem := hρ.1
      simp only [ZerosBelow] at hmem
      split_ifs at hmem with hfin
      · exact criticalZeros_eq ▸ (hfin.mem_toFinset.mp hmem).1
      · simp at hmem
    exact absurd hρ.2 (ZetaZeros.Density.zetaNontrivialZero_im_ne_zero hρz)
  -- Step 3: Simplify
  simp only [one_mul] at hreal_zero ⊢
  rw [hreal_zero, add_zero]
  -- Step 4: (ZerosBelow T).filter (0 < ·.im) = positiveImZerosBelow T
  rw [zerosBelow_filter_pos_im_eq_unconditional T]
  -- Step 5: positiveImZerosBelow T = (finite_zeros_le T).toFinset by definition
  unfold piMainFromZeros positiveImZerosBelow
  ring

end Aristotle.Standalone.RHPiZeroSumConventionBridge
