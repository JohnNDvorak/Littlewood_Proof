/-
# MultBridgeHelpers — Concrete Finset helpers for the mult→Abel bridge

These lemmas instantiate the abstract hypotheses of
`MultConjugatePairing.conjugate_pairing_identity` and
`MultKernelConversion.kernel_conversion` for the concrete repo types
`ZerosBelow T`, `positiveImZerosBelow T`, `zeroMultiplicity`, etc.

Claude 1 imports these to close W2 (ExplicitFormulaAbelBoundMultBridge:64).

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaAbelBoundPlaceholder
import Littlewood.Aristotle.CriticalZeros
import Littlewood.Aristotle.Standalone.AnalyticOrderAtConj

set_option maxHeartbeats 1600000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Littlewood.Classical.MultBridgeHelpers

open Complex ZetaZeros
open Aristotle.DirichletPhaseAlignment (CriticalZeros ZerosBelow)
open Littlewood.Classical (positiveImZerosBelow zeroMultiplicity)

/-! ### Helper 1: Conjugate membership in ZerosBelow -/

/-- Conjugate of a zero below T is also below T (under RH). -/
theorem conj_mem_zerosBelow (hRH : RiemannHypothesis') {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ ZerosBelow T) : starRingEnd ℂ ρ ∈ ZerosBelow T := by
  have hρz : ρ ∈ zetaNontrivialZeros := by
    simp only [ZerosBelow] at hρ
    split_ifs at hρ with hfin
    · exact ((hfin.mem_toFinset).mp hρ).1
    · simp at hρ
  have hconj_crit : starRingEnd ℂ ρ ∈ CriticalZeros := by
    simpa [CriticalZeros, zetaNontrivialZeros] using (zero_conj_zero hρz)
  have hρ_im_le : |ρ.im| ≤ T := by
    simp only [ZerosBelow] at hρ
    split_ifs at hρ with hfin
    · exact ((hfin.mem_toFinset).mp hρ).2
    · simp at hρ
  have hconj_im_le : |((starRingEnd ℂ) ρ).im| ≤ T := by
    change |(star ρ).im| ≤ T
    simp [Complex.conj_im, abs_neg]
    exact hρ_im_le
  have hfin : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite := by
    exact (critical_zeros_finite T).subset (fun ρ hρ => by
      rcases hρ with ⟨hcrit, him⟩
      refine ⟨?_, hcrit.1⟩
      refine ⟨ρ.im, ?_, ?_⟩
      · simpa [abs_le] using him
      · apply Complex.ext
        · simpa using (rh_implies_critical_line (hRH := hRH) ρ (by
            simpa [CriticalZeros, zetaNontrivialZeros] using hcrit)).symm
        · simp)
  rw [ZerosBelow, dif_pos hfin]
  exact hfin.mem_toFinset.mpr ⟨hconj_crit, hconj_im_le⟩

/-! ### Helper 2: Re(x^{ρ̄}/ρ̄) = Re(x^ρ/ρ) for real x > 0 -/

/-- The real part of x^ρ/ρ is invariant under complex conjugation of ρ. -/
theorem re_cpow_div_conj_eq (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    (((x : ℂ) ^ (starRingEnd ℂ ρ)) / (starRingEnd ℂ ρ)).re =
    (((x : ℂ) ^ ρ) / ρ).re := by
  have harg : (↑x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact ne_of_lt Real.pi_pos
  have h_cpow : (↑x : ℂ) ^ (starRingEnd ℂ ρ) = starRingEnd ℂ ((↑x : ℂ) ^ ρ) := by
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  have h_div :
      starRingEnd ℂ ((↑x : ℂ) ^ ρ) / starRingEnd ℂ ρ =
        starRingEnd ℂ (((↑x : ℂ) ^ ρ) / ρ) := (map_div₀ (starRingEnd ℂ) _ _).symm
  rw [h_cpow, h_div, Complex.conj_re]

/-! ### Helper 3: zeroMultiplicity is conj-invariant -/

/-- `zeroMultiplicity (conj ρ) = zeroMultiplicity ρ` for zeros in ZerosBelow T.
    Uses: ζ(conj s) = conj(ζ(s)) (Schwarz reflection, proved as riemannZeta_conj).
    The analyticOrderAt is preserved because conjugation is a homeomorphism
    that maps the power series at ρ to the conjugate power series at conj ρ,
    preserving the leading order. -/
theorem zeroMultiplicity_conj_eq (ρ : ℂ) :
    zeroMultiplicity (starRingEnd ℂ ρ) = zeroMultiplicity ρ := by
  unfold zeroMultiplicity
  congr 1
  -- Use the proved conjugation lemma from AnalyticOrderAtConj.lean.
  -- For ρ = 1 or conj ρ = 1: analyticOrderAt is 0 at both (ζ has a pole, not analytic),
  -- so .toNat gives 0 = 0. But congr 1 asks for the ℕ∞ values to match.
  -- Actually: if ρ = 1, then conj ρ = 1, and both sides are analyticOrderAt ζ 1 = 0
  -- (not analytic). If ρ ≠ 1 and conj ρ ≠ 1: use the proved lemma.
  by_cases hρ : ρ = 1
  · simp [hρ, Complex.conj_ofReal]
  · have hρc : starRingEnd ℂ ρ ≠ 1 := by
      intro h; apply hρ
      have := congr_arg (starRingEnd ℂ) h
      simp [star_star, Complex.conj_ofReal] at this
      exact this
    exact Aristotle.AnalyticOrderAtConj.analyticOrderAt_riemannZeta_conj ρ hρ hρc

/-! ### Helper 4: positiveImZerosBelow has positive imaginary parts -/

/-- Members of positiveImZerosBelow have positive imaginary part. -/
theorem positiveImZerosBelow_im_pos' {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow T) : 0 < ρ.im :=
  (mem_positiveImZerosBelow.mp hρ).1 |>.2

/-! ### Helper 5: zeroMultiplicity cast is nonneg -/

/-- The real cast of zeroMultiplicity is nonneg. -/
theorem zeroMultiplicity_cast_nonneg (ρ : ℂ) : (0 : ℝ) ≤ (zeroMultiplicity ρ : ℝ) :=
  Nat.cast_nonneg _

/-! ### Helper 6: ZerosBelow filtered by positive Im = positiveImZerosBelow -/

/-- Under RH, the positive-Im filter of ZerosBelow T equals positiveImZerosBelow T. -/
theorem zerosBelow_filter_pos_im_eq (hRH : RiemannHypothesis') (T : ℝ) :
    (ZerosBelow T).filter (fun ρ => 0 < ρ.im) = positiveImZerosBelow T := by
  have hfin : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite := by
    exact (critical_zeros_finite T).subset (fun ρ hρ => by
      rcases hρ with ⟨hcrit, him⟩
      refine ⟨?_, hcrit.1⟩
      refine ⟨ρ.im, ?_, ?_⟩
      · simpa [abs_le] using him
      · apply Complex.ext
        · simpa using (rh_implies_critical_line (hRH := hRH) ρ (by
            simpa [CriticalZeros, zetaNontrivialZeros] using hcrit)).symm
        · simp)
  ext ρ
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨hmem, him_pos⟩
    rw [ZerosBelow, dif_pos hfin] at hmem
    have ⟨hcrit, him_le⟩ := hfin.mem_toFinset.mp hmem
    rw [mem_positiveImZerosBelow]
    refine ⟨?_, ?_⟩
    · exact mem_zetaNontrivialZerosPos.mpr
        ⟨by simpa [CriticalZeros, zetaNontrivialZeros] using hcrit, him_pos⟩
    · exact (abs_le.mp him_le).2
  · intro hmem
    rcases mem_positiveImZerosBelow.mp hmem with ⟨hpos, hle⟩
    rcases mem_zetaNontrivialZerosPos.mp hpos with ⟨hzeta, him_pos⟩
    constructor
    · rw [ZerosBelow, dif_pos hfin]
      exact hfin.mem_toFinset.mpr ⟨by
        simpa [CriticalZeros, zetaNontrivialZeros] using hzeta,
        by simp [abs_of_pos him_pos]; exact hle⟩
    · exact him_pos

/-! ### Helper 7: RH bound on Re for zeros -/

/-- Under RH, all zeros have Re = 1/2. -/
theorem zerosBelow_re_half (hRH : RiemannHypothesis') {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ ZerosBelow T) : ρ.re = 1 / 2 := by
  have hρz : ρ ∈ zetaNontrivialZeros := by
    simp only [ZerosBelow] at hρ
    split_ifs at hρ with hfin
    · exact ((hfin.mem_toFinset).mp hρ).1
    · simp at hρ
  exact rh_implies_critical_line (hRH := hRH) ρ hρz

/-! ### Helper 8: |Re(x^ρ/ρ)| bound for Im=0 zeros -/

/-- Under RH, a zero with Im=0 has |Re(x^ρ/ρ)| ≤ 2√x. -/
theorem zeroIm_term_bound' (hRH : RiemannHypothesis') {T x : ℝ} (hx : 2 ≤ x)
    {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) (him : ρ.im = 0) :
    |(((x : ℂ) ^ ρ / ρ)).re| ≤ 2 * Real.sqrt x := by
  have hre : ρ.re = 1 / 2 := zerosBelow_re_half hRH hρ
  have hx_pos : (0 : ℝ) < x := by linarith
  calc
    |(((x : ℂ) ^ ρ / ρ)).re|
        ≤ ‖((x : ℂ) ^ ρ / ρ)‖ := Complex.abs_re_le_norm _
    _ = ‖(x : ℂ) ^ ρ‖ / ‖ρ‖ := norm_div _ _
    _ = x ^ ρ.re / ‖ρ‖ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    _ = x ^ (1 / 2 : ℝ) / ‖ρ‖ := by rw [hre]
    _ = Real.sqrt x / ‖ρ‖ := by rw [Real.sqrt_eq_rpow]
    _ = 2 * Real.sqrt x := by
          have hρ_eq : ρ = (↑(1 / 2 : ℝ) : ℂ) := Complex.ext (by simp [hre]) (by simp [him])
          rw [hρ_eq, Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          ring

end Littlewood.Classical.MultBridgeHelpers
