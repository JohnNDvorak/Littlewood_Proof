import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.Development.PerronContourShift
import Littlewood.Development.ZetaLogDerivBound

/-!
Cycle-free interface for the shifted explicit-formula remainder used in the
Hadamard/Perron lane.

This module deliberately sits below `HadamardProductZeta` in the import graph:

- it depends only on `DirichletPhaseAlignment` for the concrete remainder
  definition;
- it depends only on `PerronContourShift` for the generic segment-form to
  standard-form reduction;
- it does not import `HadamardProductZeta`, so downstream files can share this
  interface without creating a cycle.

The intended follow-up is:

1. `HadamardProductZeta` imports this file and supplies the large-`T`
   segment-form theorem for the concrete `shiftedRemainderRe`;
2. `ExplicitFormulaPsiB5aDefs` imports this file instead of importing
   `HadamardProductZeta` just to recover the same interface.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Littlewood.Development.ShiftedRemainderInterface

open Aristotle.DirichletPhaseAlignment (chebyshevPsi ZerosBelow)

/-- The real part of the truncated nontrivial-zero sum
`Σ_{|γ|≤T} x^ρ / ρ`. -/
def zeroSumRe (x T : ℝ) : ℝ :=
  (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re

/-- The shifted remainder appearing in the truncated explicit formula:
`ψ(x) - x + Σ Re(x^ρ/ρ)`. -/
def shiftedRemainderRe (x T : ℝ) : ℝ :=
  Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + zeroSumRe x T

/-- Cycle-free large-`T` interface for the exact segment-form bound expected
by `PerronContourShift.contour_bound_from_pointwise`. This is the analytic leaf
that `HadamardProductZeta` currently carries privately. -/
class ShiftedRemainderSegmentBoundLargeTHyp : Prop where
  bound : ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
    |shiftedRemainderRe x T| ≤
      P * (Real.sqrt x * (Real.log T) ^ 3 / T) +
      2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)

/-- Once the direct segment-form large-`T` estimate is available, the generic
Perron contour algebra reduces it to the standard
`sqrt(x) * (log T)^2 / sqrt(T) + (log x)^2` contour bound. -/
theorem contour_bound_from_segment_hyp [ShiftedRemainderSegmentBoundLargeTHyp] :
    ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  obtain ⟨P, hP, hseg⟩ := ShiftedRemainderSegmentBoundLargeTHyp.bound
  simpa using
    Littlewood.Development.PerronContourShift.contour_bound_from_pointwise
      shiftedRemainderRe P hP hseg

/-- Cycle-free alias for the large-`T` pointwise Hadamard input on `-ζ'/ζ`
used by the shifted-remainder Perron closure. This matches the private local
abbreviation currently used in `HadamardProductZeta`. -/
abbrev ZetaLogDerivPointwiseLargeTHyp : Prop :=
    ∃ C > (0 : ℝ), ∀ (σ t : ℝ), 1 / 2 ≤ σ → σ ≤ 2 → 2 ≤ |t| →
      ‖(-deriv riemannZeta (↑σ + ↑t * Complex.I) /
        riemannZeta (↑σ + ↑t * Complex.I))‖ ≤ C * (Real.log |t|) ^ 2

/-- Smaller cycle-free support surface for the Hadamard large-`T` lane:
assuming the pointwise large-`T` bound on `-ζ'/ζ`, produce the exact
segment-form bound on the concrete shifted remainder. This isolates the
remaining Perron/contour/residue closure away from `HadamardProductZeta`. -/
class ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp : Prop where
  bound :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |shiftedRemainderRe x T| ≤
          P * (Real.sqrt x * (Real.log T) ^ 3 / T) +
          2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)

/-- Strictly smaller support surface than the direct segment-form bound:
assuming the pointwise large-`T` bound on `-ζ'/ζ`, produce explicit real
vertical and horizontal pieces of the shifted remainder with their separate
segment-form bounds. This matches the actual Perron/CIF bookkeeping more
closely than the absolute-value conclusion. -/
class ShiftedRemainderContourPieceBoundsFromLogDerivLargeTHyp : Prop where
  bound :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        ∃ vertRe horizRe : ℝ,
          shiftedRemainderRe x T = vertRe + horizRe ∧
          |vertRe| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) ∧
          |horizRe| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)

/-- The Perron-formula/residue bookkeeping surface below the log-derivative
leaf: choose concrete vertical and horizontal real contour pieces once and for
all and prove they decompose the shifted remainder. This is the smallest honest
support target for the actual contour identity itself. -/
class ShiftedRemainderContourDecompLargeTHyp where
  vertRe : ℝ → ℝ → ℝ
  horizRe : ℝ → ℝ → ℝ
  decomp : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
    shiftedRemainderRe x T = vertRe x T + horizRe x T

/-- Separate vertical large-`T` support surface on top of a fixed contour
decomposition. -/
class ShiftedRemainderContourVertBoundFromLogDerivLargeTHyp
    [ShiftedRemainderContourDecompLargeTHyp] : Prop where
  bound : ZetaLogDerivPointwiseLargeTHyp →
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |ShiftedRemainderContourDecompLargeTHyp.vertRe x T| ≤
        P * (Real.sqrt x * (Real.log T) ^ 3 / T)

/-- Separate horizontal large-`T` support surface on top of a fixed contour
decomposition. -/
class ShiftedRemainderContourHorizBoundFromLogDerivLargeTHyp
    [ShiftedRemainderContourDecompLargeTHyp] : Prop where
  bound : ZetaLogDerivPointwiseLargeTHyp →
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |ShiftedRemainderContourDecompLargeTHyp.horizRe x T| ≤
        2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)

/-- Complex-valued vertical contour-piece surface below the real bound class:
the chosen real vertical piece is the real part of a complex contour term, and
that complex term satisfies the required large-`T` norm bound from the pointwise
`-ζ'/ζ` hypothesis. -/
class ShiftedRemainderContourVertComplexBoundFromLogDerivLargeTHyp
    [ShiftedRemainderContourDecompLargeTHyp] where
  vertC : ℝ → ℝ → ℂ
  realPart :
    ∀ x T : ℝ,
      ShiftedRemainderContourDecompLargeTHyp.vertRe x T = (vertC x T).re
  bound : ZetaLogDerivPointwiseLargeTHyp →
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ‖vertC x T‖ ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T)

/-- Complex-valued horizontal contour-piece surface below the real bound class:
the chosen real horizontal piece is the real part of a complex contour term,
and that complex term satisfies the required large-`T` norm bound from the
pointwise `-ζ'/ζ` hypothesis. -/
class ShiftedRemainderContourHorizComplexBoundFromLogDerivLargeTHyp
    [ShiftedRemainderContourDecompLargeTHyp] where
  horizC : ℝ → ℝ → ℂ
  realPart :
    ∀ x T : ℝ,
      ShiftedRemainderContourDecompLargeTHyp.horizRe x T = (horizC x T).re
  bound : ZetaLogDerivPointwiseLargeTHyp →
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ‖horizC x T‖ ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)

/-- A structured support surface bundling the contour decomposition with both
separate large-`T` bounds. This can be assembled automatically from the three
smaller support classes above. -/
class ShiftedRemainderContourDecompFromLogDerivLargeTHyp where
  vertRe : ℝ → ℝ → ℝ
  horizRe : ℝ → ℝ → ℝ
  decomp : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
    shiftedRemainderRe x T = vertRe x T + horizRe x T
  vertBound : ZetaLogDerivPointwiseLargeTHyp →
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |vertRe x T| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T)
  horizBound : ZetaLogDerivPointwiseLargeTHyp →
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |horizRe x T| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)

/-- The structured contour-decomposition class is a wrapper over the smaller
component surfaces: a concrete decomposition plus separate vertical and
horizontal large-`T` bounds. -/
instance
    [ShiftedRemainderContourDecompLargeTHyp]
    [ShiftedRemainderContourVertBoundFromLogDerivLargeTHyp]
    [ShiftedRemainderContourHorizBoundFromLogDerivLargeTHyp] :
    ShiftedRemainderContourDecompFromLogDerivLargeTHyp where
  vertRe := ShiftedRemainderContourDecompLargeTHyp.vertRe
  horizRe := ShiftedRemainderContourDecompLargeTHyp.horizRe
  decomp := ShiftedRemainderContourDecompLargeTHyp.decomp
  vertBound := ShiftedRemainderContourVertBoundFromLogDerivLargeTHyp.bound
  horizBound := ShiftedRemainderContourHorizBoundFromLogDerivLargeTHyp.bound

/-- A complex contour decomposition immediately yields the corresponding real
decomposition by taking real parts of the two complex pieces. This is the
smallest honest support target for the bookkeeping side when the Hadamard lane
already has complex contour pieces in hand. -/
theorem real_decomp_from_complex_sum
    (vertC horizC : ℝ → ℝ → ℂ)
    (hdecomp : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      shiftedRemainderRe x T = (vertC x T + horizC x T).re) :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      shiftedRemainderRe x T = (vertC x T).re + (horizC x T).re := by
  intro x T hx hT
  rw [hdecomp x T hx hT, Complex.add_re]

/-- If a real vertical piece is realized as the real part of a complex contour
integral, a norm bound on the complex piece immediately yields the required
vertical large-`T` bound. -/
theorem vertical_bound_from_complex_piece
    (vertRe : ℝ → ℝ → ℝ)
    (vertC : ℝ → ℝ → ℂ)
    (hreal : ∀ x T : ℝ, vertRe x T = (vertC x T).re)
    (hbound : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        ‖vertC x T‖ ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T)) :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |vertRe x T| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) := by
  intro h_logderiv
  obtain ⟨P, hP, hbound'⟩ := hbound h_logderiv
  refine ⟨P, hP, ?_⟩
  intro x T hx hT
  rw [hreal x T]
  exact le_trans (Complex.abs_re_le_norm _) (hbound' x T hx hT)

/-- If a real horizontal piece is realized as the real part of a complex contour
integral, a norm bound on the complex piece immediately yields the required
horizontal large-`T` bound. -/
theorem horizontal_bound_from_complex_piece
    (horizRe : ℝ → ℝ → ℝ)
    (horizC : ℝ → ℝ → ℂ)
    (hreal : ∀ x T : ℝ, horizRe x T = (horizC x T).re)
    (hbound : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        ‖horizC x T‖ ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)) :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |horizRe x T| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  intro h_logderiv
  obtain ⟨P, hP, hbound'⟩ := hbound h_logderiv
  refine ⟨P, hP, ?_⟩
  intro x T hx hT
  rw [hreal x T]
  exact le_trans (Complex.abs_re_le_norm _) (hbound' x T hx hT)

/-- A vertical complex contour piece becomes a wrapper once it is exhibited as
an integral over `[-T, T]` whose integrand satisfies the normalized pointwise
majorant required by `PerronContourShift.left_vertical_bound`. -/
theorem vertical_complex_bound_from_normalized_integrand
    (vertC : ℝ → ℝ → ℂ)
    (vertIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hrep : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      vertC x T = ∫ t in (-T)..T, vertIntegrand x T t)
    (hint : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun t => vertIntegrand x T t) MeasureTheory.volume (-T) T)
    (hpointwise : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand x T t‖ ≤
          (P * (Real.sqrt x * (Real.log T) ^ 3 / T)) / (2 * T)) :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        ‖vertC x T‖ ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) := by
  intro h_logderiv
  obtain ⟨P, hP, hpointwise'⟩ := hpointwise h_logderiv
  refine ⟨P, hP, ?_⟩
  intro x T hx hT
  rw [hrep x T hx hT]
  have hT_pos : 0 < T := by linarith
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
  have hB : 0 ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) := by
    apply mul_nonneg hP.le
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT_nonneg 3))
      hT_pos.le
  exact
    Littlewood.Development.PerronContourShift.left_vertical_bound_from_normalized_pointwise
      hT_pos hB
      (fun t ht => hpointwise' x T t hx hT ht)
      (hint x T hx hT)

/-- A horizontal complex contour piece becomes a wrapper once it is exhibited
as an integral over `[σ₀, c]` whose integrand satisfies the normalized
pointwise majorant required by `PerronContourShift.horiz_bound`. -/
theorem horizontal_complex_bound_from_normalized_integrand
    (σ₀ c : ℝ) (hσc : σ₀ < c)
    (horizC : ℝ → ℝ → ℂ)
    (horizIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hrep : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      horizC x T = ∫ σ in σ₀..c, horizIntegrand x T σ)
    (hint : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun σ => horizIntegrand x T σ) MeasureTheory.volume σ₀ c)
    (hpointwise : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
        ‖horizIntegrand x T σ‖ ≤
          (2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)) / (c - σ₀)) :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        ‖horizC x T‖ ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  intro h_logderiv
  obtain ⟨P, hP, hpointwise'⟩ := hpointwise h_logderiv
  refine ⟨P, hP, ?_⟩
  intro x T hx hT
  rw [hrep x T hx hT]
  have hT_pos : 0 < T := by linarith
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
  have hB : 0 ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
    apply mul_nonneg (by positivity : 0 ≤ 2 * P)
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT_nonneg 2))
      hT_pos.le
  exact
    Littlewood.Development.PerronContourShift.horiz_bound_from_normalized_pointwise
      hσc hB
      (fun σ hσ => hpointwise' x T σ hx hT hσ)
      (hint x T hx hT)

/-- Reduce the vertical normalized pointwise majorant to a smaller factor bound:
it suffices to bound the integrand by a geometric kernel times the pointwise
`-ζ'/ζ` term along a contour path that stays in the strip and whose imaginary
part has size between `2` and `T`. -/
theorem vertical_normalized_pointwise_from_logderiv_factor
    (vertIntegrand : ℝ → ℝ → ℝ → ℂ)
    (sigmaArg tauArg : ℝ → ℝ → ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hfactor : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      ‖vertIntegrand x T t‖ ≤
        ((K * (Real.sqrt x * Real.log T / T)) / (2 * T)) *
          ‖(-deriv riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I) /
            riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I))‖)
    (hσ : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      1 / 2 ≤ sigmaArg x T t ∧ sigmaArg x T t ≤ 2)
    (hτlo : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      2 ≤ |tauArg x T t|)
    (hτhi : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      |tauArg x T t| ≤ T) :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand x T t‖ ≤
          (P * (Real.sqrt x * (Real.log T) ^ 3 / T)) / (2 * T) := by
  intro h_logderiv
  obtain ⟨C, hC, hCbound⟩ := h_logderiv
  refine ⟨K * C + 1, by positivity, ?_⟩
  intro x T t hx hT ht
  have hT_pos : 0 < T := by linarith
  have hσ' := hσ x T t hx hT ht
  have hτlo' := hτlo x T t hx hT ht
  have hτhi' := hτhi x T t hx hT ht
  have hld_raw :=
    hCbound (sigmaArg x T t) (tauArg x T t) hσ'.1 hσ'.2 hτlo'
  have htau_pos : 0 < |tauArg x T t| := by linarith
  have hlog_mono : Real.log |tauArg x T t| ≤ Real.log T :=
    Real.log_le_log htau_pos hτhi'
  have hlog_tau_nonneg : 0 ≤ Real.log |tauArg x T t| :=
    Real.log_nonneg (by linarith : 1 ≤ |tauArg x T t|)
  have hsq :
      (Real.log |tauArg x T t|) ^ 2 ≤ (Real.log T) ^ 2 :=
    pow_le_pow_left₀ hlog_tau_nonneg hlog_mono 2
  have hld :
      ‖(-deriv riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I) /
          riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I))‖ ≤
        C * (Real.log T) ^ 2 := by
    have hsq_nonneg : 0 ≤ C := hC.le
    exact hld_raw.trans <| mul_le_mul_of_nonneg_left hsq hsq_nonneg
  have hkernel_nonneg : 0 ≤ (K * (Real.sqrt x * Real.log T / T)) / (2 * T) := by
    have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
    have hnum : 0 ≤ K * (Real.sqrt x * Real.log T / T) := by
      apply mul_nonneg hK
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg x) hlogT_nonneg)
        hT_pos.le
    exact div_nonneg hnum (by nlinarith : 0 ≤ (2 : ℝ) * T)
  have hmain :=
    le_trans (hfactor x T t hx hT ht) (mul_le_mul_of_nonneg_left hld hkernel_nonneg)
  have hdenT : T ≠ 0 := by linarith
  have hden2T : (2 : ℝ) * T ≠ 0 := by nlinarith
  have hshape_nonneg : 0 ≤ (Real.sqrt x * (Real.log T) ^ 3 / T) / (2 * T) := by
    have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
    have hnum : 0 ≤ Real.sqrt x * (Real.log T) ^ 3 / T := by
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT_nonneg 3))
        hT_pos.le
    exact div_nonneg hnum (by nlinarith : 0 ≤ (2 : ℝ) * T)
  have hKCle : K * C ≤ K * C + 1 := by linarith
  have hrewrite :
      ((K * (Real.sqrt x * Real.log T / T)) / (2 * T)) * (C * (Real.log T) ^ 2) =
        (K * C) * ((Real.sqrt x * (Real.log T) ^ 3 / T) / (2 * T)) := by
    field_simp [hdenT, hden2T]
  have hgrow :
      (K * C) * ((Real.sqrt x * (Real.log T) ^ 3 / T) / (2 * T)) ≤
        (K * C + 1) * ((Real.sqrt x * (Real.log T) ^ 3 / T) / (2 * T)) :=
    mul_le_mul_of_nonneg_right hKCle hshape_nonneg
  calc
    ‖vertIntegrand x T t‖
        ≤ ((K * (Real.sqrt x * Real.log T / T)) / (2 * T)) * (C * (Real.log T) ^ 2) := hmain
    _ = (K * C) * ((Real.sqrt x * (Real.log T) ^ 3 / T) / (2 * T)) := hrewrite
    _ ≤ (K * C + 1) * ((Real.sqrt x * (Real.log T) ^ 3 / T) / (2 * T)) := hgrow
    _ = ((K * C + 1) * (Real.sqrt x * (Real.log T) ^ 3 / T)) / (2 * T) := by
        field_simp [hden2T]

/-- Reduce the horizontal normalized pointwise majorant to a smaller factor
bound: it suffices to bound the integrand by a geometric kernel times the
pointwise `-ζ'/ζ` term on the fixed-height contour line. -/
theorem horizontal_normalized_pointwise_from_logderiv_factor
    (σ₀ c : ℝ) (hσ0 : 1 / 2 ≤ σ₀) (hc : c ≤ 2) (hσc : σ₀ < c)
    (horizIntegrand : ℝ → ℝ → ℝ → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hfactor : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      ‖horizIntegrand x T σ‖ ≤
        ((K * (Real.sqrt x / T)) / (c - σ₀)) *
          ‖(-deriv riemannZeta (↑σ + ↑T * Complex.I) /
            riemannZeta (↑σ + ↑T * Complex.I))‖) :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
        ‖horizIntegrand x T σ‖ ≤
          (2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)) / (c - σ₀) := by
  intro h_logderiv
  obtain ⟨C, hC, hCbound⟩ := h_logderiv
  refine ⟨K * C + 1, by positivity, ?_⟩
  intro x T σ hx hT hσmem
  have hT_pos : 0 < T := by linarith
  have hσlo : 1 / 2 ≤ σ := le_trans hσ0 hσmem.1
  have hσhi : σ ≤ 2 := le_trans hσmem.2 hc
  have hTabs : 2 ≤ |T| := by
    simpa [abs_of_nonneg hT_pos.le] using (show (2 : ℝ) ≤ T by linarith)
  have hld_raw := hCbound σ T hσlo hσhi hTabs
  have hld :
      ‖(-deriv riemannZeta (↑σ + ↑T * Complex.I) /
          riemannZeta (↑σ + ↑T * Complex.I))‖ ≤
        C * (Real.log T) ^ 2 := by
    simpa [abs_of_nonneg hT_pos.le] using hld_raw
  have hkernel_nonneg : 0 ≤ (K * (Real.sqrt x / T)) / (c - σ₀) := by
    have hnum : 0 ≤ K * (Real.sqrt x / T) := by
      apply mul_nonneg hK
      exact div_nonneg (Real.sqrt_nonneg x) hT_pos.le
    exact div_nonneg hnum (by linarith : 0 ≤ c - σ₀)
  have hmain :=
    le_trans (hfactor x T σ hx hT hσmem) (mul_le_mul_of_nonneg_left hld hkernel_nonneg)
  have hdenT : T ≠ 0 := by linarith
  have hdenσ : c - σ₀ ≠ 0 := by linarith
  have hshape_nonneg : 0 ≤ (Real.sqrt x * (Real.log T) ^ 2 / T) / (c - σ₀) := by
    have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
    have hnum : 0 ≤ Real.sqrt x * (Real.log T) ^ 2 / T := by
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT_nonneg 2))
        hT_pos.le
    exact div_nonneg hnum (by linarith : 0 ≤ c - σ₀)
  have hKCle : K * C ≤ 2 * (K * C + 1) := by nlinarith [hK, hC.le]
  have hrewrite :
      ((K * (Real.sqrt x / T)) / (c - σ₀)) * (C * (Real.log T) ^ 2) =
        (K * C) * ((Real.sqrt x * (Real.log T) ^ 2 / T) / (c - σ₀)) := by
    field_simp [hdenT, hdenσ]
  have hgrow :
      (K * C) * ((Real.sqrt x * (Real.log T) ^ 2 / T) / (c - σ₀)) ≤
        (2 * (K * C + 1)) * ((Real.sqrt x * (Real.log T) ^ 2 / T) / (c - σ₀)) :=
    mul_le_mul_of_nonneg_right hKCle hshape_nonneg
  calc
    ‖horizIntegrand x T σ‖
        ≤ ((K * (Real.sqrt x / T)) / (c - σ₀)) * (C * (Real.log T) ^ 2) := hmain
    _ = (K * C) * ((Real.sqrt x * (Real.log T) ^ 2 / T) / (c - σ₀)) := hrewrite
    _ ≤ (2 * (K * C + 1)) * ((Real.sqrt x * (Real.log T) ^ 2 / T) / (c - σ₀)) := hgrow
    _ = (2 * (K * C + 1) * (Real.sqrt x * (Real.log T) ^ 2 / T)) / (c - σ₀) := by
        field_simp [hdenσ]

/-- A full complex contour identity immediately yields the real-part
decomposition shape used by the Hadamard large-`T` support lane. -/
theorem integral_sum_real_decomp_from_complex_identity
    (vertIntegrand : ℝ → ℝ → ℝ → ℂ)
    (σ₀ c : ℝ)
    (horizIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hcomplex : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ((shiftedRemainderRe x T : ℂ)) =
        (∫ t in (-T)..T, vertIntegrand x T t) +
          (∫ σ in σ₀..c, horizIntegrand x T σ)) :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      shiftedRemainderRe x T =
        ((∫ t in (-T)..T, vertIntegrand x T t) +
          (∫ σ in σ₀..c, horizIntegrand x T σ)).re := by
  intro x T hx hT
  simpa using congrArg Complex.re (hcomplex x T hx hT)

/-- A continuous vertical contour integrand is automatically interval-integrable
on the compact segment `[-T, T]`. -/
theorem vertical_intervalIntegrable_from_continuous
    (vertIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hcont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      Continuous (fun t => vertIntegrand x T t)) :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun t => vertIntegrand x T t) MeasureTheory.volume (-T) T := by
  intro x T hx hT
  exact (hcont x T hx hT).intervalIntegrable _ _

/-- A continuous horizontal contour integrand is automatically interval-integrable
on the compact segment `[σ₀, c]`. -/
theorem horizontal_intervalIntegrable_from_continuous
    (σ₀ c : ℝ)
    (horizIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hcont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      Continuous (fun σ => horizIntegrand x T σ)) :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun σ => horizIntegrand x T σ) MeasureTheory.volume σ₀ c := by
  intro x T hx hT
  exact (hcont x T hx hT).intervalIntegrable _ _

/-- Reduce the vertical factor-bound hypothesis to a smaller kernel estimate:
it is enough to identify the integrand as a product of a contour kernel with
the pointwise `-ζ'/ζ` term and bound only the kernel. -/
theorem vertical_factor_bound_from_logderiv_kernel
    (vertIntegrand vertKernel : ℝ → ℝ → ℝ → ℂ)
    (sigmaArg tauArg : ℝ → ℝ → ℝ → ℝ)
    (K : ℝ)
    (hrep : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      vertIntegrand x T t =
        vertKernel x T t *
          (-deriv riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I) /
            riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I)))
    (hkernel : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      ‖vertKernel x T t‖ ≤ ((K * (Real.sqrt x * Real.log T / T)) / (2 * T))) :
    ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      ‖vertIntegrand x T t‖ ≤
        ((K * (Real.sqrt x * Real.log T / T)) / (2 * T)) *
          ‖(-deriv riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I) /
            riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I))‖ := by
  intro x T t hx hT ht
  rw [hrep x T t hx hT ht, norm_mul]
  exact mul_le_mul_of_nonneg_right (hkernel x T t hx hT ht) (norm_nonneg _)

/-- Reduce the horizontal factor-bound hypothesis to a smaller kernel estimate:
it is enough to identify the integrand as a product of a contour kernel with
the pointwise `-ζ'/ζ` term and bound only the kernel. -/
theorem horizontal_factor_bound_from_logderiv_kernel
    (σ₀ c : ℝ)
    (horizIntegrand horizKernel : ℝ → ℝ → ℝ → ℂ)
    (K : ℝ)
    (hrep : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      horizIntegrand x T σ =
        horizKernel x T σ *
          (-deriv riemannZeta (↑σ + ↑T * Complex.I) /
            riemannZeta (↑σ + ↑T * Complex.I)))
    (hkernel : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      ‖horizKernel x T σ‖ ≤ ((K * (Real.sqrt x / T)) / (c - σ₀))) :
    ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      ‖horizIntegrand x T σ‖ ≤
        ((K * (Real.sqrt x / T)) / (c - σ₀)) *
          ‖(-deriv riemannZeta (↑σ + ↑T * Complex.I) /
            riemannZeta (↑σ + ↑T * Complex.I))‖ := by
  intro x T σ hx hT hσmem
  rw [hrep x T σ hx hT hσmem, norm_mul]
  exact mul_le_mul_of_nonneg_right (hkernel x T σ hx hT hσmem) (norm_nonneg _)

/-- `ζ` is analytic away from `1`, so its derivative is continuous there. This
is the only analytic input needed to turn explicit product-form contour
integrands into interval-integrable functions. -/
private lemma analyticOn_riemannZeta_ne_one :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_ne
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

private lemma continuousAt_deriv_riemannZeta_ne_one (s : ℂ) (hs : s ≠ 1) :
    ContinuousAt (deriv riemannZeta) s :=
  ((analyticOn_riemannZeta_ne_one s hs).deriv).continuousAt

/-- The vertical contour path automatically avoids the pole at `1` once its
imaginary part is bounded away from `0`. This removes the separate
`path ≠ 1` bookkeeping premise from the support surface. -/
theorem vertical_path_ne_one_from_tau_lower_bound
    (sigmaArg tauArg : ℝ → ℝ → ℝ → ℝ)
    (hτlo : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      2 ≤ |tauArg x T t|) :
    ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I : ℂ) ≠ 1 := by
  intro x T t hx hT ht hEq
  have him : tauArg x T t = 0 := by
    have := congrArg Complex.im hEq
    simpa using this
  have habs : |tauArg x T t| = 0 := by simp [him]
  linarith [hτlo x T t hx hT ht]

/-- The vertical contour integrand is automatically interval-integrable once it
is expressed as a kernel times `-ζ'/ζ` and the kernel/path data are continuous
on the contour segment. This is strictly smaller than assuming continuity of the
full integrand. -/
theorem vertical_intervalIntegrable_from_logderiv_kernel_continuousOn
    (vertIntegrand vertKernel : ℝ → ℝ → ℝ → ℂ)
    (sigmaArg tauArg : ℝ → ℝ → ℝ → ℝ)
    (hrep : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      vertIntegrand x T t =
        vertKernel x T t *
          (-deriv riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I) /
            riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I)))
    (hkernel_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun t => vertKernel x T t) (Set.Icc (-T) T))
    (hsigma_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun t => sigmaArg x T t) (Set.Icc (-T) T))
    (htau_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun t => tauArg x T t) (Set.Icc (-T) T))
    (hτlo : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      2 ≤ |tauArg x T t|)
    (hzeta_ne : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I) ≠ 0) :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun t => vertIntegrand x T t) MeasureTheory.volume (-T) T := by
  intro x T hx hT
  let s : Set ℝ := Set.Icc (-T) T
  let φ : ℝ → ℂ := fun t => ↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I
  have hsigmaC : ContinuousOn (fun t => (↑(sigmaArg x T t) : ℂ)) s := by
    exact (Complex.continuous_ofReal.continuousOn).comp (hsigma_cont x T hx hT)
      (by intro t ht; exact Set.mem_univ _)
  have htauC : ContinuousOn (fun t => (↑(tauArg x T t) : ℂ)) s := by
    exact (Complex.continuous_ofReal.continuousOn).comp (htau_cont x T hx hT)
      (by intro t ht; exact Set.mem_univ _)
  have hφ : ContinuousOn φ s := by
    exact hsigmaC.add (htauC.mul continuousOn_const)
  have hmaps : Set.MapsTo φ s {z : ℂ | z ≠ 1} := by
    intro t ht
    exact vertical_path_ne_one_from_tau_lower_bound sigmaArg tauArg hτlo x T t hx hT ht
  have hnum0 : ContinuousOn (deriv riemannZeta) {z : ℂ | z ≠ 1} := by
    intro z hz
    exact (continuousAt_deriv_riemannZeta_ne_one z hz).continuousWithinAt
  have hden0 : ContinuousOn riemannZeta {z : ℂ | z ≠ 1} := by
    intro z hz
    exact (differentiableAt_riemannZeta hz).continuousAt.continuousWithinAt
  have hnum : ContinuousOn (fun t => deriv riemannZeta (φ t)) s :=
    hnum0.comp hφ hmaps
  have hden : ContinuousOn (fun t => riemannZeta (φ t)) s :=
    hden0.comp hφ hmaps
  have hquot :
      ContinuousOn (fun t => -deriv riemannZeta (φ t) / riemannZeta (φ t)) s := by
    exact (hnum.neg).div hden (fun t ht => hzeta_ne x T t hx hT ht)
  have hprod :
      ContinuousOn
        (fun t => vertKernel x T t *
          (-deriv riemannZeta (φ t) / riemannZeta (φ t))) s :=
    (hkernel_cont x T hx hT).mul hquot
  have hint :
      ContinuousOn (fun t => vertIntegrand x T t) s := by
    refine hprod.congr ?_
    intro t ht
    exact hrep x T t hx hT ht
  have hle : -T ≤ T := by linarith
  have hint' : ContinuousOn (fun t => vertIntegrand x T t) (Set.uIcc (-T) T) := by
    simpa [s, Set.uIcc_of_le hle] using hint
  exact hint'.intervalIntegrable

/-- The horizontal contour integrand is automatically interval-integrable once
it is expressed as a kernel times `-ζ'/ζ` and the kernel is continuous on the
horizontal segment. The path itself is explicit, so only nonvanishing of `ζ`
along that segment remains to check. -/
theorem horizontal_intervalIntegrable_from_logderiv_kernel_continuousOn
    (σ₀ c : ℝ) (hσc : σ₀ < c)
    (horizIntegrand horizKernel : ℝ → ℝ → ℝ → ℂ)
    (hrep : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      horizIntegrand x T σ =
        horizKernel x T σ *
          (-deriv riemannZeta (↑σ + ↑T * Complex.I) /
            riemannZeta (↑σ + ↑T * Complex.I)))
    (hkernel_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun σ => horizKernel x T σ) (Set.Icc σ₀ c))
    (hzeta_ne : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      riemannZeta (↑σ + ↑T * Complex.I) ≠ 0) :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun σ => horizIntegrand x T σ) MeasureTheory.volume σ₀ c := by
  intro x T hx hT
  let s : Set ℝ := Set.Icc σ₀ c
  let φ : ℝ → ℂ := fun σ => ↑σ + ↑T * Complex.I
  have hφ : ContinuousOn φ s := by
    simpa [φ] using (Complex.continuous_ofReal.continuousOn.add continuousOn_const)
  have hmaps : Set.MapsTo φ s {z : ℂ | z ≠ 1} := by
    intro σ hσ hEq
    have him := congrArg Complex.im hEq
    simp [φ] at him
    linarith
  have hnum0 : ContinuousOn (deriv riemannZeta) {z : ℂ | z ≠ 1} := by
    intro z hz
    exact (continuousAt_deriv_riemannZeta_ne_one z hz).continuousWithinAt
  have hden0 : ContinuousOn riemannZeta {z : ℂ | z ≠ 1} := by
    intro z hz
    exact (differentiableAt_riemannZeta hz).continuousAt.continuousWithinAt
  have hnum : ContinuousOn (fun σ => deriv riemannZeta (φ σ)) s :=
    hnum0.comp hφ hmaps
  have hden : ContinuousOn (fun σ => riemannZeta (φ σ)) s :=
    hden0.comp hφ hmaps
  have hquot :
      ContinuousOn (fun σ => -deriv riemannZeta (φ σ) / riemannZeta (φ σ)) s := by
    exact (hnum.neg).div hden (fun σ hσ => hzeta_ne x T σ hx hT (by simpa [s] using hσ))
  have hprod :
      ContinuousOn
        (fun σ => horizKernel x T σ *
          (-deriv riemannZeta (φ σ) / riemannZeta (φ σ))) s :=
    (hkernel_cont x T hx hT).mul hquot
  have hint :
      ContinuousOn (fun σ => horizIntegrand x T σ) s := by
    refine hprod.congr ?_
    intro σ hσ
    exact hrep x T σ hx hT hσ
  have hint' : ContinuousOn (fun σ => horizIntegrand x T σ) (Set.uIcc σ₀ c) := by
    simpa [s, Set.uIcc_of_le hσc.le] using hint
  exact hint'.intervalIntegrable

/-- Direct support reduction for the remaining Hadamard factor-bound leaf:
from a full complex contour identity, continuity of the contour integrands, and
kernel estimates for the two product-form contour integrands, the exact
factor-bound existential package follows automatically. -/
theorem factor_bound_complex_integrands_from_complex_identity_and_kernel_bounds
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp)
    (vertIntegrand vertKernel : ℝ → ℝ → ℝ → ℂ)
    (sigmaArg tauArg : ℝ → ℝ → ℝ → ℝ)
    (Kvert : ℝ) (hKvert : 0 ≤ Kvert)
    (hvert_rep : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      vertIntegrand x T t =
        vertKernel x T t *
          (-deriv riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I) /
            riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I)))
    (hvert_kernel : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      ‖vertKernel x T t‖ ≤
        ((Kvert * (Real.sqrt x * Real.log T / T)) / (2 * T)))
    (hσ : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      1 / 2 ≤ sigmaArg x T t ∧ sigmaArg x T t ≤ 2)
    (hτlo : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      2 ≤ |tauArg x T t|)
    (hτhi : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      |tauArg x T t| ≤ T)
    (σ₀ c : ℝ) (hσ0 : 1 / 2 ≤ σ₀) (hc : c ≤ 2) (hσc : σ₀ < c)
    (horizIntegrand horizKernel : ℝ → ℝ → ℝ → ℂ)
    (Khoriz : ℝ) (hKhoriz : 0 ≤ Khoriz)
    (hhoriz_rep : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      horizIntegrand x T σ =
        horizKernel x T σ *
          (-deriv riemannZeta (↑σ + ↑T * Complex.I) /
            riemannZeta (↑σ + ↑T * Complex.I)))
    (hhoriz_kernel : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      ‖horizKernel x T σ‖ ≤
        ((Khoriz * (Real.sqrt x / T)) / (c - σ₀)))
    (hcomplex : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ((shiftedRemainderRe x T : ℂ)) =
        (∫ t in (-T)..T, vertIntegrand x T t) +
          (∫ σ in σ₀..c, horizIntegrand x T σ))
    (hvert_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      Continuous (fun t => vertIntegrand x T t))
    (hhoriz_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      Continuous (fun σ => horizIntegrand x T σ)) :
    ∃ (_h_logderiv : ZetaLogDerivPointwiseLargeTHyp)
      (vertIntegrand' : ℝ → ℝ → ℝ → ℂ)
      (sigmaArg' tauArg' : ℝ → ℝ → ℝ → ℝ)
      (Kvert' : ℝ)
      (σ₀' c' : ℝ)
      (horizIntegrand' : ℝ → ℝ → ℝ → ℂ)
      (Khoriz' : ℝ),
      0 ≤ Kvert' ∧
      0 ≤ Khoriz' ∧
      1 / 2 ≤ σ₀' ∧
      c' ≤ 2 ∧
      σ₀' < c' ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        shiftedRemainderRe x T =
          ((∫ t in (-T)..T, vertIntegrand' x T t) +
            (∫ σ in σ₀'..c', horizIntegrand' x T σ)).re) ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        IntervalIntegrable (fun t => vertIntegrand' x T t) MeasureTheory.volume (-T) T) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand' x T t‖ ≤
          ((Kvert' * (Real.sqrt x * Real.log T / T)) / (2 * T)) *
            ‖(-deriv riemannZeta (↑(sigmaArg' x T t) + ↑(tauArg' x T t) * Complex.I) /
              riemannZeta (↑(sigmaArg' x T t) + ↑(tauArg' x T t) * Complex.I))‖) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        1 / 2 ≤ sigmaArg' x T t ∧ sigmaArg' x T t ≤ 2) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        2 ≤ |tauArg' x T t|) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        |tauArg' x T t| ≤ T) ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        IntervalIntegrable (fun σ => horizIntegrand' x T σ) MeasureTheory.volume σ₀' c') ∧
      (∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀' c' →
        ‖horizIntegrand' x T σ‖ ≤
          ((Khoriz' * (Real.sqrt x / T)) / (c' - σ₀')) *
            ‖(-deriv riemannZeta (↑σ + ↑T * Complex.I) /
              riemannZeta (↑σ + ↑T * Complex.I))‖) := by
  refine ⟨h_logderiv, vertIntegrand, sigmaArg, tauArg, Kvert, σ₀, c,
    horizIntegrand, Khoriz, hKvert, hKhoriz, hσ0, hc, hσc, ?_, ?_, ?_, hσ,
    hτlo, hτhi, ?_, ?_⟩
  · exact integral_sum_real_decomp_from_complex_identity
      vertIntegrand σ₀ c horizIntegrand hcomplex
  · exact vertical_intervalIntegrable_from_continuous vertIntegrand hvert_cont
  · exact vertical_factor_bound_from_logderiv_kernel
      vertIntegrand vertKernel sigmaArg tauArg Kvert hvert_rep hvert_kernel
  · exact horizontal_intervalIntegrable_from_continuous σ₀ c horizIntegrand hhoriz_cont
  · exact horizontal_factor_bound_from_logderiv_kernel
      σ₀ c horizIntegrand horizKernel Khoriz hhoriz_rep hhoriz_kernel

/-- Strictly smaller wrapper for the current Hadamard kernel-bound leaf: it is
enough to supply the full complex contour identity, product-form identities,
kernel bounds, and interval-local continuity/nonvanishing data for the kernels
and the `-ζ'/ζ` factors. The support cone reconstructs the required
interval-integrability premises automatically. -/
theorem factor_bound_complex_integrands_from_complex_identity_and_kernel_continuity
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp)
    (vertIntegrand vertKernel : ℝ → ℝ → ℝ → ℂ)
    (sigmaArg tauArg : ℝ → ℝ → ℝ → ℝ)
    (Kvert : ℝ) (hKvert : 0 ≤ Kvert)
    (hvert_rep : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      vertIntegrand x T t =
        vertKernel x T t *
          (-deriv riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I) /
            riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I)))
    (hvert_kernel : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      ‖vertKernel x T t‖ ≤
        ((Kvert * (Real.sqrt x * Real.log T / T)) / (2 * T)))
    (hvert_kernel_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun t => vertKernel x T t) (Set.Icc (-T) T))
    (hsigma_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun t => sigmaArg x T t) (Set.Icc (-T) T))
    (htau_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun t => tauArg x T t) (Set.Icc (-T) T))
    (hvert_zeta_ne : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I) ≠ 0)
    (hσ : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      1 / 2 ≤ sigmaArg x T t ∧ sigmaArg x T t ≤ 2)
    (hτlo : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      2 ≤ |tauArg x T t|)
    (hτhi : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      |tauArg x T t| ≤ T)
    (σ₀ c : ℝ) (hσ0 : 1 / 2 ≤ σ₀) (hc : c ≤ 2) (hσc : σ₀ < c)
    (horizIntegrand horizKernel : ℝ → ℝ → ℝ → ℂ)
    (Khoriz : ℝ) (hKhoriz : 0 ≤ Khoriz)
    (hhoriz_rep : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      horizIntegrand x T σ =
        horizKernel x T σ *
          (-deriv riemannZeta (↑σ + ↑T * Complex.I) /
            riemannZeta (↑σ + ↑T * Complex.I)))
    (hhoriz_kernel : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      ‖horizKernel x T σ‖ ≤
        ((Khoriz * (Real.sqrt x / T)) / (c - σ₀)))
    (hhoriz_kernel_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun σ => horizKernel x T σ) (Set.Icc σ₀ c))
    (hhoriz_zeta_ne : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      riemannZeta (↑σ + ↑T * Complex.I) ≠ 0)
    (hcomplex : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ((shiftedRemainderRe x T : ℂ)) =
        (∫ t in (-T)..T, vertIntegrand x T t) +
          (∫ σ in σ₀..c, horizIntegrand x T σ)) :
    ∃ (_h_logderiv : ZetaLogDerivPointwiseLargeTHyp)
      (vertIntegrand' : ℝ → ℝ → ℝ → ℂ)
      (sigmaArg' tauArg' : ℝ → ℝ → ℝ → ℝ)
      (Kvert' : ℝ)
      (σ₀' c' : ℝ)
      (horizIntegrand' : ℝ → ℝ → ℝ → ℂ)
      (Khoriz' : ℝ),
      0 ≤ Kvert' ∧
      0 ≤ Khoriz' ∧
      1 / 2 ≤ σ₀' ∧
      c' ≤ 2 ∧
      σ₀' < c' ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        shiftedRemainderRe x T =
          ((∫ t in (-T)..T, vertIntegrand' x T t) +
            (∫ σ in σ₀'..c', horizIntegrand' x T σ)).re) ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        IntervalIntegrable (fun t => vertIntegrand' x T t) MeasureTheory.volume (-T) T) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand' x T t‖ ≤
          ((Kvert' * (Real.sqrt x * Real.log T / T)) / (2 * T)) *
            ‖(-deriv riemannZeta (↑(sigmaArg' x T t) + ↑(tauArg' x T t) * Complex.I) /
              riemannZeta (↑(sigmaArg' x T t) + ↑(tauArg' x T t) * Complex.I))‖) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        1 / 2 ≤ sigmaArg' x T t ∧ sigmaArg' x T t ≤ 2) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        2 ≤ |tauArg' x T t|) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        |tauArg' x T t| ≤ T) ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        IntervalIntegrable (fun σ => horizIntegrand' x T σ) MeasureTheory.volume σ₀' c') ∧
      (∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀' c' →
        ‖horizIntegrand' x T σ‖ ≤
          ((Khoriz' * (Real.sqrt x / T)) / (c' - σ₀')) *
            ‖(-deriv riemannZeta (↑σ + ↑T * Complex.I) /
              riemannZeta (↑σ + ↑T * Complex.I))‖) := by
  refine ⟨h_logderiv, vertIntegrand, sigmaArg, tauArg, Kvert, σ₀, c, horizIntegrand,
    Khoriz, hKvert, hKhoriz, hσ0, hc, hσc, ?_, ?_, ?_, hσ, hτlo, hτhi, ?_, ?_⟩
  · exact integral_sum_real_decomp_from_complex_identity
      vertIntegrand σ₀ c horizIntegrand hcomplex
  · exact vertical_intervalIntegrable_from_logderiv_kernel_continuousOn
      vertIntegrand vertKernel sigmaArg tauArg hvert_rep
      hvert_kernel_cont hsigma_cont htau_cont hτlo hvert_zeta_ne
  · exact vertical_factor_bound_from_logderiv_kernel
      vertIntegrand vertKernel sigmaArg tauArg Kvert hvert_rep hvert_kernel
  · exact horizontal_intervalIntegrable_from_logderiv_kernel_continuousOn
      σ₀ c hσc horizIntegrand horizKernel hhoriz_rep hhoriz_kernel_cont hhoriz_zeta_ne
  · exact horizontal_factor_bound_from_logderiv_kernel
      σ₀ c horizIntegrand horizKernel Khoriz hhoriz_rep hhoriz_kernel

/-- Standard-contour specialization of the kernel-bounds support theorem:
for the canonical Hadamard contour `Re s = 1 / 2`, `σ ∈ [1 / 2, 2]`, the
generic strip bookkeeping disappears and the factor-bound package follows from
the concrete standard-contour data alone. -/
theorem standard_contour_factor_bound_complex_integrands_from_complex_identity_and_kernel_bounds
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp)
    (vertIntegrand vertKernel : ℝ → ℝ → ℝ → ℂ)
    (tauArg : ℝ → ℝ → ℝ → ℝ)
    (Kvert : ℝ) (hKvert : 0 ≤ Kvert)
    (hvert_rep : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      vertIntegrand x T t =
        vertKernel x T t *
          (-deriv riemannZeta (↑((1 / 2 : ℝ)) + ↑(tauArg x T t) * Complex.I) /
            riemannZeta (↑((1 / 2 : ℝ)) + ↑(tauArg x T t) * Complex.I)))
    (hvert_kernel : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      ‖vertKernel x T t‖ ≤
        ((Kvert * (Real.sqrt x * Real.log T / T)) / (2 * T)))
    (hτlo : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      2 ≤ |tauArg x T t|)
    (hτhi : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      |tauArg x T t| ≤ T)
    (horizIntegrand horizKernel : ℝ → ℝ → ℝ → ℂ)
    (Khoriz : ℝ) (hKhoriz : 0 ≤ Khoriz)
    (hhoriz_rep : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc (1 / 2 : ℝ) 2 →
      horizIntegrand x T σ =
        horizKernel x T σ *
          (-deriv riemannZeta (↑σ + ↑T * Complex.I) /
            riemannZeta (↑σ + ↑T * Complex.I)))
    (hhoriz_kernel : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc (1 / 2 : ℝ) 2 →
      ‖horizKernel x T σ‖ ≤
        ((Khoriz * (Real.sqrt x / T)) / ((2 : ℝ) - (1 / 2 : ℝ))))
    (hcomplex : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ((shiftedRemainderRe x T : ℂ)) =
        (∫ t in (-T)..T, vertIntegrand x T t) +
          (∫ σ in (1 / 2 : ℝ)..2, horizIntegrand x T σ))
    (hvert_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      Continuous (fun t => vertIntegrand x T t))
    (hhoriz_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      Continuous (fun σ => horizIntegrand x T σ)) :
    ∃ (_h_logderiv : ZetaLogDerivPointwiseLargeTHyp)
      (vertIntegrand' : ℝ → ℝ → ℝ → ℂ)
      (sigmaArg' tauArg' : ℝ → ℝ → ℝ → ℝ)
      (Kvert' : ℝ)
      (σ₀' c' : ℝ)
      (horizIntegrand' : ℝ → ℝ → ℝ → ℂ)
      (Khoriz' : ℝ),
      0 ≤ Kvert' ∧
      0 ≤ Khoriz' ∧
      1 / 2 ≤ σ₀' ∧
      c' ≤ 2 ∧
      σ₀' < c' ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        shiftedRemainderRe x T =
          ((∫ t in (-T)..T, vertIntegrand' x T t) +
            (∫ σ in σ₀'..c', horizIntegrand' x T σ)).re) ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        IntervalIntegrable (fun t => vertIntegrand' x T t) MeasureTheory.volume (-T) T) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand' x T t‖ ≤
          ((Kvert' * (Real.sqrt x * Real.log T / T)) / (2 * T)) *
            ‖(-deriv riemannZeta (↑(sigmaArg' x T t) + ↑(tauArg' x T t) * Complex.I) /
              riemannZeta (↑(sigmaArg' x T t) + ↑(tauArg' x T t) * Complex.I))‖) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        1 / 2 ≤ sigmaArg' x T t ∧ sigmaArg' x T t ≤ 2) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        2 ≤ |tauArg' x T t|) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        |tauArg' x T t| ≤ T) ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        IntervalIntegrable (fun σ => horizIntegrand' x T σ) MeasureTheory.volume σ₀' c') ∧
      (∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀' c' →
        ‖horizIntegrand' x T σ‖ ≤
          ((Khoriz' * (Real.sqrt x / T)) / (c' - σ₀')) *
            ‖(-deriv riemannZeta (↑σ + ↑T * Complex.I) /
              riemannZeta (↑σ + ↑T * Complex.I))‖) := by
  let sigmaArg : ℝ → ℝ → ℝ → ℝ := fun _ _ _ => (1 / 2 : ℝ)
  let σ₀ : ℝ := 1 / 2
  let c : ℝ := 2
  exact factor_bound_complex_integrands_from_complex_identity_and_kernel_bounds
      h_logderiv
      vertIntegrand vertKernel sigmaArg tauArg Kvert hKvert
      (by
        intro x T t hx hT ht
        simpa [sigmaArg] using hvert_rep x T t hx hT ht)
      hvert_kernel
      (by
        intro x T t hx hT ht
        constructor <;> norm_num [sigmaArg])
      hτlo hτhi
      σ₀ c (by norm_num [σ₀]) (by norm_num [c]) (by norm_num [σ₀, c])
      horizIntegrand horizKernel Khoriz hKhoriz
      (by
        intro x T σ hx hT hσmem
        simpa [σ₀, c] using hhoriz_rep x T σ hx hT hσmem)
      (by
        intro x T σ hx hT hσmem
        simpa [σ₀, c] using hhoriz_kernel x T σ hx hT hσmem)
      (by
        intro x T hx hT
        simpa [σ₀, c] using hcomplex x T hx hT)
      hvert_cont
      (by
        intro x T hx hT
        simpa [σ₀, c] using hhoriz_cont x T hx hT)

/-- Standard-contour specialization of the kernel-continuity support theorem:
for the canonical Hadamard contour `Re s = 1 / 2`, `σ ∈ [1 / 2, 2]`, the
generic strip bookkeeping disappears and only the concrete vertical/horizontal
kernel data remain. -/
theorem standard_contour_factor_bound_complex_integrands_from_complex_identity_and_kernel_continuity
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp)
    (vertIntegrand vertKernel : ℝ → ℝ → ℝ → ℂ)
    (tauArg : ℝ → ℝ → ℝ → ℝ)
    (Kvert : ℝ) (hKvert : 0 ≤ Kvert)
    (hvert_rep : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      vertIntegrand x T t =
        vertKernel x T t *
          (-deriv riemannZeta (↑((1 / 2 : ℝ)) + ↑(tauArg x T t) * Complex.I) /
            riemannZeta (↑((1 / 2 : ℝ)) + ↑(tauArg x T t) * Complex.I)))
    (hvert_kernel : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      ‖vertKernel x T t‖ ≤
        ((Kvert * (Real.sqrt x * Real.log T / T)) / (2 * T)))
    (hvert_kernel_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun t => vertKernel x T t) (Set.Icc (-T) T))
    (htau_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun t => tauArg x T t) (Set.Icc (-T) T))
    (hvert_zeta_ne : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      riemannZeta (↑((1 / 2 : ℝ)) + ↑(tauArg x T t) * Complex.I) ≠ 0)
    (hτlo : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      2 ≤ |tauArg x T t|)
    (hτhi : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      |tauArg x T t| ≤ T)
    (horizIntegrand horizKernel : ℝ → ℝ → ℝ → ℂ)
    (Khoriz : ℝ) (hKhoriz : 0 ≤ Khoriz)
    (hhoriz_rep : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc (1 / 2 : ℝ) 2 →
      horizIntegrand x T σ =
        horizKernel x T σ *
          (-deriv riemannZeta (↑σ + ↑T * Complex.I) /
            riemannZeta (↑σ + ↑T * Complex.I)))
    (hhoriz_kernel : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc (1 / 2 : ℝ) 2 →
      ‖horizKernel x T σ‖ ≤
        ((Khoriz * (Real.sqrt x / T)) / ((2 : ℝ) - (1 / 2 : ℝ))))
    (hhoriz_kernel_cont : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ContinuousOn (fun σ => horizKernel x T σ) (Set.Icc (1 / 2 : ℝ) 2))
    (hhoriz_zeta_ne : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc (1 / 2 : ℝ) 2 →
      riemannZeta (↑σ + ↑T * Complex.I) ≠ 0)
    (hcomplex : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ((shiftedRemainderRe x T : ℂ)) =
        (∫ t in (-T)..T, vertIntegrand x T t) +
          (∫ σ in (1 / 2 : ℝ)..2, horizIntegrand x T σ)) :
    ∃ (_h_logderiv : ZetaLogDerivPointwiseLargeTHyp)
      (vertIntegrand' : ℝ → ℝ → ℝ → ℂ)
      (tauArg' : ℝ → ℝ → ℝ → ℝ)
      (Kvert' : ℝ)
      (horizIntegrand' : ℝ → ℝ → ℝ → ℂ)
      (Khoriz' : ℝ),
      0 ≤ Kvert' ∧
      0 ≤ Khoriz' ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        shiftedRemainderRe x T =
          ((∫ t in (-T)..T, vertIntegrand' x T t) +
            (∫ σ in (1 / 2 : ℝ)..2, horizIntegrand' x T σ)).re) ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        IntervalIntegrable (fun t => vertIntegrand' x T t) MeasureTheory.volume (-T) T) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand' x T t‖ ≤
          ((Kvert' * (Real.sqrt x * Real.log T / T)) / (2 * T)) *
            ‖(-deriv riemannZeta (↑((1 / 2 : ℝ)) + ↑(tauArg' x T t) * Complex.I) /
              riemannZeta (↑((1 / 2 : ℝ)) + ↑(tauArg' x T t) * Complex.I))‖) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        2 ≤ |tauArg' x T t|) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        |tauArg' x T t| ≤ T) ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        IntervalIntegrable (fun σ => horizIntegrand' x T σ) MeasureTheory.volume (1 / 2 : ℝ) 2) ∧
      (∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc (1 / 2 : ℝ) 2 →
        ‖horizIntegrand' x T σ‖ ≤
          ((Khoriz' * (Real.sqrt x / T)) / ((2 : ℝ) - (1 / 2 : ℝ))) *
            ‖(-deriv riemannZeta (↑σ + ↑T * Complex.I) /
              riemannZeta (↑σ + ↑T * Complex.I))‖) := by
  let sigmaArg : ℝ → ℝ → ℝ → ℝ := fun _ _ _ => (1 / 2 : ℝ)
  refine ⟨h_logderiv, vertIntegrand, tauArg, Kvert, horizIntegrand, Khoriz,
    hKvert, hKhoriz, ?_, ?_, ?_, hτlo, hτhi, ?_, ?_⟩
  · exact integral_sum_real_decomp_from_complex_identity
      vertIntegrand (1 / 2 : ℝ) 2 horizIntegrand hcomplex
  · exact vertical_intervalIntegrable_from_logderiv_kernel_continuousOn
      vertIntegrand vertKernel sigmaArg tauArg
      (by
        intro x T t hx hT ht
        simpa [sigmaArg] using hvert_rep x T t hx hT ht)
      hvert_kernel_cont
      (by
        intro x T hx hT
        simpa [sigmaArg] using (continuousOn_const :
          ContinuousOn (fun t : ℝ => (1 / 2 : ℝ)) (Set.Icc (-T) T)))
      htau_cont hτlo
      (by
        intro x T t hx hT ht
        simpa [sigmaArg] using hvert_zeta_ne x T t hx hT ht)
  · exact vertical_factor_bound_from_logderiv_kernel
      vertIntegrand vertKernel sigmaArg tauArg Kvert
      (by
        intro x T t hx hT ht
        simpa [sigmaArg] using hvert_rep x T t hx hT ht)
      hvert_kernel
  · exact horizontal_intervalIntegrable_from_logderiv_kernel_continuousOn
      (1 / 2 : ℝ) 2 (by norm_num)
      horizIntegrand horizKernel hhoriz_rep hhoriz_kernel_cont hhoriz_zeta_ne
  · exact horizontal_factor_bound_from_logderiv_kernel
      (1 / 2 : ℝ) 2 horizIntegrand horizKernel Khoriz hhoriz_rep hhoriz_kernel

/-- Direct support reduction for the remaining Hadamard normalized-integrand
leaf: once the shifted remainder is identified with the sum of one vertical and
one horizontal contour integral, integrability is known, and each integrand is
controlled by a smaller geometric-factor bound against the pointwise
`-ζ'/ζ` input, the exact existential package of normalized majorants follows
automatically. -/
theorem normalized_complex_integrands_from_logderiv_factors
    (vertIntegrand : ℝ → ℝ → ℝ → ℂ)
    (sigmaArg tauArg : ℝ → ℝ → ℝ → ℝ)
    (Kv : ℝ) (hKv : 0 ≤ Kv)
    (hvert_factor : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      ‖vertIntegrand x T t‖ ≤
        ((Kv * (Real.sqrt x * Real.log T / T)) / (2 * T)) *
          ‖(-deriv riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I) /
            riemannZeta (↑(sigmaArg x T t) + ↑(tauArg x T t) * Complex.I))‖)
    (hσ : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      1 / 2 ≤ sigmaArg x T t ∧ sigmaArg x T t ≤ 2)
    (hτlo : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      2 ≤ |tauArg x T t|)
    (hτhi : ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
      |tauArg x T t| ≤ T)
    (σ₀ c : ℝ) (hσ0 : 1 / 2 ≤ σ₀) (hc : c ≤ 2) (hσc : σ₀ < c)
    (horizIntegrand : ℝ → ℝ → ℝ → ℂ)
    (Kh : ℝ) (hKh : 0 ≤ Kh)
    (hhoriz_factor : ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
      ‖horizIntegrand x T σ‖ ≤
        ((Kh * (Real.sqrt x / T)) / (c - σ₀)) *
          ‖(-deriv riemannZeta (↑σ + ↑T * Complex.I) /
            riemannZeta (↑σ + ↑T * Complex.I))‖)
    (hdecomp : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      shiftedRemainderRe x T =
        ((∫ t in (-T)..T, vertIntegrand x T t) +
          (∫ σ in σ₀..c, horizIntegrand x T σ)).re)
    (hvert_int : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun t => vertIntegrand x T t) MeasureTheory.volume (-T) T)
    (hhoriz_int : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun σ => horizIntegrand x T σ) MeasureTheory.volume σ₀ c)
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ P : ℝ, P > (0 : ℝ) ∧
      ∃ vertIntegrand' : ℝ → ℝ → ℝ → ℂ,
      ∃ σ₀' c' : ℝ,
      ∃ horizIntegrand' : ℝ → ℝ → ℝ → ℂ,
      σ₀' < c' ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        shiftedRemainderRe x T =
          ((∫ t in (-T)..T, vertIntegrand' x T t) +
            (∫ σ in σ₀'..c', horizIntegrand' x T σ)).re) ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        IntervalIntegrable (fun t => vertIntegrand' x T t) MeasureTheory.volume (-T) T) ∧
      (∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand' x T t‖ ≤
          (P * (Real.sqrt x * (Real.log T) ^ 3 / T)) / (2 * T)) ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        IntervalIntegrable (fun σ => horizIntegrand' x T σ) MeasureTheory.volume σ₀' c') ∧
      (∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀' c' →
        ‖horizIntegrand' x T σ‖ ≤
          (2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)) / (c' - σ₀')) := by
  obtain ⟨Pv, hPv, hvert_pointwise⟩ :=
    vertical_normalized_pointwise_from_logderiv_factor
      vertIntegrand sigmaArg tauArg Kv hKv hvert_factor hσ hτlo hτhi h_logderiv
  obtain ⟨Ph, hPh, hhoriz_pointwise⟩ :=
    horizontal_normalized_pointwise_from_logderiv_factor
      σ₀ c hσ0 hc hσc horizIntegrand Kh hKh hhoriz_factor h_logderiv
  refine ⟨max Pv Ph, lt_of_lt_of_le hPv (le_max_left _ _), vertIntegrand, σ₀, c,
    horizIntegrand, hσc, hdecomp, hvert_int, ?_, hhoriz_int, ?_⟩
  · intro x T t hx hT ht
    have hT_pos : 0 < T := by linarith
    have hshape_nonneg : 0 ≤ Real.sqrt x * (Real.log T) ^ 3 / T := by
      have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT_nonneg 3))
        hT_pos.le
    have hnum :
        Pv * (Real.sqrt x * (Real.log T) ^ 3 / T) ≤
          max Pv Ph * (Real.sqrt x * (Real.log T) ^ 3 / T) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hshape_nonneg
    have hden : 0 ≤ (2 : ℝ) * T := by nlinarith
    calc
      ‖vertIntegrand x T t‖
          ≤ (Pv * (Real.sqrt x * (Real.log T) ^ 3 / T)) / (2 * T) :=
            hvert_pointwise x T t hx hT ht
      _ ≤ (max Pv Ph * (Real.sqrt x * (Real.log T) ^ 3 / T)) / (2 * T) :=
            div_le_div_of_nonneg_right hnum hden
  · intro x T σ hx hT hσmem
    have hT_pos : 0 < T := by linarith
    have hshape_nonneg : 0 ≤ Real.sqrt x * (Real.log T) ^ 2 / T := by
      have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT_nonneg 2))
        hT_pos.le
    have hnum :
        2 * Ph * (Real.sqrt x * (Real.log T) ^ 2 / T) ≤
          2 * max Pv Ph * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
      nlinarith [le_max_right Pv Ph, hshape_nonneg]
    have hden : 0 ≤ c - σ₀ := by linarith
    calc
      ‖horizIntegrand x T σ‖
          ≤ (2 * Ph * (Real.sqrt x * (Real.log T) ^ 2 / T)) / (c - σ₀) :=
            hhoriz_pointwise x T σ hx hT hσmem
      _ ≤ (2 * max Pv Ph * (Real.sqrt x * (Real.log T) ^ 2 / T)) / (c - σ₀) :=
            div_le_div_of_nonneg_right hnum hden

/-- Smaller vertical support theorem: if the complex vertical piece is defined
directly as the corresponding contour integral, only integrability and the
normalized pointwise majorant remain to prove its large-`T` norm bound. -/
theorem vertical_integral_complex_bound_from_normalized_integrand
    (vertIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hint : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun t => vertIntegrand x T t) MeasureTheory.volume (-T) T)
    (hpointwise : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand x T t‖ ≤
          (P * (Real.sqrt x * (Real.log T) ^ 3 / T)) / (2 * T)) :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        ‖∫ t in (-T)..T, vertIntegrand x T t‖ ≤
          P * (Real.sqrt x * (Real.log T) ^ 3 / T) := by
  exact
    vertical_complex_bound_from_normalized_integrand
      (fun x T => ∫ t in (-T)..T, vertIntegrand x T t)
      vertIntegrand
      (fun _ _ _ _ => rfl)
      hint
      hpointwise

/-- Smaller horizontal support theorem: if the complex horizontal piece is
defined directly as the corresponding contour integral, only integrability and
the normalized pointwise majorant remain to prove its large-`T` norm bound. -/
theorem horizontal_integral_complex_bound_from_normalized_integrand
    (σ₀ c : ℝ) (hσc : σ₀ < c)
    (horizIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hint : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun σ => horizIntegrand x T σ) MeasureTheory.volume σ₀ c)
    (hpointwise : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
        ‖horizIntegrand x T σ‖ ≤
          (2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)) / (c - σ₀)) :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        ‖∫ σ in σ₀..c, horizIntegrand x T σ‖ ≤
          2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  exact
    horizontal_complex_bound_from_normalized_integrand
      σ₀ c hσc
      (fun x T => ∫ σ in σ₀..c, horizIntegrand x T σ)
      horizIntegrand
      (fun _ _ _ _ => rfl)
      hint
      hpointwise

/-- Direct cycle-free closure for the Hadamard large-`T` piece leaf: once the
shifted remainder is decomposed into concrete vertical and horizontal real
pieces, and each piece is the real part of a contour integral with the
normalized pointwise majorant expected by the two theorems above, the full
existential contour-piece bound follows automatically. -/
theorem contour_piece_bounds_from_normalized_complex_integrands
    (vertRe horizRe : ℝ → ℝ → ℝ)
    (vertC horizC : ℝ → ℝ → ℂ)
    (hdecomp : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      shiftedRemainderRe x T = vertRe x T + horizRe x T)
    (hvert_real : ∀ x T : ℝ, vertRe x T = (vertC x T).re)
    (hhoriz_real : ∀ x T : ℝ, horizRe x T = (horizC x T).re)
    (vertIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hvert_rep : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      vertC x T = ∫ t in (-T)..T, vertIntegrand x T t)
    (hvert_int : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun t => vertIntegrand x T t) MeasureTheory.volume (-T) T)
    (hvert_pointwise : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand x T t‖ ≤
          (P * (Real.sqrt x * (Real.log T) ^ 3 / T)) / (2 * T))
    (σ₀ c : ℝ) (hσc : σ₀ < c)
    (horizIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hhoriz_rep : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      horizC x T = ∫ σ in σ₀..c, horizIntegrand x T σ)
    (hhoriz_int : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun σ => horizIntegrand x T σ) MeasureTheory.volume σ₀ c)
    (hhoriz_pointwise : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
        ‖horizIntegrand x T σ‖ ≤
          (2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)) / (c - σ₀))
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ∃ vert horiz : ℝ,
        shiftedRemainderRe x T = vert + horiz ∧
        |vert| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) ∧
        |horiz| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  have hvert_bound :
      ZetaLogDerivPointwiseLargeTHyp →
        ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
          |vertRe x T| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) := by
    exact
      vertical_bound_from_complex_piece vertRe vertC hvert_real
        (vertical_complex_bound_from_normalized_integrand
          vertC vertIntegrand hvert_rep hvert_int hvert_pointwise)
  have hhoriz_bound :
      ZetaLogDerivPointwiseLargeTHyp →
        ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
          |horizRe x T| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
    exact
      horizontal_bound_from_complex_piece horizRe horizC hhoriz_real
        (horizontal_complex_bound_from_normalized_integrand
          σ₀ c hσc horizC horizIntegrand hhoriz_rep hhoriz_int hhoriz_pointwise)
  obtain ⟨Pv, hPv, hvert'⟩ := hvert_bound h_logderiv
  obtain ⟨Ph, hPh, hhoriz'⟩ := hhoriz_bound h_logderiv
  refine ⟨max Pv Ph, lt_of_lt_of_le hPv (le_max_left _ _), ?_⟩
  intro x T hx hT
  refine ⟨vertRe x T, horizRe x T, hdecomp x T hx hT, ?_, ?_⟩
  · have hfac : 0 ≤ Real.sqrt x * (Real.log T) ^ 3 / T := by
      have hT_pos : 0 < T := by linarith
      have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT_nonneg 3))
        hT_pos.le
    exact le_trans (hvert' x T hx hT) <|
      mul_le_mul_of_nonneg_right (le_max_left _ _) hfac
  · have hfac : 0 ≤ Real.sqrt x * (Real.log T) ^ 2 / T := by
      have hT_pos : 0 < T := by linarith
      have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT_nonneg 2))
        hT_pos.le
    have hmax :
        2 * Ph * (Real.sqrt x * (Real.log T) ^ 2 / T) ≤
          2 * max Pv Ph * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
      nlinarith [le_max_right Pv Ph, hfac]
    exact le_trans (hhoriz' x T hx hT) hmax

/-- Smaller direct closure theorem for the Hadamard large-`T` piece leaf:
the decomposition side is reduced to a single complex identity
`shiftedRemainderRe = Re (vertC + horizC)`. The real-piece bookkeeping is then
reconstructed automatically. -/
theorem contour_piece_bounds_from_complex_decomp_and_normalized_integrands
    (vertC horizC : ℝ → ℝ → ℂ)
    (hdecomp : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      shiftedRemainderRe x T = (vertC x T + horizC x T).re)
    (vertIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hvert_rep : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      vertC x T = ∫ t in (-T)..T, vertIntegrand x T t)
    (hvert_int : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun t => vertIntegrand x T t) MeasureTheory.volume (-T) T)
    (hvert_pointwise : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand x T t‖ ≤
          (P * (Real.sqrt x * (Real.log T) ^ 3 / T)) / (2 * T))
    (σ₀ c : ℝ) (hσc : σ₀ < c)
    (horizIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hhoriz_rep : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      horizC x T = ∫ σ in σ₀..c, horizIntegrand x T σ)
    (hhoriz_int : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun σ => horizIntegrand x T σ) MeasureTheory.volume σ₀ c)
    (hhoriz_pointwise : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
        ‖horizIntegrand x T σ‖ ≤
          (2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)) / (c - σ₀))
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ∃ vert horiz : ℝ,
        shiftedRemainderRe x T = vert + horiz ∧
        |vert| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) ∧
        |horiz| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  exact
    contour_piece_bounds_from_normalized_complex_integrands
      (fun x T => (vertC x T).re)
      (fun x T => (horizC x T).re)
      vertC horizC
      (real_decomp_from_complex_sum vertC horizC hdecomp)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      vertIntegrand hvert_rep hvert_int hvert_pointwise
      σ₀ c hσc horizIntegrand hhoriz_rep hhoriz_int hhoriz_pointwise
      h_logderiv

/-- Smallest cycle-free closure theorem currently available for the Hadamard
large-`T` piece leaf: provide only the vertical/horizontal contour integrands,
a single complex decomposition identity for the sum of the two integrals,
integrability, and the two normalized pointwise bounds. All intermediate
complex-piece witnesses are reconstructed in the support cone. -/
theorem contour_piece_bounds_from_integral_decomp_and_normalized_integrands
    (vertIntegrand : ℝ → ℝ → ℝ → ℂ)
    (σ₀ c : ℝ) (hσc : σ₀ < c)
    (horizIntegrand : ℝ → ℝ → ℝ → ℂ)
    (hdecomp : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      shiftedRemainderRe x T =
        ((∫ t in (-T)..T, vertIntegrand x T t) +
          (∫ σ in σ₀..c, horizIntegrand x T σ)).re)
    (hvert_int : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun t => vertIntegrand x T t) MeasureTheory.volume (-T) T)
    (hvert_pointwise : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T t : ℝ, x ≥ 2 → T ≥ 16 → t ∈ Set.Icc (-T) T →
        ‖vertIntegrand x T t‖ ≤
          (P * (Real.sqrt x * (Real.log T) ^ 3 / T)) / (2 * T))
    (hhoriz_int : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      IntervalIntegrable (fun σ => horizIntegrand x T σ) MeasureTheory.volume σ₀ c)
    (hhoriz_pointwise : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T σ : ℝ, x ≥ 2 → T ≥ 16 → σ ∈ Set.Icc σ₀ c →
        ‖horizIntegrand x T σ‖ ≤
          (2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T)) / (c - σ₀))
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ∃ vert horiz : ℝ,
        shiftedRemainderRe x T = vert + horiz ∧
        |vert| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) ∧
        |horiz| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  exact
    contour_piece_bounds_from_complex_decomp_and_normalized_integrands
      (fun x T => ∫ t in (-T)..T, vertIntegrand x T t)
      (fun x T => ∫ σ in σ₀..c, horizIntegrand x T σ)
      hdecomp
      vertIntegrand
      (fun _ _ _ _ => rfl)
      hvert_int
      hvert_pointwise
      σ₀ c hσc
      horizIntegrand
      (fun _ _ _ _ => rfl)
      hhoriz_int
      hhoriz_pointwise
      h_logderiv

/-- A complex vertical contour-piece theorem discharges the real vertical bound
class automatically by taking real parts. -/
theorem contour_vert_bound_from_complex_hyp
    [ShiftedRemainderContourDecompLargeTHyp]
    [ShiftedRemainderContourVertComplexBoundFromLogDerivLargeTHyp] :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |ShiftedRemainderContourDecompLargeTHyp.vertRe x T| ≤
          P * (Real.sqrt x * (Real.log T) ^ 3 / T) := by
  exact
    vertical_bound_from_complex_piece
      ShiftedRemainderContourDecompLargeTHyp.vertRe
      ShiftedRemainderContourVertComplexBoundFromLogDerivLargeTHyp.vertC
      ShiftedRemainderContourVertComplexBoundFromLogDerivLargeTHyp.realPart
      ShiftedRemainderContourVertComplexBoundFromLogDerivLargeTHyp.bound

/-- A complex horizontal contour-piece theorem discharges the real horizontal
bound class automatically by taking real parts. -/
theorem contour_horiz_bound_from_complex_hyp
    [ShiftedRemainderContourDecompLargeTHyp]
    [ShiftedRemainderContourHorizComplexBoundFromLogDerivLargeTHyp] :
    ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |ShiftedRemainderContourDecompLargeTHyp.horizRe x T| ≤
          2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  exact
    horizontal_bound_from_complex_piece
      ShiftedRemainderContourDecompLargeTHyp.horizRe
      ShiftedRemainderContourHorizComplexBoundFromLogDerivLargeTHyp.horizC
      ShiftedRemainderContourHorizComplexBoundFromLogDerivLargeTHyp.realPart
      ShiftedRemainderContourHorizComplexBoundFromLogDerivLargeTHyp.bound

/-- Backward-compatible wrapper from a complex vertical contour-piece theorem to
the real vertical bound class. -/
instance
    [ShiftedRemainderContourDecompLargeTHyp]
    [ShiftedRemainderContourVertComplexBoundFromLogDerivLargeTHyp] :
    ShiftedRemainderContourVertBoundFromLogDerivLargeTHyp where
  bound := contour_vert_bound_from_complex_hyp

/-- Backward-compatible wrapper from a complex horizontal contour-piece theorem
to the real horizontal bound class. -/
instance
    [ShiftedRemainderContourDecompLargeTHyp]
    [ShiftedRemainderContourHorizComplexBoundFromLogDerivLargeTHyp] :
    ShiftedRemainderContourHorizBoundFromLogDerivLargeTHyp where
  bound := contour_horiz_bound_from_complex_hyp

/-- Direct wrapper route for the Hadamard large-`T` leaf: if one can choose
concrete vertical and horizontal real pieces of the shifted remainder, prove the
decomposition, and bound those two pieces separately from the large-`T`
pointwise `-ζ'/ζ` hypothesis, then the combined contour-piece bound follows
automatically. -/
theorem contour_piece_bounds_from_logderiv_of_decomp
    (vertRe horizRe : ℝ → ℝ → ℝ)
    (hdecomp : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      shiftedRemainderRe x T = vertRe x T + horizRe x T)
    (hvert : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |vertRe x T| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T))
    (hhoriz : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |horizRe x T| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T))
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ∃ vert horiz : ℝ,
        shiftedRemainderRe x T = vert + horiz ∧
        |vert| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) ∧
        |horiz| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  obtain ⟨Pv, hPv, hvert'⟩ := hvert h_logderiv
  obtain ⟨Ph, hPh, hhoriz'⟩ := hhoriz h_logderiv
  refine ⟨max Pv Ph, lt_of_lt_of_le hPv (le_max_left _ _), ?_⟩
  intro x T hx hT
  refine ⟨vertRe x T, horizRe x T, hdecomp x T hx hT, ?_, ?_⟩
  · have hfac : 0 ≤ Real.sqrt x * (Real.log T) ^ 3 / T := by
      have hT_pos : 0 < T := by linarith
      have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : 1 ≤ T)
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT_nonneg 3))
        hT_pos.le
    exact le_trans (hvert' x T hx hT) <|
      mul_le_mul_of_nonneg_right (le_max_left _ _) hfac
  · have hfac : 0 ≤ Real.sqrt x * (Real.log T) ^ 2 / T := by
      have hT_pos : 0 < T := by linarith
      have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : 1 ≤ T)
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg x) (pow_nonneg hlogT_nonneg 2))
        hT_pos.le
    have hmax : 2 * Ph * (Real.sqrt x * (Real.log T) ^ 2 / T) ≤
        2 * max Pv Ph * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
      nlinarith [le_max_right Pv Ph, hfac]
    exact le_trans (hhoriz' x T hx hT) hmax

/-- The direct segment-form Hadamard leaf becomes a wrapper once one has a
decomposition into concrete vertical and horizontal pieces with the separate
large-`T` bounds above. -/
theorem segment_bound_from_logderiv_of_decomp
    (vertRe horizRe : ℝ → ℝ → ℝ)
    (hdecomp : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      shiftedRemainderRe x T = vertRe x T + horizRe x T)
    (hvert : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |vertRe x T| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T))
    (hhoriz : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |horizRe x T| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T))
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        P * (Real.sqrt x * (Real.log T) ^ 3 / T) +
        2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  obtain ⟨P, hP, hpieces⟩ :=
    contour_piece_bounds_from_logderiv_of_decomp vertRe horizRe hdecomp hvert hhoriz h_logderiv
  refine ⟨P, hP, ?_⟩
  exact
    Littlewood.Development.PerronContourShift.segment_bound_from_piece_bounds
      shiftedRemainderRe P hpieces

/-- The standard large-`T` contour bound also becomes a wrapper once the
concrete vertical/horizontal decomposition and its separate bounds are proved. -/
theorem contour_bound_from_logderiv_of_decomp
    (vertRe horizRe : ℝ → ℝ → ℝ)
    (hdecomp : ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      shiftedRemainderRe x T = vertRe x T + horizRe x T)
    (hvert : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |vertRe x T| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T))
    (hhoriz : ZetaLogDerivPointwiseLargeTHyp →
      ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
        |horizRe x T| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T))
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  obtain ⟨P, hP, hpieces⟩ :=
    contour_piece_bounds_from_logderiv_of_decomp vertRe horizRe hdecomp hvert hhoriz h_logderiv
  simpa using
    Littlewood.Development.PerronContourShift.contour_bound_from_piece_bounds
      shiftedRemainderRe P hP hpieces

/-- If the support cone provides concrete contour-piece functions with their
decomposition and separate vertical/horizontal bounds, the older existential
contour-piece class is recovered by a wrapper. This is the smallest structured
surface currently visible below `HadamardProductZeta`. -/
theorem contour_piece_bounds_from_logderiv_decomp_hyp
    [ShiftedRemainderContourDecompFromLogDerivLargeTHyp]
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ∃ vert horiz : ℝ,
        shiftedRemainderRe x T = vert + horiz ∧
        |vert| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) ∧
        |horiz| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  exact
    contour_piece_bounds_from_logderiv_of_decomp
      ShiftedRemainderContourDecompFromLogDerivLargeTHyp.vertRe
      ShiftedRemainderContourDecompFromLogDerivLargeTHyp.horizRe
      ShiftedRemainderContourDecompFromLogDerivLargeTHyp.decomp
      ShiftedRemainderContourDecompFromLogDerivLargeTHyp.vertBound
      ShiftedRemainderContourDecompFromLogDerivLargeTHyp.horizBound
      h_logderiv

/-- Backward-compatible wrapper: the structured decomposition class implies the
existential contour-piece class. -/
instance
    [ShiftedRemainderContourDecompFromLogDerivLargeTHyp] :
    ShiftedRemainderContourPieceBoundsFromLogDerivLargeTHyp where
  bound := contour_piece_bounds_from_logderiv_decomp_hyp

/-- Public wrapper for the smaller contour-piece support surface. -/
theorem contour_piece_bounds_from_logderiv_hyp
    [ShiftedRemainderContourPieceBoundsFromLogDerivLargeTHyp]
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      ∃ vertRe horizRe : ℝ,
        shiftedRemainderRe x T = vertRe + horizRe ∧
        |vertRe| ≤ P * (Real.sqrt x * (Real.log T) ^ 3 / T) ∧
        |horizRe| ≤ 2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  exact ShiftedRemainderContourPieceBoundsFromLogDerivLargeTHyp.bound h_logderiv

/-- The smaller contour-piece surface implies the older direct segment-form
surface by the generic triangle-inequality reduction in `PerronContourShift`. -/
theorem segment_bound_from_logderiv_piece_hyp
    [ShiftedRemainderContourPieceBoundsFromLogDerivLargeTHyp]
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        P * (Real.sqrt x * (Real.log T) ^ 3 / T) +
        2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  obtain ⟨P, hP, hpieces⟩ := contour_piece_bounds_from_logderiv_hyp h_logderiv
  refine ⟨P, hP, ?_⟩
  exact
    Littlewood.Development.PerronContourShift.segment_bound_from_piece_bounds
      shiftedRemainderRe P hpieces

/-- Backward-compatible instance: a proof of the smaller contour-piece support
surface automatically supplies the older direct segment-form surface. -/
instance
    [ShiftedRemainderContourPieceBoundsFromLogDerivLargeTHyp] :
    ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp where
  bound := segment_bound_from_logderiv_piece_hyp

/-- Public wrapper exposing the exact segment-form theorem that
`HadamardProductZeta.shifted_remainder_segment_bound_from_logderiv_large_T`
currently carries privately. -/
theorem segment_bound_from_logderiv_hyp
    [ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp]
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        P * (Real.sqrt x * (Real.log T) ^ 3 / T) +
        2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) := by
  exact ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp.bound h_logderiv

/- There is deliberately no automatic upgrade here from the log-derivative
support classes to the public large-`T` segment class. Downstream modules must
either provide `ShiftedRemainderSegmentBoundLargeTHyp` directly or invoke the
wrapper theorems above with an explicit pointwise hypothesis. This keeps the
interface honest when no global pointwise `-ζ'/ζ` theorem is available. -/

/-- Once the pointwise `-ζ'/ζ` input and the Perron/contour closure are both
available in the support cone, the standard large-`T` contour bound follows by
the generic normalization theorem from `PerronContourShift`. -/
theorem contour_bound_from_logderiv_hyp
    [ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp]
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  obtain ⟨P, hP, hseg⟩ := segment_bound_from_logderiv_hyp h_logderiv
  simpa using
    Littlewood.Development.PerronContourShift.contour_bound_from_pointwise
      shiftedRemainderRe P hP hseg

/-- If the smaller contour-piece support surface is available directly, the
standard large-`T` contour bound follows without passing through the older
direct segment-form class. -/
theorem contour_bound_from_logderiv_piece_hyp
    [ShiftedRemainderContourPieceBoundsFromLogDerivLargeTHyp]
    (h_logderiv : ZetaLogDerivPointwiseLargeTHyp) :
    ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |shiftedRemainderRe x T| ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  obtain ⟨P, hP, hpieces⟩ := contour_piece_bounds_from_logderiv_hyp h_logderiv
  simpa using
    Littlewood.Development.PerronContourShift.contour_bound_from_piece_bounds
      shiftedRemainderRe P hP hpieces

end Littlewood.Development.ShiftedRemainderInterface
