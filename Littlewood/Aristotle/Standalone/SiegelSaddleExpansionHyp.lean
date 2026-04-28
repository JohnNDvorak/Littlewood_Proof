/-
Hypothesis bridge for the Siegel saddle-point expansion remainder bound.

This encapsulates the irreducible steepest-descent content of Gabcke 1979 Satz 1:
on each Riemann-Siegel block, the remainder after extracting the leading correction
is bounded by (2π/t)^{1/4} · (1/4) · t^{-1/2}.

The hypothesis class `SiegelSaddleExpansionHyp` now records a block-coordinate
normalization of the remaining steepest-descent leaf. The bridge theorem
`gabcke_from_hyp` reconstructs the standard Gabcke next-order estimate from it.

## Mathematical content

The saddle-point remainder is:
  R(k,t) = [ErrorTerm(t) - (-1)^k · (2π/t)^{1/4} · Ψ(blockParam k t)] / (2π/t)^{1/4}

The hypothesis asserts |R(k,t)| ≤ (1/4) · t^{-1/2} for t in block k (open on
the right: hardyStart k ≤ t < hardyStart(k+1)) with t > 0.
This is the content of Siegel's steepest-descent expansion through the saddle
w₀ = √(t/2π), with the bound coming from the Fresnel coefficient |c₁(p)| ≤ 1/4
(Gabcke 1979, Tabelle 1).

## Decomposition (retargeted 2026-03-18)

The gap is now isolated to a single weighted block-profile leaf:

1. **Weighted profile bound** (`SiegelSaddleExpansionHyp.weighted_profile_bound`):
   on block coordinates `t = blockCoord k p`,
   `|(k+1+p) · R(k,t)| ≤ fresnelC1Bound / √(2π)`.
2. **Admissible coefficient witness** (`saddle_remainder_admissible_constant`):
   derived constructively from (1) by the identity
   `t^(-1/2) = 1 / (√(2π) · (k+1+p))`.
3. **Atomic normalized remainder bound** (`SiegelSaddleExpansionHyp.remainder_bound`):
   derived constructively from (2) and `fresnelC1Bound ≤ 1/4`.

Everything else in the file is sorry-free algebra rebuilding the standard
main-chain statement
  |ErrorTerm(t) - (-1)^k · (2π/t)^{1/4} · Ψ(p)|
    ≤ (2π/t)^{1/4} · (1/4) · t^{-1/2}
from that single normalized bound.

The bound uses `p ∈ Ico 0 1` (half-open: the saddle expansion is only valid
strictly inside the block, i.e. t < hardyStart(k+1)). The integral bounds
downstream use the ae version of norm_integral_le to handle the boundary.

SORRY COUNT: 0

Reference: Siegel 1932 S3; Gabcke 1979 Satz 1, Tabelle 1.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.Standalone.FresnelSaddlePointInfra
import Littlewood.Aristotle.Standalone.SaddlePointMethod
import Littlewood.Aristotle.Standalone.SteepestDescentContour

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

set_option linter.dupNamespace false

namespace Aristotle.Standalone.SiegelSaddleExpansionHyp

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam Aristotle.ErrorTermExpansion
open Aristotle.Standalone.FresnelSaddlePointInfra
open Aristotle.Standalone.SteepestDescentContour

/-! ## Definition: saddle-point remainder -/

/-- The saddle-point remainder on block k at parameter t:
    R(k,t) = [ErrorTerm(t) - (-1)^k · (2π/t)^{1/4} · Ψ(blockParam k t)] / (2π/t)^{1/4}

    This is the "next-order correction" after extracting the leading Riemann-Siegel
    correction term. The steepest-descent analysis shows this is O(t^{-1/2}). -/
def saddlePointRemainder (k : ℕ) (t : ℝ) : ℝ :=
  (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
    rsPsi (blockParam k t)) / (2 * Real.pi / t) ^ ((1 : ℝ) / 4)

/-! ## Gabcke constant

The steepest-descent expansion at w₀ = √(t/2π) produces subleading coefficients
c₁(p), c₂(p), ... where p = blockParam k t. Gabcke 1979, Tabelle 1 shows that
sup_{p in [0,1]} |c₁(p)| approximately equals 0.083. We use the conservative
bound 1/4.

Rather than defining c₁(p) explicitly (which requires the exact Gabcke formula
involving scaled Hermite polynomials), we record a conservative numerical bound
`fresnelC1Bound ≤ 1/4`. The remaining analytic leaf is encoded in
`SiegelSaddleExpansionHyp.weighted_profile_bound`: on block coordinates
`t = 2π(k+1+p)^2`, it asks for the explicit weighted profile bound
`|(k+1+p) · R(k,t)| ≤ fresnelC1Bound / √(2π)`. The admissible coefficient
witness and the exact quarter-bound are then recovered constructively.
-/

/-- The supremum of |c₁(p)| over p in [0,1]. Gabcke 1979, Tabelle 1 gives
    this value as approximately 0.083. -/
def fresnelC1Bound : ℝ := 0.083

/-- The Gabcke constant is positive. -/
theorem fresnelC1Bound_pos : 0 < fresnelC1Bound := by
  unfold fresnelC1Bound; norm_num

/-- The conservative Gabcke constant is at most 1/4. -/
theorem fresnelC1Bound_le_quarter : fresnelC1Bound ≤ 1 / 4 := by
  unfold fresnelC1Bound
  norm_num

/-! ## Atomic placeholder

All downstream users only need the normalized saddle-point remainder estimate.
The heavier standard-form `ErrorTerm - leading = O(t^{-3/4})` placeholder has
been eliminated; `gabcke_from_hyp` reconstructs the exact main-chain bound from
the hypothesis field below.

SORRY COUNT: 0. -/

/-- On block coordinates, `t^(-1/2)` becomes the linear inverse scale
    `1 / (√(2π) · (k+1+p))`. -/
private theorem blockCoord_rpow_neg_half (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    (blockCoord k p) ^ (-(1 : ℝ) / 2) =
      1 / (Real.sqrt (2 * Real.pi) * ((k : ℝ) + 1 + p)) := by
  have hu : 0 ≤ (k : ℝ) + 1 + p := by positivity
  have hcoord : blockCoord k p = 2 * Real.pi * ((k : ℝ) + 1 + p) ^ 2 := by
    unfold blockCoord
    ring
  have hcoord_pos : 0 < blockCoord k p := by
    rw [hcoord]
    positivity
  have hsqrt :
      Real.sqrt (2 * Real.pi * ((k : ℝ) + 1 + p) ^ 2) =
        Real.sqrt (2 * Real.pi) * ((k : ℝ) + 1 + p) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), Real.sqrt_sq hu]
  rw [SaddlePointMethod.rpow_neg_half_eq_inv_sqrt (blockCoord k p) hcoord_pos]
  rw [hcoord, hsqrt]

/-- **Siegel saddle-point expansion hypothesis** (Gabcke 1979 Satz 1).

    The class records the remaining steepest-descent leaf in block coordinates:
    after writing `t = blockCoord k p = 2π(k+1+p)^2`, the weighted profile
    `(k+1+p) · R(k,t)` is bounded by `fresnelC1Bound / √(2π)` on `p ∈ [0,1)`.

    NOTE: The bound uses the half-open interval `Ico 0 1` (excluding p=1,
    corresponding to t = hardyStart(k+1)), because the saddle-point expansion
    is only valid strictly inside each block. -/
class SiegelSaddleExpansionHyp : Prop where
  weighted_profile_bound : ∀ k : ℕ, ∀ p : ℝ,
    p ∈ Ico (0 : ℝ) 1 →
      |(((k : ℝ) + 1 + p) * saddlePointRemainder k (blockCoord k p))| ≤
        fresnelC1Bound / Real.sqrt (2 * Real.pi)
  /-- Gabcke Satz 4 (A): the signed saddle-point remainder is nonneg on all
      blocks k ≥ 1. Encodes positivity of the first Fresnel coefficient
      c₁(p) > 0. Reference: Gabcke 1979 Satz 4. -/
  signed_nonneg : ∀ k : ℕ, 1 ≤ k → ∀ p : ℝ,
    p ∈ Ioc (0 : ℝ) 1 →
      0 ≤ (-1 : ℝ) ^ k * saddlePointRemainder k (blockCoord k p)
  /-- Gabcke Satz 4 (B): the normalized signed remainder is nonincreasing
      in k for k ≥ 1. Encodes monotone convergence of the weighted saddle
      remainder to c₁(p)/√(2π). Reference: Gabcke 1979 Satz 4. -/
  normalized_antitone : ∀ k : ℕ, 1 ≤ k → ∀ p : ℝ,
    p ∈ Ioc (0 : ℝ) 1 →
      ((k : ℝ) + 2 + p) * ((-1 : ℝ) ^ (k + 1) * saddlePointRemainder (k + 1) (blockCoord (k + 1) p)) ≤
        ((k : ℝ) + 1 + p) * ((-1 : ℝ) ^ k * saddlePointRemainder k (blockCoord k p))

/-- The Gabcke Satz 1 weighted-profile component of
`SiegelSaddleExpansionHyp`, separated from the signed adjacent Satz 4 fields.
This is the absolute first-coefficient bound on block coordinates. -/
def SiegelWeightedProfileBoundProp : Prop :=
  ∀ k : ℕ, ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    |(((k : ℝ) + 1 + p) * saddlePointRemainder k (blockCoord k p))| ≤
      fresnelC1Bound / Real.sqrt (2 * Real.pi)

/-- Coordinate pointwise form of the same Gabcke Satz 1 absolute atom. This
removes the profile factor `(k+1+p)` and asks directly for the normalized
saddle remainder decay on block coordinates. -/
def SiegelCoordinateRemainderBoundProp : Prop :=
  ∀ k : ℕ, ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    |saddlePointRemainder k (blockCoord k p)| ≤
      fresnelC1Bound * (blockCoord k p) ^ (-(1 : ℝ) / 2)

/-- Exact block-coordinate stationary-phase error estimate below
`SiegelCoordinateRemainderBoundProp`.

This is the local Taylor/remainder atom before normalizing by the saddle
amplitude. The left side is the raw `ErrorTerm` error after extracting the
leading Riemann-Siegel correction at `t = blockCoord k p`. -/
def SiegelCoordinateStationaryPhaseErrorProp : Prop :=
  ∀ k : ℕ, ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    |ErrorTerm (blockCoord k p)
      - (-1 : ℝ) ^ k * (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p| ≤
      (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) *
        (fresnelC1Bound * (blockCoord k p) ^ (-(1 : ℝ) / 2))

/-- Exact coefficient identity below the coordinate stationary-phase error
bound.

For a future explicit local Taylor coefficient `C`, this says the raw
stationary-phase defect is the saddle amplitude times `C k p` at the natural
`t^(-1/2)` scale. The analytic source should be Siegel/Gabcke's local
steepest-descent expansion in the exact coordinates `t = blockCoord k p`. -/
def SiegelStationaryPhaseCoefficientIdentityProp (C : ℕ → ℝ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    ErrorTerm (blockCoord k p)
      - (-1 : ℝ) ^ k * (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) * rsPsi p =
      (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) *
        (C k p * (blockCoord k p) ^ (-(1 : ℝ) / 2))

/-- Uniform coefficient bound for the local stationary-phase Taylor remainder. -/
def SiegelStationaryPhaseCoefficientBoundProp (C : ℕ → ℝ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    |C k p| ≤ fresnelC1Bound

/-- The quotient-normalized `psi` used in standard Riemann-Siegel coefficient
tables. This is intentionally kept separate from the project-local `rsPsi`:
the raw quotient normalization is not definitionally equal to the positive
local cosine convention used by the block-integral pipeline. -/
def standardGabckeRawPsi (p : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * (p ^ 2 - p - 1 / 16)) / Real.cos (2 * Real.pi * p)

/-- The standard first Riemann-Siegel/Gabcke coefficient as it appears in
coefficient-table form, before reconciling the source normalization with the
project-local `rsPsi` leading term. -/
def standardGabckeRawFirstCoefficient (p : ℝ) : ℝ :=
  -deriv (deriv (deriv standardGabckeRawPsi)) p / (96 * Real.pi ^ 2)

/-- Standard-normalized stationary-phase identity, parameterized by the
standard leading coefficient and standard first coefficient after any necessary
source-side phase/parameter conversion has been made explicit.

This is the bridge surface immediately below the local
`SiegelStationaryPhaseCoefficientIdentityProp`: once `stdLead` is proved to be
the local `rsPsi` convention, this identity becomes the local coefficient
identity. -/
def StandardGabckeStationaryPhaseIdentityProp
    (stdLead stdCoeff : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    ErrorTerm (blockCoord k p)
      - (-1 : ℝ) ^ k * (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) *
        stdLead p =
      (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) *
        (stdCoeff p * (blockCoord k p) ^ (-(1 : ℝ) / 2))

/-- The missing normalization bridge from a standard Riemann-Siegel leading
coefficient convention to the repo-local `rsPsi` convention. -/
def StandardGabckeLocalLeadingNormalizationProp (stdLead : ℝ → ℝ) : Prop :=
  ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 → stdLead p = rsPsi p

/-- The standard first-coefficient bound in source normalization. -/
def StandardGabckeCoefficientBoundProp (stdCoeff : ℝ → ℝ) : Prop :=
  ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 → |stdCoeff p| ≤ fresnelC1Bound

/-- A standard-normalized stationary-phase identity becomes the local
coefficient identity once the leading coefficient normalization has been
bridged to `rsPsi`. -/
theorem siegelStationaryPhaseCoefficientIdentityProp_of_standardGabckeNormalization
    {stdLead stdCoeff : ℝ → ℝ}
    (h_standard : StandardGabckeStationaryPhaseIdentityProp stdLead stdCoeff)
    (h_leading : StandardGabckeLocalLeadingNormalizationProp stdLead) :
    SiegelStationaryPhaseCoefficientIdentityProp (fun _ p => stdCoeff p) := by
  intro k p hp
  rw [← h_leading p hp]
  exact h_standard k p hp

/-- A standard source-side coefficient bound supplies the local coefficient
bound for the corresponding block-independent coefficient candidate. -/
theorem siegelStationaryPhaseCoefficientBoundProp_of_standardGabckeBound
    {stdCoeff : ℝ → ℝ}
    (h_bound : StandardGabckeCoefficientBoundProp stdCoeff) :
    SiegelStationaryPhaseCoefficientBoundProp (fun _ p => stdCoeff p) := by
  intro _ p hp
  exact h_bound p hp

/-- Project the weighted-profile atom from the current Siegel/Gabcke class. -/
theorem siegelWeightedProfileBoundProp_of_siegelSaddleExpansionHyp
    [h : SiegelSaddleExpansionHyp] :
    SiegelWeightedProfileBoundProp :=
  h.weighted_profile_bound

/-- An exact local Taylor coefficient identity plus the `fresnelC1Bound`
coefficient estimate imply the coordinate stationary-phase error bound. -/
theorem siegelCoordinateStationaryPhaseErrorProp_of_coefficientAtoms
    {C : ℕ → ℝ → ℝ}
    (h_id : SiegelStationaryPhaseCoefficientIdentityProp C)
    (h_bound : SiegelStationaryPhaseCoefficientBoundProp C) :
    SiegelCoordinateStationaryPhaseErrorProp := by
  intro k p hp
  let t : ℝ := blockCoord k p
  let amp : ℝ := (2 * Real.pi / t) ^ ((1 : ℝ) / 4)
  let scale : ℝ := t ^ (-(1 : ℝ) / 2)
  have ht_pos : 0 < t := by
    dsimp [t]
    have hbase : 0 < (k : ℝ) + 1 + p := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith [hp.1, hk]
    have hcoord : blockCoord k p = 2 * Real.pi * ((k : ℝ) + 1 + p) ^ 2 := by
      unfold blockCoord
      ring
    rw [hcoord]
    exact mul_pos (by positivity) (sq_pos_of_pos hbase)
  have hamp_pos : 0 < amp := by
    dsimp [amp]
    exact Real.rpow_pos_of_pos (div_pos (by positivity) ht_pos) _
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    exact Real.rpow_nonneg (le_of_lt ht_pos) _
  have hid := h_id k p hp
  have hcoef := h_bound k p hp
  rw [hid]
  change |amp * (C k p * scale)| ≤ amp * (fresnelC1Bound * scale)
  calc
    |amp * (C k p * scale)| = amp * (|C k p| * scale) := by
      rw [abs_mul, abs_of_pos hamp_pos, abs_mul, abs_of_nonneg hscale_nonneg]
    _ ≤ amp * (fresnelC1Bound * scale) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoef hscale_nonneg) (le_of_lt hamp_pos)

/-- The exact block-coordinate stationary-phase error estimate implies the
coordinate normalized saddle-remainder bound. -/
theorem siegelCoordinateRemainderBoundProp_of_stationaryPhaseError
    (h : SiegelCoordinateStationaryPhaseErrorProp) :
    SiegelCoordinateRemainderBoundProp := by
  intro k p hp
  let t : ℝ := blockCoord k p
  let amp : ℝ := (2 * Real.pi / t) ^ ((1 : ℝ) / 4)
  have ht_pos : 0 < t := by
    dsimp [t]
    have hbase : 0 < (k : ℝ) + 1 + p := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith [hp.1, hk]
    have hcoord : blockCoord k p = 2 * Real.pi * ((k : ℝ) + 1 + p) ^ 2 := by
      unfold blockCoord
      ring
    rw [hcoord]
    exact mul_pos (by positivity) (sq_pos_of_pos hbase)
  have hamp_pos : 0 < amp := by
    dsimp [amp]
    exact Real.rpow_pos_of_pos (div_pos (by positivity) ht_pos) _
  have hparam : blockParam k t = p := by
    dsimp [t]
    exact blockParam_blockCoord k p hp.1
  have hstat := h k p hp
  change |saddlePointRemainder k t| ≤ fresnelC1Bound * t ^ (-(1 : ℝ) / 2)
  unfold saddlePointRemainder
  change
    |(ErrorTerm t - (-1 : ℝ) ^ k * amp * rsPsi (blockParam k t)) / amp| ≤
      fresnelC1Bound * t ^ (-(1 : ℝ) / 2)
  rw [hparam, abs_div, abs_of_pos hamp_pos]
  rw [div_le_iff₀ hamp_pos]
  simpa [t, amp, mul_comm, mul_left_comm, mul_assoc] using hstat

/-- On block coordinates, the weighted profile bound is equivalent to the
expected `fresnelC1Bound · t^(-1/2)` decay for the normalized remainder. -/
theorem siegelCoordinateRemainderBoundProp_of_weightedProfile
    (h : SiegelWeightedProfileBoundProp) :
    SiegelCoordinateRemainderBoundProp := by
  intro k p hp
  let u : ℝ := (k : ℝ) + 1 + p
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    linarith [hp.1]
  have hu_pos : 0 < u := by
    have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
    dsimp [u]
    linarith [hp.1, hk1_pos]
  have hprof := h k p hp
  have hprof' : u * |saddlePointRemainder k (blockCoord k p)| ≤
      fresnelC1Bound / Real.sqrt (2 * Real.pi) := by
    simpa [u, abs_mul, abs_of_nonneg hu_nonneg, mul_comm, mul_left_comm, mul_assoc] using hprof
  have hdiv : |saddlePointRemainder k (blockCoord k p)| ≤
      (fresnelC1Bound / Real.sqrt (2 * Real.pi)) / u := by
    rw [le_div_iff₀ hu_pos]
    simpa [u, mul_comm, mul_left_comm, mul_assoc] using hprof'
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  calc
    |saddlePointRemainder k (blockCoord k p)|
      ≤ (fresnelC1Bound / Real.sqrt (2 * Real.pi)) / u := hdiv
    _ = fresnelC1Bound / (Real.sqrt (2 * Real.pi) * u) := by
          field_simp [hu_pos.ne', hsqrt_ne]
    _ = fresnelC1Bound * (1 / (Real.sqrt (2 * Real.pi) * u)) := by
          rw [div_eq_mul_inv, one_div]
    _ = fresnelC1Bound * (blockCoord k p) ^ (-(1 : ℝ) / 2) := by
          rw [blockCoord_rpow_neg_half k p hp.1]

/-- The coordinate pointwise remainder bound implies the weighted profile
bound by multiplying through by the positive block-coordinate factor. -/
theorem siegelWeightedProfileBoundProp_of_coordinateRemainder
    (h : SiegelCoordinateRemainderBoundProp) :
    SiegelWeightedProfileBoundProp := by
  intro k p hp
  let u : ℝ := (k : ℝ) + 1 + p
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    linarith [hp.1]
  have hu_pos : 0 < u := by
    have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
    dsimp [u]
    linarith [hp.1, hk1_pos]
  have hcoord := h k p hp
  rw [blockCoord_rpow_neg_half k p hp.1] at hcoord
  have hmul :
      u * |saddlePointRemainder k (blockCoord k p)| ≤
        u * (fresnelC1Bound * (1 / (Real.sqrt (2 * Real.pi) * u))) :=
    mul_le_mul_of_nonneg_left hcoord hu_nonneg
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hscaled :
      u * |saddlePointRemainder k (blockCoord k p)| ≤
        fresnelC1Bound / Real.sqrt (2 * Real.pi) := by
    calc
      u * |saddlePointRemainder k (blockCoord k p)|
          ≤ u * (fresnelC1Bound * (1 / (Real.sqrt (2 * Real.pi) * u))) := hmul
      _ = fresnelC1Bound / Real.sqrt (2 * Real.pi) := by
            field_simp [hu_pos.ne', hsqrt_ne]
  simpa [u, abs_mul, abs_of_nonneg hu_nonneg, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- The weighted-profile and coordinate pointwise forms of the Gabcke Satz 1
absolute atom are exactly equivalent. -/
theorem siegelWeightedProfileBoundProp_iff_coordinateRemainder :
    SiegelWeightedProfileBoundProp ↔ SiegelCoordinateRemainderBoundProp :=
  ⟨siegelCoordinateRemainderBoundProp_of_weightedProfile,
    siegelWeightedProfileBoundProp_of_coordinateRemainder⟩

/-- On block coordinates, the weighted profile bound implies the expected
    `fresnelC1Bound · t^(-1/2)` decay for the normalized remainder. -/
private theorem saddle_remainder_fresnel_bound_on_coords [h : SiegelSaddleExpansionHyp]
    (k : ℕ) (p : ℝ) (hp : p ∈ Ico (0 : ℝ) 1) :
    |saddlePointRemainder k (blockCoord k p)| ≤
      fresnelC1Bound * (blockCoord k p) ^ (-(1 : ℝ) / 2) := by
  have hcoord : SiegelCoordinateRemainderBoundProp :=
    siegelCoordinateRemainderBoundProp_of_weightedProfile
      siegelWeightedProfileBoundProp_of_siegelSaddleExpansionHyp
  exact hcoord k p hp

/-- Admissible coefficient witness recovered from the weighted block profile. -/
private theorem saddle_remainder_admissible_constant [h : SiegelSaddleExpansionHyp]
    (k : ℕ) (t : ℝ)
    (hlo : hardyStart k ≤ t) (hhi : t < hardyStart (k + 1)) (hpos : 0 < t) :
    ∃ C : ℝ, C ≤ (1 / 4 : ℝ) ∧
      |saddlePointRemainder k t| ≤ C * t ^ (-(1 : ℝ) / 2) := by
  let p : ℝ := blockParam k t
  have hp : p ∈ Ico (0 : ℝ) 1 := blockParam_mem_Ico k t hlo hhi
  have hcoord : blockCoord k p = t := by
    dsimp [p]
    exact blockCoord_blockParam k t hpos.le
  refine ⟨fresnelC1Bound, fresnelC1Bound_le_quarter, ?_⟩
  simpa [p, hcoord] using saddle_remainder_fresnel_bound_on_coords k p hp

/-- Atomic saddle-point remainder bound (Gabcke 1979 Satz 1).

    This is the irreducible steepest-descent input: on each Riemann-Siegel
    block, the normalized remainder after removing the leading correction is
    bounded by `(1/4) * t^{-1/2}`. Uses strict inequality on the right:
    `t < hardyStart(k+1)`. -/
theorem SiegelSaddleExpansionHyp.remainder_bound [h : SiegelSaddleExpansionHyp]
    (k : ℕ) (t : ℝ)
    (hlo : hardyStart k ≤ t) (hhi : t < hardyStart (k + 1)) (hpos : 0 < t) :
    |saddlePointRemainder k t| ≤ (1 / 4) * t ^ (-(1 : ℝ) / 2) := by
  rcases saddle_remainder_admissible_constant k t hlo hhi hpos with ⟨C, hC, hbound⟩
  have h_pow_nonneg : 0 ≤ t ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hpos.le _
  exact le_trans hbound (mul_le_mul_of_nonneg_right hC h_pow_nonneg)

/-- Private alias for the derived normalized quarter-bound. -/
private theorem saddle_remainder_bound_atomic [SiegelSaddleExpansionHyp]
    (k : ℕ) (t : ℝ)
    (hlo : hardyStart k ≤ t) (hhi : t < hardyStart (k + 1)) (hpos : 0 < t) :
    |saddlePointRemainder k t| ≤ (1 / 4) * t ^ (-(1 : ℝ) / 2) :=
  SiegelSaddleExpansionHyp.remainder_bound k t hlo hhi hpos

/-! ## Bridge theorem -/

/-- Two-pi-over-t to the 1/4 is positive when t > 0. -/
private theorem two_pi_div_t_rpow_pos (t : ℝ) (ht : 0 < t) :
    0 < (2 * Real.pi / t) ^ ((1 : ℝ) / 4) :=
  rpow_pos_of_pos (div_pos (by positivity) ht) _

/-- **Bridge theorem**: derives the exact statement of `gabcke_next_order_bound`
    from `SiegelSaddleExpansionHyp`.

    The key algebraic step is:
      |E(t) - leading(t)| = |R(k,t)| · (2π/t)^{1/4}
                           ≤ (1/4) · t^{-1/2} · (2π/t)^{1/4}
                           = (2π/t)^{1/4} · (1/4) · t^{-1/2}

    Uses strict inequality on the right: `t < hardyStart(k+1)`. -/
theorem gabcke_from_hyp [SiegelSaddleExpansionHyp] :
    ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t < hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤
        (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * ((1 / 4) * t ^ (-(1 : ℝ) / 2)) := by
  intro k t hlo hhi hpos
  have h_amp_pos := two_pi_div_t_rpow_pos t hpos
  -- Unfold saddlePointRemainder: |E - leading| = |R| · amp
  have h_eq : ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
      rsPsi (blockParam k t) =
      saddlePointRemainder k t * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) := by
    unfold saddlePointRemainder
    rw [div_mul_cancel₀]
    exact ne_of_gt h_amp_pos
  rw [h_eq, abs_mul, abs_of_pos h_amp_pos, mul_comm]
  exact mul_le_mul_of_nonneg_left
    (SiegelSaddleExpansionHyp.remainder_bound k t hlo hhi hpos)
    h_amp_pos.le

end Aristotle.Standalone.SiegelSaddleExpansionHyp
