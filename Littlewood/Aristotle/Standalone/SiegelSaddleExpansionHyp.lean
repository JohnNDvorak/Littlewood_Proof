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
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.Shift

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

/-- The phase/parameter-normalized standard leading coefficient in the local
block convention. This is the standard leading phase after translating into
the project-local `p` and absorbing the phase convention used by `rsPsi`. -/
def standardGabckePhaseNormalizedLead (p : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * (p ^ 2 - p + 1 / 8))

/-- The phase-normalized standard leading coefficient is exactly the local
`rsPsi` convention. -/
theorem standardGabckePhaseNormalizedLead_eq_rsPsi (p : ℝ) :
    standardGabckePhaseNormalizedLead p = rsPsi p := by
  unfold standardGabckePhaseNormalizedLead rsPsi
  congr 1
  ring

/-- The missing normalization bridge from a standard Riemann-Siegel leading
coefficient convention to the repo-local `rsPsi` convention. -/
def StandardGabckeLocalLeadingNormalizationProp (stdLead : ℝ → ℝ) : Prop :=
  ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 → stdLead p = rsPsi p

/-- The correctly phase/parameter-normalized standard leading coefficient
satisfies the local leading-normalization bridge. -/
theorem standardGabckeLocalLeadingNormalization_phaseNormalized :
    StandardGabckeLocalLeadingNormalizationProp standardGabckePhaseNormalizedLead := by
  intro p _hp
  exact standardGabckePhaseNormalizedLead_eq_rsPsi p

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

/-- The standard first-coefficient bound in source normalization. -/
def StandardGabckeCoefficientBoundProp (stdCoeff : ℝ → ℝ) : Prop :=
  ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 → |stdCoeff p| ≤ fresnelC1Bound

/-! ## Standard Gabcke source atoms

The phase-normalized leading term is now fixed. The remaining missing source
input is the actual contour/Taylor theorem identifying the first source
coefficient with the third-derivative formula below, plus the corresponding
Tabelle-1 coefficient estimate. These atoms are deliberately stated with the
unfolded derivative formula so they are tied to Gabcke's coefficient source,
not to a defect quotient or an abstract local provider. -/

/-- Source-level contour/Taylor identity for Gabcke's first coefficient, in
the already phase-normalized local leading convention. -/
def StandardGabckeContourTaylorFirstCoefficientIdentityProp : Prop :=
  ∀ k : ℕ, ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    ErrorTerm (blockCoord k p)
      - (-1 : ℝ) ^ k * (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) *
        standardGabckePhaseNormalizedLead p =
      (2 * Real.pi / blockCoord k p) ^ ((1 : ℝ) / 4) *
        ((-deriv (deriv (deriv standardGabckeRawPsi)) p / (96 * Real.pi ^ 2)) *
          (blockCoord k p) ^ (-(1 : ℝ) / 2))

/-- Source-level Tabelle-1 bound for Gabcke's explicit first coefficient. -/
def StandardGabckeTabelleFirstCoefficientBoundProp : Prop :=
  ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    |(-deriv (deriv (deriv standardGabckeRawPsi)) p / (96 * Real.pi ^ 2))| ≤
      fresnelC1Bound

/-- The unscaled third derivative of the raw quotient-normalized standard
Gabcke `psi`. This is the exact derivative payload behind the first source
coefficient. -/
def standardGabckeRawPsiThirdDerivative (p : ℝ) : ℝ :=
  deriv (deriv (deriv standardGabckeRawPsi)) p

/-- Candidate smooth-removable standard quotient: away from the denominator
zeros it is the raw quotient, while the two removable values are filled by
the common l'Hopital value `1/2`. The remaining bridge atoms must still prove
that this is the actual smooth Gabcke/Tabelle normalization at derivative
level; this definition does not assert regularity of the raw quotient. -/
def standardGabckeRemovablePsiCandidate (p : ℝ) : ℝ :=
  if p = (1 / 4 : ℝ) ∨ p = (3 / 4 : ℝ) then
    1 / 2
  else
    standardGabckeRawPsi p

/-- The instantiated smooth-removable source derivative candidate for the
two denominator-zero point atoms. This is intentionally not definitionally the
raw totalized derivative. -/
def standardGabckeRemovableSourceThirdDerivative (p : ℝ) : ℝ :=
  deriv (deriv (deriv standardGabckeRemovablePsiCandidate)) p

/-- Local coordinate form of the removable quotient near the first
denominator-zero point, with `x = p - 1/4`. The two filled values correspond
to `x = 0` and `x = 1/2`; the first one is the local atom needed for the
quarter-point derivative formula. -/
def standardGabckeQuarterLocalPsi (x : ℝ) : ℝ :=
  if x = 0 ∨ x = (1 / 2 : ℝ) then
    1 / 2
  else
    Real.sin (Real.pi * x - 2 * Real.pi * x ^ 2) /
      Real.sin (2 * Real.pi * x)

/-- Smaller Tabelle-1 source atom: bound the unscaled third derivative before
dividing by the explicit positive normalizing factor `96*pi^2`. -/
def StandardGabckeRawPsiThirdDerivativeBoundProp : Prop :=
  ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    |standardGabckeRawPsiThirdDerivative p| ≤
      fresnelC1Bound * (96 * Real.pi ^ 2)

/-- The denominator-zero locus of the raw quotient-normalized standard
Gabcke `psi`. These are the removable singular points that must be handled
separately before the unfolded derivative bound can be sourced from the
standard coefficient table. -/
def standardGabckeRawPsiDenominatorZero (p : ℝ) : Prop :=
  Real.cos (2 * Real.pi * p) = 0

/-- Regular-point part of the unscaled third-derivative Tabelle bound, away
from the denominator-zero locus of the raw quotient normalization. -/
def StandardGabckeRawPsiRegularThirdDerivativeBoundProp : Prop :=
  ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    ¬ standardGabckeRawPsiDenominatorZero p →
      |standardGabckeRawPsiThirdDerivative p| ≤
        fresnelC1Bound * (96 * Real.pi ^ 2)

/-- Removable-singularity part of the unscaled third-derivative Tabelle bound.
This is the exact missing normalization bridge at the raw quotient's
denominator-zero points. -/
def StandardGabckeRawPsiRemovableThirdDerivativeBoundProp : Prop :=
  ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    standardGabckeRawPsiDenominatorZero p →
      |standardGabckeRawPsiThirdDerivative p| ≤
        fresnelC1Bound * (96 * Real.pi ^ 2)

/-- Exact classification of the denominator-zero locus inside the Gabcke
block parameter interval. For the raw quotient normalization, the only
removable singular points in `Ico 0 1` are `1/4` and `3/4`. -/
def StandardGabckeRawPsiDenominatorZeroClassifiedProp : Prop :=
  ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    standardGabckeRawPsiDenominatorZero p →
      p = (1 / 4 : ℝ) ∨ p = (3 / 4 : ℝ)

/-- Trigonometric lattice form of the denominator-zero condition for the raw
quotient normalization. This is the direct `cos = 0` source theorem before
using the block-parameter range. -/
def StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp : Prop :=
  ∀ p : ℝ, p ∈ Ico (0 : ℝ) 1 →
    standardGabckeRawPsiDenominatorZero p →
      ∃ m : ℤ, p = (m : ℝ) / 2 + 1 / 4

/-- The raw quotient denominator vanishes only on the standard quarter
lattice. This is just the real `cos_eq_zero` theorem for the angle
`2*pi*p`, divided by `2*pi`. -/
theorem standardGabckeRawPsiDenominatorZeroQuarterLatticeProp_proved :
    StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp := by
  intro p _hp hzero
  unfold standardGabckeRawPsiDenominatorZero at hzero
  rcases (Real.cos_eq_zero_iff).mp hzero with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  calc
    p = (2 * Real.pi * p) / (2 * Real.pi) := by
      field_simp [hpi_ne]
    _ = ((2 * (m : ℝ) + 1) * Real.pi / 2) / (2 * Real.pi) := by
      rw [hm]
    _ = (m : ℝ) / 2 + 1 / 4 := by
      field_simp [hpi_ne]
      ring

/-- Range restriction for the denominator-zero lattice: inside `Ico 0 1`, the
quarter-lattice points are exactly `1/4` and `3/4`. -/
def StandardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp : Prop :=
  ∀ m : ℤ,
    ((m : ℝ) / 2 + 1 / 4) ∈ Ico (0 : ℝ) 1 →
      (m : ℝ) / 2 + 1 / 4 = (1 / 4 : ℝ) ∨
        (m : ℝ) / 2 + 1 / 4 = (3 / 4 : ℝ)

/-- The quarter-lattice range restriction is elementary integer arithmetic:
`0 <= m/2 + 1/4 < 1` forces `m = 0` or `m = 1`. -/
theorem standardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp_proved :
    StandardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp := by
  intro m hm
  have hm_gt_neg_one_real : (-1 : ℝ) < (m : ℝ) := by
    linarith [hm.1]
  have hm_lt_two_real : (m : ℝ) < 2 := by
    linarith [hm.2]
  have hm_gt_neg_one : (-1 : ℤ) < m := by
    exact_mod_cast hm_gt_neg_one_real
  have hm_lt_two : m < 2 := by
    exact_mod_cast hm_lt_two_real
  have hm_cases : m = 0 ∨ m = 1 := by omega
  rcases hm_cases with rfl | rfl
  · left
    norm_num
  · right
    norm_num

/-- The denominator-zero classification follows from the standard `cos = 0`
quarter-lattice theorem plus the elementary range restriction. -/
theorem standardGabckeRawPsiDenominatorZeroClassifiedProp_of_quarterLattice
    (h_lattice : StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp)
    (h_range : StandardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp) :
    StandardGabckeRawPsiDenominatorZeroClassifiedProp := by
  intro p hp hzero
  rcases h_lattice p hp hzero with ⟨m, hm⟩
  have hm_mem : ((m : ℝ) / 2 + 1 / 4) ∈ Ico (0 : ℝ) 1 := by
    rwa [← hm]
  rcases h_range m hm_mem with h_quarter | h_threeQuarter
  · exact Or.inl (hm.trans h_quarter)
  · exact Or.inr (hm.trans h_threeQuarter)

/-- With the interval range restriction proved, the denominator-zero
classification now depends only on the standard trigonometric quarter-lattice
source theorem. -/
theorem standardGabckeRawPsiDenominatorZeroClassifiedProp_of_quarterLattice_only
    (h_lattice : StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp) :
    StandardGabckeRawPsiDenominatorZeroClassifiedProp :=
  standardGabckeRawPsiDenominatorZeroClassifiedProp_of_quarterLattice h_lattice
    standardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp_proved

/-- The denominator-zero locus in the block interval is exactly the two
quarter points `1/4` and `3/4`. -/
theorem standardGabckeRawPsiDenominatorZeroClassifiedProp_proved :
    StandardGabckeRawPsiDenominatorZeroClassifiedProp :=
  standardGabckeRawPsiDenominatorZeroClassifiedProp_of_quarterLattice_only
    standardGabckeRawPsiDenominatorZeroQuarterLatticeProp_proved

/-- Pointwise removable-singularity bounds at the two denominator-zero
parameters of the raw quotient normalization. -/
def StandardGabckeRawPsiRemovablePointBoundsProp : Prop :=
  |standardGabckeRawPsiThirdDerivative (1 / 4 : ℝ)| ≤
      fresnelC1Bound * (96 * Real.pi ^ 2) ∧
    |standardGabckeRawPsiThirdDerivative (3 / 4 : ℝ)| ≤
      fresnelC1Bound * (96 * Real.pi ^ 2)

/-- Exact source value for the raw third derivative at the first removable
quarter point. This keeps the totalized raw quotient separate from the smooth
removable extension or Tabelle value used to source the number. -/
def StandardGabckeRawPsiQuarterThirdDerivativeValueProp (C14 : ℝ) : Prop :=
  standardGabckeRawPsiThirdDerivative (1 / 4 : ℝ) = C14

/-- Exact source value for the raw third derivative at the second removable
quarter point. -/
def StandardGabckeRawPsiThreeQuarterThirdDerivativeValueProp (C34 : ℝ) : Prop :=
  standardGabckeRawPsiThirdDerivative (3 / 4 : ℝ) = C34

/-- Numeric source bound for the two removable-point third-derivative values
after their exact values have been supplied by the local Taylor/Tabelle
normalization. -/
def StandardGabckeRawPsiRemovablePointValueBoundsProp (C14 C34 : ℝ) : Prop :=
  |C14| ≤ fresnelC1Bound * (96 * Real.pi ^ 2) ∧
    |C34| ≤ fresnelC1Bound * (96 * Real.pi ^ 2)

/-- First-point bridge from the smooth removable quotient normalization to the
raw totalized quotient derivative. -/
def StandardGabckeRawPsiQuarterRemovableSourceBridgeProp
    (D : ℝ → ℝ) : Prop :=
  standardGabckeRawPsiThirdDerivative (1 / 4 : ℝ) = D (1 / 4)

/-- Second-point bridge from the smooth removable quotient normalization to the
raw totalized quotient derivative. -/
def StandardGabckeRawPsiThreeQuarterRemovableSourceBridgeProp
    (D : ℝ → ℝ) : Prop :=
  standardGabckeRawPsiThirdDerivative (3 / 4 : ℝ) = D (3 / 4)

/-- Pointwise bridge from Gabcke's smooth removable quotient normalization to
the raw totalized quotient derivative at the two denominator-zero points.
This is deliberately only a two-point statement; it does not assert global
regularity of `standardGabckeRawPsi`. -/
def StandardGabckeRawPsiRemovableSourceBridgeProp (D : ℝ → ℝ) : Prop :=
  standardGabckeRawPsiThirdDerivative (1 / 4 : ℝ) = D (1 / 4) ∧
    standardGabckeRawPsiThirdDerivative (3 / 4 : ℝ) = D (3 / 4)

/-- The paired removable-source bridge follows from its two independent
quarter-point bridge atoms. -/
theorem standardGabckeRawPsiRemovableSourceBridgeProp_of_pointBridges
    {D : ℝ → ℝ}
    (h_quarter : StandardGabckeRawPsiQuarterRemovableSourceBridgeProp D)
    (h_threeQuarter :
      StandardGabckeRawPsiThreeQuarterRemovableSourceBridgeProp D) :
    StandardGabckeRawPsiRemovableSourceBridgeProp D :=
  ⟨h_quarter, h_threeQuarter⟩

/-- Tabelle/source value for the smooth removable third-derivative payload at
the first denominator-zero point. -/
def StandardGabckeRemovableSourceQuarterThirdDerivativeValueProp
    (D : ℝ → ℝ) (C14 : ℝ) : Prop :=
  D (1 / 4) = C14

/-- Tabelle/source value for the smooth removable third-derivative payload at
the second denominator-zero point. -/
def StandardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp
    (D : ℝ → ℝ) (C34 : ℝ) : Prop :=
  D (3 / 4) = C34

/-- The first removable-source value atom is closed canonically by choosing
the actual source value as the constant to be bounded. -/
theorem standardGabckeRemovableSourceQuarterThirdDerivativeValueProp_self
    (D : ℝ → ℝ) :
    StandardGabckeRemovableSourceQuarterThirdDerivativeValueProp D (D (1 / 4)) :=
  rfl

/-- The second removable-source value atom is closed canonically by choosing
the actual source value as the constant to be bounded. -/
theorem standardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp_self
    (D : ℝ → ℝ) :
    StandardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp D (D (3 / 4)) :=
  rfl

/-- The quarter source-value atom for the instantiated removable candidate,
with the constant fixed to the candidate's actual source value. -/
theorem standardGabckeRemovableSourceQuarterThirdDerivativeValueProp_candidate :
    StandardGabckeRemovableSourceQuarterThirdDerivativeValueProp
      standardGabckeRemovableSourceThirdDerivative
      (standardGabckeRemovableSourceThirdDerivative (1 / 4)) :=
  standardGabckeRemovableSourceQuarterThirdDerivativeValueProp_self
    standardGabckeRemovableSourceThirdDerivative

/-- The three-quarter source-value atom for the instantiated removable
candidate, with the constant fixed to the candidate's actual source value. -/
theorem standardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp_candidate :
    StandardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp
      standardGabckeRemovableSourceThirdDerivative
      (standardGabckeRemovableSourceThirdDerivative (3 / 4)) :=
  standardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp_self
    standardGabckeRemovableSourceThirdDerivative

/-- Tabelle/source values for the smooth removable third-derivative payload at
the two denominator-zero points. -/
def StandardGabckeRemovableSourceThirdDerivativeValueProp
    (D : ℝ → ℝ) (C14 C34 : ℝ) : Prop :=
  D (1 / 4) = C14 ∧ D (3 / 4) = C34

/-- The paired removable-source value atom is closed canonically once the
constants are chosen to be the actual source values. The remaining analytic
work is then the numeric Tabelle bound for these source values. -/
theorem standardGabckeRemovableSourceThirdDerivativeValueProp_self
    (D : ℝ → ℝ) :
    StandardGabckeRemovableSourceThirdDerivativeValueProp
      D (D (1 / 4)) (D (3 / 4)) :=
  ⟨standardGabckeRemovableSourceQuarterThirdDerivativeValueProp_self D,
    standardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp_self D⟩

/-- The paired Tabelle/source value atom follows from its two point-value
atoms. -/
theorem standardGabckeRemovableSourceThirdDerivativeValueProp_of_pointValues
    {D : ℝ → ℝ} {C14 C34 : ℝ}
    (h_quarter :
      StandardGabckeRemovableSourceQuarterThirdDerivativeValueProp D C14)
    (h_threeQuarter :
      StandardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp D C34) :
    StandardGabckeRemovableSourceThirdDerivativeValueProp D C14 C34 :=
  ⟨h_quarter, h_threeQuarter⟩

/-- Numeric Tabelle bound for the smooth removable-source derivative at the
first denominator-zero point. -/
def StandardGabckeRemovableSourceQuarterThirdDerivativeBoundProp
    (D : ℝ → ℝ) : Prop :=
  |D (1 / 4)| ≤ fresnelC1Bound * (96 * Real.pi ^ 2)

/-- Exact local Taylor value of the instantiated removable quotient candidate
at the first removable point. In local coordinate `x = p - 1/4`, the smooth
quotient has cubic coefficient `-pi^2/6`, hence third derivative `-pi^2`. -/
def StandardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp : Prop :=
  standardGabckeRemovableSourceThirdDerivative (1 / 4) = -Real.pi ^ 2

/-- Exact coordinate bridge for the third derivative at the first removable
point, reducing the candidate derivative at `p = 1/4` to the local coordinate
function `standardGabckeQuarterLocalPsi` at `x = 0`. -/
def StandardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp : Prop :=
  standardGabckeRemovableSourceThirdDerivative (1 / 4) =
    deriv (deriv (deriv standardGabckeQuarterLocalPsi)) 0

/-- Translation part of the quarter coordinate bridge: third derivative at
`p = 1/4` becomes the third derivative at `x = 0` after the coordinate change
`p = x + 1/4`. This is a local calculus/chain-rule atom and does not identify
the shifted candidate with the trigonometric quotient. -/
def StandardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp : Prop :=
  standardGabckeRemovableSourceThirdDerivative (1 / 4) =
    deriv (deriv (deriv (fun x : ℝ =>
      standardGabckeRemovablePsiCandidate (x + 1 / 4)))) 0

/-- The third derivative commutes with the coordinate translation
`p = x + 1/4`; this is repeated use of Mathlib's derivative-shift lemma. -/
theorem standardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp_proved :
    StandardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp := by
  unfold StandardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp
  unfold standardGabckeRemovableSourceThirdDerivative
  let f : ℝ → ℝ := standardGabckeRemovablePsiCandidate
  let a : ℝ := 1 / 4
  change deriv (deriv (deriv f)) a =
    deriv (deriv (deriv (fun x : ℝ => f (x + a)))) 0
  have h1 :
      deriv (fun x : ℝ => f (x + a)) =
        fun x : ℝ => deriv f (x + a) := by
    funext x
    exact deriv_comp_add_const f a x
  have h2 :
      deriv (fun x : ℝ => deriv f (x + a)) =
        fun x : ℝ => deriv (deriv f) (x + a) := by
    funext x
    exact deriv_comp_add_const (deriv f) a x
  rw [h1, h2]
  rw [deriv_comp_add_const]
  norm_num [a]

/-- Pointwise local-coordinate identity for the removable candidate after the
shift `p = x + 1/4`. This is the exact algebraic/trigonometric and removable
fill statement; it is separate from derivative translation. -/
def StandardGabckeRemovableCandidateQuarterLocalFunctionEqProp : Prop :=
  ∀ x : ℝ,
    standardGabckeRemovablePsiCandidate (x + 1 / 4) =
      standardGabckeQuarterLocalPsi x

/-- The two filled removable values match exactly under the quarter-point
coordinate shift `p = x + 1/4`. -/
def StandardGabckeRemovableCandidateQuarterShiftedFillEquivProp : Prop :=
  ∀ x : ℝ,
    (x + 1 / 4 = (1 / 4 : ℝ) ∨ x + 1 / 4 = (3 / 4 : ℝ)) ↔
      x = 0 ∨ x = (1 / 2 : ℝ)

/-- Off the two filled removable values, the shifted raw quotient is the
trigonometric local quotient in the coordinate `x = p - 1/4`. -/
def StandardGabckeRemovableCandidateQuarterShiftedRawTrigIdentityProp : Prop :=
  ∀ x : ℝ, x ≠ 0 → x ≠ (1 / 2 : ℝ) →
    standardGabckeRawPsi (x + 1 / 4) =
      Real.sin (Real.pi * x - 2 * Real.pi * x ^ 2) /
        Real.sin (2 * Real.pi * x)

/-- Numerator trigonometric shift for the raw quotient at `p = x + 1/4`. -/
def StandardGabckeQuarterShiftedRawNumeratorTrigProp : Prop :=
  ∀ x : ℝ,
    Real.cos (2 * Real.pi * ((x + 1 / 4) ^ 2 - (x + 1 / 4) - 1 / 16)) =
      -Real.sin (Real.pi * x - 2 * Real.pi * x ^ 2)

/-- The numerator quarter-shift identity after normalizing the shifted
quadratic phase to `-(y + pi/2)`. -/
theorem standardGabckeQuarterShiftedRawNumeratorTrigProp_proved :
    StandardGabckeQuarterShiftedRawNumeratorTrigProp := by
  intro x
  let y : ℝ := Real.pi * x - 2 * Real.pi * x ^ 2
  have hangle :
      2 * Real.pi * ((x + 1 / 4) ^ 2 - (x + 1 / 4) - 1 / 16) =
        -(y + Real.pi / 2) := by
    dsimp [y]
    ring
  rw [hangle, Real.cos_neg, Real.cos_add, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  dsimp [y]
  ring

/-- Denominator trigonometric shift for the raw quotient at `p = x + 1/4`. -/
def StandardGabckeQuarterShiftedRawDenominatorTrigProp : Prop :=
  ∀ x : ℝ,
    Real.cos (2 * Real.pi * (x + 1 / 4)) = -Real.sin (2 * Real.pi * x)

/-- The denominator quarter-shift identity follows from angle normalization
`2*pi*(x+1/4) = 2*pi*x + pi/2` and the standard addition formula. -/
theorem standardGabckeQuarterShiftedRawDenominatorTrigProp_proved :
    StandardGabckeQuarterShiftedRawDenominatorTrigProp := by
  intro x
  have hangle :
      2 * Real.pi * (x + 1 / 4) = 2 * Real.pi * x + Real.pi / 2 := by
    ring
  rw [hangle, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-- The quotient signs introduced by the two quarter-shift trig identities
cancel algebraically. -/
def StandardGabckeQuarterShiftedRawTrigSignCancellationProp : Prop :=
  ∀ x : ℝ,
    (-Real.sin (Real.pi * x - 2 * Real.pi * x ^ 2)) /
        (-Real.sin (2 * Real.pi * x)) =
      Real.sin (Real.pi * x - 2 * Real.pi * x ^ 2) /
        Real.sin (2 * Real.pi * x)

/-- The sign cancellation in the shifted raw quotient is pure field algebra;
it uses no nonvanishing or regularity assumption. -/
theorem standardGabckeQuarterShiftedRawTrigSignCancellationProp_proved :
    StandardGabckeQuarterShiftedRawTrigSignCancellationProp := by
  intro x
  simp [div_eq_mul_inv]

/-- The shifted raw trigonometric identity follows from the numerator and
denominator quarter-shift trig formulas. The off-filled-point hypotheses are
preserved because this theorem feeds the local-function identity route. -/
theorem standardGabckeRemovableCandidateQuarterShiftedRawTrigIdentityProp_of_num_den
    (h_num : StandardGabckeQuarterShiftedRawNumeratorTrigProp)
    (h_den : StandardGabckeQuarterShiftedRawDenominatorTrigProp) :
    StandardGabckeRemovableCandidateQuarterShiftedRawTrigIdentityProp := by
  intro x _hx_zero _hx_half
  unfold standardGabckeRawPsi
  rw [h_num x, h_den x]
  exact standardGabckeQuarterShiftedRawTrigSignCancellationProp_proved x

/-- The shifted raw quotient trigonometric identity is now closed from the
two quarter-shift identities and the algebraic sign cancellation. -/
theorem standardGabckeRemovableCandidateQuarterShiftedRawTrigIdentityProp_proved :
    StandardGabckeRemovableCandidateQuarterShiftedRawTrigIdentityProp :=
  standardGabckeRemovableCandidateQuarterShiftedRawTrigIdentityProp_of_num_den
    standardGabckeQuarterShiftedRawNumeratorTrigProp_proved
    standardGabckeQuarterShiftedRawDenominatorTrigProp_proved

/-- The filled removable values are exactly `x = 0` and `x = 1/2` in the
quarter-point coordinate. -/
theorem standardGabckeRemovableCandidateQuarterShiftedFillEquivProp_proved :
    StandardGabckeRemovableCandidateQuarterShiftedFillEquivProp := by
  intro x
  constructor
  · intro h
    rcases h with h | h
    · left
      linarith
    · right
      linarith
  · intro h
    rcases h with h | h
    · left
      linarith
    · right
      linarith

/-- The shifted local-function identity follows from the elementary filled
point equivalence and the remaining off-point trigonometric quotient identity. -/
theorem standardGabckeRemovableCandidateQuarterLocalFunctionEqProp_of_shiftedRawTrigIdentity
    (h_trig : StandardGabckeRemovableCandidateQuarterShiftedRawTrigIdentityProp) :
    StandardGabckeRemovableCandidateQuarterLocalFunctionEqProp := by
  intro x
  unfold standardGabckeRemovablePsiCandidate standardGabckeQuarterLocalPsi
  have hfill := standardGabckeRemovableCandidateQuarterShiftedFillEquivProp_proved x
  by_cases hx : x = 0 ∨ x = (1 / 2 : ℝ)
  · have hshift :
        x + 1 / 4 = (1 / 4 : ℝ) ∨ x + 1 / 4 = (3 / 4 : ℝ) :=
      hfill.mpr hx
    rw [if_pos hshift, if_pos hx]
  · have hshift :
        ¬ (x + 1 / 4 = (1 / 4 : ℝ) ∨ x + 1 / 4 = (3 / 4 : ℝ)) := by
      intro h
      exact hx (hfill.mp h)
    have hx_zero : x ≠ 0 := by
      intro h
      exact hx (Or.inl h)
    have hx_half : x ≠ (1 / 2 : ℝ) := by
      intro h
      exact hx (Or.inr h)
    rw [if_neg hshift, if_neg hx]
    exact h_trig x hx_zero hx_half

/-- The pointwise quarter-local removable candidate identity follows from the
closed shifted raw quotient identity and the filled-point equivalence. -/
theorem standardGabckeRemovableCandidateQuarterLocalFunctionEqProp_proved :
    StandardGabckeRemovableCandidateQuarterLocalFunctionEqProp :=
  standardGabckeRemovableCandidateQuarterLocalFunctionEqProp_of_shiftedRawTrigIdentity
    standardGabckeRemovableCandidateQuarterShiftedRawTrigIdentityProp_proved

/-- The quarter coordinate bridge follows from the translation derivative atom
and the pointwise local-coordinate identity. -/
theorem standardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp_of_translation_and_functionEq
    (h_translate :
      StandardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp)
    (h_fun : StandardGabckeRemovableCandidateQuarterLocalFunctionEqProp) :
    StandardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp := by
  unfold StandardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp at h_translate
  unfold StandardGabckeRemovableCandidateQuarterLocalFunctionEqProp at h_fun
  unfold StandardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp
  have hfun :
      (fun x : ℝ => standardGabckeRemovablePsiCandidate (x + 1 / 4)) =
        standardGabckeQuarterLocalPsi := funext h_fun
  have hderiv :
      deriv (deriv (deriv (fun x : ℝ =>
        standardGabckeRemovablePsiCandidate (x + 1 / 4)))) 0 =
        deriv (deriv (deriv standardGabckeQuarterLocalPsi)) 0 := by
    rw [hfun]
  exact h_translate.trans hderiv

/-- The quarter coordinate bridge is now closed from the translation derivative
lemma and the already-closed pointwise local-function identity. -/
theorem standardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp_proved :
    StandardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp :=
  standardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp_of_translation_and_functionEq
    standardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp_proved
    standardGabckeRemovableCandidateQuarterLocalFunctionEqProp_proved

/-- Exact one-variable local Taylor value for the quarter removable quotient.
This is the pure calculus atom for the expansion
`sin (pi*x - 2*pi*x^2) / sin (2*pi*x)` at `x = 0`. -/
def StandardGabckeQuarterLocalThirdDerivativeFormulaProp : Prop :=
  deriv (deriv (deriv standardGabckeQuarterLocalPsi)) 0 = -Real.pi ^ 2

/-- Exact local power-series source for the cubic Taylor coefficient of the
filled quotient `standardGabckeQuarterLocalPsi` at `0`.

The coefficient statement is deliberately local and coefficient-shaped:
`-pi^2 / 6` is the cubic Taylor coefficient, hence the third derivative is
`3! * (-pi^2 / 6) = -pi^2`. -/
def StandardGabckeQuarterLocalCubicTaylorCoefficientProp : Prop :=
  ∃ P : FormalMultilinearSeries ℝ ℝ ℝ,
    HasFPowerSeriesAt standardGabckeQuarterLocalPsi P 0 ∧
      P 3 (fun _ : Fin 3 => (1 : ℝ)) = -Real.pi ^ 2 / 6

/-- Scalar Taylor-series source for the filled local quotient at `0`.
This keeps the remaining analytic work at the one-variable coefficient level:
exhibit scalar coefficients for the local power series and prove the cubic
coefficient is `-pi^2 / 6`. -/
def StandardGabckeQuarterLocalScalarTaylorSeriesProp : Prop :=
  ∃ a : ℕ → ℝ,
    HasFPowerSeriesAt standardGabckeQuarterLocalPsi
      (FormalMultilinearSeries.ofScalars ℝ a) 0 ∧
      a 3 = -Real.pi ^ 2 / 6

/-- One-variable scalar source for the filled local quotient expansion at
`0`. This removes the formal multilinear layer from the remaining work:
prove the usual local scalar series sum and its cubic coefficient. -/
def StandardGabckeQuarterLocalScalarHasSumExpansionProp : Prop :=
  ∃ a : ℕ → ℝ,
    (∀ᶠ w in 𝓝 (0 : ℝ),
      HasSum (fun n : ℕ => w ^ n * a n) (standardGabckeQuarterLocalPsi w)) ∧
      a 3 = -Real.pi ^ 2 / 6

/-- Punctured-neighborhood sine-quotient source for the local scalar
expansion. This is the exact analytic atom below the filled local quotient:
away from the removable point `0`, expand the explicit sine quotient and
record the constant and cubic coefficients. -/
def StandardGabckeQuarterLocalPuncturedSineQuotientExpansionProp : Prop :=
  ∃ a : ℕ → ℝ,
    a 0 = 1 / 2 ∧
      a 3 = -Real.pi ^ 2 / 6 ∧
      ∀ᶠ w in 𝓝[≠] (0 : ℝ),
        HasSum (fun n : ℕ => w ^ n * a n)
          (Real.sin (Real.pi * w - 2 * Real.pi * w ^ 2) /
            Real.sin (2 * Real.pi * w))

/-- The sine quotient with only the `w = 0` removable value filled. This is
the local analytic object below `standardGabckeQuarterLocalPsi`; the later
`x = 1/2` fill is irrelevant near `0`. -/
def standardGabckeQuarterLocalRemovableSineQuotient (w : ℝ) : ℝ :=
  if w = 0 then
    1 / 2
  else
    Real.sin (Real.pi * w - 2 * Real.pi * w ^ 2) /
      Real.sin (2 * Real.pi * w)

/-- Numerator of the local sine quotient before removing the common zero at
`w = 0`. -/
def standardGabckeQuarterLocalSineNumerator (w : ℝ) : ℝ :=
  Real.sin (Real.pi * w - 2 * Real.pi * w ^ 2)

/-- Denominator of the local sine quotient before removing the common zero at
`w = 0`. -/
def standardGabckeQuarterLocalSineDenominator (w : ℝ) : ℝ :=
  Real.sin (2 * Real.pi * w)

/-- Exact local power-series source for the removable sine quotient at `0`.
This is the remaining analytic expansion theorem in standard `HasFPowerSeriesAt`
form, with the two coefficients needed downstream named explicitly. -/
def StandardGabckeQuarterLocalRemovableSineQuotientPowerSeriesProp : Prop :=
  ∃ a : ℕ → ℝ,
    HasFPowerSeriesAt standardGabckeQuarterLocalRemovableSineQuotient
      (FormalMultilinearSeries.ofScalars ℝ a) 0 ∧
      a 0 = 1 / 2 ∧
      a 3 = -Real.pi ^ 2 / 6

/-- Exact local power-series source for the quotient after removing the common
zero by `dslope`. This is the remaining sine-composition/division coefficient
calculation without the removable `if` wrapper. -/
def StandardGabckeQuarterLocalDslopeQuotientPowerSeriesProp : Prop :=
  ∃ a : ℕ → ℝ,
    HasFPowerSeriesAt
      (fun w : ℝ =>
        dslope standardGabckeQuarterLocalSineNumerator 0 w /
          dslope standardGabckeQuarterLocalSineDenominator 0 w)
      (FormalMultilinearSeries.ofScalars ℝ a) 0 ∧
      a 0 = 1 / 2 ∧
      a 3 = -Real.pi ^ 2 / 6

/-- Exact coefficient data for the numerator dslope through cubic order.
For `sin(pi*w - 2*pi*w^2) / w`, the coefficients are
`pi, -2*pi, -pi^3/6, pi^3`. -/
def StandardGabckeQuarterLocalNumeratorDslopeCoefficientDataProp : Prop :=
  ∃ A : ℕ → ℝ,
    HasFPowerSeriesAt (dslope standardGabckeQuarterLocalSineNumerator 0)
      (FormalMultilinearSeries.ofScalars ℝ A) 0 ∧
      A 0 = Real.pi ∧
      A 1 = -2 * Real.pi ∧
      A 2 = -Real.pi ^ 3 / 6 ∧
      A 3 = Real.pi ^ 3

/-- Exact raw Taylor coefficient data for
`sin (pi*w - 2*pi*w^2)` through fourth order. The `dslope`/`fslope`
transfer shifts these indices down to the numerator dslope coefficient data. -/
def StandardGabckeQuarterLocalNumeratorRawSineCoefficientDataProp : Prop :=
  ∃ A : ℕ → ℝ,
    HasFPowerSeriesAt standardGabckeQuarterLocalSineNumerator
      (FormalMultilinearSeries.ofScalars ℝ A) 0 ∧
      A 1 = Real.pi ∧
      A 2 = -2 * Real.pi ∧
      A 3 = -Real.pi ^ 3 / 6 ∧
      A 4 = Real.pi ^ 3

/-- Exact coefficient data for the denominator dslope through cubic order.
For `sin(2*pi*w) / w`, the coefficients are
`2*pi, 0, -4*pi^3/3, 0`. -/
def StandardGabckeQuarterLocalDenominatorDslopeCoefficientDataProp : Prop :=
  ∃ B : ℕ → ℝ,
    HasFPowerSeriesAt (dslope standardGabckeQuarterLocalSineDenominator 0)
      (FormalMultilinearSeries.ofScalars ℝ B) 0 ∧
      B 0 = 2 * Real.pi ∧
      B 1 = 0 ∧
      B 2 = -(4 * Real.pi ^ 3 / 3) ∧
      B 3 = 0

/-- Explicit all-order coefficient formula for the denominator dslope
`sin(2*pi*w) / w`. Only even powers occur, with coefficient
`(-1)^m * (2*pi)^(2*m+1)/(2*m+1)!` at order `2*m`. -/
def standardGabckeQuarterLocalDenominatorDslopeCoeff (n : ℕ) : ℝ :=
  if Even n then
    (-1 : ℝ) ^ (n / 2) * (2 * Real.pi) ^ (n + 1) /
      ((n + 1).factorial : ℝ)
  else
    0

/-- Exact sine-series source for the denominator dslope. This is the all-order
source formula below the finite denominator coefficient data. -/
def StandardGabckeQuarterLocalDenominatorDslopeSineSeriesProp : Prop :=
  HasFPowerSeriesAt (dslope standardGabckeQuarterLocalSineDenominator 0)
    (FormalMultilinearSeries.ofScalars ℝ
      standardGabckeQuarterLocalDenominatorDslopeCoeff) 0

/-- Low-order Taylor derivative source for the denominator dslope
`sin(2*pi*w) / w`. This is the finite coefficient content needed downstream
if the all-order sine series has not yet been instantiated. -/
def StandardGabckeQuarterLocalDenominatorDslopeLowOrderDerivativeProp : Prop :=
  iteratedDeriv 1 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 = 0 ∧
    iteratedDeriv 2 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 =
      -(8 * Real.pi ^ 3 / 3) ∧
    iteratedDeriv 3 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 = 0

/-- First derivative value for the denominator dslope at the removable point. -/
def StandardGabckeQuarterLocalDenominatorDslopeFirstDerivativeProp : Prop :=
  iteratedDeriv 1 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 = 0

/-- Second derivative value for the denominator dslope at the removable point. -/
def StandardGabckeQuarterLocalDenominatorDslopeSecondDerivativeProp : Prop :=
  iteratedDeriv 2 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 =
    -(8 * Real.pi ^ 3 / 3)

/-- Exact quadratic coefficient source for the denominator dslope. This is the
coefficient-level input equivalent to the second derivative value, stated in
the local `HasFPowerSeriesAt` form used by the quotient calculation. -/
def StandardGabckeQuarterLocalDenominatorDslopeQuadraticCoefficientProp : Prop :=
  ∃ B : ℕ → ℝ,
    HasFPowerSeriesAt (dslope standardGabckeQuarterLocalSineDenominator 0)
      (FormalMultilinearSeries.ofScalars ℝ B) 0 ∧
      B 2 = -(4 * Real.pi ^ 3 / 3)

/-- Exact cubic coefficient source for the raw denominator sine
`sin (2*pi*w)`. The `dslope`/`fslope` transfer shifts this cubic coefficient
to the quadratic coefficient of `sin (2*pi*w) / w`. -/
def StandardGabckeQuarterLocalDenominatorRawSineCubicCoefficientProp : Prop :=
  ∃ A : ℕ → ℝ,
    HasFPowerSeriesAt standardGabckeQuarterLocalSineDenominator
      (FormalMultilinearSeries.ofScalars ℝ A) 0 ∧
      A 3 = -(4 * Real.pi ^ 3 / 3)

/-- Third derivative value for the denominator dslope at the removable point. -/
def StandardGabckeQuarterLocalDenominatorDslopeThirdDerivativeProp : Prop :=
  iteratedDeriv 3 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 = 0

/-- Formal division/coefficient step from the numerator and denominator dslope
series data to the quotient series coefficient `-pi^2/6`. -/
def StandardGabckeQuarterLocalDslopeQuotientDivisionCoefficientProp : Prop :=
  StandardGabckeQuarterLocalNumeratorDslopeCoefficientDataProp →
    StandardGabckeQuarterLocalDenominatorDslopeCoefficientDataProp →
      StandardGabckeQuarterLocalDslopeQuotientPowerSeriesProp

/-- Cubic derivative value for the removable sine quotient at `0`. -/
def StandardGabckeQuarterLocalRemovableSineQuotientThirdDerivativeProp : Prop :=
  iteratedDeriv 3 standardGabckeQuarterLocalRemovableSineQuotient 0 =
    -Real.pi ^ 2

/-- Exact removable-division bridge for the sine quotient. The common zero is
removed by passing to `dslope` for the numerator and denominator; the remaining
division is ordinary analytic division because the denominator dslope is
nonzero at `0`. -/
def StandardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp : Prop :=
  (standardGabckeQuarterLocalRemovableSineQuotient =ᶠ[𝓝 (0 : ℝ)]
      fun w : ℝ =>
        dslope standardGabckeQuarterLocalSineNumerator 0 w /
          dslope standardGabckeQuarterLocalSineDenominator 0 w) ∧
    AnalyticAt ℝ (dslope standardGabckeQuarterLocalSineNumerator 0) 0 ∧
    AnalyticAt ℝ (dslope standardGabckeQuarterLocalSineDenominator 0) 0 ∧
    dslope standardGabckeQuarterLocalSineDenominator 0 0 ≠ 0 ∧
    iteratedDeriv 3 standardGabckeQuarterLocalRemovableSineQuotient 0 =
      -Real.pi ^ 2

/-- Exact value of the denominator dslope at the removable point. -/
def StandardGabckeQuarterLocalDenominatorDslopeValueProp : Prop :=
  dslope standardGabckeQuarterLocalSineDenominator 0 0 = 2 * Real.pi

/-- The denominator dslope is nonzero at the removable point. -/
def StandardGabckeQuarterLocalDenominatorDslopeNonzeroProp : Prop :=
  dslope standardGabckeQuarterLocalSineDenominator 0 0 ≠ 0

/-- The denominator dslope is analytic at the removable point. -/
def StandardGabckeQuarterLocalDenominatorDslopeAnalyticProp : Prop :=
  AnalyticAt ℝ (dslope standardGabckeQuarterLocalSineDenominator 0) 0

/-- The numerator dslope is analytic at the removable point. -/
def StandardGabckeQuarterLocalNumeratorDslopeAnalyticProp : Prop :=
  AnalyticAt ℝ (dslope standardGabckeQuarterLocalSineNumerator 0) 0

/-- Exact value of the numerator dslope at the removable point. -/
def StandardGabckeQuarterLocalNumeratorDslopeValueProp : Prop :=
  dslope standardGabckeQuarterLocalSineNumerator 0 0 = Real.pi

/-- The removable quotient is locally the quotient of numerator and
denominator dslopes. -/
def StandardGabckeQuarterLocalRemovableSineQuotientDslopeEqualityProp : Prop :=
  standardGabckeQuarterLocalRemovableSineQuotient =ᶠ[𝓝 (0 : ℝ)]
    fun w : ℝ =>
      dslope standardGabckeQuarterLocalSineNumerator 0 w /
        dslope standardGabckeQuarterLocalSineDenominator 0 w

/-- The denominator dslope is the derivative of `sin (2*pi*w)` at `0`, hence
`2*pi`. -/
theorem standardGabckeQuarterLocalDenominatorDslopeValueProp_proved :
    StandardGabckeQuarterLocalDenominatorDslopeValueProp := by
  unfold StandardGabckeQuarterLocalDenominatorDslopeValueProp
  rw [dslope_same]
  have hlin : HasDerivAt (fun w : ℝ => (2 * Real.pi) * w) (2 * Real.pi) 0 := by
    simpa using (hasDerivAt_const_mul (x := (0 : ℝ)) (2 * Real.pi))
  have hsin :
      HasDerivAt (fun w : ℝ => Real.sin ((2 * Real.pi) * w))
        (2 * Real.pi) 0 := by
    simpa using hlin.sin
  have hderiv :
      deriv (fun w : ℝ => Real.sin ((2 * Real.pi) * w)) 0 =
        2 * Real.pi := hsin.deriv
  simpa [standardGabckeQuarterLocalSineDenominator] using hderiv

/-- Nonvanishing follows from the exact denominator-dslope value. -/
theorem standardGabckeQuarterLocalDenominatorDslopeNonzeroProp_proved :
    StandardGabckeQuarterLocalDenominatorDslopeNonzeroProp := by
  unfold StandardGabckeQuarterLocalDenominatorDslopeNonzeroProp
  rw [standardGabckeQuarterLocalDenominatorDslopeValueProp_proved]
  exact mul_ne_zero (by norm_num) Real.pi_ne_zero

/-- A differentiable function that is locally even at the origin has zero first
derivative there. -/
private theorem deriv_zero_of_eventually_even_at_zero {f : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f 0) (heven : (fun x : ℝ => f (-x)) =ᶠ[𝓝 0] f) :
    deriv f 0 = 0 := by
  have hderiv : HasDerivAt f (deriv f 0) 0 := hf.hasDerivAt
  have hneg : HasDerivAt (fun x : ℝ => f (-x)) (-(deriv f 0)) 0 := by
    have hderiv_neg_zero : HasDerivAt f (deriv f 0) (-0) := by
      simpa using hderiv
    simpa using hderiv_neg_zero.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have hsame : HasDerivAt f (-(deriv f 0)) 0 :=
    hneg.congr_of_eventuallyEq heven.symm
  have h_eq : deriv f 0 = -(deriv f 0) := hsame.deriv
  linarith

/-- Analyticity of the denominator dslope follows from the power series of
`sin (2*pi*w)` and the Mathlib `dslope` power-series transfer. -/
theorem standardGabckeQuarterLocalDenominatorDslopeAnalyticProp_proved :
    StandardGabckeQuarterLocalDenominatorDslopeAnalyticProp := by
  unfold StandardGabckeQuarterLocalDenominatorDslopeAnalyticProp
  have hden : AnalyticAt ℝ standardGabckeQuarterLocalSineDenominator 0 := by
    have hlin : AnalyticAt ℝ (fun w : ℝ => (2 * Real.pi) * w) 0 :=
      analyticAt_const.mul analyticAt_id
    simpa [standardGabckeQuarterLocalSineDenominator] using
      (Real.analyticAt_sin.comp hlin)
  obtain ⟨p, hp⟩ := hden
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- The denominator dslope is an even function. -/
private theorem standardGabckeQuarterLocalDenominatorDslope_even :
    (fun w : ℝ => dslope standardGabckeQuarterLocalSineDenominator 0 (-w)) =
      fun w : ℝ => dslope standardGabckeQuarterLocalSineDenominator 0 w := by
  funext w
  by_cases hw : w = 0
  · subst w
    simp
  · have hn : -w ≠ 0 := neg_ne_zero.mpr hw
    rw [dslope_of_ne standardGabckeQuarterLocalSineDenominator hn,
      dslope_of_ne standardGabckeQuarterLocalSineDenominator hw]
    simp [slope_def_field, standardGabckeQuarterLocalSineDenominator]

/-- The first derivative of the denominator dslope vanishes at the removable
point by evenness. -/
theorem standardGabckeQuarterLocalDenominatorDslopeFirstDerivativeProp_proved :
    StandardGabckeQuarterLocalDenominatorDslopeFirstDerivativeProp := by
  unfold StandardGabckeQuarterLocalDenominatorDslopeFirstDerivativeProp
  rw [iteratedDeriv_one]
  have hf : DifferentiableAt ℝ (dslope standardGabckeQuarterLocalSineDenominator 0) 0 :=
    standardGabckeQuarterLocalDenominatorDslopeAnalyticProp_proved.differentiableAt
  have heven :
      (fun w : ℝ => dslope standardGabckeQuarterLocalSineDenominator 0 (-w)) =ᶠ[𝓝 0]
        dslope standardGabckeQuarterLocalSineDenominator 0 :=
    Filter.Eventually.of_forall (congrFun standardGabckeQuarterLocalDenominatorDslope_even)
  exact deriv_zero_of_eventually_even_at_zero hf heven

/-- A quadratic Taylor coefficient for the denominator dslope gives the exact
second derivative value by uniqueness of local power-series coefficients. -/
theorem standardGabckeQuarterLocalDenominatorDslopeSecondDerivativeProp_of_quadraticCoefficient
    (hquad : StandardGabckeQuarterLocalDenominatorDslopeQuadraticCoefficientProp) :
    StandardGabckeQuarterLocalDenominatorDslopeSecondDerivativeProp := by
  rcases hquad with ⟨B, hB, hB2⟩
  unfold StandardGabckeQuarterLocalDenominatorDslopeSecondDerivativeProp
  let f : ℝ → ℝ := dslope standardGabckeQuarterLocalSineDenominator 0
  have h_analytic : AnalyticAt ℝ f 0 :=
    standardGabckeQuarterLocalDenominatorDslopeAnalyticProp_proved
  have hTaylor :
      HasFPowerSeriesAt f
        (FormalMultilinearSeries.ofScalars ℝ
          (fun n : ℕ => iteratedDeriv n f 0 / n.factorial)) 0 :=
    h_analytic.hasFPowerSeriesAt
  have hseries :
      FormalMultilinearSeries.ofScalars ℝ B =
        FormalMultilinearSeries.ofScalars ℝ
          (fun n : ℕ => iteratedDeriv n f 0 / n.factorial) :=
    hB.eq_formalMultilinearSeries hTaylor
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff 2) hseries
  have hquad' :
      iteratedDeriv 2 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 / 2 =
        -(4 * Real.pi ^ 3 / 3) := by
    simpa [f, hB2] using hcoeff.symm
  calc
    iteratedDeriv 2 (dslope standardGabckeQuarterLocalSineDenominator 0) 0
        = 2 * (iteratedDeriv 2 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 / 2) := by
          ring
    _ = 2 * (-(4 * Real.pi ^ 3 / 3)) := by rw [hquad']
    _ = -(8 * Real.pi ^ 3 / 3) := by ring

/-- Analyticity of the numerator dslope follows from the analytic polynomial
phase `pi*w - 2*pi*w^2` and the Mathlib `dslope` power-series transfer. -/
theorem standardGabckeQuarterLocalNumeratorDslopeAnalyticProp_proved :
    StandardGabckeQuarterLocalNumeratorDslopeAnalyticProp := by
  unfold StandardGabckeQuarterLocalNumeratorDslopeAnalyticProp
  have hnum : AnalyticAt ℝ standardGabckeQuarterLocalSineNumerator 0 := by
    have hphase :
        AnalyticAt ℝ (fun w : ℝ => Real.pi * w - 2 * Real.pi * w ^ 2) 0 :=
      (analyticAt_const.mul analyticAt_id).sub
        (analyticAt_const.mul (analyticAt_id.pow 2))
    simpa [standardGabckeQuarterLocalSineNumerator] using
      (Real.analyticAt_sin.comp hphase)
  obtain ⟨p, hp⟩ := hnum
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- The numerator dslope is the derivative of
`sin (pi*w - 2*pi*w^2)` at `0`, hence `pi`. -/
theorem standardGabckeQuarterLocalNumeratorDslopeValueProp_proved :
    StandardGabckeQuarterLocalNumeratorDslopeValueProp := by
  unfold StandardGabckeQuarterLocalNumeratorDslopeValueProp
  rw [dslope_same]
  have hphase :
      HasDerivAt (fun w : ℝ => Real.pi * w - 2 * Real.pi * w ^ 2) Real.pi 0 := by
    have hlin : HasDerivAt (fun w : ℝ => Real.pi * w) Real.pi 0 := by
      simpa using (hasDerivAt_const_mul (x := (0 : ℝ)) Real.pi)
    have hquad : HasDerivAt (fun w : ℝ => 2 * Real.pi * w ^ 2) 0 0 := by
      have hquad' : HasDerivAt (fun w : ℝ => (2 * Real.pi * w) * w) 0 0 := by
        simpa using
        ((hasDerivAt_const_mul (x := (0 : ℝ)) (2 * Real.pi)).mul
          (hasDerivAt_id (x := (0 : ℝ))))
      convert hquad' using 1
      · ext w
        ring
    simpa using hlin.sub hquad
  have hsin :
      HasDerivAt (fun w : ℝ => Real.sin (Real.pi * w - 2 * Real.pi * w ^ 2))
        Real.pi 0 := by
    simpa using hphase.sin
  have hderiv :
      deriv (fun w : ℝ => Real.sin (Real.pi * w - 2 * Real.pi * w ^ 2)) 0 =
        Real.pi := hsin.deriv
  simpa [standardGabckeQuarterLocalSineNumerator] using hderiv

/-- Pointwise form of the local removable-division identity. At `w = 0` this
uses the just-proved numerator and denominator dslope values; away from `0` it
is the quotient identity for the two slopes. -/
theorem standardGabckeQuarterLocalRemovableSineQuotient_eq_dslope_quotient
    (w : ℝ) :
    standardGabckeQuarterLocalRemovableSineQuotient w =
      dslope standardGabckeQuarterLocalSineNumerator 0 w /
        dslope standardGabckeQuarterLocalSineDenominator 0 w := by
  by_cases hw : w = 0
  · subst w
    rw [standardGabckeQuarterLocalNumeratorDslopeValueProp_proved,
      standardGabckeQuarterLocalDenominatorDslopeValueProp_proved]
    simp [standardGabckeQuarterLocalRemovableSineQuotient]
    field_simp [Real.pi_ne_zero]
  · have hw0 : w ≠ 0 := hw
    rw [standardGabckeQuarterLocalRemovableSineQuotient, if_neg hw0]
    rw [dslope_of_ne standardGabckeQuarterLocalSineNumerator hw0,
      dslope_of_ne standardGabckeQuarterLocalSineDenominator hw0]
    simp [slope, standardGabckeQuarterLocalSineNumerator,
      standardGabckeQuarterLocalSineDenominator]
    rw [mul_div_mul_left _ _ (inv_ne_zero hw0)]

/-- The local equality clause of the dslope bridge is now pointwise true. -/
theorem standardGabckeQuarterLocalRemovableSineQuotientDslopeEqualityProp_proved :
    StandardGabckeQuarterLocalRemovableSineQuotientDslopeEqualityProp := by
  exact Filter.Eventually.of_forall
    standardGabckeQuarterLocalRemovableSineQuotient_eq_dslope_quotient

/-- A power series for the dslope quotient transfers to the removable sine
quotient by the already-proved pointwise equality. -/
theorem standardGabckeQuarterLocalRemovableSineQuotientPowerSeriesProp_of_dslopeQuotient
    (h_series : StandardGabckeQuarterLocalDslopeQuotientPowerSeriesProp) :
    StandardGabckeQuarterLocalRemovableSineQuotientPowerSeriesProp := by
  rcases h_series with ⟨a, hseries, ha0, ha3⟩
  refine ⟨a, ?_, ha0, ha3⟩
  exact hseries.congr
    standardGabckeQuarterLocalRemovableSineQuotientDslopeEqualityProp_proved.symm

/-- The explicit all-order denominator sine-series formula supplies the finite
coefficient data needed by the quotient calculation. -/
theorem standardGabckeQuarterLocalDenominatorDslopeCoefficientDataProp_of_sineSeries
    (h_series : StandardGabckeQuarterLocalDenominatorDslopeSineSeriesProp) :
    StandardGabckeQuarterLocalDenominatorDslopeCoefficientDataProp := by
  refine ⟨standardGabckeQuarterLocalDenominatorDslopeCoeff, h_series, ?_, ?_, ?_, ?_⟩
  · norm_num [standardGabckeQuarterLocalDenominatorDslopeCoeff]
  · norm_num [standardGabckeQuarterLocalDenominatorDslopeCoeff]
  · norm_num [standardGabckeQuarterLocalDenominatorDslopeCoeff]
    ring
  · norm_num [standardGabckeQuarterLocalDenominatorDslopeCoeff]

/-- The all-order denominator sine-series source supplies the exact quadratic
coefficient source needed for the second-derivative value. -/
theorem standardGabckeQuarterLocalDenominatorDslopeQuadraticCoefficientProp_of_sineSeries
    (h_series : StandardGabckeQuarterLocalDenominatorDslopeSineSeriesProp) :
    StandardGabckeQuarterLocalDenominatorDslopeQuadraticCoefficientProp := by
  refine ⟨standardGabckeQuarterLocalDenominatorDslopeCoeff, h_series, ?_⟩
  norm_num [standardGabckeQuarterLocalDenominatorDslopeCoeff]
  ring

/-- The third derivative of the raw denominator sine at the origin. -/
private theorem standardGabckeQuarterLocalDenominatorRawSine_thirdDerivative :
    iteratedDeriv 3 standardGabckeQuarterLocalSineDenominator 0 =
      -(8 * Real.pi ^ 3) := by
  have hcomp := congrFun
    (iteratedDeriv_comp_const_mul (𝕜 := ℝ) (n := 3) Real.contDiff_sin (2 * Real.pi)) 0
  have hsin3 : iteratedDeriv 3 Real.sin 0 = -1 := by
    norm_num [Real.iteratedDeriv_odd_sin]
  have hcomp' :
      iteratedDeriv 3 standardGabckeQuarterLocalSineDenominator 0 =
        (2 * Real.pi) ^ 3 * iteratedDeriv 3 Real.sin ((2 * Real.pi) * 0) := by
    simpa [standardGabckeQuarterLocalSineDenominator] using hcomp
  have hsin3' : iteratedDeriv 3 Real.sin ((2 * Real.pi) * 0) = -1 := by
    simp [hsin3]
  rw [hcomp', hsin3']
  ring

/-- The fourth derivative of the raw denominator sine vanishes at the origin. -/
private theorem standardGabckeQuarterLocalDenominatorRawSine_fourthDerivative :
    iteratedDeriv 4 standardGabckeQuarterLocalSineDenominator 0 = 0 := by
  have hcomp := congrFun
    (iteratedDeriv_comp_const_mul (𝕜 := ℝ) (n := 4) Real.contDiff_sin (2 * Real.pi)) 0
  have hsin4 : iteratedDeriv 4 Real.sin 0 = 0 := by
    norm_num [Real.iteratedDeriv_even_sin]
  have hcomp' :
      iteratedDeriv 4 standardGabckeQuarterLocalSineDenominator 0 =
        (2 * Real.pi) ^ 4 * iteratedDeriv 4 Real.sin ((2 * Real.pi) * 0) := by
    simpa [standardGabckeQuarterLocalSineDenominator] using hcomp
  have hsin4' : iteratedDeriv 4 Real.sin ((2 * Real.pi) * 0) = 0 := by
    simp [hsin4]
  rw [hcomp', hsin4']
  ring

/-- The raw sine Taylor series has cubic coefficient
`-(4*pi^3/3)`. This is the local sine-composition coefficient source below
the denominator dslope quadratic coefficient. -/
theorem standardGabckeQuarterLocalDenominatorRawSineCubicCoefficientProp_proved :
    StandardGabckeQuarterLocalDenominatorRawSineCubicCoefficientProp := by
  unfold StandardGabckeQuarterLocalDenominatorRawSineCubicCoefficientProp
  let f : ℝ → ℝ := standardGabckeQuarterLocalSineDenominator
  let A : ℕ → ℝ := fun n => iteratedDeriv n f 0 / n.factorial
  have h_analytic : AnalyticAt ℝ f 0 := by
    have hlin : AnalyticAt ℝ (fun w : ℝ => (2 * Real.pi) * w) 0 :=
      analyticAt_const.mul analyticAt_id
    simpa [f, standardGabckeQuarterLocalSineDenominator] using
      (Real.analyticAt_sin.comp hlin)
  refine ⟨A, h_analytic.hasFPowerSeriesAt, ?_⟩
  dsimp [A, f]
  rw [standardGabckeQuarterLocalDenominatorRawSine_thirdDerivative]
  ring

/-- For one-variable scalar power series, `fslope` shifts the scalar
coefficients down by one. This is the local coefficient-transfer step from the
raw sine series to the denominator dslope series. -/
private theorem standardGabckeQuarterLocalDenominatorDslope_fslope_ofScalars
    (A : ℕ → ℝ) :
    (FormalMultilinearSeries.ofScalars ℝ A).fslope =
      FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => A (n + 1)) := by
  simp_rw [FormalMultilinearSeries.ext_iff, FormalMultilinearSeries.fslope,
    FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.ext_iff,
    ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.smul_apply]
  intro n v
  simp [ContinuousMultilinearMap.mkPiAlgebraFin_apply]

/-- Raw numerator sine coefficient data transfers to numerator dslope
coefficient data by the same `dslope`/`fslope` index shift. -/
theorem standardGabckeQuarterLocalNumeratorDslopeCoefficientDataProp_of_rawSineCoefficientData
    (h_raw : StandardGabckeQuarterLocalNumeratorRawSineCoefficientDataProp) :
    StandardGabckeQuarterLocalNumeratorDslopeCoefficientDataProp := by
  rcases h_raw with ⟨A, hA, hA1, hA2, hA3, hA4⟩
  refine ⟨fun n : ℕ => A (n + 1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← standardGabckeQuarterLocalDenominatorDslope_fslope_ofScalars A]
    exact hA.has_fpower_series_dslope_fslope
  · simpa using hA1
  · simpa using hA2
  · simpa using hA3
  · simpa using hA4

/-- A raw cubic coefficient for `sin (2*pi*w)` gives the quadratic coefficient
of the removable quotient `sin (2*pi*w) / w` via the Mathlib `dslope`/`fslope`
transfer. -/
theorem standardGabckeQuarterLocalDenominatorDslopeQuadraticCoefficientProp_of_rawSineCubicCoefficient
    (h_raw : StandardGabckeQuarterLocalDenominatorRawSineCubicCoefficientProp) :
    StandardGabckeQuarterLocalDenominatorDslopeQuadraticCoefficientProp := by
  rcases h_raw with ⟨A, hA, hA3⟩
  refine ⟨fun n : ℕ => A (n + 1), ?_, ?_⟩
  · rw [← standardGabckeQuarterLocalDenominatorDslope_fslope_ofScalars A]
    exact hA.has_fpower_series_dslope_fslope
  · simpa using hA3

/-- The denominator dslope quadratic coefficient follows from the now-proved
raw sine cubic coefficient and the `dslope`/`fslope` coefficient transfer. -/
theorem standardGabckeQuarterLocalDenominatorDslopeQuadraticCoefficientProp_proved :
    StandardGabckeQuarterLocalDenominatorDslopeQuadraticCoefficientProp :=
  standardGabckeQuarterLocalDenominatorDslopeQuadraticCoefficientProp_of_rawSineCubicCoefficient
    standardGabckeQuarterLocalDenominatorRawSineCubicCoefficientProp_proved

/-- The exact second derivative value for the denominator dslope follows from
the proved quadratic coefficient by uniqueness of Taylor coefficients. -/
theorem standardGabckeQuarterLocalDenominatorDslopeSecondDerivativeProp_proved :
    StandardGabckeQuarterLocalDenominatorDslopeSecondDerivativeProp :=
  standardGabckeQuarterLocalDenominatorDslopeSecondDerivativeProp_of_quadraticCoefficient
    standardGabckeQuarterLocalDenominatorDslopeQuadraticCoefficientProp_proved

/-- The denominator dslope third derivative vanishes. This is the shifted
fourth Taylor coefficient of the raw denominator sine. -/
theorem standardGabckeQuarterLocalDenominatorDslopeThirdDerivativeProp_proved :
    StandardGabckeQuarterLocalDenominatorDslopeThirdDerivativeProp := by
  unfold StandardGabckeQuarterLocalDenominatorDslopeThirdDerivativeProp
  let g : ℝ → ℝ := standardGabckeQuarterLocalSineDenominator
  let A : ℕ → ℝ := fun n => iteratedDeriv n g 0 / n.factorial
  let B : ℕ → ℝ := fun n => A (n + 1)
  let f : ℝ → ℝ := dslope standardGabckeQuarterLocalSineDenominator 0
  have hg_analytic : AnalyticAt ℝ g 0 := by
    have hlin : AnalyticAt ℝ (fun w : ℝ => (2 * Real.pi) * w) 0 :=
      analyticAt_const.mul analyticAt_id
    simpa [g, standardGabckeQuarterLocalSineDenominator] using
      (Real.analyticAt_sin.comp hlin)
  have hA :
      HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℝ A) 0 :=
    hg_analytic.hasFPowerSeriesAt
  have hB :
      HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ B) 0 := by
    rw [← standardGabckeQuarterLocalDenominatorDslope_fslope_ofScalars A]
    simpa [f, g] using hA.has_fpower_series_dslope_fslope
  have h_analytic : AnalyticAt ℝ f 0 :=
    standardGabckeQuarterLocalDenominatorDslopeAnalyticProp_proved
  have hTaylor :
      HasFPowerSeriesAt f
        (FormalMultilinearSeries.ofScalars ℝ
          (fun n : ℕ => iteratedDeriv n f 0 / n.factorial)) 0 :=
    h_analytic.hasFPowerSeriesAt
  have hseries :
      FormalMultilinearSeries.ofScalars ℝ B =
        FormalMultilinearSeries.ofScalars ℝ
          (fun n : ℕ => iteratedDeriv n f 0 / n.factorial) :=
    hB.eq_formalMultilinearSeries hTaylor
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff 3) hseries
  have hB3 : B 3 = 0 := by
    dsimp [B, A, g]
    rw [standardGabckeQuarterLocalDenominatorRawSine_fourthDerivative]
    norm_num
  have hthird' :
      iteratedDeriv 3 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 / 6 = 0 := by
    have hcoeff' : B 3 = iteratedDeriv 3 f 0 / ((3 : ℕ).factorial : ℝ) := by
      simpa using hcoeff
    rw [hB3] at hcoeff'
    have hcoeff'' :
        iteratedDeriv 3 f 0 / ((3 : ℕ).factorial : ℝ) = 0 := hcoeff'.symm
    norm_num at hcoeff''
    simpa [f] using hcoeff''
  have hthird_mul :
      6 * (iteratedDeriv 3 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 / 6) =
        0 := by
    rw [hthird']
    ring
  calc
    iteratedDeriv 3 (dslope standardGabckeQuarterLocalSineDenominator 0) 0
        = 6 * (iteratedDeriv 3 (dslope standardGabckeQuarterLocalSineDenominator 0) 0 / 6) := by
          ring
    _ = 0 := hthird_mul

/-- The denominator low-order derivative bundle is now closed from the first,
second, and third derivative point values. -/
theorem standardGabckeQuarterLocalDenominatorDslopeLowOrderDerivativeProp_proved :
    StandardGabckeQuarterLocalDenominatorDslopeLowOrderDerivativeProp :=
  ⟨standardGabckeQuarterLocalDenominatorDslopeFirstDerivativeProp_proved,
    standardGabckeQuarterLocalDenominatorDslopeSecondDerivativeProp_proved,
    standardGabckeQuarterLocalDenominatorDslopeThirdDerivativeProp_proved⟩

/-- The finite denominator coefficient data follows from the low-order
derivative values of the removable sine quotient, using Mathlib's Taylor
coefficient power series for analytic one-variable real functions. -/
theorem standardGabckeQuarterLocalDenominatorDslopeCoefficientDataProp_of_lowOrderDerivatives
    (h_deriv : StandardGabckeQuarterLocalDenominatorDslopeLowOrderDerivativeProp) :
    StandardGabckeQuarterLocalDenominatorDslopeCoefficientDataProp := by
  rcases h_deriv with ⟨h1, h2, h3⟩
  let f : ℝ → ℝ := dslope standardGabckeQuarterLocalSineDenominator 0
  let B : ℕ → ℝ := fun n => iteratedDeriv n f 0 / n.factorial
  have h_analytic : AnalyticAt ℝ f 0 :=
    standardGabckeQuarterLocalDenominatorDslopeAnalyticProp_proved
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_analytic.hasFPowerSeriesAt
  · dsimp [B, f]
    rw [iteratedDeriv_zero, standardGabckeQuarterLocalDenominatorDslopeValueProp_proved]
    norm_num
  · dsimp [B, f]
    rw [h1]
    norm_num
  · dsimp [B, f]
    rw [h2]
    ring
  · dsimp [B, f]
    rw [h3]
    norm_num

/-- The denominator dslope coefficient data is closed from the proved
low-order derivative values. -/
theorem standardGabckeQuarterLocalDenominatorDslopeCoefficientDataProp_proved :
    StandardGabckeQuarterLocalDenominatorDslopeCoefficientDataProp :=
  standardGabckeQuarterLocalDenominatorDslopeCoefficientDataProp_of_lowOrderDerivatives
    standardGabckeQuarterLocalDenominatorDslopeLowOrderDerivativeProp_proved

/-- The low-order derivative bundle is reduced to its three point-value atoms.
The first one is already closed by evenness. -/
theorem standardGabckeQuarterLocalDenominatorDslopeLowOrderDerivativeProp_of_pointDerivatives
    (h2 : StandardGabckeQuarterLocalDenominatorDslopeSecondDerivativeProp)
    (h3 : StandardGabckeQuarterLocalDenominatorDslopeThirdDerivativeProp) :
    StandardGabckeQuarterLocalDenominatorDslopeLowOrderDerivativeProp := by
  exact ⟨standardGabckeQuarterLocalDenominatorDslopeFirstDerivativeProp_proved, h2, h3⟩

/-- The quotient series is reduced to explicit numerator/denominator dslope
coefficient data plus the finite formal-division calculation. -/
theorem standardGabckeQuarterLocalDslopeQuotientPowerSeriesProp_of_coefficientData
    (hnum : StandardGabckeQuarterLocalNumeratorDslopeCoefficientDataProp)
    (hden : StandardGabckeQuarterLocalDenominatorDslopeCoefficientDataProp)
    (hdiv : StandardGabckeQuarterLocalDslopeQuotientDivisionCoefficientProp) :
    StandardGabckeQuarterLocalDslopeQuotientPowerSeriesProp :=
  hdiv hnum hden

/-- With the denominator nonzero clause closed, the dslope bridge reduces to
local equality, dslope analyticity, and the third-derivative value. -/
theorem standardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp_of_core
    (heq :
      standardGabckeQuarterLocalRemovableSineQuotient =ᶠ[𝓝 (0 : ℝ)]
        fun w : ℝ =>
          dslope standardGabckeQuarterLocalSineNumerator 0 w /
            dslope standardGabckeQuarterLocalSineDenominator 0 w)
    (hnum : AnalyticAt ℝ (dslope standardGabckeQuarterLocalSineNumerator 0) 0)
    (hden : AnalyticAt ℝ (dslope standardGabckeQuarterLocalSineDenominator 0) 0)
    (hthird :
      iteratedDeriv 3 standardGabckeQuarterLocalRemovableSineQuotient 0 =
        -Real.pi ^ 2) :
    StandardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp := by
  exact ⟨heq, hnum, hden,
    standardGabckeQuarterLocalDenominatorDslopeNonzeroProp_proved, hthird⟩

/-- With the denominator dslope clauses closed, the dslope bridge reduces to
local equality, numerator dslope analyticity, and the third-derivative value. -/
theorem standardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp_of_reducedCore
    (heq :
      standardGabckeQuarterLocalRemovableSineQuotient =ᶠ[𝓝 (0 : ℝ)]
        fun w : ℝ =>
          dslope standardGabckeQuarterLocalSineNumerator 0 w /
            dslope standardGabckeQuarterLocalSineDenominator 0 w)
    (hnum : AnalyticAt ℝ (dslope standardGabckeQuarterLocalSineNumerator 0) 0)
    (hthird :
      iteratedDeriv 3 standardGabckeQuarterLocalRemovableSineQuotient 0 =
        -Real.pi ^ 2) :
    StandardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp := by
  exact standardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp_of_core heq hnum
    standardGabckeQuarterLocalDenominatorDslopeAnalyticProp_proved hthird

/-- With both dslope analytic clauses and denominator nonvanishing closed, the
dslope bridge reduces to local equality and the third-derivative value. -/
theorem standardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp_of_equality_and_third
    (heq :
      standardGabckeQuarterLocalRemovableSineQuotient =ᶠ[𝓝 (0 : ℝ)]
        fun w : ℝ =>
          dslope standardGabckeQuarterLocalSineNumerator 0 w /
            dslope standardGabckeQuarterLocalSineDenominator 0 w)
    (hthird :
      iteratedDeriv 3 standardGabckeQuarterLocalRemovableSineQuotient 0 =
        -Real.pi ^ 2) :
    StandardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp := by
  exact standardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp_of_reducedCore heq
    standardGabckeQuarterLocalNumeratorDslopeAnalyticProp_proved hthird

/-- With all dslope bridge clauses except the cubic derivative closed, the
bridge reduces to the third-derivative value. -/
theorem standardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp_of_third
    (hthird :
      iteratedDeriv 3 standardGabckeQuarterLocalRemovableSineQuotient 0 =
        -Real.pi ^ 2) :
    StandardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp := by
  exact standardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp_of_equality_and_third
    standardGabckeQuarterLocalRemovableSineQuotientDslopeEqualityProp_proved hthird

/-- A removable sine-quotient power series with cubic coefficient `-pi^2/6`
gives the cubic derivative value `-pi^2`. -/
theorem standardGabckeQuarterLocalRemovableSineQuotientThirdDerivativeProp_of_powerSeries
    (h_series : StandardGabckeQuarterLocalRemovableSineQuotientPowerSeriesProp) :
    StandardGabckeQuarterLocalRemovableSineQuotientThirdDerivativeProp := by
  rcases h_series with ⟨a, hseries, _ha0, ha3⟩
  rcases hseries with ⟨_r, hball⟩
  unfold StandardGabckeQuarterLocalRemovableSineQuotientThirdDerivativeProp
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hF :
      iteratedFDeriv ℝ 3 standardGabckeQuarterLocalRemovableSineQuotient 0
          (fun _ : Fin 3 => (1 : ℝ)) =
        ∑ σ : Equiv.Perm (Fin 3),
          (FormalMultilinearSeries.ofScalars ℝ a) 3
            (fun i : Fin 3 => (fun _ : Fin 3 => (1 : ℝ)) (σ i)) := by
    exact hball.iteratedFDeriv_eq_sum_of_completeSpace
      (n := 3) (v := fun _ : Fin 3 => (1 : ℝ))
  refine hF.trans ?_
  calc
    (∑ σ : Equiv.Perm (Fin 3),
        (FormalMultilinearSeries.ofScalars ℝ a) 3
          (fun i : Fin 3 => (fun _ : Fin 3 => (1 : ℝ)) (σ i))) =
        ∑ _σ : Equiv.Perm (Fin 3), (-Real.pi ^ 2 / 6) := by
      simp [ha3]
    _ = (6 : ℝ) * (-Real.pi ^ 2 / 6) := by
      norm_num [Fintype.card_perm]
    _ = -Real.pi ^ 2 := by
      ring

/-- The removable sine-quotient power-series atom supplies the remaining
cubic derivative input to the dslope bridge. -/
theorem standardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp_of_powerSeries
    (h_series : StandardGabckeQuarterLocalRemovableSineQuotientPowerSeriesProp) :
    StandardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp := by
  exact standardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp_of_third
    (standardGabckeQuarterLocalRemovableSineQuotientThirdDerivativeProp_of_powerSeries h_series)

/-- The dslope removable-division bridge supplies the canonical Taylor
power series for the removable sine quotient, with the required constant and
cubic coefficients. -/
theorem standardGabckeQuarterLocalRemovableSineQuotientPowerSeriesProp_of_dslopeBridge
    (h_bridge : StandardGabckeQuarterLocalRemovableSineQuotientDslopeBridgeProp) :
    StandardGabckeQuarterLocalRemovableSineQuotientPowerSeriesProp := by
  rcases h_bridge with ⟨heq, hnum, hden, hden0, hthird⟩
  let f : ℝ → ℝ := standardGabckeQuarterLocalRemovableSineQuotient
  let a : ℕ → ℝ := fun n => iteratedDeriv n f 0 / (n.factorial : ℝ)
  refine ⟨a, ?_, ?_, ?_⟩
  · have hquot :
        AnalyticAt ℝ
          (fun w : ℝ =>
            dslope standardGabckeQuarterLocalSineNumerator 0 w /
              dslope standardGabckeQuarterLocalSineDenominator 0 w) 0 :=
      hnum.div hden hden0
    exact (hquot.congr heq.symm).hasFPowerSeriesAt
  · dsimp [a, f]
    simp [iteratedDeriv_zero, standardGabckeQuarterLocalRemovableSineQuotient]
  · dsimp [a, f]
    rw [hthird]
    norm_num

/-- A local power series for the removable sine quotient gives the punctured
quotient expansion by unfolding `HasFPowerSeriesAt` and ignoring the filled
value away from `w = 0`. -/
theorem standardGabckeQuarterLocalPuncturedSineQuotientExpansionProp_of_removablePowerSeries
    (h_series : StandardGabckeQuarterLocalRemovableSineQuotientPowerSeriesProp) :
    StandardGabckeQuarterLocalPuncturedSineQuotientExpansionProp := by
  rcases h_series with ⟨a, hseries, ha0, ha3⟩
  refine ⟨a, ha0, ha3, ?_⟩
  rw [hasFPowerSeriesAt_iff] at hseries
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hseries] with w hw hw0
  have hw0_ne : w ≠ 0 := by
    simpa using hw0
  simpa [standardGabckeQuarterLocalRemovableSineQuotient,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, hw0_ne] using hw

/-- The punctured sine-quotient expansion plus the removable value at `0`
gives the filled local scalar expansion. The second filled point `1/2` is
outside a sufficiently small neighborhood of `0`. -/
theorem standardGabckeQuarterLocalScalarHasSumExpansionProp_of_puncturedSineQuotient
    (h_series : StandardGabckeQuarterLocalPuncturedSineQuotientExpansionProp) :
    StandardGabckeQuarterLocalScalarHasSumExpansionProp := by
  rcases h_series with ⟨a, ha0, ha3, hpunct⟩
  refine ⟨a, ?_, ha3⟩
  rw [eventually_nhdsWithin_iff] at hpunct
  filter_upwards [hpunct, eventually_ne_nhds (by norm_num :
      (0 : ℝ) ≠ (1 / 2 : ℝ))] with w hquot hw_half
  by_cases hw0 : w = 0
  · subst w
    have hzero :
        HasSum (fun n : ℕ => (0 : ℝ) ^ n * a n) (a 0) := by
      simpa [smul_eq_mul] using
        (HasSum.hasSum_at_zero (𝕜 := ℝ) (E := ℝ) a)
    simpa [standardGabckeQuarterLocalPsi, ha0] using hzero
  · have hw_fill : ¬(w = 0 ∨ w = (1 / 2 : ℝ)) := by
      exact not_or.mpr ⟨hw0, hw_half⟩
    change HasSum (fun n : ℕ => w ^ n * a n)
      (if w = 0 ∨ w = (1 / 2 : ℝ) then
        1 / 2
      else
        Real.sin (Real.pi * w - 2 * Real.pi * w ^ 2) /
          Real.sin (2 * Real.pi * w))
    rw [if_neg hw_fill]
    exact hquot hw0

/-- A scalar local `HasSum` expansion is exactly the one-dimensional
`ofScalars` power-series source required by the scalar Taylor atom. -/
theorem standardGabckeQuarterLocalScalarTaylorSeriesProp_of_hasSumExpansion
    (h_series : StandardGabckeQuarterLocalScalarHasSumExpansionProp) :
    StandardGabckeQuarterLocalScalarTaylorSeriesProp := by
  rcases h_series with ⟨a, hsum, ha3⟩
  refine ⟨a, ?_, ha3⟩
  rw [hasFPowerSeriesAt_iff]
  refine hsum.mono ?_
  intro w hw
  simpa [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul] using hw

/-- A scalar Taylor series with cubic coefficient `-pi^2 / 6` supplies the
formal multilinear witness required by the cubic-coefficient atom. -/
theorem standardGabckeQuarterLocalCubicTaylorCoefficientProp_of_scalarTaylorSeries
    (h_series : StandardGabckeQuarterLocalScalarTaylorSeriesProp) :
    StandardGabckeQuarterLocalCubicTaylorCoefficientProp := by
  rcases h_series with ⟨a, hseries, ha3⟩
  refine ⟨FormalMultilinearSeries.ofScalars ℝ a, hseries, ?_⟩
  rw [FormalMultilinearSeries.ofScalars_apply_eq, ha3]
  norm_num

/-- The exact cubic Taylor coefficient of the local quotient gives the
third-derivative value used by the Gabcke removable-source route. -/
theorem standardGabckeQuarterLocalThirdDerivativeFormulaProp_of_cubicTaylorCoefficient
    (h_coeff : StandardGabckeQuarterLocalCubicTaylorCoefficientProp) :
    StandardGabckeQuarterLocalThirdDerivativeFormulaProp := by
  rcases h_coeff with ⟨P, hP, hP3⟩
  rcases hP with ⟨_r, hPball⟩
  unfold StandardGabckeQuarterLocalThirdDerivativeFormulaProp
  have hF :
      iteratedFDeriv ℝ 3 standardGabckeQuarterLocalPsi 0
          (fun _ : Fin 3 => (1 : ℝ)) =
        ∑ σ : Equiv.Perm (Fin 3),
          P 3 (fun i : Fin 3 => (fun _ : Fin 3 => (1 : ℝ)) (σ i)) := by
    exact hPball.iteratedFDeriv_eq_sum_of_completeSpace
      (n := 3) (v := fun _ : Fin 3 => (1 : ℝ))
  have h_iter :
      iteratedDeriv 3 standardGabckeQuarterLocalPsi 0 = -Real.pi ^ 2 := by
    unfold iteratedDeriv
    refine hF.trans ?_
    calc
      (∑ σ : Equiv.Perm (Fin 3),
          P 3 (fun i : Fin 3 => (fun _ : Fin 3 => (1 : ℝ)) (σ i))) =
          ∑ _σ : Equiv.Perm (Fin 3), (-Real.pi ^ 2 / 6) := by
        simp [hP3]
      _ = (6 : ℝ) * (-Real.pi ^ 2 / 6) := by
        norm_num [Fintype.card_perm]
      _ = -Real.pi ^ 2 := by
        ring
  have h_nested :
      deriv (deriv (deriv standardGabckeQuarterLocalPsi)) 0 =
        iteratedDeriv 3 standardGabckeQuarterLocalPsi 0 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_zero]
  exact h_nested.trans h_iter

/-- `HasDerivAt` form of the local Taylor atom: the second derivative of the
quarter local quotient has derivative `-pi^2` at `x = 0`. This is the smallest
calculus statement needed to identify the third derivative value. -/
def StandardGabckeQuarterLocalSecondDerivativeHasDerivAtProp : Prop :=
  HasDerivAt (deriv (deriv standardGabckeQuarterLocalPsi)) (-Real.pi ^ 2) 0

/-- The `HasDerivAt` local Taylor atom supplies the derivative-value form used
by the Gabcke coefficient route. -/
theorem standardGabckeQuarterLocalThirdDerivativeFormulaProp_of_secondDerivative_hasDerivAt
    (h_deriv : StandardGabckeQuarterLocalSecondDerivativeHasDerivAtProp) :
    StandardGabckeQuarterLocalThirdDerivativeFormulaProp := by
  unfold StandardGabckeQuarterLocalSecondDerivativeHasDerivAtProp at h_deriv
  unfold StandardGabckeQuarterLocalThirdDerivativeFormulaProp
  exact h_deriv.deriv

/-- The candidate quarter-point value formula follows from the exact local
coordinate bridge and the one-variable local Taylor calculation. -/
theorem standardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp_of_localTaylor
    (h_coord :
      StandardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp)
    (h_local : StandardGabckeQuarterLocalThirdDerivativeFormulaProp) :
    StandardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp := by
  unfold StandardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp at h_coord
  unfold StandardGabckeQuarterLocalThirdDerivativeFormulaProp at h_local
  unfold StandardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp
  exact h_coord.trans h_local

/-- The candidate quarter-point value formula follows from the coordinate
bridge plus the `HasDerivAt` form of the local Taylor atom. -/
theorem standardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp_of_localSecondDerivative_hasDerivAt
    (h_coord :
      StandardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp)
    (h_deriv : StandardGabckeQuarterLocalSecondDerivativeHasDerivAtProp) :
    StandardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp :=
  standardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp_of_localTaylor
    h_coord
    (standardGabckeQuarterLocalThirdDerivativeFormulaProp_of_secondDerivative_hasDerivAt
      h_deriv)

/-- The quarter-point numeric Tabelle bound follows from the exact local
Taylor value of the instantiated removable candidate. -/
theorem standardGabckeRemovableSourceQuarterThirdDerivativeBoundProp_of_candidateValueFormula
    (h_value :
      StandardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp) :
    StandardGabckeRemovableSourceQuarterThirdDerivativeBoundProp
      standardGabckeRemovableSourceThirdDerivative := by
  unfold StandardGabckeRemovableSourceQuarterThirdDerivativeBoundProp
  rw [h_value]
  have hpi2_nonneg : 0 ≤ Real.pi ^ 2 := sq_nonneg Real.pi
  have hcoef : (1 : ℝ) ≤ fresnelC1Bound * 96 := by
    unfold fresnelC1Bound
    norm_num
  calc
    |(-Real.pi ^ 2)| = Real.pi ^ 2 := by
      rw [abs_neg, abs_of_nonneg hpi2_nonneg]
    _ = 1 * Real.pi ^ 2 := by ring
    _ ≤ (fresnelC1Bound * 96) * Real.pi ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef hpi2_nonneg
    _ = fresnelC1Bound * (96 * Real.pi ^ 2) := by ring

/-- The quarter-point numeric Tabelle bound follows from the local coordinate
bridge plus the one-variable local Taylor calculation. -/
theorem standardGabckeRemovableSourceQuarterThirdDerivativeBoundProp_of_localTaylor
    (h_coord :
      StandardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp)
    (h_local : StandardGabckeQuarterLocalThirdDerivativeFormulaProp) :
    StandardGabckeRemovableSourceQuarterThirdDerivativeBoundProp
      standardGabckeRemovableSourceThirdDerivative :=
  standardGabckeRemovableSourceQuarterThirdDerivativeBoundProp_of_candidateValueFormula
    (standardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp_of_localTaylor
      h_coord h_local)

/-- The quarter-point candidate value formula follows from the already-closed
coordinate bridge plus the local cubic Taylor coefficient source. -/
theorem standardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp_of_cubicTaylorCoefficient
    (h_coeff : StandardGabckeQuarterLocalCubicTaylorCoefficientProp) :
    StandardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp :=
  standardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp_of_localTaylor
    standardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp_proved
    (standardGabckeQuarterLocalThirdDerivativeFormulaProp_of_cubicTaylorCoefficient
      h_coeff)

/-- The quarter-point numeric Tabelle bound follows from the local cubic Taylor
coefficient source. -/
theorem standardGabckeRemovableSourceQuarterThirdDerivativeBoundProp_of_cubicTaylorCoefficient
    (h_coeff : StandardGabckeQuarterLocalCubicTaylorCoefficientProp) :
    StandardGabckeRemovableSourceQuarterThirdDerivativeBoundProp
      standardGabckeRemovableSourceThirdDerivative :=
  standardGabckeRemovableSourceQuarterThirdDerivativeBoundProp_of_candidateValueFormula
    (standardGabckeRemovableCandidateQuarterThirdDerivativeValueFormulaProp_of_cubicTaylorCoefficient
      h_coeff)

/-- The quarter-point numeric Tabelle bound follows from the coordinate bridge
plus the `HasDerivAt` form of the local Taylor atom. -/
theorem standardGabckeRemovableSourceQuarterThirdDerivativeBoundProp_of_localSecondDerivative_hasDerivAt
    (h_coord :
      StandardGabckeRemovableCandidateQuarterLocalCoordinateThirdDerivativeProp)
    (h_deriv : StandardGabckeQuarterLocalSecondDerivativeHasDerivAtProp) :
    StandardGabckeRemovableSourceQuarterThirdDerivativeBoundProp
      standardGabckeRemovableSourceThirdDerivative :=
  standardGabckeRemovableSourceQuarterThirdDerivativeBoundProp_of_localTaylor
    h_coord
    (standardGabckeQuarterLocalThirdDerivativeFormulaProp_of_secondDerivative_hasDerivAt
      h_deriv)

/-- Numeric Tabelle bound for the smooth removable-source derivative at the
second denominator-zero point. -/
def StandardGabckeRemovableSourceThreeQuarterThirdDerivativeBoundProp
    (D : ℝ → ℝ) : Prop :=
  |D (3 / 4)| ≤ fresnelC1Bound * (96 * Real.pi ^ 2)

/-- Numeric Tabelle bounds for the smooth removable-source derivative at both
denominator-zero points, after the source constants have been fixed to the
actual source values. -/
def StandardGabckeRemovableSourcePointBoundsProp (D : ℝ → ℝ) : Prop :=
  StandardGabckeRawPsiRemovablePointValueBoundsProp (D (1 / 4)) (D (3 / 4))

/-- The paired removable-source point bound follows from the two independent
point bounds. -/
theorem standardGabckeRemovableSourcePointBoundsProp_of_pointBounds
    {D : ℝ → ℝ}
    (h_quarter : StandardGabckeRemovableSourceQuarterThirdDerivativeBoundProp D)
    (h_threeQuarter :
      StandardGabckeRemovableSourceThreeQuarterThirdDerivativeBoundProp D) :
    StandardGabckeRemovableSourcePointBoundsProp D :=
  ⟨h_quarter, h_threeQuarter⟩

/-- Exact raw point-value atoms follow from a two-point bridge to the smooth
removable source derivative plus the sourced Tabelle values. -/
theorem standardGabckeRawPsiRemovablePointValues_of_sourceBridge
    {D : ℝ → ℝ} {C14 C34 : ℝ}
    (h_bridge : StandardGabckeRawPsiRemovableSourceBridgeProp D)
    (h_values : StandardGabckeRemovableSourceThirdDerivativeValueProp D C14 C34) :
    StandardGabckeRawPsiQuarterThirdDerivativeValueProp C14 ∧
      StandardGabckeRawPsiThreeQuarterThirdDerivativeValueProp C34 := by
  constructor
  · exact h_bridge.1.trans h_values.1
  · exact h_bridge.2.trans h_values.2

/-- The removable-point bounds follow from the exact two-point
raw/removable-source bridge, the sourced values, and their numeric Tabelle
bounds. -/
theorem standardGabckeRawPsiRemovablePointBoundsProp_of_sourceBridge
    {D : ℝ → ℝ} {C14 C34 : ℝ}
    (h_bridge : StandardGabckeRawPsiRemovableSourceBridgeProp D)
    (h_values : StandardGabckeRemovableSourceThirdDerivativeValueProp D C14 C34)
    (h_bounds : StandardGabckeRawPsiRemovablePointValueBoundsProp C14 C34) :
    StandardGabckeRawPsiRemovablePointBoundsProp := by
  have h_quarter :
      standardGabckeRawPsiThirdDerivative (1 / 4 : ℝ) = C14 :=
    h_bridge.1.trans h_values.1
  have h_threeQuarter :
      standardGabckeRawPsiThirdDerivative (3 / 4 : ℝ) = C34 :=
    h_bridge.2.trans h_values.2
  constructor
  · rw [h_quarter]
    exact h_bounds.1
  · rw [h_threeQuarter]
    exact h_bounds.2

/-- The two removable-point bounds follow from exact source values at the two
quarter points plus the corresponding numeric bounds for those values. -/
theorem standardGabckeRawPsiRemovablePointBoundsProp_of_pointValues
    {C14 C34 : ℝ}
    (h_quarter : StandardGabckeRawPsiQuarterThirdDerivativeValueProp C14)
    (h_threeQuarter :
      StandardGabckeRawPsiThreeQuarterThirdDerivativeValueProp C34)
    (h_bounds : StandardGabckeRawPsiRemovablePointValueBoundsProp C14 C34) :
    StandardGabckeRawPsiRemovablePointBoundsProp := by
  have h_quarter' :
      standardGabckeRawPsiThirdDerivative (1 / 4 : ℝ) = C14 := h_quarter
  have h_threeQuarter' :
      standardGabckeRawPsiThirdDerivative (3 / 4 : ℝ) = C34 := h_threeQuarter
  constructor
  · rw [h_quarter']
    exact h_bounds.1
  · rw [h_threeQuarter']
    exact h_bounds.2

/-- The removable-singularity derivative bound follows from classifying the
denominator-zero locus and checking the two removable points. -/
theorem standardGabckeRawPsiRemovableThirdDerivativeBoundProp_of_denominatorZeroClassified
    (h_class : StandardGabckeRawPsiDenominatorZeroClassifiedProp)
    (h_points : StandardGabckeRawPsiRemovablePointBoundsProp) :
    StandardGabckeRawPsiRemovableThirdDerivativeBoundProp := by
  intro p hp hzero
  rcases h_class p hp hzero with hp_quarter | hp_threeQuarter
  · rw [hp_quarter]
    exact h_points.1
  · rw [hp_threeQuarter]
    exact h_points.2

/-- The global raw third-derivative bound follows from its regular-point
estimate plus the removable-singularity bridge. -/
theorem standardGabckeRawPsiThirdDerivativeBoundProp_of_regular_and_removable
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_removable : StandardGabckeRawPsiRemovableThirdDerivativeBoundProp) :
    StandardGabckeRawPsiThirdDerivativeBoundProp := by
  intro p hp
  by_cases hsing : standardGabckeRawPsiDenominatorZero p
  · exact h_removable p hp hsing
  · exact h_regular p hp hsing

/-- The unscaled third-derivative estimate implies the coefficient-level
Tabelle-1 bound. -/
theorem standardGabckeTabelleFirstCoefficientBoundProp_of_rawPsiThirdDerivativeBound
    (h : StandardGabckeRawPsiThirdDerivativeBoundProp) :
    StandardGabckeTabelleFirstCoefficientBoundProp := by
  intro p hp
  have hden_pos : 0 < 96 * Real.pi ^ 2 := by positivity
  have hderiv := h p hp
  unfold standardGabckeRawPsiThirdDerivative at hderiv
  rw [abs_div, abs_neg, abs_of_pos hden_pos]
  exact (div_le_iff₀ hden_pos).2 hderiv

/-- The unfolded contour/Taylor source identity supplies the standard
stationary-phase identity for the concrete raw first coefficient. -/
theorem standardGabckeStationaryPhaseIdentity_rawFirstCoefficient_of_contourTaylor
    (h : StandardGabckeContourTaylorFirstCoefficientIdentityProp) :
    StandardGabckeStationaryPhaseIdentityProp
      standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient := by
  intro k p hp
  simpa [standardGabckeRawFirstCoefficient] using h k p hp

/-- The unfolded Tabelle-1 source bound supplies the standard coefficient bound
for the concrete raw first coefficient. -/
theorem standardGabckeCoefficientBound_rawFirstCoefficient_of_tabelleBound
    (h : StandardGabckeTabelleFirstCoefficientBoundProp) :
    StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient := by
  intro p hp
  simpa [standardGabckeRawFirstCoefficient] using h p hp

/-- Combined source surface for Gabcke's first coefficient after the leading
phase normalization has been fixed. -/
def StandardGabckeFirstCoefficientSourceProp : Prop :=
  StandardGabckeContourTaylorFirstCoefficientIdentityProp ∧
    StandardGabckeTabelleFirstCoefficientBoundProp

/-- The two concrete standard Gabcke target propositions follow from the two
source atoms above. -/
theorem standardGabckeTargets_of_firstCoefficientSource
    (h : StandardGabckeFirstCoefficientSourceProp) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  ⟨standardGabckeStationaryPhaseIdentity_rawFirstCoefficient_of_contourTaylor h.1,
    standardGabckeCoefficientBound_rawFirstCoefficient_of_tabelleBound h.2⟩

/-- Source package with the coefficient bound reduced to the unscaled
third-derivative estimate. -/
theorem standardGabckeFirstCoefficientSourceProp_of_contourTaylor_and_rawPsiThirdDerivativeBound
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_deriv : StandardGabckeRawPsiThirdDerivativeBoundProp) :
    StandardGabckeFirstCoefficientSourceProp :=
  ⟨h_id,
    standardGabckeTabelleFirstCoefficientBoundProp_of_rawPsiThirdDerivativeBound h_deriv⟩

/-- Direct route from the contour/Taylor identity and the unscaled
third-derivative estimate to the two standard Gabcke target propositions. -/
theorem standardGabckeTargets_of_contourTaylor_and_rawPsiThirdDerivativeBound
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_deriv : StandardGabckeRawPsiThirdDerivativeBoundProp) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_firstCoefficientSource
    (standardGabckeFirstCoefficientSourceProp_of_contourTaylor_and_rawPsiThirdDerivativeBound
      h_id h_deriv)

/-- Direct route to the two standard Gabcke target propositions when the raw
third-derivative estimate has been split into regular and removable-singularity
pieces. -/
theorem standardGabckeTargets_of_contourTaylor_and_rawPsiThirdDerivativeSplit
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_removable : StandardGabckeRawPsiRemovableThirdDerivativeBoundProp) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_contourTaylor_and_rawPsiThirdDerivativeBound h_id
    (standardGabckeRawPsiThirdDerivativeBoundProp_of_regular_and_removable
      h_regular h_removable)

/-- Global raw derivative bound from the regular quotient estimate plus the
classified two-point removable-singularity checks. -/
theorem standardGabckeRawPsiThirdDerivativeBoundProp_of_regular_classified_and_removablePoints
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_class : StandardGabckeRawPsiDenominatorZeroClassifiedProp)
    (h_points : StandardGabckeRawPsiRemovablePointBoundsProp) :
    StandardGabckeRawPsiThirdDerivativeBoundProp :=
  standardGabckeRawPsiThirdDerivativeBoundProp_of_regular_and_removable h_regular
    (standardGabckeRawPsiRemovableThirdDerivativeBoundProp_of_denominatorZeroClassified
      h_class h_points)

/-- Direct route to the two standard Gabcke target propositions when the
removable side of the raw third-derivative estimate is reduced to denominator
classification and two pointwise bounds. -/
theorem standardGabckeTargets_of_contourTaylor_regular_classified_and_removablePoints
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_class : StandardGabckeRawPsiDenominatorZeroClassifiedProp)
    (h_points : StandardGabckeRawPsiRemovablePointBoundsProp) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_contourTaylor_and_rawPsiThirdDerivativeBound h_id
    (standardGabckeRawPsiThirdDerivativeBoundProp_of_regular_classified_and_removablePoints
      h_regular h_class h_points)

/-- Direct target route with the denominator-zero classification reduced to
the quarter-lattice theorem and its interval range restriction. -/
theorem standardGabckeTargets_of_contourTaylor_regular_quarterLattice_and_removablePoints
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_lattice : StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp)
    (h_range : StandardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp)
    (h_points : StandardGabckeRawPsiRemovablePointBoundsProp) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_contourTaylor_regular_classified_and_removablePoints
    h_id h_regular
    (standardGabckeRawPsiDenominatorZeroClassifiedProp_of_quarterLattice
      h_lattice h_range)
    h_points

/-- Direct target route after closing the quarter-lattice range restriction:
the remaining denominator-classification input is only the trigonometric
quarter-lattice theorem. -/
theorem standardGabckeTargets_of_contourTaylor_regular_latticeOnly_and_removablePoints
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_lattice : StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp)
    (h_points : StandardGabckeRawPsiRemovablePointBoundsProp) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_contourTaylor_regular_classified_and_removablePoints
    h_id h_regular
    (standardGabckeRawPsiDenominatorZeroClassifiedProp_of_quarterLattice_only
      h_lattice)
    h_points

/-- Direct target route after closing denominator-zero classification. The
remaining removable-singularity input is just the two pointwise bounds. -/
theorem standardGabckeTargets_of_contourTaylor_regular_and_removablePointBounds
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_points : StandardGabckeRawPsiRemovablePointBoundsProp) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_contourTaylor_regular_classified_and_removablePoints
    h_id h_regular
    standardGabckeRawPsiDenominatorZeroClassifiedProp_proved
    h_points

/-- Direct target route when the removable-point input is supplied as exact
third-derivative values at `1/4` and `3/4` plus numeric bounds for those
values. -/
theorem standardGabckeTargets_of_contourTaylor_regular_and_removablePointValues
    {C14 C34 : ℝ}
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_quarter : StandardGabckeRawPsiQuarterThirdDerivativeValueProp C14)
    (h_threeQuarter :
      StandardGabckeRawPsiThreeQuarterThirdDerivativeValueProp C34)
    (h_bounds : StandardGabckeRawPsiRemovablePointValueBoundsProp C14 C34) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_contourTaylor_regular_and_removablePointBounds
    h_id h_regular
    (standardGabckeRawPsiRemovablePointBoundsProp_of_pointValues
      h_quarter h_threeQuarter h_bounds)

/-- Direct target route when the two removable point values are supplied by a
smooth removable-source derivative and a two-point bridge back to the raw
totalized quotient derivative. -/
theorem standardGabckeTargets_of_contourTaylor_regular_and_removableSourceBridge
    {D : ℝ → ℝ} {C14 C34 : ℝ}
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_bridge : StandardGabckeRawPsiRemovableSourceBridgeProp D)
    (h_values : StandardGabckeRemovableSourceThirdDerivativeValueProp D C14 C34)
    (h_bounds : StandardGabckeRawPsiRemovablePointValueBoundsProp C14 C34) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_contourTaylor_regular_and_removablePointBounds
    h_id h_regular
    (standardGabckeRawPsiRemovablePointBoundsProp_of_sourceBridge
      h_bridge h_values h_bounds)

/-- Direct target route when the smooth removable-source bridge and source
values are supplied point-by-point at `1/4` and `3/4`. -/
theorem standardGabckeTargets_of_contourTaylor_regular_and_removableSourcePointData
    {D : ℝ → ℝ} {C14 C34 : ℝ}
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_bridge_quarter :
      StandardGabckeRawPsiQuarterRemovableSourceBridgeProp D)
    (h_bridge_threeQuarter :
      StandardGabckeRawPsiThreeQuarterRemovableSourceBridgeProp D)
    (h_value_quarter :
      StandardGabckeRemovableSourceQuarterThirdDerivativeValueProp D C14)
    (h_value_threeQuarter :
      StandardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp D C34)
    (h_bounds : StandardGabckeRawPsiRemovablePointValueBoundsProp C14 C34) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_contourTaylor_regular_and_removableSourceBridge
    h_id h_regular
    (standardGabckeRawPsiRemovableSourceBridgeProp_of_pointBridges
      h_bridge_quarter h_bridge_threeQuarter)
    (standardGabckeRemovableSourceThirdDerivativeValueProp_of_pointValues
      h_value_quarter h_value_threeQuarter)
    h_bounds

/-- Direct target route after closing the removable-source value atoms
canonically: the remaining source-side removable input is the raw/source bridge
at the two quarter points plus numeric bounds for the smooth source derivative
there. -/
theorem standardGabckeTargets_of_contourTaylor_regular_and_removableSourcePointBounds
    {D : ℝ → ℝ}
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_bridge_quarter :
      StandardGabckeRawPsiQuarterRemovableSourceBridgeProp D)
    (h_bridge_threeQuarter :
      StandardGabckeRawPsiThreeQuarterRemovableSourceBridgeProp D)
    (h_bounds : StandardGabckeRemovableSourcePointBoundsProp D) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_contourTaylor_regular_and_removableSourcePointData
    h_id h_regular h_bridge_quarter h_bridge_threeQuarter
    (standardGabckeRemovableSourceQuarterThirdDerivativeValueProp_self D)
    (standardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp_self D)
    (show StandardGabckeRawPsiRemovablePointValueBoundsProp
        (D (1 / 4)) (D (3 / 4)) from h_bounds)

/-- Direct route specialized to the instantiated removable quotient candidate.
The remaining source inputs are the two raw/candidate derivative bridge
equalities and the Tabelle bound for the candidate's two point values. -/
theorem standardGabckeTargets_of_contourTaylor_regular_and_removableCandidatePointBounds
    (h_id : StandardGabckeContourTaylorFirstCoefficientIdentityProp)
    (h_regular : StandardGabckeRawPsiRegularThirdDerivativeBoundProp)
    (h_bridge_quarter :
      StandardGabckeRawPsiQuarterRemovableSourceBridgeProp
        standardGabckeRemovableSourceThirdDerivative)
    (h_bridge_threeQuarter :
      StandardGabckeRawPsiThreeQuarterRemovableSourceBridgeProp
        standardGabckeRemovableSourceThirdDerivative)
    (h_bounds :
      StandardGabckeRemovableSourcePointBoundsProp
        standardGabckeRemovableSourceThirdDerivative) :
    StandardGabckeStationaryPhaseIdentityProp
        standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient ∧
      StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient :=
  standardGabckeTargets_of_contourTaylor_regular_and_removableSourcePointBounds
    h_id h_regular h_bridge_quarter h_bridge_threeQuarter h_bounds

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
