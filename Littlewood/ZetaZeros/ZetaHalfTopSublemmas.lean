/-
Sub-lemmas for ZetaHalfTopArgVariationBoundHyp (S(T) = O(log T)).

The integral ∫_{1/2}^{2} Im(ζ'/ζ(x+iT)) dx is decomposed into:
  Sub-lemma A: [1, 2] segment — O(1) via FTC + arg bound
  Sub-lemma B: [1/2, 1] segment — O(log T) via Backlund's split

Each sub-lemma is a hypothesis class. Instances fed from separate proofs.
-/

import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.ZetaZeros.ZeroCountingMultiplicity
import Littlewood.Aristotle.Standalone.HadamardFactorizationXi

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace ZetaZeros

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators
open scoped Real

/-! ## Sub-lemma A: [1, 2] segment is O(log T)

The constructive split mirrors the half-strip decomposition:

1. the short interval `[1, 1 + 1/log T]`, where a pointwise
   `O((log T)^2)` bound suffices because the interval length is `1/log T`;
2. the tail `[1 + 1/log T, 2]`, where the existing near-one majorant gives a
   direct `O(log T)` integral bound.

This avoids the stronger global pointwise surface on all of `[1,2]`, which is
not the natural constructive target on the current branch. -/
class ZetaLogDerivOneTwoThinStripPointwiseBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      ∀ x ∈ Set.Icc (1 : ℝ) (1 + 1 / Real.log T),
        ‖logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)‖ ≤
          C * (Real.log T) ^ 2

class ZetaLogDerivIntegralOneTwoBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |∫ x in (1 : ℝ)..2,
        (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im| ≤ C * Real.log T

/-! ## Sub-lemma B: [1/2, 1] segment is O(log T)

This is the hard part. The classical Backlund split writes the segment as:

1. the thin strip `[1/2, 1/2 + 1/log T]`, where a pointwise
   `O((log T)^2)` bound suffices because the interval length is `1/log T`;
2. the mid-strip `[1/2 + 1/log T, 1]`, where one needs the genuine
   `O(log T)` integral bound.

Infrastructure needed:
- logDeriv_xi_product_decomposition (XiLogDerivDecomposition.lean): Hadamard
- digamma_log_bound (DigammaAsymptotic.lean): |ψ(z) - log z| ≤ C/|z|
- finite_zeros_le (ZeroCountingFunction.lean): finitely many zeros below T
- Short-interval zero density: N(T+1) - N(T-1) = O(log T) [from Jensen] -/
class ZetaLogDerivHalfOneThinStripPointwiseBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) ((1 / 2 : ℝ) + 1 / Real.log T),
        ‖logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)‖ ≤
          C * (Real.log T) ^ 2

/-- Zeros with ordinate in `(T - 1, T + 1]`, represented as a finite zeta-zero finset. -/
noncomputable def halfOneNearZeroFinset (T : ℝ) : Finset ℂ :=
  ((finite_zeros_le (T + 1)).toFinset).filter (fun ρ => T - 1 < ρ.im)

/-- Multiplicity-weighted principal part from zeros with ordinate in `(T - 1, T + 1]`. -/
noncomputable def halfOneNearZeroPrincipalPart (T : ℝ) (s : ℂ) : ℂ :=
  ∑ ρ ∈ halfOneNearZeroFinset T, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (s - ρ))

/-- The explicit smooth background in the completed-zeta logarithmic derivative:
pole at `1`, the trivial `1 / s` term, the constant `-(1/2) log π`, and the
digamma contribution. -/
noncomputable def halfOneMidStripSmoothBackground (s : ℂ) : ℂ :=
  s⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
    (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2)

/-- The zeta-side mid-strip remainder after removing the nearby principal part.
This is now a derived Backlund surface; the active constructive frontier is the
far-zero cancellation term below. -/
noncomputable def halfOneMidStripPairedRemainder (T : ℝ) (s : ℂ) : ℂ :=
  logDeriv riemannZeta s - halfOneNearZeroPrincipalPart T s

/-- The zeta-side mid-strip far-zero cancellation term used by the downstream
Backlund wrappers. This is now a compatibility alias; the active constructive
frontier is the paired zeta-zero surface immediately below. -/
noncomputable def halfOneMidStripFarZeroCancellation (T : ℝ) (s : ℂ) : ℂ :=
  halfOneMidStripPairedRemainder T s + halfOneMidStripSmoothBackground s

/-- Active zeta-zero far-zero cancellation surface for Backlund's mid-strip
argument. This is the pairing-friendly surface that future constructive work
should target directly. -/
noncomputable def halfOneMidStripPairedFarZeroCancellation (T : ℝ) (s : ℂ) : ℂ :=
  halfOneMidStripFarZeroCancellation T s

/-- Compatibility Hadamard-side far-zero cancellation term:
the canonical-product zero sum plus constant, minus the nearby zeta-zero
principal part. This is no longer the active constructive frontier. -/
noncomputable def halfOneMidStripHadamardFarZeroCancellation
    [h : HadamardXi.HadamardXiCanonicalProductCriticalZeros] (T : ℝ) (s : ℂ) : ℂ :=
  (h.B + HadamardXi.zeroSum s) - halfOneNearZeroPrincipalPart T s

/-- The Hadamard-side mid-strip remainder used in the older Backlund decomposition:
the canonical-product zero sum plus constant, minus the explicit pole/gamma
background and minus the nearby zeta-zero principal part. -/
noncomputable def halfOneMidStripHadamardRemainder
    [h : HadamardXi.HadamardXiCanonicalProductCriticalZeros] (T : ℝ) (s : ℂ) : ℂ :=
  (h.B + HadamardXi.zeroSum s) -
    (s⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * Complex.log (↑Real.pi) +
      (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2)) -
    halfOneNearZeroPrincipalPart T s

/-- Legacy compatibility surface for the old Hadamard-enumeration leaf.
This is no longer the active constructive target for Backlund's mid-strip
argument; the active leaf is the Hadamard-side far-zero cancellation class
below. -/
class ZetaLogDerivHalfOneMidStripHadamardRemainderBoundHyp
    [h : HadamardXi.HadamardXiCanonicalProductCriticalZeros] : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      let a : ℝ := (1 / 2 : ℝ) + 1 / Real.log T
      IntervalIntegrable
        (fun x : ℝ =>
          (halfOneMidStripHadamardRemainder T ((↑x : ℂ) + (↑T : ℂ) * I)).im)
        volume a 1 ∧
      |∫ x in a..1,
        (halfOneMidStripHadamardRemainder T ((↑x : ℂ) + (↑T : ℂ) * I)).im| ≤
        C * Real.log T

/-- Active Backlund mid-strip leaf on the pairing-friendly zeta-zero side. -/
class ZetaLogDerivHalfOneMidStripPairedFarZeroCancellationHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      let a : ℝ := (1 / 2 : ℝ) + 1 / Real.log T
      IntervalIntegrable
        (fun x : ℝ =>
          (halfOneMidStripPairedFarZeroCancellation T ((↑x : ℂ) + (↑T : ℂ) * I)).im)
        volume a 1 ∧
      |∫ x in a..1,
        (halfOneMidStripPairedFarZeroCancellation T ((↑x : ℂ) + (↑T : ℂ) * I)).im| ≤
        C * Real.log T

/-- Compatibility Backlund mid-strip leaf on the Hadamard side.
This isolates the same far-zero cancellation content through the abstract
canonical-product enumeration, but it is no longer the active constructive
target. -/
class ZetaLogDerivHalfOneMidStripHadamardFarZeroCancellationHyp
    [h : HadamardXi.HadamardXiCanonicalProductCriticalZeros] : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      let a : ℝ := (1 / 2 : ℝ) + 1 / Real.log T
      IntervalIntegrable
        (fun x : ℝ =>
          (halfOneMidStripHadamardFarZeroCancellation T ((↑x : ℂ) + (↑T : ℂ) * I)).im)
        volume a 1 ∧
      |∫ x in a..1,
        (halfOneMidStripHadamardFarZeroCancellation T ((↑x : ℂ) + (↑T : ℂ) * I)).im| ≤
        C * Real.log T

/-- Derived public Backlund mid-strip leaf on the zeta side.
The active constructive frontier is the paired zeta-zero class above; this
surface is used by the downstream remainder wrappers. -/
class ZetaLogDerivHalfOneMidStripFarZeroCancellationHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      let a : ℝ := (1 / 2 : ℝ) + 1 / Real.log T
      IntervalIntegrable
        (fun x : ℝ =>
          (halfOneMidStripFarZeroCancellation T ((↑x : ℂ) + (↑T : ℂ) * I)).im)
        volume a 1 ∧
      |∫ x in a..1,
        (halfOneMidStripFarZeroCancellation T ((↑x : ℂ) + (↑T : ℂ) * I)).im| ≤
        C * Real.log T

/-- Derived Backlund mid-strip leaf on the zeta-zero side.
The active constructive frontier is the far-zero cancellation class above. -/
class ZetaLogDerivHalfOneMidStripPairedRemainderBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      let a : ℝ := (1 / 2 : ℝ) + 1 / Real.log T
      IntervalIntegrable
        (fun x : ℝ =>
          (halfOneMidStripPairedRemainder T ((↑x : ℂ) + (↑T : ℂ) * I)).im)
        volume a 1 ∧
      |∫ x in a..1,
        (halfOneMidStripPairedRemainder T ((↑x : ℂ) + (↑T : ℂ) * I)).im| ≤
        C * Real.log T

/-- Compatibility wrapper exposing the public zeta-side remainder surface used
by the downstream Backlund integral assembly. -/
class ZetaLogDerivHalfOneMidStripRemainderBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      let a : ℝ := (1 / 2 : ℝ) + 1 / Real.log T
      IntervalIntegrable
        (fun x : ℝ =>
          (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I) -
            halfOneNearZeroPrincipalPart T ((↑x : ℂ) + (↑T : ℂ) * I)).im)
        volume a 1 ∧
      |∫ x in a..1,
        (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I) -
          halfOneNearZeroPrincipalPart T ((↑x : ℂ) + (↑T : ℂ) * I)).im| ≤
        C * Real.log T

class ZetaLogDerivHalfOneMidStripIntegralBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |∫ x in ((1 / 2 : ℝ) + 1 / Real.log T)..1,
        (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im| ≤ C * Real.log T

class ZetaLogDerivIntegralHalfOneBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |∫ x in (1 / 2 : ℝ)..1,
        (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im| ≤ C * Real.log T

/-! ## Wiring: A + B → ZetaHalfTopArgVariationBoundHyp

The integral ∫_{1/2}^{2} splits as ∫_{1/2}^{1} + ∫_{1}^{2} via
integral_add_adjacent_intervals. The O(1) bound on [1,2] absorbs into O(log T).
Triangle inequality gives the final bound. -/

-- NOTE: The wiring instance connecting these sub-lemmas to
-- ZetaHalfTopArgVariationBoundHyp should be added to
-- RiemannVonMangoldtReal.lean (which has the private continuity lemmas needed
-- for the integral splitting). The connection is:
--
-- [ZetaLogDerivIntegralOneTwoBoundHyp] [ZetaLogDerivIntegralHalfOneBoundHyp]
--   → ZetaHalfTopArgVariationBoundHyp
--
-- via: |(1/π)·∫_{1/2}^{2}| ≤ (1/π)·(|∫_{1/2}^{1}| + |∫_{1}^{2}|)
--                            ≤ (1/π)·(C_B·log T + C_A)
--                            ≤ ((C_B + C_A/log 14)/π)·log T

end ZetaZeros
