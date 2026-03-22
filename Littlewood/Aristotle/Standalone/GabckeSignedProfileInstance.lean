import Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra

/-!
Constructive instance of `GabckeSignedProfileHyp` from two atomic
steepest-descent leaves.

The exact remaining theorem-first Gabcke boundary is the atomic conjunction
`GabckeAtomicHyp`; everything below is a compatibility route out of that
boundary.

This file is intentionally additive: it does not change the current
`GabckeSignedAdjacentHyp`-first surface, but it records a clean stronger route
through two atomic analytic leaves that may still be useful upstream.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.GabckeSignedProfileInstance

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam Aristotle.ErrorTermExpansion
open Aristotle.Standalone.GabckePhaseCouplingInfra
open Aristotle.Standalone.SiegelSaddleExpansionHyp

/-- Atom 1: on block coordinates, the normalized signed gap depends only on
`p`, not on the block index `k`. -/
class GabckeBlockIndependence : Prop where
  normalized_gap_eq :
    ∀ k : ℕ, ∀ p : ℝ, p ∈ Ioc (0 : ℝ) 1 →
      ((k : ℝ) + 1 + p) * signedSPR k (blockCoord k p) =
        (2 + p) * signedSPR 1 (blockCoord 1 p)

/-- Atom 2: the signed saddle remainder is nonnegative on the first block. -/
class GabckeSignPositivity : Prop where
  signed_remainder_nonneg :
    ∀ p : ℝ, p ∈ Ioc (0 : ℝ) 1 → 0 ≤ signedSPR 1 (blockCoord 1 p)

/-- The exact theorem-first remaining Gabcke boundary: the normalized signed
gap is block-independent, and the first-block signed saddle remainder is
nonnegative. This is just a named conjunction of the two atomic classes, not a
new bundled hypothesis surface. -/
abbrev GabckeAtomicHyp : Prop :=
  GabckeBlockIndependence ∧ GabckeSignPositivity

/-- Extract the first Gabcke atomic class from the theorem-first atomic
boundary. -/
theorem gabckeBlockIndependence_of_atomicHyp (h : GabckeAtomicHyp) :
    GabckeBlockIndependence :=
  h.1

/-- Extract the second Gabcke atomic class from the theorem-first atomic
boundary. -/
theorem gabckeSignPositivity_of_atomicHyp (h : GabckeAtomicHyp) :
    GabckeSignPositivity :=
  h.2

/-- Package the two atomic Gabcke classes into the exact theorem-first
boundary proposition. -/
theorem gabckeAtomicHyp_of_atoms
    [GabckeBlockIndependence] [GabckeSignPositivity] :
    GabckeAtomicHyp :=
  ⟨inferInstance, inferInstance⟩

/-- The Gabcke profile is the normalized first-block signed gap. -/
theorem gabckeSignedProfile_unfold (p : ℝ) (hp : 0 ≤ p) :
    gabckeSignedProfile p = (2 + p) * signedSPR 1 (blockCoord 1 p) := by
  unfold gabckeSignedProfile weightedSignedSPR
  have h2p : (0 : ℝ) ≤ 2 + p := by linarith
  have hcast : ((1 : ℕ) : ℝ) + 1 + p = 2 + p := by push_cast; ring
  rw [hcast]
  have hsq : Real.sqrt (2 + p) * Real.sqrt (2 + p) = 2 + p := by
    simpa [sq] using Real.sq_sqrt h2p
  calc
    Real.sqrt (2 + p) * (Real.sqrt (2 + p) * signedSPR 1 (blockCoord 1 p))
        = (Real.sqrt (2 + p) * Real.sqrt (2 + p)) * signedSPR 1 (blockCoord 1 p) := by
          ring
    _ = (2 + p) * signedSPR 1 (blockCoord 1 p) := by rw [hsq]

/-- Atom 1 implies the explicit profile formula for `weightedSignedSPR`. -/
private theorem weightedSignedSPR_eq_profile_from_atom
    [hbi : GabckeBlockIndependence]
    (k : ℕ) (p : ℝ) (hp : p ∈ Ioc (0 : ℝ) 1) :
    weightedSignedSPR k p = gabckeSignedProfile p / Real.sqrt ((k : ℝ) + 1 + p) := by
  have hp0 : 0 ≤ p := le_of_lt hp.1
  have hu_pos : 0 < (k : ℝ) + 1 + p := by positivity
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1 + p) := Real.sqrt_pos.mpr hu_pos
  have hsqrt_ne : Real.sqrt ((k : ℝ) + 1 + p) ≠ 0 := ne_of_gt hsqrt_pos
  have hu_ne : ((k : ℝ) + 1 + p) ≠ 0 := ne_of_gt hu_pos
  have hu_nonneg : 0 ≤ (k : ℝ) + 1 + p := le_of_lt hu_pos
  have hbi_eq := hbi.normalized_gap_eq k p hp
  have hprof := gabckeSignedProfile_unfold p hp0
  have hkey : ((k : ℝ) + 1 + p) * signedSPR k (blockCoord k p) = gabckeSignedProfile p := by
    rw [hbi_eq, hprof]
  unfold weightedSignedSPR
  have hspr_eq :
      signedSPR k (blockCoord k p) = gabckeSignedProfile p / ((k : ℝ) + 1 + p) := by
    field_simp [hu_ne]
    linarith [hkey]
  rw [hspr_eq]
  have hsq_sqrt :
      Real.sqrt ((k : ℝ) + 1 + p) * Real.sqrt ((k : ℝ) + 1 + p) = (k : ℝ) + 1 + p := by
    simpa [sq] using Real.sq_sqrt hu_nonneg
  calc
    Real.sqrt ((k : ℝ) + 1 + p) * (gabckeSignedProfile p / ((k : ℝ) + 1 + p))
        = Real.sqrt ((k : ℝ) + 1 + p) *
            (gabckeSignedProfile p /
              (Real.sqrt ((k : ℝ) + 1 + p) * Real.sqrt ((k : ℝ) + 1 + p))) := by
                rw [hsq_sqrt]
    _ = gabckeSignedProfile p / Real.sqrt ((k : ℝ) + 1 + p) := by
          field_simp [hsqrt_ne]

/-- Atom 2 implies nonnegativity of the Gabcke profile. -/
private theorem gabckeSignedProfile_nonneg_from_atom
    [hsp : GabckeSignPositivity]
    (p : ℝ) (hp : p ∈ Ioc (0 : ℝ) 1) :
    0 ≤ gabckeSignedProfile p := by
  have hp0 : 0 ≤ p := le_of_lt hp.1
  rw [gabckeSignedProfile_unfold p hp0]
  exact mul_nonneg (by linarith) (hsp.signed_remainder_nonneg p hp)

/-- The two atomic Gabcke leaves imply the older stronger profile package. -/
instance gabckeSignedProfileHyp_from_atoms
    [GabckeBlockIndependence] [GabckeSignPositivity] :
    GabckeSignedProfileHyp where
  weightedSignedSPR_eq_profile := fun k p hp =>
    weightedSignedSPR_eq_profile_from_atom k p hp
  profile_nonneg := fun p hp =>
    gabckeSignedProfile_nonneg_from_atom p hp

/-- Direct theorem-first builder for the legacy profile wrapper from the two
atomic Gabcke classes. -/
def gabckeSignedProfileHyp_of_atoms
    [GabckeBlockIndependence] [GabckeSignPositivity] :
    GabckeSignedProfileHyp :=
  gabckeSignedProfileHyp_from_atoms

/-- Direct theorem-first builder for the legacy profile wrapper from the exact
atomic boundary proposition. -/
def gabckeSignedProfileHyp_of_atomicHyp (h : GabckeAtomicHyp) :
    GabckeSignedProfileHyp := by
  let _ : GabckeBlockIndependence := gabckeBlockIndependence_of_atomicHyp h
  let _ : GabckeSignPositivity := gabckeSignPositivity_of_atomicHyp h
  exact gabckeSignedProfileHyp_from_atoms

/-- The two atomic Gabcke leaves imply the current minimal adjacent-pointwise
theorem surface directly. This keeps the direct adjacent statement primary,
with the stronger profile package remaining only a sufficient route. -/
theorem gabckeSignedAdjacentProp_from_atoms
    [GabckeBlockIndependence] [GabckeSignPositivity] :
    GabckeSignedAdjacentProp :=
  gabckeSignedAdjacentProp_of_profile

/-- Direct theorem-first builder for the legacy adjacent wrapper from the two
atomic Gabcke classes. -/
def gabckeSignedAdjacentHyp_of_atoms
    [GabckeBlockIndependence] [GabckeSignPositivity] :
    GabckeSignedAdjacentHyp :=
  gabckeSignedAdjacentHyp_of_prop gabckeSignedAdjacentProp_from_atoms

/-- Direct theorem-first adjacent-pointwise Gabcke route from the exact atomic
boundary proposition. -/
theorem gabckeSignedAdjacentProp_of_atomicHyp (h : GabckeAtomicHyp) :
    GabckeSignedAdjacentProp := by
  let _ : GabckeBlockIndependence := gabckeBlockIndependence_of_atomicHyp h
  let _ : GabckeSignPositivity := gabckeSignPositivity_of_atomicHyp h
  exact gabckeSignedAdjacentProp_from_atoms

/-- Direct theorem-first builder for the legacy adjacent wrapper from the exact
atomic boundary proposition. -/
def gabckeSignedAdjacentHyp_of_atomicHyp (h : GabckeAtomicHyp) :
    GabckeSignedAdjacentHyp :=
  gabckeSignedAdjacentHyp_of_prop (gabckeSignedAdjacentProp_of_atomicHyp h)

/-- Direct no-axiom Gabcke remainder antitonicity from the two atomic
steepest-descent leaves, phrased through the minimal adjacent theorem
surface rather than the larger profile package. -/
theorem remainder_antitone_for_ge_one_of_atoms
    [GabckeBlockIndependence] [GabckeSignPositivity]
    (k : ℕ) (hk : 1 ≤ k) :
    blockRemainder (k + 1) ≤ blockRemainder k :=
  remainder_antitone_for_ge_one_of_adjacent_prop
    gabckeSignedAdjacentProp_from_atoms k hk

/-- Direct no-axiom Gabcke remainder antitonicity from the exact theorem-first
atomic boundary proposition. -/
theorem remainder_antitone_for_ge_one_of_atomicHyp
    (h : GabckeAtomicHyp) (k : ℕ) (hk : 1 ≤ k) :
    blockRemainder (k + 1) ≤ blockRemainder k :=
  remainder_antitone_for_ge_one_of_adjacent_prop
    (gabckeSignedAdjacentProp_of_atomicHyp h) k hk

end Aristotle.Standalone.GabckeSignedProfileInstance
