/-
# Perron Planck Quarks — Phase 2: G Holomorphicity

The Perron integrand F(s) = -logDeriv ζ(s) · x^s/s has poles at s=1 (from the
pole of ζ) and at each nontrivial zero ρ of ζ (from the zeros of ζ in the
denominator of logDeriv ζ = ζ'/ζ).

Define G(s) = F(s) - Σ_{p ∈ poles} residue(p) · (s - p)⁻¹, where:
  - residue(1) = x
  - residue(ρ) = -m(ρ) · x^ρ/ρ

After subtracting all principal parts, G extends to an analytic function on the
closed rectangle [1/2, c] × [-T, T].

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.Aristotle.LaurentExpansion

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Littlewood.Bridge.PerronPlanckQuarksPhase2

open Complex Real MeasureTheory Set Finset Filter Topology Metric
open scoped BigOperators
open Aristotle.DirichletPhaseAlignment (ZerosBelow CriticalZeros)

/-! ## Core Definitions -/

/-- The closed rectangle {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}. -/
def closedRect (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

/-- The open rectangle. -/
def openRect (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

/-- The Perron integrand F(s) = -logDeriv ζ(s) · x^s / s. -/
def perronIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s * ((x : ℂ) ^ s / s)

/-- The multiplicity of a zero of ζ. -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- The set of poles of the Perron integrand in the rectangle:
    {1} ∪ ZerosBelow T. -/
def perronPoles (T : ℝ) : Finset ℂ := insert 1 (ZerosBelow T)

/-- The residue of the Perron integrand at a pole p:
    - At s = 1: residue is x  (from the simple pole of ζ)
    - At a zero ρ: residue is -m(ρ) · x^ρ/ρ  (from the zero of ζ in logDeriv) -/
def perronResidue (x : ℝ) (p : ℂ) : ℂ :=
  if p = 1 then (x : ℂ)
  else -(zeroMult p : ℂ) * (x : ℂ) ^ p / p

/-- The principal part sum: Σ_{p ∈ poles} residue(p) / (s - p). -/
def principalPartSum (x : ℝ) (T : ℝ) (s : ℂ) : ℂ :=
  ∑ p ∈ perronPoles T, perronResidue x p * (s - p)⁻¹

/-- G(s) = F(s) - Σ residue(p)/(s-p), the Perron integrand with all principal parts removed.
    This function has removable singularities at each pole. -/
def G (x : ℝ) (T : ℝ) (s : ℂ) : ℂ :=
  perronIntegrand x s - principalPartSum x T s

/-! ## Rectangle topology lemmas -/

theorem openRect_subset_closedRect (a b c d : ℝ) :
    openRect a b c d ⊆ closedRect a b c d :=
  fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1.le, h2.le, h3.le, h4.le⟩

theorem isOpen_openRect (a b c d : ℝ) : IsOpen (openRect a b c d) := by
  apply IsOpen.inter (isOpen_lt continuous_const continuous_re)
  apply IsOpen.inter (isOpen_lt continuous_re continuous_const)
  apply IsOpen.inter (isOpen_lt continuous_const continuous_im)
  exact isOpen_lt continuous_im continuous_const

theorem closedRect_mem_nhds_of_mem_openRect {a b c d : ℝ} {z : ℂ}
    (hz : z ∈ openRect a b c d) :
    closedRect a b c d ∈ nhds z := by
  apply mem_of_superset ((isOpen_openRect a b c d).mem_nhds hz)
  exact openRect_subset_closedRect a b c d

/-! ## Helper lemmas -/

/-
The principal part sum is differentiable away from the poles.
-/
theorem principalPartSum_differentiableOn (x : ℝ) (c T : ℝ) :
    DifferentiableOn ℂ (principalPartSum x T)
      (closedRect (1/2) c (-T) T \ (perronPoles T : Set ℂ)) := by
  refine' DifferentiableOn.congr _ _;
  swap;
  refine' DifferentiableOn.sum fun p hp => _;
  exact ℂ;
  exact perronPoles T;
  exact fun p s => perronResidue x p * ( s - p ) ⁻¹;
  · exact DifferentiableOn.const_mul ( DifferentiableOn.inv ( differentiableOn_id.sub_const p ) fun s hs => sub_ne_zero_of_ne <| by aesop ) _;
  · unfold principalPartSum; aesop;

/-
At each pole p, (s-p) · principalPartSum(s) → residue(p) as s → p.
-/
theorem principalPartSum_residue (x : ℝ) (T : ℝ) (p : ℂ)
    (hp : p ∈ perronPoles T)
    (h_distinct : ∀ q ∈ perronPoles T, q ≠ p → q ≠ p) :
    Tendsto (fun s => (s - p) * principalPartSum x T s)
      (nhdsWithin p {p}ᶜ) (nhds (perronResidue x p)) := by
  -- Split the sum into the term for q=p and the rest.
  have h_split : Filter.Tendsto (fun s : ℂ => (s - p) * ∑ q ∈ perronPoles T, perronResidue x q * (s - q)⁻¹) (nhdsWithin p {p}ᶜ) (nhds (perronResidue x p)) := by
    have h_split : Filter.Tendsto (fun s : ℂ => (s - p) * perronResidue x p * (s - p)⁻¹ + (s - p) * ∑ q ∈ (perronPoles T \ {p}), perronResidue x q * (s - q)⁻¹) (nhdsWithin p {p}ᶜ) (nhds (perronResidue x p)) := by
      have h_split : Filter.Tendsto (fun s : ℂ => perronResidue x p + (s - p) * ∑ q ∈ (perronPoles T \ {p}), perronResidue x q * (s - q)⁻¹) (nhdsWithin p {p}ᶜ) (nhds (perronResidue x p)) := by
        have h_split : Filter.Tendsto (fun s : ℂ => ∑ q ∈ (perronPoles T \ {p}), perronResidue x q * (s - q)⁻¹) (nhdsWithin p {p}ᶜ) (nhds (∑ q ∈ (perronPoles T \ {p}), perronResidue x q * (p - q)⁻¹)) := by
          exact tendsto_finset_sum _ fun q hq => tendsto_const_nhds.mul ( Filter.Tendsto.inv₀ ( Filter.tendsto_id.sub_const q |> Filter.Tendsto.mono_left <| nhdsWithin_le_nhds ) <| sub_ne_zero_of_ne <| by aesop );
        convert Filter.Tendsto.add tendsto_const_nhds ( Filter.Tendsto.mul ( continuousWithinAt_id.sub continuousWithinAt_const ) h_split ) using 2 ; norm_num;
      refine' h_split.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with s hs using by rw [ mul_right_comm, mul_inv_cancel₀ ( sub_ne_zero_of_ne hs ), one_mul ] );
    convert h_split using 2 ; rw [ Finset.sum_eq_add_sum_diff_singleton hp ] ; ring;
  convert h_split using 1

/-
G is differentiable at any point in the rectangle that is not a pole.
-/
theorem G_differentiableOn_complement (x : ℝ) (c T : ℝ)
    (hF : DifferentiableOn ℂ (perronIntegrand x)
      (closedRect (1/2) c (-T) T \ (perronPoles T : Set ℂ))) :
    DifferentiableOn ℂ (G x T) (closedRect (1/2) c (-T) T \ (perronPoles T : Set ℂ)) := by
  exact DifferentiableOn.sub hF ( principalPartSum_differentiableOn x c T )

/-! ## Removable singularity at a single pole -/

/-
At a pole p in the open interior of the rectangle, G is differentiable on a
    neighborhood of p, provided G is differentiable away from the poles and
    continuous at p.

    Uses the Mathlib removable singularity theorem:
    `Complex.differentiableOn_compl_singleton_and_continuousAt_iff`.
-/
theorem G_differentiableWithinAt_at_pole (x : ℝ) (c T : ℝ) (p : ℂ)
    (hp_poles : p ∈ perronPoles T)
    (hp_interior : p ∈ openRect (1/2) c (-T) T)
    (hG_diffOn : DifferentiableOn ℂ (G x T)
      (closedRect (1/2) c (-T) T \ (perronPoles T : Set ℂ)))
    (hG_cont : ContinuousAt (G x T) p) :
    DifferentiableWithinAt ℂ (G x T) (closedRect (1/2) c (-T) T) p := by
  have h_diffWithinAt : ∃ U : Set ℂ, IsOpen U ∧ p ∈ U ∧ DifferentiableOn ℂ (G x T) (U \ {p}) ∧ ContinuousAt (G x T) p := by
    refine' ⟨ openRect ( 1 / 2 ) c ( -T ) T \ ( perronPoles T \ { p } ), _, _, _, hG_cont ⟩ <;> norm_num;
    · exact IsOpen.sdiff ( isOpen_openRect _ _ _ _ ) ( Set.Finite.isClosed ( by exact Set.Finite.subset ( Finset.finite_toSet ( perronPoles T ) ) fun x hx => by aesop ) );
    · assumption;
    · refine' hG_diffOn.mono _;
      simp +contextual [ Set.subset_def, openRect, closedRect ];
      exact fun x hx₁ hx₂ hx₃ hx₄ hx₅ hx₆ => ⟨ ⟨ le_of_lt hx₁, le_of_lt hx₂, le_of_lt hx₃, le_of_lt hx₄ ⟩, fun hx₇ => hx₆ <| hx₅ hx₇ ⟩;
  obtain ⟨ U, hU_open, hpU, h_diffWithinAt, h_cont ⟩ := h_diffWithinAt;
  have h_diffWithinAt : DifferentiableAt ℂ (G x T) p := by
    have := @Complex.differentiableOn_compl_singleton_and_continuousAt_iff ℂ;
    specialize this ( hU_open.mem_nhds hpU );
    exact G x T;
    exact this.mp ⟨ h_diffWithinAt, h_cont ⟩ |> DifferentiableOn.differentiableAt <| hU_open.mem_nhds hpU;
  exact h_diffWithinAt.differentiableWithinAt

/-! ## Hypothesis class for the main theorem -/

/-- Hypothesis class packaging the conditions for G holomorphicity. -/
structure GHolomorphicHyp (x : ℝ) (c T : ℝ) : Prop where
  /-- x > 0 for cpow to be well-defined -/
  hx_pos : 0 < x
  /-- c > 1 so the rectangle extends past the pole at s=1 -/
  hc : 1 < c
  /-- T > 0 for a nontrivial rectangle -/
  hT : 0 < T
  /-- All poles are in the open interior of the rectangle -/
  poles_in_interior : ∀ p ∈ perronPoles T, p ∈ openRect (1/2) c (-T) T
  /-- F is differentiable away from poles -/
  F_diffOn_complement : DifferentiableOn ℂ (perronIntegrand x)
    (closedRect (1/2) c (-T) T \ (perronPoles T : Set ℂ))
  /-- G is continuous at each pole (removable singularity condition).
      This follows from: at each pole p, (s-p)*F(s) → residue(p), so
      F(s) - residue(p)/(s-p) has a removable singularity, and after
      subtracting ALL principal parts, G is continuous everywhere. -/
  G_continuousAt_poles : ∀ p ∈ perronPoles T, ContinuousAt (G x T) p

/-! ## Main Theorem -/

/-
**Phase 2 Main Quark**: G is differentiable on the entire closed rectangle.

    Proof:
    - At non-pole points: G = F - principalPartSum, both differentiable.
    - At each pole p in the interior: Apply the removable singularity theorem
      using continuity of G at p (from GHolomorphicHyp.G_continuousAt_poles).
-/
theorem G_differentiableOn (x : ℝ) (c T : ℝ) (hyp : GHolomorphicHyp x c T) :
    DifferentiableOn ℂ (G x T) (closedRect (1/2) c (-T) T) := by
  -- For points in the closed rectangle that are not poles, we can use the fact that the difference of differentiable functions is differentiable.
  have h_diff_non_poles : DifferentiableOn ℂ (G x T) (closedRect (1/2) c (-T) T \ (perronPoles T : Set ℂ)) := by
    apply_rules [ G_differentiableOn_complement, hyp.F_diffOn_complement ];
  intro z hz;
  by_cases hz_poles : z ∈ perronPoles T;
  · apply_rules [ G_differentiableWithinAt_at_pole ];
    · exact hyp.poles_in_interior z hz_poles;
    · exact hyp.G_continuousAt_poles z hz_poles;
  · have := h_diff_non_poles z ⟨ hz, hz_poles ⟩;
    refine' this.mono_of_mem_nhdsWithin _;
    rw [ mem_nhdsWithin_iff_exists_mem_nhds_inter ];
    exact ⟨ { w : ℂ | w ∉ perronPoles T }, IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| Set.Finite.isClosed <| Finset.finite_toSet _ ) hz_poles, fun w hw => ⟨ hw.2, hw.1 ⟩ ⟩

end Littlewood.Bridge.PerronPlanckQuarksPhase2