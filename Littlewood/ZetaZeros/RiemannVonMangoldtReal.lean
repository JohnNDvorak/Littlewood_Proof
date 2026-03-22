/-
Riemann-von Mangoldt Formula

Provides the `ZeroCountingRvmExplicitHyp` instance, which states:
  |N(T) - (T/2π) log(T/2π) + T/2π| ≤ C · log T
for all T ≥ T₀.

This automatically triggers the instance chain in ZeroCountingFunction.lean:
  `ZeroCountingRvmExplicitHyp` → `ZeroCountingAsymptoticHyp`
    → `ZeroCountingMainTermHyp` → `ZeroCountingLowerBoundHyp`

thereby closing sorry #10 (ZeroCountingLowerBoundHyp) in ZeroCountingAssumptions.lean.

## Proof Strategy

The RvM formula is proved by decomposing into three sub-results:
(a) Argument principle bridge: N(T) equals the number of zeros of
    the entire function RiemannXiAlt in a rectangle containing the critical strip
(b) Stirling approximation: arg(Γ(s/2)) integral gives the main term
(c) S(T) = O(log T): the zeta log-derivative contribution is bounded

Sub-results (b) and (c) are packaged as the single sorry
`rvm_contour_evaluation`, which encodes the Stirling + zeta-bound content.

## References
- Titchmarsh, "Theory of the Riemann Zeta Function", Theorem 9.4
- Montgomery-Vaughan, "Multiplicative Number Theory I", Theorem 14.5
- Davenport, "Multiplicative Number Theory", Chapter 15

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.RectArgumentPrinciple
import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.ZetaZeros.ZeroCountingMultiplicity
import Littlewood.ZetaZeros.DistinctMultiplicityCompatibility
import Littlewood.ZetaZeros.StirlingForRvM
import Littlewood.Aristotle.RiemannXiEntire
import Littlewood.ZetaZeros.RvMFormulaProof
import Littlewood.ZetaZeros.RvMContourFTC
import Littlewood.ZetaZeros.RvMContourEvaluation
import Littlewood.ZetaZeros.RvMEdgeIntegrals
import Littlewood.ZetaZeros.RvMRightEdge
import Littlewood.ZetaZeros.RightEdgeGammaMainTerm
import Littlewood.Aristotle.ZetaAnalyticProperties
import Littlewood.Aristotle.XiLogDerivDecomposition
import Littlewood.Aristotle.HardyThetaSmooth
import Littlewood.Aristotle.Standalone.HolomorphicLogOnHalfPlane


set_option maxHeartbeats 1600000
set_option autoImplicit false

noncomputable section

namespace ZetaZeros

open Complex Set MeasureTheory Topology Filter RectArgumentPrinciple
open scoped Real ComplexConjugate

/-! ## Bridge: RiemannXiAlt zeros in critical strip = nontrivial zeta zeros

The key connection: `RiemannXiAlt s = (1/2) s(s-1) Λ(s)` for s ≠ 0, 1.
In the critical strip (0 < Re s < 1), s ≠ 0 and s ≠ 1, so
  RiemannXiAlt s = 0 ↔ completedRiemannZeta s = 0 ↔ riemannZeta s = 0.
-/

/-- RiemannXiAlt(s) = 0 iff riemannZeta(s) = 0, for s in the critical strip. -/
theorem riemannXiAlt_zero_iff_zeta_zero {s : ℂ}
    (hre_pos : 0 < s.re) (hre_lt : s.re < 1) :
    RiemannXiAlt s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hre_pos; simp at hre_pos
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hre_lt; simp at hre_lt
  rw [RiemannXiAlt_eq_formula hs0 hs1]
  have h2 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hprod : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2 hs0) (sub_ne_zero.mpr hs1)
  constructor
  · intro h
    have : completedRiemannZeta s = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hprod
      · exact h
    exact (completedRiemannZeta_eq_zero_iff_riemannZeta hre_pos).mp this
  · intro h
    have hcomp := (completedRiemannZeta_eq_zero_iff_riemannZeta hre_pos).mpr h
    rw [hcomp]; ring

/-- RiemannXiAlt has no zeros with Re(s) ≥ 1 except possibly at s = 1.
    For Re > 1, zeta has no zeros by the Euler product.
    For Re = 1, zeta has no zeros by de la Vallee-Poussin (in Mathlib). -/
theorem riemannXiAlt_ne_zero_of_re_ge_one {s : ℂ} (hre : 1 ≤ s.re) (hs1 : s ≠ 1) :
    RiemannXiAlt s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; subst h; norm_num at hre
  rw [RiemannXiAlt_eq_formula hs0 hs1]
  intro h
  have h2 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hprod : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2 hs0) (sub_ne_zero.mpr hs1)
  have : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hprod
    · exact h
  have hzeta := (completedRiemannZeta_eq_zero_iff_riemannZeta (by linarith)).mp this
  exact riemannZeta_ne_zero_of_one_le_re hre hzeta

/-- RiemannXiAlt has no zeros with Re(s) > 1. -/
theorem riemannXiAlt_ne_zero_of_re_gt_one {s : ℂ} (hre : 1 < s.re) :
    RiemannXiAlt s ≠ 0 :=
  riemannXiAlt_ne_zero_of_re_ge_one (le_of_lt hre) (by
    intro h; subst h; norm_num at hre)

/-- The functional equation: RiemannXiAlt(1-s) = RiemannXiAlt(s). -/
theorem riemannXiAlt_one_sub (s : ℂ) : RiemannXiAlt (1 - s) = RiemannXiAlt s := by
  unfold RiemannXiAlt
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- RiemannXiAlt has no zeros with Re(s) ≤ 0 except possibly at s = 0.
    By the functional equation, RiemannXiAlt(s) = RiemannXiAlt(1-s), and
    Re(1-s) ≥ 1, so riemannXiAlt_ne_zero_of_re_ge_one applies. -/
theorem riemannXiAlt_ne_zero_of_re_le_zero {s : ℂ} (hre : s.re ≤ 0) (hs0 : s ≠ 0) :
    RiemannXiAlt s ≠ 0 := by
  rw [← riemannXiAlt_one_sub]
  apply riemannXiAlt_ne_zero_of_re_ge_one
  · simp [Complex.sub_re, Complex.one_re]; linarith
  · intro h
    have : s = 0 := by
      have hre_eq := congr_arg Complex.re h
      simp [Complex.sub_re, Complex.one_re] at hre_eq
      have him_eq : s.im = 0 := by
        have := congr_arg Complex.im h
        simp [Complex.sub_im, Complex.one_im] at this
        linarith
      have hre_z : s.re = 0 := by linarith
      exact Complex.ext hre_z him_eq
    exact hs0 this

/-- RiemannXiAlt has no zeros with Re(s) < 0. -/
theorem riemannXiAlt_ne_zero_of_re_neg {s : ℂ} (hre : s.re < 0) :
    RiemannXiAlt s ≠ 0 :=
  riemannXiAlt_ne_zero_of_re_le_zero (le_of_lt hre) (by
    intro h; subst h; simp at hre)

/-! ## Sub-lemma: Zeros in rectangle = N(T)

For T not equal to any zero ordinate and T > 14, the zeros of RiemannXiAlt
in the open rectangle (-1, 2) × (1, T) are exactly the nontrivial zeta zeros
with 0 < Im(ρ) < T. The only low-height input is that every nontrivial
zero ordinate is strictly larger than 1, so the restriction Im > 1 is
equivalent to Im > 0 for nontrivial zeros.
-/

/-- The set of zeros of RiemannXiAlt in the rectangle (-1,2)×(1,T) equals
    the set of nontrivial zeta zeros with 0 < Im(ρ) < T, provided T is not
    a zero ordinate and all nontrivial zero ordinates exceed 1. -/
theorem xi_zeros_in_rect_eq_strip [ZeroOrdinateLowerBoundHyp] (T : ℝ) (_hT : 14 ≤ T)
    (_hT_not_ord : T ∉ zetaZeroOrdinates) :
    {z ∈ openRect (-1) 2 1 T | RiemannXiAlt z = 0} =
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im < T} := by
  ext z
  constructor
  · rintro ⟨hz_rect, hz_zero⟩
    obtain ⟨ha, hb, hc, hd⟩ := hz_rect
    have him_pos : 0 < z.im := by linarith
    have hre_pos : 0 < z.re := by
      by_contra h
      push_neg at h
      have hz_ne_zero : z ≠ 0 := by
        intro heq; rw [heq] at hc; simp at hc; linarith
      exact riemannXiAlt_ne_zero_of_re_le_zero h hz_ne_zero hz_zero
    have hre_lt : z.re < 1 := by
      by_contra h
      push_neg at h
      have hz_ne_one : z ≠ 1 := by
        intro heq; rw [heq] at hc; simp at hc; linarith
      exact riemannXiAlt_ne_zero_of_re_ge_one h hz_ne_one hz_zero
    exact ⟨(riemannXiAlt_zero_iff_zeta_zero hre_pos hre_lt).mp hz_zero,
      hre_pos, hre_lt, him_pos, hd⟩
  · rintro ⟨hzeta, hre_pos, hre_lt, him_pos, him_lt⟩
    constructor
    · refine ⟨by linarith, by linarith, ?_, him_lt⟩
      exact zero_ord_lower_bound z ⟨⟨hzeta, hre_pos, hre_lt⟩, him_pos⟩
    · exact (riemannXiAlt_zero_iff_zeta_zero hre_pos hre_lt).mpr hzeta

/-- The ncard of zeros of RiemannXiAlt in the rectangle (-1,2)×(1,T) equals N(T)
    for T not a zero ordinate. Uses `ZeroOrdinateLowerBoundHyp` to show zeros with
    Im ∈ (1,T) = zeros with Im ∈ (0,T] (all zeros have Im ≥ 14.13 > 1). -/
theorem xi_zero_count_eq_N [ZeroOrdinateLowerBoundHyp] (T : ℝ) (hT : 14 ≤ T)
    (hT_not_ord : T ∉ zetaZeroOrdinates) :
    Set.ncard {z ∈ openRect (-1) 2 1 T | RiemannXiAlt z = 0} = N T := by
  rw [xi_zeros_in_rect_eq_strip T hT hT_not_ord]
  show Set.ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im < T} = N T
  congr 1
  ext z
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨hzeta, hre_pos, hre_lt, him_pos, him_lt⟩
    have hmem : z ∈ zetaNontrivialZerosPos := by
      rw [mem_zetaNontrivialZerosPos, mem_zetaNontrivialZeros]
      exact ⟨⟨hzeta, hre_pos, hre_lt⟩, him_pos⟩
    show z ∈ zerosUpTo T
    exact ⟨hmem, le_of_lt him_lt⟩
  · intro hz
    obtain ⟨hzpos, hle'⟩ := hz
    have hle : z.im ≤ T := hle'
    obtain ⟨hznon, him_pos⟩ := mem_zetaNontrivialZerosPos.mp hzpos
    obtain ⟨hzeta, hre_pos, hre_lt⟩ := mem_zetaNontrivialZeros.mp hznon
    refine ⟨hzeta, hre_pos, hre_lt, him_pos, ?_⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      apply hT_not_ord
      exact ⟨z, hzpos, h⟩

/-- The zeros of `RiemannXiAlt` in the rectangle `(-1,2) × (1,T)` are exactly
    the nontrivial zeta zeros counted by `zerosUpTo T`. -/
private theorem xi_zeros_in_rect_eq_zerosUpTo [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    {z ∈ openRect (-1) 2 1 T | RiemannXiAlt z = 0} = zerosUpTo T := by
  rw [xi_zeros_in_rect_eq_strip T hT hT_not_ord]
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzeta, hre_pos, hre_lt, him_pos, him_lt⟩
    have hzpos : z ∈ zetaNontrivialZerosPos :=
      (mem_zetaNontrivialZerosPos).2
        ⟨(mem_zetaNontrivialZeros).2 ⟨hzeta, hre_pos, hre_lt⟩, him_pos⟩
    simpa [zerosUpTo] using And.intro hzpos (le_of_lt him_lt)
  · intro hz
    have hz' : z ∈ zetaNontrivialZerosPos ∧ z.im ≤ T := by
      simpa [zerosUpTo] using hz
    rcases mem_zetaNontrivialZerosPos.mp hz'.1 with ⟨hznon, him_pos⟩
    rcases mem_zetaNontrivialZeros.mp hznon with ⟨hzeta, hre_pos, hre_lt⟩
    refine ⟨hzeta, hre_pos, hre_lt, him_pos, ?_⟩
    rcases lt_or_eq_of_le hz'.2 with him_lt | him_eq
    · exact him_lt
    · exfalso
      exact hT_not_ord ⟨z, hz'.1, him_eq⟩

/-- Inside the critical strip, `RiemannXiAlt` and `ζ` have the same analytic
    order because they differ by a nowhere-vanishing analytic factor. -/
private theorem analyticOrderAt_RiemannXiAlt_eq_riemannZeta_of_mem_zerosUpTo
    {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ zerosUpTo T) :
    analyticOrderAt RiemannXiAlt ρ = analyticOrderAt riemannZeta ρ := by
  have hρ' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hρ
  rcases mem_zetaNontrivialZerosPos.mp hρ'.1 with ⟨hρnon, _⟩
  rcases mem_zetaNontrivialZeros.mp hρnon with ⟨_, hρre_pos, hρre_lt⟩
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hρre_pos
    simp at hρre_pos
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at hρre_lt
    norm_num at hρre_lt
  let g : ℂ → ℂ := fun s => ((1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s)
  have hGamma_analytic : AnalyticAt ℂ Gammaℝ ρ := by
    refine DifferentiableOn.analyticAt (s := {s : ℂ | 0 < s.re}) ?_ ?_
    · intro s hs
      exact (RvMRightEdge.differentiableAt_GammaR s hs).differentiableWithinAt
    · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρre_pos
  have hg_analytic : AnalyticAt ℂ g ρ := by
    unfold g
    exact (((analyticAt_const.mul analyticAt_id).mul
      (analyticAt_id.sub analyticAt_const)).mul hGamma_analytic)
  have hzeta_analytic : AnalyticAt ℂ riemannZeta ρ := by
    refine DifferentiableOn.analyticAt (s := {s : ℂ | s ≠ 1}) ?_ ?_
    · intro s hs
      exact (differentiableAt_riemannZeta hs).differentiableWithinAt
    · exact isOpen_ne.mem_nhds hρ1
  have hcongr : RiemannXiAlt =ᶠ[𝓝 ρ] fun s => g s * riemannZeta s := by
    filter_upwards [isOpen_ne.mem_nhds hρ0, isOpen_ne.mem_nhds hρ1,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρre_pos] with s hs0 hs1 hsre
    rw [RiemannXiAlt_eq_formula hs0 hs1,
      RvMRightEdge.completedZeta_eq_GammaR_mul_zeta s hs0 (Gammaℝ_ne_zero_of_re_pos hsre)]
    show (1 / 2 : ℂ) * s * (s - 1) * (Gammaℝ s * riemannZeta s) =
        (((1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s) * riemannZeta s)
    ring_nf
  have hg_nonzero : g ρ ≠ 0 := by
    unfold g
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) hρ0)
        (sub_ne_zero.mpr hρ1))
      (Gammaℝ_ne_zero_of_re_pos hρre_pos)
  have hg_order : analyticOrderAt g ρ = 0 :=
    hg_analytic.analyticOrderAt_eq_zero.2 hg_nonzero
  calc
    analyticOrderAt RiemannXiAlt ρ
        = analyticOrderAt (fun s => g s * riemannZeta s) ρ := analyticOrderAt_congr hcongr
    _ = analyticOrderAt g ρ + analyticOrderAt riemannZeta ρ := by
      simpa using analyticOrderAt_mul hg_analytic hzeta_analytic
    _ = analyticOrderAt riemannZeta ρ := by rw [hg_order, zero_add]

/-- The multiplicity-counted zero count for `RiemannXiAlt` on the canonical
    rectangle matches `Nmult`. -/
private theorem xi_zeroCountRectMult_eq_Nmult [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    zeroCountRectMult RiemannXiAlt (-1) 2 1 T = Nmult T := by
  have hrect_eq : {z ∈ openRect (-1) 2 1 T | RiemannXiAlt z = 0} = zerosUpTo T :=
    xi_zeros_in_rect_eq_zerosUpTo T hT hT_not_ord
  have hfin_rect : {z ∈ openRect (-1) 2 1 T | RiemannXiAlt z = 0}.Finite := by
    simpa [hrect_eq] using (finite_zeros_le T)
  rw [zeroCountRectMult_eq_sum (f := RiemannXiAlt) (a := -1) (b := 2) (c := 1) (d := T) hfin_rect,
    zeroCountingFunctionMult_eq_sum]
  have htoFinset : hfin_rect.toFinset = (finite_zeros_le T).toFinset := by
    ext z
    simp [Set.Finite.mem_toFinset, hrect_eq]
  rw [htoFinset]
  refine Finset.sum_congr rfl ?_
  intro z hz
  have hz_mem : z ∈ zerosUpTo T := by
    simpa [Set.Finite.mem_toFinset] using hz
  rw [analyticOrderAt_RiemannXiAlt_eq_riemannZeta_of_mem_zerosUpTo hz_mem]

/-! ## Deep analytic content: Contour evaluation (Stirling + S(T) bound)

This is the deep analytic content of the RvM formula. Given that the
argument principle identifies N(T) with the log-integral of RiemannXiAlt
(proved above via `xi_zero_count_eq_N`), the contour integral evaluation
requires:
- Stirling's approximation for Γ: Im log Γ(1/4 + iT/2) = (T/2)log(T/2) - T/2 - π/8 + O(1/T)
- The bound S(T) = (1/π) arg ζ(1/2 + iT) = O(log T) (Backlund/Littlewood)
- Standard bounds for ζ'/ζ on vertical lines Re = 2 and Re = -1

Together these give: N(T) = (T/2π)log(T/2π) - T/2π + O(log T).

## Proved infrastructure feeding into this sorry:
- `RiemannXiAlt_entire`: RiemannXiAlt is entire (Mathlib: `differentiable_completedZeta₀`)
- `riemannXiAlt_one_sub`: functional equation RiemannXiAlt(1-s) = RiemannXiAlt(s)
- `riemannXiAlt_ne_zero_of_re_ge_one`: no zeros for Re ≥ 1 (Mathlib: `riemannZeta_ne_zero_of_one_le_re`)
- `riemannXiAlt_ne_zero_of_re_le_zero`: no zeros for Re ≤ 0 (via functional equation)
- `xi_zeros_in_rect_eq_strip`: zeros in rectangle = critical strip zeros
- `xi_zero_count_eq_N`: zero count = N(T)
- `argument_principle_rect_entire`: argument principle for rectangles (RectArgumentPrinciple.lean)
-/

/-! ## Utility: Nearby non-ordinate

Zero ordinates form a discrete (in fact finite in bounded intervals) set,
so for any T there exists T' close to T that is not a zero ordinate. -/

/-- For any T, there exists T' ∈ (T, T+1] that is not a zero ordinate.
    This follows from the finite zero density: zetaZeroOrdinates ∩ (T, T+1]
    is finite (since zerosUpTo(T+1) is finite), but (T, T+1] is infinite. -/
theorem exists_nearby_non_ordinate (T : ℝ) :
    ∃ T' ∈ Set.Ioc T (T + 1), T' ∉ zetaZeroOrdinates := by
  by_contra hall
  push_neg at hall
  -- Every point of (T, T+1] is a zero ordinate
  have hsub : Set.Ioc T (T + 1) ⊆ zetaZeroOrdinates ∩ Set.Ioc T (T + 1) :=
    fun x hx => ⟨hall x hx, hx⟩
  -- But (T, T+1] is infinite
  have hinf : (Set.Ioc T (T + 1)).Infinite := Set.Ioc_infinite (by linarith)
  -- And zero ordinates in (T, T+1] are finite
  have hfin : (zetaZeroOrdinates ∩ Set.Ioc T (T + 1)).Finite := by
    apply Set.Finite.subset (Set.Finite.image _ (finite_zeros_le (T + 1)))
    intro γ ⟨hγ_mem, hγ_range⟩
    obtain ⟨z, hzpos, rfl⟩ := hγ_mem
    exact ⟨z, ⟨hzpos, hγ_range.2⟩, rfl⟩
  exact hinf (hfin.subset hsub)

/-! ## RvM Decomposition and Main Theorem

The Riemann-von Mangoldt formula connects N(T) to the Stirling approximation
and the argument of zeta on the critical line:

  N(T) = (1/π)·Im(logΓ(1/4+iT/2)) − (T/2π)·logπ + 1 + S(T)

where S(T) = (1/π)·arg(ζ(1/2+iT)).

This follows from the argument principle applied to ξ(s) on the rectangle
(-1,2)×(0,T), decomposing ξ'/ξ = Γ'/Γ + ζ'/ζ + rational terms, and
evaluating the resulting contour integrals.

## Proof of riemann_von_mangoldt_explicit

We compose four proved results:
1. `rvm_decomposition_bounded`: N(T) = Stirling + S(T) + 1 + O(logT)
2. `stirling_im_approx`: Im(stirlingApprox T) = main formula + O(1/T) [proved]
3. `backlund_ST_bound`: S(T) = O(logT) [proved]
4. `rvm_stirling_algebra`: algebraic identity [proved]

All error terms are absorbed into O(log T). -/

/-! ## RvM Decomposition Proof

**RvM decomposition**: N(T) equals the Stirling/theta contribution plus S(T) plus 1,
up to O(log T). This is the output of applying the argument principle to ξ(s)
on the rectangle (-1,2)×(0,T) and decomposing the logarithmic derivative.

Specifically: N(T) = (1/π)·Im(stirlingApprox T) − (T/2π)·logπ
                     + (1/π)·arg(ζ(1/2+iT)) + 1 + O(log T)

Reference: Titchmarsh, "Theory of the Riemann Zeta Function", §9.3-9.4 -/

/-! ### Sub-lemma: Xi is nonvanishing on the rectangle boundary

We use the rectangle (-1, 2) × (1, T) with bottom edge at height 1 to avoid
the hard analytic fact that ζ(s) ≠ 0 for real s ∈ (0,1). The only low-height
input needed here is `ZeroOrdinateLowerBoundHyp`, which says every positive
nontrivial zero ordinate is strictly larger than 1. This means neither Im = 1
nor Im = T (T not an ordinate) can be a zero ordinate.

On the boundary of (-1, 2) × (1, T) for T not a zero ordinate:
- Bottom edge (Im = 1): no nontrivial zero has Im = 1 (all ordinates are > 1)
- Top edge (Im = T): xi ≠ 0 since no zero has imaginary part T (T not an ordinate)
- Right edge (Re = 2): xi ≠ 0 by riemannXiAlt_ne_zero_of_re_ge_one
- Left edge (Re = -1): xi ≠ 0 by riemannXiAlt_ne_zero_of_re_le_zero
-/

/-- 1 is not a zero ordinate: every nontrivial zero ordinate is strictly larger than 1. -/
private theorem one_not_zero_ordinate [ZeroOrdinateLowerBoundHyp] :
    (1 : ℝ) ∉ zetaZeroOrdinates := by
  rintro ⟨ρ, hρ, hρim⟩
  nlinarith [zero_ord_lower_bound ρ hρ, hρim]

/-- Xi does not vanish on the boundary of the rectangle (-1, 2) × (1, T)
    when T > 1 is not a zero ordinate. Uses `ZeroOrdinateLowerBoundHyp` to
    ensure no zero ordinate equals 1. -/
private theorem xi_ne_zero_on_boundary [ZeroOrdinateLowerBoundHyp] (T : ℝ) (_hT : 1 < T)
    (hT_not_ord : T ∉ zetaZeroOrdinates) :
    ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 1 T, RiemannXiAlt z ≠ 0 := by
  intro z ⟨hclosed, hnot_open⟩
  -- z is in the closed rectangle but not the open rectangle
  obtain ⟨hre_lo, hre_hi, him_lo, him_hi⟩ := hclosed
  -- Cases: z is on the boundary, so at least one coordinate is extremal
  intro h
  -- h : RiemannXiAlt z = 0
  -- Zeros of xi are in the critical strip (0 < Re < 1)
  have hre_pos : 0 < z.re := by
    by_contra h2
    push_neg at h2
    have hz_ne : z ≠ 0 := by
      intro heq; subst heq; simp [RiemannXiAlt] at h
    exact (riemannXiAlt_ne_zero_of_re_le_zero h2 hz_ne) h
  have hre_lt : z.re < 1 := by
    by_contra h2
    push_neg at h2
    have hz_ne : z ≠ 1 := by
      intro heq; subst heq; simp [RiemannXiAlt] at h
    exact (riemannXiAlt_ne_zero_of_re_ge_one h2 hz_ne) h
  -- So z is in the critical strip with Re ∈ (0,1). Since z is on the boundary
  -- but not in the open rect, either Im(z) = 1 or Im(z) = T.
  -- In either case, z would be a nontrivial zero with Im equal to 1 or T,
  -- making that value a zero ordinate — contradiction.
  have him_pos : 0 < z.im := by linarith
  have hzeta_zero := (riemannXiAlt_zero_iff_zeta_zero hre_pos hre_lt).mp h
  have hmem : z ∈ zetaNontrivialZeros := ⟨hzeta_zero, hre_pos, hre_lt⟩
  have hzpos : z ∈ zetaNontrivialZerosPos := ⟨hmem, him_pos⟩
  have hopen_def : z ∈ RectArgumentPrinciple.openRect (-1) 2 1 T := by
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · -- Need Im(z) > 1.
      by_contra h_le
      push_neg at h_le
      have him_eq : z.im = 1 := le_antisymm h_le him_lo
      -- z is a nontrivial zero with Im = 1, making 1 a zero ordinate — contradiction
      exact one_not_zero_ordinate ⟨z, hzpos, him_eq⟩
    · -- Need Im(z) < T. If Im(z) = T, then z is a zero with Im = T, contradicting hT_not_ord
      by_contra h_ge
      push_neg at h_ge
      have him_eq : z.im = T := le_antisymm him_hi h_ge
      exact hT_not_ord ⟨z, hzpos, him_eq⟩
  exact hnot_open hopen_def

/-- The multiplicity-counted rectangle argument principle identifies the
    normalized logarithmic integral of `RiemannXiAlt` with `Nmult(T)`. -/
private theorem xi_logIntegralRect_eq_Nmult [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    logIntegralRect RiemannXiAlt (-1) 2 1 T = (Nmult T : ℂ) := by
  have hbdy := xi_ne_zero_on_boundary T (by linarith) hT_not_ord
  calc
    logIntegralRect RiemannXiAlt (-1) 2 1 T
        = ↑(zeroCountRectMult RiemannXiAlt (-1) 2 1 T) := by
          exact argument_principle_rect_entire_mult RiemannXiAlt (-1) 2 1 T
            (by norm_num) (by linarith) RiemannXiAlt_entire hbdy
    _ = (Nmult T : ℂ) := by
          rw [xi_zeroCountRectMult_eq_Nmult T hT hT_not_ord]

/-- The xi log-derivative splits into the simple poles plus the completed-zeta
    log-derivative at points with positive imaginary part. -/
private theorem logDeriv_xi_eq_inv_plus_logDeriv_completed (s : ℂ)
    (h_im : 0 < s.im) (hcomp : completedRiemannZeta s ≠ 0) :
    logDeriv RiemannXiAlt s =
      (s⁻¹ + (s - 1)⁻¹) + logDeriv completedRiemannZeta s := by
  have h0 : s ≠ 0 := by
    intro h
    rw [h] at h_im
    simp at h_im
  have h1 : s ≠ 1 := by
    intro h
    rw [h] at h_im
    simp at h_im
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  set g := fun z : ℂ => z * (z - 1) * completedRiemannZeta₀ z + 1 with hg_def
  have hld_const : logDeriv RiemannXiAlt s = logDeriv g s := by
    show logDeriv (fun z => (1 / 2 : ℂ) * g z) s = logDeriv g s
    exact logDeriv_const_mul s (1 / 2 : ℂ) (by norm_num)
  have hgf_eq : ∀ z : ℂ, z ≠ 0 → z ≠ 1 →
      g z = z * (z - 1) * completedRiemannZeta z := by
    intro z hz0 hz1
    simp only [hg_def]
    have h := completedRiemannZeta_eq z
    rw [h]
    have hz1' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    field_simp [hz0, hz1']
    ring
  have hg_at_s : g s = s * (s - 1) * completedRiemannZeta s := hgf_eq s h0 h1
  have hgf_nhds : g =ᶠ[nhds s] (fun z => z * (z - 1) * completedRiemannZeta z) :=
    Filter.Eventually.mono
      (IsOpen.mem_nhds (isOpen_ne.inter isOpen_ne) ⟨h0, h1⟩)
      (fun z ⟨hz0, hz1⟩ => hgf_eq z hz0 hz1)
  have hlogderiv_eq : logDeriv g s =
      logDeriv (fun z => z * (z - 1) * completedRiemannZeta z) s := by
    simp only [logDeriv_apply, hg_at_s, Filter.EventuallyEq.deriv_eq hgf_nhds]
  have hdLam : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta h0 h1
  have hd_poly : HasDerivAt (fun z : ℂ => z * (z - 1)) (2 * s - 1) s := by
    convert (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const (1 : ℂ)) using 1
    simp only [id]
    ring
  have hd_prod : HasDerivAt (fun z => z * (z - 1) * completedRiemannZeta z)
      ((2 * s - 1) * completedRiemannZeta s +
        s * (s - 1) * deriv completedRiemannZeta s) s := by
    have h1' := hd_poly.mul hdLam.hasDerivAt
    have : ((fun z => z * (z - 1)) * completedRiemannZeta) =
        (fun z => z * (z - 1) * completedRiemannZeta z) := by
      ext z
      simp [Pi.mul_apply]
    rwa [this] at h1'
  rw [hld_const, hlogderiv_eq]
  simp only [logDeriv_apply, hd_prod.deriv]
  field_simp [h0, hs1, hcomp]
  ring

/-- Boundary points on the bottom edge of the canonical RvM rectangle. -/
private theorem bottom_edge_mem_rectBoundary (T : ℝ) (hT : 1 ≤ T) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 2) :
    ((↑x : ℂ) + (1 : ℂ) * I) ∈ RectArgumentPrinciple.rectBoundary (-1) 2 1 T := by
  refine ⟨?_, ?_⟩
  · exact ⟨by simpa using hx.1, by simpa using hx.2, by simp, by simpa using hT⟩
  · intro hopen
    obtain ⟨_, _, him, _⟩ := hopen
    simp at him

/-- Boundary points on the top edge of the canonical RvM rectangle. -/
private theorem top_edge_mem_rectBoundary (T : ℝ) (hT : 1 ≤ T) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 2) :
    ((↑x : ℂ) + (↑T : ℂ) * I) ∈ RectArgumentPrinciple.rectBoundary (-1) 2 1 T := by
  refine ⟨?_, ?_⟩
  · exact ⟨by simpa using hx.1, by simpa using hx.2, by simpa using hT, by simp⟩
  · intro hopen
    obtain ⟨_, _, _, him⟩ := hopen
    simp at him

/-- Boundary points on the right edge of the canonical RvM rectangle. -/
private theorem right_edge_mem_rectBoundary (T : ℝ) (_hT : 1 ≤ T) {y : ℝ}
    (hy : y ∈ Set.Icc (1 : ℝ) T) :
    ((2 : ℂ) + (↑y : ℂ) * I) ∈ RectArgumentPrinciple.rectBoundary (-1) 2 1 T := by
  refine ⟨?_, ?_⟩
  · exact ⟨by norm_num, by simp, by simpa using hy.1, by simpa using hy.2⟩
  · intro hopen
    obtain ⟨_, hre, _, _⟩ := hopen
    simp at hre

/-- Boundary points on the left edge of the canonical RvM rectangle. -/
private theorem left_edge_mem_rectBoundary (T : ℝ) (_hT : 1 ≤ T) {y : ℝ}
    (hy : y ∈ Set.Icc (1 : ℝ) T) :
    ((-1 : ℂ) + (↑y : ℂ) * I) ∈ RectArgumentPrinciple.rectBoundary (-1) 2 1 T := by
  refine ⟨?_, ?_⟩
  · exact ⟨by simp, by norm_num, by simpa using hy.1, by simpa using hy.2⟩
  · intro hopen
    obtain ⟨hre, _, _, _⟩ := hopen
    simp at hre

/-- Nonvanishing of `completedRiemannZeta` on the canonical rectangle boundary,
    deduced from the corresponding `RiemannXiAlt` boundary theorem. -/
private theorem completedZeta_ne_zero_on_boundary [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 1 T, completedRiemannZeta z ≠ 0 := by
  intro z hz hb
  have hclosed := hz.1
  obtain ⟨_, _, him_lo, _⟩ := hclosed
  have h0 : z ≠ 0 := by
    intro h
    rw [h] at him_lo
    simp at him_lo
    linarith
  have h1 : z ≠ 1 := by
    intro h
    rw [h] at him_lo
    simp at him_lo
    linarith
  have hxi_ne := xi_ne_zero_on_boundary T (by linarith) hT_not_ord z hz
  apply hxi_ne
  rw [RiemannXiAlt_eq_formula h0 h1]
  simp [hb]

/-- The logarithmic rectangle integral for `RiemannXiAlt` equals the one for
    `completedRiemannZeta`; this removes the simple-pole terms from the contour
    evaluation problem. -/
private theorem xi_logIntegralRect_eq_completedZeta [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    logIntegralRect RiemannXiAlt (-1) 2 1 T =
      logIntegralRect completedRiemannZeta (-1) 2 1 T := by
  have hT1 : 1 ≤ T := by linarith
  have hbdy := completedZeta_ne_zero_on_boundary T hT hT_not_ord
  have h_decomp_bot : ∀ x ∈ Set.Icc (-1 : ℝ) 2,
      logDeriv RiemannXiAlt ((↑x : ℂ) + (1 : ℂ) * I) =
        ((((↑x : ℂ) + (1 : ℂ) * I)⁻¹ + ((((↑x : ℂ) + (1 : ℂ) * I) - 1)⁻¹)) +
          logDeriv completedRiemannZeta ((↑x : ℂ) + (1 : ℂ) * I)) := by
    intro x hx
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp
    · exact hbdy _ (bottom_edge_mem_rectBoundary T hT1 hx)
  have h_decomp_top : ∀ x ∈ Set.Icc (-1 : ℝ) 2,
      logDeriv RiemannXiAlt ((↑x : ℂ) + (↑T : ℂ) * I) =
        ((((↑x : ℂ) + (↑T : ℂ) * I)⁻¹ + ((((↑x : ℂ) + (↑T : ℂ) * I) - 1)⁻¹)) +
          logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) := by
    intro x hx
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp
      linarith
    · exact hbdy _ (top_edge_mem_rectBoundary T hT1 hx)
  have h_decomp_right : ∀ y ∈ Set.Icc (1 : ℝ) T,
      logDeriv RiemannXiAlt ((2 : ℂ) + (↑y : ℂ) * I) =
        ((((2 : ℂ) + (↑y : ℂ) * I)⁻¹ + ((((2 : ℂ) + (↑y : ℂ) * I) - 1)⁻¹)) +
          logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)) := by
    intro y hy
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp
      linarith [hy.1]
    · exact hbdy _ (right_edge_mem_rectBoundary T hT1 hy)
  have h_decomp_left : ∀ y ∈ Set.Icc (1 : ℝ) T,
      logDeriv RiemannXiAlt ((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I) =
        ((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)⁻¹ +
          ((((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I) - 1)⁻¹) +
          logDeriv completedRiemannZeta ((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I) := by
    intro y hy
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp
      linarith [hy.1]
    · exact hbdy _ (by
        show ((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I) ∈ RectArgumentPrinciple.rectBoundary (-1) 2 1 T
        simpa using left_edge_mem_rectBoundary T hT1 hy)
  have hxi_deriv_cont : Continuous (deriv RiemannXiAlt) := by
    simpa using
      ((RiemannXiAlt_entire.contDiff : ContDiff ℂ ⊤ RiemannXiAlt).continuous_deriv (by simp))
  have hh_bot_cont : ContinuousOn
      (fun x : ℝ => ((↑x : ℂ) + (1 : ℂ) * I)⁻¹ + ((((↑x : ℂ) + (1 : ℂ) * I) - 1)⁻¹))
      (Set.Icc (-1 : ℝ) 2) := by
    apply ContinuousOn.add
    · apply ContinuousOn.inv₀
      · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
      · intro x _ hx0
        have him := congr_arg Complex.im hx0
        simp at him
    · apply ContinuousOn.inv₀
      · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub continuousOn_const
      · intro x _ hx1
        have him := congr_arg Complex.im hx1
        simp at him
  have hh_top_cont : ContinuousOn
      (fun x : ℝ => ((↑x : ℂ) + (↑T : ℂ) * I)⁻¹ + ((((↑x : ℂ) + (↑T : ℂ) * I) - 1)⁻¹))
      (Set.Icc (-1 : ℝ) 2) := by
    apply ContinuousOn.add
    · apply ContinuousOn.inv₀
      · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
      · intro x _ hx0
        have him := congr_arg Complex.im hx0
        simp at him
        linarith
    · apply ContinuousOn.inv₀
      · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub continuousOn_const
      · intro x _ hx1
        have him := congr_arg Complex.im hx1
        simp at him
        linarith
  have hh_right_cont : ContinuousOn
      (fun y : ℝ => ((2 : ℂ) + (↑y : ℂ) * I)⁻¹ + ((((2 : ℂ) + (↑y : ℂ) * I) - 1)⁻¹))
      (Set.Icc (1 : ℝ) T) := by
    apply ContinuousOn.add
    · apply ContinuousOn.inv₀
      · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      · intro y _ hy0
        have hre := congr_arg Complex.re hy0
        simp at hre
    · apply ContinuousOn.inv₀
      · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub continuousOn_const
      · intro y _ hy1
        have hre := congr_arg Complex.re hy1
        norm_num at hre
  have hh_left_cont : ContinuousOn
      (fun y : ℝ => (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)⁻¹ +
          ((((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I) - 1)⁻¹)))
      (Set.Icc (1 : ℝ) T) := by
    apply ContinuousOn.add
    · apply ContinuousOn.inv₀
      · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      · intro y _ hy0
        have hre := congr_arg Complex.re hy0
        simp at hre
    · apply ContinuousOn.inv₀
      · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub continuousOn_const
      · intro y _ hy1
        have hre := congr_arg Complex.re hy1
        norm_num at hre
  have hh_bot : IntervalIntegrable
      (fun x : ℝ => ((↑x : ℂ) + (1 : ℂ) * I)⁻¹ + ((((↑x : ℂ) + (1 : ℂ) * I) - 1)⁻¹))
      volume (-1) 2 :=
    hh_bot_cont.intervalIntegrable_of_Icc (by norm_num)
  have hh_top : IntervalIntegrable
      (fun x : ℝ => ((↑x : ℂ) + (↑T : ℂ) * I)⁻¹ + ((((↑x : ℂ) + (↑T : ℂ) * I) - 1)⁻¹))
      volume (-1) 2 :=
    hh_top_cont.intervalIntegrable_of_Icc (by norm_num)
  have hh_right : IntervalIntegrable
      (fun y : ℝ => ((2 : ℂ) + (↑y : ℂ) * I)⁻¹ + ((((2 : ℂ) + (↑y : ℂ) * I) - 1)⁻¹))
      volume 1 T :=
    hh_right_cont.intervalIntegrable_of_Icc hT1
  have hh_left : IntervalIntegrable
      (fun y : ℝ => (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)⁻¹ +
          ((((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I) - 1)⁻¹)))
      volume 1 T :=
    hh_left_cont.intervalIntegrable_of_Icc hT1
  have hg_bot_cont : ContinuousOn
      (fun x : ℝ => logDeriv completedRiemannZeta ((↑x : ℂ) + (1 : ℂ) * I))
      (Set.Icc (-1 : ℝ) 2) := by
    have hxi_bot_cont : ContinuousOn
        (fun x : ℝ => logDeriv RiemannXiAlt ((↑x : ℂ) + (1 : ℂ) * I))
        (Set.Icc (-1 : ℝ) 2) := by
      have hnum : ContinuousOn
          (fun x : ℝ => deriv RiemannXiAlt ((↑x : ℂ) + (1 : ℂ) * I))
          (Set.Icc (-1 : ℝ) 2) :=
        (hxi_deriv_cont.comp (continuous_ofReal.add (continuous_const.mul continuous_const))).continuousOn
      have hden : ContinuousOn
          (fun x : ℝ => RiemannXiAlt ((↑x : ℂ) + (1 : ℂ) * I))
          (Set.Icc (-1 : ℝ) 2) :=
        (RiemannXiAlt_entire.continuous.comp
          (continuous_ofReal.add (continuous_const.mul continuous_const))).continuousOn
      have hne : ∀ x ∈ Set.Icc (-1 : ℝ) 2, RiemannXiAlt ((↑x : ℂ) + (1 : ℂ) * I) ≠ 0 := by
        intro x hx
        exact xi_ne_zero_on_boundary T (by linarith) hT_not_ord _
          (bottom_edge_mem_rectBoundary T hT1 hx)
      simpa [logDeriv_apply] using hnum.div hden hne
    refine (hxi_bot_cont.sub hh_bot_cont).congr ?_
    intro x hx
    symm
    exact (sub_eq_iff_eq_add).2 (by
      simpa [add_comm, add_left_comm, add_assoc] using h_decomp_bot x hx)
  have hg_top_cont : ContinuousOn
      (fun x : ℝ => logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
      (Set.Icc (-1 : ℝ) 2) := by
    have hxi_top_cont : ContinuousOn
        (fun x : ℝ => logDeriv RiemannXiAlt ((↑x : ℂ) + (↑T : ℂ) * I))
        (Set.Icc (-1 : ℝ) 2) := by
      have hnum : ContinuousOn
          (fun x : ℝ => deriv RiemannXiAlt ((↑x : ℂ) + (↑T : ℂ) * I))
          (Set.Icc (-1 : ℝ) 2) :=
        (hxi_deriv_cont.comp (continuous_ofReal.add (continuous_const.mul continuous_const))).continuousOn
      have hden : ContinuousOn
          (fun x : ℝ => RiemannXiAlt ((↑x : ℂ) + (↑T : ℂ) * I))
          (Set.Icc (-1 : ℝ) 2) :=
        (RiemannXiAlt_entire.continuous.comp
          (continuous_ofReal.add (continuous_const.mul continuous_const))).continuousOn
      have hne : ∀ x ∈ Set.Icc (-1 : ℝ) 2, RiemannXiAlt ((↑x : ℂ) + (↑T : ℂ) * I) ≠ 0 := by
        intro x hx
        exact xi_ne_zero_on_boundary T (by linarith) hT_not_ord _
          (top_edge_mem_rectBoundary T hT1 hx)
      simpa [logDeriv_apply] using hnum.div hden hne
    refine (hxi_top_cont.sub hh_top_cont).congr ?_
    intro x hx
    symm
    exact (sub_eq_iff_eq_add).2 (by
      simpa [add_comm, add_left_comm, add_assoc] using h_decomp_top x hx)
  have hg_right_cont : ContinuousOn
      (fun y : ℝ => logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
      (Set.Icc (1 : ℝ) T) := by
    have hxi_right_cont : ContinuousOn
        (fun y : ℝ => logDeriv RiemannXiAlt ((2 : ℂ) + (↑y : ℂ) * I))
        (Set.Icc (1 : ℝ) T) := by
      have hnum : ContinuousOn
          (fun y : ℝ => deriv RiemannXiAlt ((2 : ℂ) + (↑y : ℂ) * I))
          (Set.Icc (1 : ℝ) T) :=
        (hxi_deriv_cont.comp (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
      have hden : ContinuousOn
          (fun y : ℝ => RiemannXiAlt ((2 : ℂ) + (↑y : ℂ) * I))
          (Set.Icc (1 : ℝ) T) :=
        (RiemannXiAlt_entire.continuous.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
      have hne : ∀ y ∈ Set.Icc (1 : ℝ) T, RiemannXiAlt ((2 : ℂ) + (↑y : ℂ) * I) ≠ 0 := by
        intro y hy
        exact xi_ne_zero_on_boundary T (by linarith) hT_not_ord _
          (right_edge_mem_rectBoundary T hT1 hy)
      simpa [logDeriv_apply] using hnum.div hden hne
    refine (hxi_right_cont.sub hh_right_cont).congr ?_
    intro y hy
    symm
    exact (sub_eq_iff_eq_add).2 (by
      simpa [add_comm, add_left_comm, add_assoc] using h_decomp_right y hy)
  have hg_left_cont : ContinuousOn
      (fun y : ℝ => logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)))
      (Set.Icc (1 : ℝ) T) := by
    have hxi_left_cont : ContinuousOn
        (fun y : ℝ => logDeriv RiemannXiAlt (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)))
        (Set.Icc (1 : ℝ) T) := by
      have hnum : ContinuousOn
          (fun y : ℝ => deriv RiemannXiAlt (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)))
          (Set.Icc (1 : ℝ) T) :=
        (hxi_deriv_cont.comp (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
      have hden : ContinuousOn
          (fun y : ℝ => RiemannXiAlt (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)))
          (Set.Icc (1 : ℝ) T) :=
        (RiemannXiAlt_entire.continuous.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
      have hne : ∀ y ∈ Set.Icc (1 : ℝ) T,
          RiemannXiAlt (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)) ≠ 0 := by
        intro y hy
        exact xi_ne_zero_on_boundary T (by linarith) hT_not_ord _
          (by
            show ((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I) ∈ RectArgumentPrinciple.rectBoundary (-1) 2 1 T
            simpa using left_edge_mem_rectBoundary T hT1 hy)
      simpa [logDeriv_apply] using hnum.div hden hne
    refine (hxi_left_cont.sub hh_left_cont).congr ?_
    intro y hy
    symm
    exact (sub_eq_iff_eq_add).2 (by
      simpa [add_comm, add_left_comm, add_assoc] using h_decomp_left y hy)
  have hg_bot : IntervalIntegrable
      (fun x : ℝ => logDeriv completedRiemannZeta ((↑x : ℂ) + (1 : ℂ) * I))
      volume (-1) 2 :=
    hg_bot_cont.intervalIntegrable_of_Icc (by norm_num)
  have hg_top : IntervalIntegrable
      (fun x : ℝ => logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
      volume (-1) 2 :=
    hg_top_cont.intervalIntegrable_of_Icc (by norm_num)
  have hg_right : IntervalIntegrable
      (fun y : ℝ => logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
      volume 1 T :=
    hg_right_cont.intervalIntegrable_of_Icc hT1
  have hg_left : IntervalIntegrable
      (fun y : ℝ => logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)))
      volume 1 T :=
    hg_left_cont.intervalIntegrable_of_Icc hT1
  have hf_bot : IntervalIntegrable
      (fun x : ℝ => ((↑x : ℂ) + (1 : ℂ) * I)⁻¹) volume (-1) 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    apply ContinuousOn.inv₀
    · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
    · intro x _ hx0
      have him := congr_arg Complex.im hx0
      simp at him
  have hf_top : IntervalIntegrable
      (fun x : ℝ => ((↑x : ℂ) + (↑T : ℂ) * I)⁻¹) volume (-1) 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    apply ContinuousOn.inv₀
    · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
    · intro x _ hx0
      have him := congr_arg Complex.im hx0
      simp at him
      linarith
  have hf_right : IntervalIntegrable
      (fun y : ℝ => ((2 : ℂ) + (↑y : ℂ) * I)⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT1
    apply ContinuousOn.inv₀
    · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
    · intro y _ hy0
      have hre := congr_arg Complex.re hy0
      simp at hre
  have hf_left : IntervalIntegrable
      (fun y : ℝ => (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)⁻¹)) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT1
    apply ContinuousOn.inv₀
    · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
    · intro y _ hy0
      have hre := congr_arg Complex.re hy0
      simp at hre
  have hsub_bot_cont : ContinuousOn
      (fun x : ℝ => ((((↑x : ℂ) + (1 : ℂ) * I) - 1)⁻¹))
      (Set.Icc (-1 : ℝ) 2) := by
    apply ContinuousOn.inv₀
    · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub continuousOn_const
    · intro x _ hx1
      have him := congr_arg Complex.im hx1
      simp at him
  have hsub_top_cont : ContinuousOn
      (fun x : ℝ => ((((↑x : ℂ) + (↑T : ℂ) * I) - 1)⁻¹))
      (Set.Icc (-1 : ℝ) 2) := by
    apply ContinuousOn.inv₀
    · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub continuousOn_const
    · intro x _ hx1
      have him := congr_arg Complex.im hx1
      simp at him
      linarith
  have hsub_right_cont : ContinuousOn
      (fun y : ℝ => ((((2 : ℂ) + (↑y : ℂ) * I) - 1)⁻¹))
      (Set.Icc (1 : ℝ) T) := by
    apply ContinuousOn.inv₀
    · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub continuousOn_const
    · intro y _ hy1
      have hre := congr_arg Complex.re hy1
      norm_num at hre
  have hsub_left_cont : ContinuousOn
      (fun y : ℝ => (((((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I) - 1)⁻¹)))
      (Set.Icc (1 : ℝ) T) := by
    apply ContinuousOn.inv₀
    · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub continuousOn_const
    · intro y _ hy1
      have hre := congr_arg Complex.re hy1
      norm_num at hre
  have hsub_bot : IntervalIntegrable
      (fun x : ℝ => ((((↑x : ℂ) + (1 : ℂ) * I) - 1)⁻¹))
      volume (-1) 2 :=
    hsub_bot_cont.intervalIntegrable_of_Icc (by norm_num)
  have hsub_top : IntervalIntegrable
      (fun x : ℝ => ((((↑x : ℂ) + (↑T : ℂ) * I) - 1)⁻¹))
      volume (-1) 2 :=
    hsub_top_cont.intervalIntegrable_of_Icc (by norm_num)
  have hsub_right : IntervalIntegrable
      (fun y : ℝ => ((((2 : ℂ) + (↑y : ℂ) * I) - 1)⁻¹))
      volume 1 T :=
    hsub_right_cont.intervalIntegrable_of_Icc hT1
  have hsub_left : IntervalIntegrable
      (fun y : ℝ => (((((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I) - 1)⁻¹)))
      volume 1 T :=
    hsub_left_cont.intervalIntegrable_of_Icc hT1
  have hk_bot : IntervalIntegrable
      (fun x : ℝ => ((((↑x : ℂ) + (1 : ℂ) * I) - 1)⁻¹) +
        logDeriv completedRiemannZeta ((↑x : ℂ) + (1 : ℂ) * I))
      volume (-1) 2 :=
    (hsub_bot_cont.add hg_bot_cont).intervalIntegrable_of_Icc (by norm_num)
  have hk_top : IntervalIntegrable
      (fun x : ℝ => ((((↑x : ℂ) + (↑T : ℂ) * I) - 1)⁻¹) +
        logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
      volume (-1) 2 :=
    (hsub_top_cont.add hg_top_cont).intervalIntegrable_of_Icc (by norm_num)
  have hk_right : IntervalIntegrable
      (fun y : ℝ => ((((2 : ℂ) + (↑y : ℂ) * I) - 1)⁻¹) +
        logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
      volume 1 T :=
    (hsub_right_cont.add hg_right_cont).intervalIntegrable_of_Icc hT1
  have hk_left : IntervalIntegrable
      (fun y : ℝ => (((((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I) - 1)⁻¹)) +
        logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)))
      volume 1 T :=
    (hsub_left_cont.add hg_left_cont).intervalIntegrable_of_Icc hT1
  have h_congr := contourIntegralRect_congr_boundary
    (logDeriv RiemannXiAlt)
    (fun s : ℂ => (s⁻¹ + (s - 1)⁻¹) + logDeriv completedRiemannZeta s)
    (-1) 2 1 T (by norm_num) hT1 h_decomp_bot h_decomp_top h_decomp_right h_decomp_left
  have hcontour :
      contourIntegralRect (logDeriv RiemannXiAlt) (-1) 2 1 T =
        contourIntegralRect (logDeriv completedRiemannZeta) (-1) 2 1 T := by
    have h_assoc :
        contourIntegralRect
            (fun s : ℂ => s⁻¹ + (s - 1)⁻¹ + logDeriv completedRiemannZeta s)
            (-1) 2 1 T
          =
        contourIntegralRect
            (fun s : ℂ => s⁻¹ + ((s - 1)⁻¹ + logDeriv completedRiemannZeta s))
            (-1) 2 1 T := by
      apply contourIntegralRect_congr_boundary
        (fun s : ℂ => s⁻¹ + (s - 1)⁻¹ + logDeriv completedRiemannZeta s)
        (fun s : ℂ => s⁻¹ + ((s - 1)⁻¹ + logDeriv completedRiemannZeta s))
        (-1) 2 1 T (by norm_num) hT1
      · intro x hx
        ring
      · intro x hx
        ring
      · intro y hy
        ring
      · intro y hy
        ring
    have hstart :
        contourIntegralRect (logDeriv RiemannXiAlt) (-1) 2 1 T =
          contourIntegralRect
            (fun s : ℂ => s⁻¹ + ((s - 1)⁻¹ + logDeriv completedRiemannZeta s))
            (-1) 2 1 T := by
      calc
        contourIntegralRect (logDeriv RiemannXiAlt) (-1) 2 1 T
            = contourIntegralRect
                (fun s : ℂ => s⁻¹ + (s - 1)⁻¹ + logDeriv completedRiemannZeta s)
                (-1) 2 1 T := h_congr
        _ = contourIntegralRect
              (fun s : ℂ => s⁻¹ + ((s - 1)⁻¹ + logDeriv completedRiemannZeta s))
              (-1) 2 1 T := h_assoc
    have hsplit1 :
        contourIntegralRect
            (fun s : ℂ => s⁻¹ + ((s - 1)⁻¹ + logDeriv completedRiemannZeta s))
            (-1) 2 1 T
          =
        contourIntegralRect (fun s : ℂ => s⁻¹) (-1) 2 1 T +
          contourIntegralRect
            (fun s : ℂ => ((s - 1)⁻¹) + logDeriv completedRiemannZeta s)
            (-1) 2 1 T := by
      exact contourIntegralRect_add
        (fun s : ℂ => s⁻¹)
        (fun s : ℂ => ((s - 1)⁻¹) + logDeriv completedRiemannZeta s)
        (-1) 2 1 T hf_bot hk_bot hf_top hk_top hf_right hk_right hf_left hk_left
    have hsplit2 :
        contourIntegralRect
            (fun s : ℂ => ((s - 1)⁻¹) + logDeriv completedRiemannZeta s)
            (-1) 2 1 T
          =
        contourIntegralRect (fun s : ℂ => (s - 1)⁻¹) (-1) 2 1 T +
          contourIntegralRect (logDeriv completedRiemannZeta) (-1) 2 1 T := by
      simpa using contourIntegralRect_add
        (fun s : ℂ => (s - 1)⁻¹) (logDeriv completedRiemannZeta)
        (-1) 2 1 T hsub_bot hg_bot hsub_top hg_top hsub_right hg_right hsub_left hg_left
    have hsplit2' :
        contourIntegralRect (fun s : ℂ => s⁻¹) (-1) 2 1 T +
            contourIntegralRect
              (fun s : ℂ => ((s - 1)⁻¹) + logDeriv completedRiemannZeta s)
              (-1) 2 1 T
          =
        contourIntegralRect (fun s : ℂ => s⁻¹) (-1) 2 1 T +
            (contourIntegralRect (fun s : ℂ => (s - 1)⁻¹) (-1) 2 1 T +
              contourIntegralRect (logDeriv completedRiemannZeta) (-1) 2 1 T) :=
      congrArg
        (fun z : ℂ => contourIntegralRect (fun s : ℂ => s⁻¹) (-1) 2 1 T + z)
        hsplit2
    calc
      contourIntegralRect (logDeriv RiemannXiAlt) (-1) 2 1 T
          = contourIntegralRect
              (fun s : ℂ => s⁻¹ + (((s - 1)⁻¹) + logDeriv completedRiemannZeta s))
              (-1) 2 1 T := hstart
      contourIntegralRect
          (fun s : ℂ => s⁻¹ + (((s - 1)⁻¹) + logDeriv completedRiemannZeta s))
          (-1) 2 1 T
          = contourIntegralRect (fun s : ℂ => s⁻¹) (-1) 2 1 T +
              contourIntegralRect
                (fun s : ℂ => ((s - 1)⁻¹) + logDeriv completedRiemannZeta s)
                (-1) 2 1 T := hsplit1
      _ = contourIntegralRect (fun s : ℂ => s⁻¹) (-1) 2 1 T +
            (contourIntegralRect (fun s : ℂ => (s - 1)⁻¹) (-1) 2 1 T +
              contourIntegralRect (logDeriv completedRiemannZeta) (-1) 2 1 T) := hsplit2'
      _ = contourIntegralRect (logDeriv completedRiemannZeta) (-1) 2 1 T := by
            rw [RvMContour.cauchy_goursat_inv_s T hT1, RvMContour.cauchy_goursat_inv_s_sub_one T hT1]
            ring
  simpa [logIntegralRect_eq_normalized_contour] using
    congrArg (fun z : ℂ => (1 / (2 * ↑Real.pi * I)) * z) hcontour

/-! ### Sub-lemma: Contour evaluation

The contour integral of logDeriv(xi) on the rectangle (-1,2)×(1,T)
decomposes into Stirling + arg(zeta) + constant + O(log T) terms.

**Proof strategy (decomposition into 4 edges):**

The `logIntegralRect` is `(1/(2πi)) * contourIntegralRect (logDeriv ξ)`.
By the argument principle (proved in this file),
  `logIntegralRect RiemannXiAlt = ↑(N T)`.
So `(logIntegralRect).re = N(T)` and the contour evaluation bound is equivalent
to the Riemann-von Mangoldt formula itself:
  `|N(T) - (Stirling + arg(ζ) + 1)| ≤ C · log T`.

We prove this by direct analytic arguments:
1. **Right vertical (σ=2):** `logDeriv(ξ)(2+it)` decomposes via the product
   `ξ(s) = (1/2)s(s-1)π^{-s/2}Γ(s/2)ζ(s)`. For σ=2, ζ has absolutely
   convergent Euler product, so |logDeriv(ζ)| ≤ C. The Gamma contribution
   gives (1/2)ψ(1+it/2) ~ (1/2)log(t/2) by Stirling.
   Integral: (i/2)∫₁ᵀ log(t/2) dt + O(T) = (i/2)(T log(T/2) - T + 1) + O(T).

2. **Left vertical (σ=-1):** By functional equation ξ(s)=ξ(1-s),
   logDeriv(ξ)(-1+it) = -logDeriv(ξ)(2-it). This mirrors the right edge.

3. **Top horizontal (t=T):** |logDeriv(ξ)(σ+iT)| ≤ C·logT for σ∈[-1,2].
   Length 3, so integral is O(logT).

4. **Bottom horizontal (t=1):** |logDeriv(ξ)(σ+i)| ≤ C on a compact set
   away from zeros. Integral is O(1).

Combining: the vertical edges give the Stirling main term and arg(ζ) term;
the horizontal edges contribute O(logT). -/

/-- The normalized bottom-edge contribution for `logIntegralRect completedRiemannZeta`
    on the canonical RvM rectangle. This is independent of `T`. -/
private def completedZetaBottomContribution : ℂ :=
  (1 / (2 * ↑Real.pi * I)) *
    (∫ x in (-1 : ℝ)..2,
      logDeriv completedRiemannZeta ((↑x : ℂ) + (↑(1 : ℝ) : ℂ) * I))

/-- The normalized contribution of the top, right, and left edges for
    `logIntegralRect completedRiemannZeta` on the canonical RvM rectangle. -/
private def completedZetaUpperThreeContribution (T : ℝ) : ℂ :=
  (1 / (2 * ↑Real.pi * I)) *
    (-(∫ x in (-1 : ℝ)..2,
        logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) +
      I * (∫ y in (1 : ℝ)..T,
        logDeriv completedRiemannZeta ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) -
      I * (∫ y in (1 : ℝ)..T,
        logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)))
    )

/-- The normalized top-edge contribution for `logIntegralRect completedRiemannZeta`
    on the canonical RvM rectangle. -/
private def completedZetaTopContribution (T : ℝ) : ℂ :=
  (1 / (2 * ↑Real.pi * I)) *
    (-(∫ x in (-1 : ℝ)..2,
        logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)))

/-- The normalized right-plus-left vertical contribution for
    `logIntegralRect completedRiemannZeta` on the canonical RvM rectangle. -/
private def completedZetaSideContribution (T : ℝ) : ℂ :=
  (1 / (2 * ↑Real.pi * I)) *
    (I * (∫ y in (1 : ℝ)..T,
        logDeriv completedRiemannZeta ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) -
      I * (∫ y in (1 : ℝ)..T,
        logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I))))

/-- Split the upper-three-edge contribution into the top edge and the two
    vertical sides. -/
private theorem completedZetaUpperThreeContribution_eq_top_add_side (T : ℝ) :
    completedZetaUpperThreeContribution T =
      completedZetaTopContribution T + completedZetaSideContribution T := by
  unfold completedZetaUpperThreeContribution completedZetaTopContribution
    completedZetaSideContribution
  ring_nf

/-- `completedRiemannZeta` does not vanish on the right edge `Re(s)=2`. -/
private theorem completedZeta_ne_zero_right_edge (y : ℝ) :
    completedRiemannZeta ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0 := by
  intro h
  have hpos : 0 < (((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re := by norm_num
  have hzeta :
      riemannZeta ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) = 0 :=
    (completedRiemannZeta_eq_zero_iff_riemannZeta hpos).1 h
  exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) hzeta

/-- `completedRiemannZeta` does not vanish on the left edge `Re(s)=-1`
    at positive heights, by the functional equation and the zero-free right edge. -/
private theorem completedZeta_ne_zero_left_edge (y : ℝ) :
    completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)) ≠ 0 := by
  have hfe :
      completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)) =
        completedRiemannZeta ((↑(2 : ℝ) : ℂ) - (↑y : ℂ) * I) := by
    calc
      completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I))
          = completedRiemannZeta ((1 : ℂ) - ((↑(2 : ℝ) : ℂ) - (↑y : ℂ) * I)) := by
              congr 1
              apply Complex.ext <;> simp <;> norm_num
      _ = completedRiemannZeta ((↑(2 : ℝ) : ℂ) - (↑y : ℂ) * I) :=
            completedRiemannZeta_one_sub _
  rw [hfe]
  simpa [sub_eq_add_neg] using completedZeta_ne_zero_right_edge (-y)

/-- Functional equation for the logarithmic derivative of
    `completedRiemannZeta` away from the poles at `0` and `1`. -/
private theorem completedZeta_logDeriv_functional_eq {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (_hz : completedRiemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
  simp only [logDeriv_apply]
  have h_eq : ∀ᶠ z in nhds s, completedRiemannZeta (1 - z) = completedRiemannZeta z :=
    Filter.Eventually.of_forall (fun z => completedRiemannZeta_one_sub z)
  have hs10 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs11 : 1 - s ≠ 1 := sub_eq_self.not.mpr hs0
  have hd : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta hs10 hs11
  have hcomp :
      deriv (fun z => completedRiemannZeta (1 - z)) s =
        -deriv completedRiemannZeta (1 - s) := by
    have := hd.hasDerivAt.comp s ((hasDerivAt_const s 1).sub (hasDerivAt_id s))
    simpa [Function.comp_apply] using this.deriv
  have hderiv_eq :
      deriv (fun z => completedRiemannZeta (1 - z)) s = deriv completedRiemannZeta s :=
    Filter.EventuallyEq.deriv_eq h_eq
  rw [completedRiemannZeta_one_sub, ← hderiv_eq, hcomp]
  ring

/-- Schwarz reflection for the logarithmic derivative of
    `completedRiemannZeta` away from `0` and `1`. -/
private theorem completedZeta_logDeriv_conj {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (_hz : completedRiemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta (conj s) = conj (logDeriv completedRiemannZeta s) := by
  simp only [logDeriv_apply]
  have h_eq :
      ∀ᶠ z in nhds (conj s), (conj ∘ completedRiemannZeta ∘ conj) z = completedRiemannZeta z :=
    Filter.Eventually.of_forall (fun z => by
      simpa [Function.comp_apply] using
        (HardyZConjugation.completedRiemannZeta_conj (conj z)).symm)
  have hd : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs0 hs1
  have hcomp :
      deriv (conj ∘ completedRiemannZeta ∘ conj) (conj s) =
        conj (deriv completedRiemannZeta s) := by
    simpa [Function.comp_apply] using (hd.hasDerivAt.conj_conj).deriv
  have hderiv_eq :
      deriv (conj ∘ completedRiemannZeta ∘ conj) (conj s) =
        deriv completedRiemannZeta (conj s) :=
    Filter.EventuallyEq.deriv_eq h_eq
  rw [← hderiv_eq, hcomp, HardyZConjugation.completedRiemannZeta_conj]
  simp

/-- The left-edge logarithmic derivative is the reflected negative conjugate
    of the right-edge logarithmic derivative. -/
private theorem completedZeta_logDeriv_left_right_edge (y : ℝ) :
    logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)) =
      -conj (logDeriv completedRiemannZeta ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) := by
  let z : ℂ := ((↑(2 : ℝ) : ℂ) - (↑y : ℂ) * I)
  have hz0 : z ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [z] at hre
  have hz1 : z ≠ 1 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [z] at hre
  have hznz : completedRiemannZeta z ≠ 0 := by
    simpa [z, sub_eq_add_neg] using completedZeta_ne_zero_right_edge (-y)
  have hright0 : ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num at hre
  have hright1 : ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 1 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num at hre
  have hone_sub_z : (1 : ℂ) - z = (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)) := by
    apply Complex.ext <;> simp [z] <;> norm_num
  calc
    logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I))
        = logDeriv completedRiemannZeta (1 - z) := by
            rw [hone_sub_z]
    _ = -logDeriv completedRiemannZeta z :=
          completedZeta_logDeriv_functional_eq hz0 hz1 hznz
    _ = -conj (logDeriv completedRiemannZeta ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) := by
          have hzconj :
              z = conj ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) := by
            apply Complex.ext <;> simp [z]
          rw [hzconj]
          exact congrArg Neg.neg
            (completedZeta_logDeriv_conj hright0 hright1 (completedZeta_ne_zero_right_edge y))

/-- Split the normalized completed-zeta contour integral into the fixed bottom
    edge and the remaining top/right/left contribution. -/
private theorem logIntegralRect_completedZeta_eq_bottom_plus_upperThree (T : ℝ) :
    logIntegralRect completedRiemannZeta (-1) 2 1 T =
      completedZetaBottomContribution + completedZetaUpperThreeContribution T := by
  unfold logIntegralRect completedZetaBottomContribution completedZetaUpperThreeContribution
  ring_nf

/-- The bottom edge is a fixed compact contribution, hence it is automatically
    `O(log T)` on `T ≥ 14`. -/
private theorem completedZeta_bottomContribution_bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |completedZetaBottomContribution.re| ≤ C * Real.log T := by
  have hlog14_pos : 0 < Real.log 14 := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < 14)
  refine ⟨|completedZetaBottomContribution.re| / Real.log 14, ?_⟩
  intro T hT
  have hlog_mono : Real.log 14 ≤ Real.log T := by
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 14) hT
  have hcoeff_nonneg : 0 ≤ |completedZetaBottomContribution.re| / Real.log 14 := by
    positivity
  calc
    |completedZetaBottomContribution.re|
        = (|completedZetaBottomContribution.re| / Real.log 14) * Real.log 14 := by
            field_simp [ne_of_gt hlog14_pos]
    _ ≤ (|completedZetaBottomContribution.re| / Real.log 14) * Real.log T := by
          gcongr

/-- Continuity of `logDeriv completedRiemannZeta` on the right edge follows from
    the already-proved xi decomposition plus nonvanishing on the boundary. -/
private theorem completedZeta_right_continuousOn [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    ContinuousOn
      (fun y : ℝ => logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
      (Set.Icc (1 : ℝ) T) := by
  have hT1 : 1 ≤ T := by linarith
  have hbdy := completedZeta_ne_zero_on_boundary T hT hT_not_ord
  have h_decomp_right : ∀ y ∈ Set.Icc (1 : ℝ) T,
      logDeriv RiemannXiAlt ((2 : ℂ) + (↑y : ℂ) * I) =
        ((((2 : ℂ) + (↑y : ℂ) * I)⁻¹ + ((((2 : ℂ) + (↑y : ℂ) * I) - 1)⁻¹)) +
          logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)) := by
    intro y hy
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp
      linarith [hy.1]
    · exact hbdy _ (right_edge_mem_rectBoundary T hT1 hy)
  have hxi_deriv_cont : Continuous (deriv RiemannXiAlt) := by
    simpa using
      ((RiemannXiAlt_entire.contDiff : ContDiff ℂ ⊤ RiemannXiAlt).continuous_deriv (by simp))
  have hh_right_cont : ContinuousOn
      (fun y : ℝ => ((2 : ℂ) + (↑y : ℂ) * I)⁻¹ + ((((2 : ℂ) + (↑y : ℂ) * I) - 1)⁻¹))
      (Set.Icc (1 : ℝ) T) := by
    apply ContinuousOn.add
    · apply ContinuousOn.inv₀
      · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      · intro y _ hy0
        have hre := congr_arg Complex.re hy0
        simp at hre
    · apply ContinuousOn.inv₀
      · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub continuousOn_const
      · intro y _ hy1
        have hre := congr_arg Complex.re hy1
        norm_num at hre
  have hxi_right_cont : ContinuousOn
      (fun y : ℝ => logDeriv RiemannXiAlt ((2 : ℂ) + (↑y : ℂ) * I))
      (Set.Icc (1 : ℝ) T) := by
    have hnum : ContinuousOn
        (fun y : ℝ => deriv RiemannXiAlt ((2 : ℂ) + (↑y : ℂ) * I))
        (Set.Icc (1 : ℝ) T) :=
      (hxi_deriv_cont.comp (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
    have hden : ContinuousOn
        (fun y : ℝ => RiemannXiAlt ((2 : ℂ) + (↑y : ℂ) * I))
        (Set.Icc (1 : ℝ) T) :=
      (RiemannXiAlt_entire.continuous.comp
        (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
    have hne : ∀ y ∈ Set.Icc (1 : ℝ) T, RiemannXiAlt ((2 : ℂ) + (↑y : ℂ) * I) ≠ 0 := by
      intro y hy
      exact xi_ne_zero_on_boundary T (by linarith) hT_not_ord _
        (right_edge_mem_rectBoundary T hT1 hy)
    simpa [logDeriv_apply] using hnum.div hden hne
  refine (hxi_right_cont.sub hh_right_cont).congr ?_
  intro y hy
  symm
  exact (sub_eq_iff_eq_add).2 (by
    simpa [add_comm, add_left_comm, add_assoc] using h_decomp_right y hy)

/-- The right-edge logarithmic derivative is interval-integrable on the RvM contour. -/
private theorem completedZeta_right_intervalIntegrable [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    IntervalIntegrable
      (fun y : ℝ => logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
      volume 1 T := by
  have hT1 : 1 ≤ T := by linarith
  exact (completedZeta_right_continuousOn T hT hT_not_ord).intervalIntegrable_of_Icc hT1

/-- Continuity of `logDeriv completedRiemannZeta` on the top edge follows from
    the xi decomposition plus nonvanishing on the boundary. -/
private theorem completedZeta_top_continuousOn [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    ContinuousOn
      (fun x : ℝ => logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
      (Set.Icc (-1 : ℝ) 2) := by
  have hT1 : 1 ≤ T := by linarith
  have hbdy := completedZeta_ne_zero_on_boundary T hT hT_not_ord
  have h_decomp_top : ∀ x ∈ Set.Icc (-1 : ℝ) 2,
      logDeriv RiemannXiAlt ((↑x : ℂ) + (↑T : ℂ) * I) =
        ((((↑x : ℂ) + (↑T : ℂ) * I)⁻¹ + ((((↑x : ℂ) + (↑T : ℂ) * I) - 1)⁻¹)) +
          logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) := by
    intro x hx
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp
      linarith
    · exact hbdy _ (top_edge_mem_rectBoundary T hT1 hx)
  have hxi_deriv_cont : Continuous (deriv RiemannXiAlt) := by
    simpa using
      ((RiemannXiAlt_entire.contDiff : ContDiff ℂ ⊤ RiemannXiAlt).continuous_deriv (by simp))
  have hh_top_cont : ContinuousOn
      (fun x : ℝ => ((↑x : ℂ) + (↑T : ℂ) * I)⁻¹ + ((((↑x : ℂ) + (↑T : ℂ) * I) - 1)⁻¹))
      (Set.Icc (-1 : ℝ) 2) := by
    apply ContinuousOn.add
    · apply ContinuousOn.inv₀
      · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
      · intro x _ hx0
        have him := congr_arg Complex.im hx0
        simp at him
        linarith
    · apply ContinuousOn.inv₀
      · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub continuousOn_const
      · intro x _ hx1
        have him := congr_arg Complex.im hx1
        simp at him
        linarith
  have hxi_top_cont : ContinuousOn
      (fun x : ℝ => logDeriv RiemannXiAlt ((↑x : ℂ) + (↑T : ℂ) * I))
      (Set.Icc (-1 : ℝ) 2) := by
    have hnum : ContinuousOn
        (fun x : ℝ => deriv RiemannXiAlt ((↑x : ℂ) + (↑T : ℂ) * I))
        (Set.Icc (-1 : ℝ) 2) :=
      (hxi_deriv_cont.comp (continuous_ofReal.add (continuous_const.mul continuous_const))).continuousOn
    have hden : ContinuousOn
        (fun x : ℝ => RiemannXiAlt ((↑x : ℂ) + (↑T : ℂ) * I))
        (Set.Icc (-1 : ℝ) 2) :=
      (RiemannXiAlt_entire.continuous.comp
        (continuous_ofReal.add (continuous_const.mul continuous_const))).continuousOn
    have hne : ∀ x ∈ Set.Icc (-1 : ℝ) 2, RiemannXiAlt ((↑x : ℂ) + (↑T : ℂ) * I) ≠ 0 := by
      intro x hx
      exact xi_ne_zero_on_boundary T (by linarith) hT_not_ord _
        (top_edge_mem_rectBoundary T hT1 hx)
    simpa [logDeriv_apply] using hnum.div hden hne
  refine (hxi_top_cont.sub hh_top_cont).congr ?_
  intro x hx
  symm
  exact (sub_eq_iff_eq_add).2 (by
    simpa [add_comm, add_left_comm, add_assoc] using h_decomp_top x hx)

/-- The top-edge logarithmic derivative is interval-integrable on the RvM contour. -/
private theorem completedZeta_top_intervalIntegrable [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    IntervalIntegrable
      (fun x : ℝ => logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
      volume (-1) 2 := by
  exact (completedZeta_top_continuousOn T hT hT_not_ord).intervalIntegrable_of_Icc (by norm_num)

/-- The left edge is the reflected conjugate of the right edge, so the side
    contribution is purely real and determined by the right-edge integral. -/
private theorem completedZetaSideContribution_eq_rightEdgeReal [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    completedZetaSideContribution T =
      (((∫ y in (1 : ℝ)..T,
          logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re : ℂ) / ↑Real.pi) := by
  set A : ℂ := ∫ y in (1 : ℝ)..T,
      logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)
  have hright :
      IntervalIntegrable
        (fun y : ℝ => logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
        volume 1 T :=
    completedZeta_right_intervalIntegrable T hT hT_not_ord
  have hleft_eq :
      ∫ y in (1 : ℝ)..T, logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I))
        = -conj A := by
    calc
      ∫ y in (1 : ℝ)..T, logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I))
          = ∫ y in (1 : ℝ)..T,
              -conj (logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)) := by
                apply intervalIntegral.integral_congr_ae
                filter_upwards with y
                intro _hy
                simpa using completedZeta_logDeriv_left_right_edge y
      _ = -(∫ y in (1 : ℝ)..T,
            conj (logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I))) := by
              rw [intervalIntegral.integral_neg]
      _ = -conj (∫ y in (1 : ℝ)..T,
            logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)) := by
              congr 1
              simpa using
                Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hright
      _ = -conj A := by rw [show A = ∫ y in (1 : ℝ)..T,
            logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I) from rfl]
  unfold completedZetaSideContribution
  rw [show (∫ y in (1 : ℝ)..T, logDeriv completedRiemannZeta ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) = A by
        simp [A],
      hleft_eq]
  calc
    (1 / (2 * ↑Real.pi * I)) * (I * A - I * (-conj A))
        = (1 / (2 * ↑Real.pi * I)) * (I * (A + conj A)) := by ring
    _ = (A + conj A) / (2 * ↑Real.pi) := by
          have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
          field_simp [hpi, Complex.I_ne_zero]
    _ = (A.re : ℂ) / ↑Real.pi := by
          rw [Complex.add_conj]
          norm_num
          have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
          field_simp [hpi]

/-- Real-part form of the side contribution. -/
private theorem completedZetaSideContribution_re_eq_rightEdgeReal [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    (completedZetaSideContribution T).re =
      (1 / Real.pi) *
        (∫ y in (1 : ℝ)..T,
          logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re := by
  rw [completedZetaSideContribution_eq_rightEdgeReal T hT hT_not_ord]
  simp [div_eq_mul_inv, mul_comm]

/-- The explicit Gamma-factor part of the right-edge contribution. -/
private def completedZetaRightGammaContribution (T : ℝ) : ℝ :=
  (1 / Real.pi) *
    (∫ y in (1 : ℝ)..T,
      ((-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
        (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2))).re

/-- The ζ-log-derivative part of the right-edge contribution. -/
private def completedZetaRightZetaContribution (T : ℝ) : ℝ :=
  (1 / Real.pi) *
    (∫ y in (1 : ℝ)..T,
      logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re

private lemma differentiableOn_gamma_re_pos :
    DifferentiableOn ℂ Complex.Gamma {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (differentiableAt_Gamma s (fun m => by
    intro h
    rw [h] at hs
    simp at hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  )).differentiableWithinAt

private lemma isOpen_re_pos : IsOpen {s : ℂ | 0 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma analyticOn_gamma_re_pos :
    AnalyticOnNhd ℂ Complex.Gamma {s : ℂ | 0 < s.re} :=
  differentiableOn_gamma_re_pos.analyticOnNhd isOpen_re_pos

private lemma continuousAt_deriv_gamma_re_pos (s : ℂ) (hs : 0 < s.re) :
    ContinuousAt (deriv Complex.Gamma) s :=
  ((analyticOn_gamma_re_pos s hs).deriv).continuousAt

private lemma analyticOn_riemannZeta_ne_one :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_ne
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

private lemma continuousAt_deriv_riemannZeta_ne_one (s : ℂ) (hs : s ≠ 1) :
    ContinuousAt (deriv riemannZeta) s :=
  ((analyticOn_riemannZeta_ne_one s hs).deriv).continuousAt

private theorem rightEdge_gamma_logDeriv_continuousOn (T : ℝ) (_hT : 1 ≤ T) :
    ContinuousOn
      (fun y : ℝ => logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2))
      (Set.Icc (1 : ℝ) T) := by
  let φ : ℝ → ℂ := fun y => ((2 : ℂ) + (↑y : ℂ) * I) / 2
  have hφ : ContinuousOn φ (Set.Icc (1 : ℝ) T) := by
    simpa [φ] using
      ((continuous_const.add (continuous_ofReal.mul continuous_const)).div_const 2).continuousOn
  have hφ_maps : Set.MapsTo φ (Set.Icc (1 : ℝ) T) {s : ℂ | 0 < s.re} := by
    intro y hy
    simp [φ]
  have hnum0 : ContinuousOn (deriv Complex.Gamma) {s : ℂ | 0 < s.re} := by
    intro s hs
    exact (continuousAt_deriv_gamma_re_pos s hs).continuousWithinAt
  have hden0 : ContinuousOn Complex.Gamma {s : ℂ | 0 < s.re} := by
    intro s hs
    exact (Complex.differentiableAt_Gamma s (fun m => by
      intro h
      rw [h] at hs
      simp at hs
      linarith [Nat.cast_nonneg (α := ℝ) m]
    )).continuousAt.continuousWithinAt
  have hnum : ContinuousOn (fun y : ℝ => deriv Complex.Gamma (φ y)) (Set.Icc (1 : ℝ) T) :=
    hnum0.comp' hφ hφ_maps
  have hden : ContinuousOn (fun y : ℝ => Complex.Gamma (φ y)) (Set.Icc (1 : ℝ) T) :=
    hden0.comp' hφ hφ_maps
  have hne : ∀ y ∈ Set.Icc (1 : ℝ) T,
      Complex.Gamma (φ y) ≠ 0 := by
    intro y hy
    have hs : 0 < (φ y).re := by
      simp [φ]
    exact Complex.Gamma_ne_zero_of_re_pos hs
  simpa [logDeriv_apply, φ] using hnum.div hden hne

private theorem rightEdge_zeta_logDeriv_continuousOn (T : ℝ) (_hT : 1 ≤ T) :
    ContinuousOn
      (fun y : ℝ => logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
      (Set.Icc (1 : ℝ) T) := by
  let φ : ℝ → ℂ := fun y => (2 : ℂ) + (↑y : ℂ) * I
  have hφ : ContinuousOn φ (Set.Icc (1 : ℝ) T) := by
    simpa [φ] using
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
  have hφ_maps : Set.MapsTo φ (Set.Icc (1 : ℝ) T) {s : ℂ | s ≠ 1} := by
    intro y hy h
    have hre := congrArg Complex.re h
    norm_num [φ] at hre
  have hnum0 : ContinuousOn (deriv riemannZeta) {s : ℂ | s ≠ 1} := by
    intro s hs
    exact (continuousAt_deriv_riemannZeta_ne_one s hs).continuousWithinAt
  have hden0 : ContinuousOn riemannZeta {s : ℂ | s ≠ 1} := by
    intro s hs
    exact (differentiableAt_riemannZeta hs).continuousAt.continuousWithinAt
  have hnum : ContinuousOn (fun y : ℝ => deriv riemannZeta (φ y)) (Set.Icc (1 : ℝ) T) :=
    hnum0.comp' hφ hφ_maps
  have hden : ContinuousOn (fun y : ℝ => riemannZeta (φ y)) (Set.Icc (1 : ℝ) T) :=
    hden0.comp' hφ hφ_maps
  have hne : ∀ y ∈ Set.Icc (1 : ℝ) T,
      riemannZeta (φ y) ≠ 0 := by
    intro y hy
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num [φ])
  simpa [logDeriv_apply, φ] using hnum.div hden hne

private theorem rightEdge_zetaIlogDeriv_continuousOn (T : ℝ) (hT : 1 ≤ T) :
    ContinuousOn
      (fun y : ℝ => I * logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
      (Set.uIcc (1 : ℝ) T) := by
  rw [Set.uIcc_of_le hT]
  exact continuousOn_const.mul (rightEdge_zeta_logDeriv_continuousOn T hT)

private theorem rightEdge_zeta_diffAt (y : ℝ) :
    DifferentiableAt ℂ riemannZeta ((2 : ℂ) + (↑y : ℂ) * I) := by
  apply differentiableAt_riemannZeta
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

private theorem rightEdge_zeta_in_slitPlane (y : ℝ) :
    riemannZeta ((2 : ℂ) + (↑y : ℂ) * I) ∈ slitPlane := by
  apply RvMFormula.zeta_in_slitPlane
  norm_num

private theorem completedZetaRightContribution_eq_gamma_plus_zeta (T : ℝ) (hT : 14 ≤ T) :
    (1 / Real.pi) *
      (∫ y in (1 : ℝ)..T,
        (logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re) =
      completedZetaRightGammaContribution T + completedZetaRightZetaContribution T := by
  have hT1 : 1 ≤ T := by linarith
  have hgamma_int : IntervalIntegrable
      (fun y : ℝ =>
        (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
          (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2))
      volume 1 T :=
    (continuousOn_const.add
      (continuousOn_const.mul (rightEdge_gamma_logDeriv_continuousOn T hT1))).intervalIntegrable_of_Icc hT1
  have hzeta_int : IntervalIntegrable
      (fun y : ℝ => logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
      volume 1 T :=
    (rightEdge_zeta_logDeriv_continuousOn T hT1).intervalIntegrable_of_Icc hT1
  have hpoint :
      ∀ y : ℝ,
        logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I) =
          (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
            (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2) +
            logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I) := by
    intro y
    simpa [add_assoc, add_comm, add_left_comm] using
      RvMRightEdge.logDeriv_completedZeta_full ((2 : ℂ) + (↑y : ℂ) * I) (by norm_num)
  have hsum_int :
      IntervalIntegrable
        (fun y : ℝ =>
          (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
            (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2) +
            logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
        volume 1 T :=
    hgamma_int.add hzeta_int
  have hcompleted_int :
      IntervalIntegrable
        (fun y : ℝ => logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I))
        volume 1 T := by
    refine hsum_int.congr_ae ?_
    refine (ae_restrict_mem measurableSet_uIoc).mono ?_
    intro y hy
    exact (hpoint y).symm
  have hcompleted_re :
      ∫ y in (1 : ℝ)..T,
          (logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re =
        (∫ y in (1 : ℝ)..T,
          logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hcompleted_int
    simp only [Complex.reCLM_apply] at this
    exact this
  have hgamma_re :
      ∫ y in (1 : ℝ)..T,
          (((-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
              (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2))).re =
        (∫ y in (1 : ℝ)..T,
          (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
            (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hgamma_int
    simp only [Complex.reCLM_apply] at this
    exact this
  have hzeta_re :
      ∫ y in (1 : ℝ)..T,
          (logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re =
        (∫ y in (1 : ℝ)..T,
          logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hzeta_int
    simp only [Complex.reCLM_apply] at this
    exact this
  unfold completedZetaRightGammaContribution completedZetaRightZetaContribution
  have hsplit :
      ∫ y in (1 : ℝ)..T, logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I) =
        ∫ y in (1 : ℝ)..T,
          (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
            (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2) +
            logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with y hy
    exact hpoint y
  have hsum :
      ∫ y in (1 : ℝ)..T,
          (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
            (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2) +
            logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)
        =
        (∫ y in (1 : ℝ)..T,
          (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
            (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2)) +
          (∫ y in (1 : ℝ)..T,
            logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)) := by
    rw [intervalIntegral.integral_add hgamma_int hzeta_int]
  calc
    (1 / Real.pi) *
        (∫ y in (1 : ℝ)..T,
          (logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re)
        = (1 / Real.pi) *
            (∫ y in (1 : ℝ)..T,
              logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re := by
            rw [hcompleted_re]
    _ = (1 / Real.pi) *
          ((∫ y in (1 : ℝ)..T,
              (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
                (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2)) +
            (∫ y in (1 : ℝ)..T,
              logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I))).re := by
          rw [hsplit, hsum]
    _ = (1 / Real.pi) *
          ((∫ y in (1 : ℝ)..T,
              (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
                (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2)).re +
            (∫ y in (1 : ℝ)..T,
              logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re) := by
          rw [Complex.add_re]
    _ = (1 / Real.pi) *
          (∫ y in (1 : ℝ)..T,
            ((-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
              (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2))).re +
        (1 / Real.pi) *
          (∫ y in (1 : ℝ)..T,
            (logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re) := by
          rw [← hgamma_re, ← hzeta_re]
          ring
    _ = completedZetaRightGammaContribution T + completedZetaRightZetaContribution T := by
          rw [completedZetaRightGammaContribution, completedZetaRightZetaContribution, hzeta_re]

private theorem completedZetaRightZetaContribution_bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |completedZetaRightZetaContribution T| ≤ C * Real.log T := by
  obtain ⟨B, hB⟩ := Aristotle.ZetaAnalyticProperties.log_zeta_bounded_on_line_two
  have hB_nonneg : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  refine ⟨(2 * B) / Real.pi, ?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by linarith
  have hbound :
      ‖∫ y in (1 : ℝ)..T, I * logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)‖ ≤ 2 * B := by
    have hBT : ‖Complex.log (riemannZeta ((2 : ℂ) + (↑T : ℂ) * I))‖ ≤ B := by
      simpa using hB T
    have hB1 : ‖Complex.log (riemannZeta ((2 : ℂ) + (↑(1 : ℝ) : ℂ) * I))‖ ≤ B := by
      simpa using hB (1 : ℝ)
    calc
      ‖∫ y in (1 : ℝ)..T, I * logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)‖
          ≤ ‖Complex.log (riemannZeta ((2 : ℂ) + (↑T : ℂ) * I))‖ +
              ‖Complex.log (riemannZeta ((2 : ℂ) + (↑(1 : ℝ) : ℂ) * I))‖ := by
                exact RvMFTC.vertical_logDeriv_integral_bound riemannZeta 2 1 T
                  (fun y _ => rightEdge_zeta_diffAt y)
                  (fun y _ => rightEdge_zeta_in_slitPlane y)
                  (rightEdge_zetaIlogDeriv_continuousOn T hT1)
      _ ≤ B + B := by
            linarith
      _ = 2 * B := by ring
  have hreal :
      |(∫ y in (1 : ℝ)..T,
          logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re| ≤ 2 * B := by
    calc
      |(∫ y in (1 : ℝ)..T,
          logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re|
          = |(I * ∫ y in (1 : ℝ)..T,
                logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).im| := by
                  simp
      _ ≤ ‖I * ∫ y in (1 : ℝ)..T,
            logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)‖ := Complex.abs_im_le_norm _
      _ = ‖∫ y in (1 : ℝ)..T,
            I * logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)‖ := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ 2 * B := hbound
  have hExp : Real.exp 1 ≤ T := by
    have hExp14 : Real.exp 1 ≤ 14 := by
      linarith [Real.exp_one_lt_d9]
    linarith
  have hlog_ge_one : 1 ≤ Real.log T := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1) hExp
  unfold completedZetaRightZetaContribution
  have hcoeff_nonneg : 0 ≤ (2 * B) / Real.pi := by
    apply div_nonneg
    · nlinarith
    · exact le_of_lt Real.pi_pos
  calc
    |(1 / Real.pi) *
        (∫ y in (1 : ℝ)..T,
          logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re|
        = (1 / Real.pi) *
            |(∫ y in (1 : ℝ)..T,
                logDeriv riemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re| := by
              rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.pi)]
    _ ≤ (1 / Real.pi) * (2 * B) := by
          gcongr
    _ = (2 * B) / Real.pi := by
          field_simp [Real.pi_ne_zero]
    _ = ((2 * B) / Real.pi) * 1 := by ring
    _ ≤ ((2 * B) / Real.pi) * Real.log T := by
          gcongr

/-- Functional equation plus conjugation fold the full top edge onto the
    half-top segment `[1/2, 2]`. -/
private theorem completedZeta_logDeriv_top_reflection [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 2) :
    logDeriv completedRiemannZeta ((↑(1 - x) : ℂ) + (↑T : ℂ) * I) =
      -conj (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) := by
  have hT1 : 1 ≤ T := by linarith
  have htop_nz :
      completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I) ≠ 0 :=
    completedZeta_ne_zero_on_boundary T hT hT_not_ord _
      (top_edge_mem_rectBoundary T hT1 hx)
  let s : ℂ := ((↑x : ℂ) - (↑T : ℂ) * I)
  have hs0 : s ≠ 0 := by
    intro hs
    have him := congr_arg Complex.im hs
    simp [s] at him
    linarith
  have hs1 : s ≠ 1 := by
    intro hs
    have him := congr_arg Complex.im hs
    simp [s] at him
    linarith
  have hs_nz : completedRiemannZeta s ≠ 0 := by
    intro hs_zero
    have hconj := HardyZConjugation.completedRiemannZeta_conj s
    have hs_conj : conj s = ((↑x : ℂ) + (↑T : ℂ) * I) := by
      apply Complex.ext <;> simp [s]
    rw [hs_conj, hs_zero] at hconj
    simp at hconj
    exact htop_nz hconj
  have htop0 : ((↑x : ℂ) + (↑T : ℂ) * I) ≠ 0 := by
    intro hs
    have him := congr_arg Complex.im hs
    simp at him
    linarith
  have htop1 : ((↑x : ℂ) + (↑T : ℂ) * I) ≠ 1 := by
    intro hs
    have him := congr_arg Complex.im hs
    simp at him
    linarith
  have hs_conj : s = conj ((↑x : ℂ) + (↑T : ℂ) * I) := by
    apply Complex.ext <;> simp [s]
  calc
    logDeriv completedRiemannZeta ((↑(1 - x) : ℂ) + (↑T : ℂ) * I)
        = logDeriv completedRiemannZeta (1 - s) := by
            congr 1
            apply Complex.ext <;> simp [s]
    _ = -logDeriv completedRiemannZeta s :=
          completedZeta_logDeriv_functional_eq hs0 hs1 hs_nz
    _ = -conj (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) := by
          rw [hs_conj]
          exact congrArg Neg.neg
            (completedZeta_logDeriv_conj htop0 htop1 htop_nz)

/-- Real-part form of the top-edge contribution after folding the top edge to
    the half-top segment `[1/2, 2]`. -/
private theorem completedZetaTopContribution_re_eq_half_top_imIntegral
    [ZeroOrdinateLowerBoundHyp]
    (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    (completedZetaTopContribution T).re =
      -(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) := by
  let f : ℝ → ℂ := fun x =>
    logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)
  have hfull_cont : ContinuousOn f (Set.Icc (-1 : ℝ) 2) :=
    completedZeta_top_continuousOn T hT hT_not_ord
  have hleft_cont : ContinuousOn f (Set.Icc (-1 : ℝ) (1 / 2 : ℝ)) := by
    refine hfull_cont.mono ?_
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hright_cont : ContinuousOn f (Set.Icc (1 / 2 : ℝ) 2) := by
    refine hfull_cont.mono ?_
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hleft_int : IntervalIntegrable f volume (-1) (1 / 2 : ℝ) :=
    hleft_cont.intervalIntegrable_of_Icc (by norm_num)
  have hright_int : IntervalIntegrable f volume (1 / 2 : ℝ) 2 :=
    hright_cont.intervalIntegrable_of_Icc (by norm_num)
  have hleft_eq :
      ∫ x in (-1 : ℝ)..(1 / 2 : ℝ), f x =
        -conj (∫ x in (1 / 2 : ℝ)..2, f x) := by
    have hcomp :
        ∫ x in (1 / 2 : ℝ)..2, f (1 - x) =
          ∫ x in (-1 : ℝ)..(1 / 2 : ℝ), f x := by
      have hcomp_raw :
          ∫ x in (1 / 2 : ℝ)..2, f (1 - x) =
            ∫ x in (1 - (2 : ℝ))..(1 - (1 / 2 : ℝ)), f x := by
        exact
          intervalIntegral.integral_comp_sub_left (f := f)
            (a := (1 / 2 : ℝ)) (b := (2 : ℝ)) (d := (1 : ℝ))
      have hrewrite :
          ∫ x in (1 - (2 : ℝ))..(1 - (1 / 2 : ℝ)), f x =
            ∫ x in (-1 : ℝ)..(1 / 2 : ℝ), f x := by
        norm_num
      exact hcomp_raw.trans hrewrite
    calc
      ∫ x in (-1 : ℝ)..(1 / 2 : ℝ), f x
          = ∫ x in (1 / 2 : ℝ)..2, f (1 - x) := by simpa using hcomp.symm
      _ = ∫ x in (1 / 2 : ℝ)..2, -conj (f x) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with x hx
            have hx' : x ∈ Set.Icc (1 / 2 : ℝ) 2 := by
              have hx'' : x ∈ Set.uIcc (1 / 2 : ℝ) 2 := Set.uIoc_subset_uIcc hx
              rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx''
              exact hx''
            have hx2 : x ∈ Set.Icc (-1 : ℝ) 2 := by
              constructor
              · linarith [hx'.1]
              · exact hx'.2
            simpa [f] using completedZeta_logDeriv_top_reflection T hT hT_not_ord hx2
      _ = -(∫ x in (1 / 2 : ℝ)..2, conj (f x)) := by
            rw [intervalIntegral.integral_neg]
      _ = -conj (∫ x in (1 / 2 : ℝ)..2, f x) := by
            congr 1
            simpa using
              Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hright_int
  set R : ℂ := ∫ x in (1 / 2 : ℝ)..2, f x
  have hsplit :
      ∫ x in (-1 : ℝ)..2, f x = R - conj R := by
    calc
      ∫ x in (-1 : ℝ)..2, f x
          =
        (∫ x in (-1 : ℝ)..(1 / 2 : ℝ), f x) +
          (∫ x in (1 / 2 : ℝ)..2, f x) := by
            simpa using
              (intervalIntegral.integral_add_adjacent_intervals hleft_int hright_int).symm
      _ = -conj R + ∫ x in (1 / 2 : ℝ)..2, f x := by rw [hleft_eq]
      _ = -conj R + R := by simp [R]
      _ = R - conj R := by ring
  have hR_im :
      ∫ x in (1 / 2 : ℝ)..2, (f x).im = R.im := by
    simpa [R] using Complex.imCLM.intervalIntegral_comp_comm hright_int
  have hmain :
      (((1 / (2 * ↑Real.pi * I)) * (-(R - conj R))).re) = -(1 / Real.pi) * R.im := by
    have hcancel :
        (1 / (2 * ↑Real.pi * I : ℂ)) * (-(((2 * R.im : ℝ) : ℂ) * I)) =
          ((-(1 / Real.pi) * R.im : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [div_eq_mul_inv, Real.pi_ne_zero]
        ring
      · simp [div_eq_mul_inv, Real.pi_ne_zero]
    rw [Complex.sub_conj, hcancel]
    simp
  calc
    (completedZetaTopContribution T).re
        = (((1 / (2 * ↑Real.pi * I)) * (-(R - conj R))).re) := by
            unfold completedZetaTopContribution
            rw [hsplit]
    _ = -(1 / Real.pi) * R.im := hmain
    _ = -(1 / Real.pi) * (∫ x in (1 / 2 : ℝ)..2, (f x).im) := by
          rw [← hR_im]
    _ = -(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) := by
          simp [f]

/-- `Gammaℝ` is differentiable on the open right half-plane. -/
private lemma differentiableOn_GammaR_re_pos :
    DifferentiableOn ℂ Gammaℝ {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (RvMRightEdge.differentiableAt_GammaR s hs).differentiableWithinAt

/-- `Gammaℝ` is analytic on the open right half-plane. -/
private lemma analyticOn_GammaR_re_pos :
    AnalyticOnNhd ℂ Gammaℝ {s : ℂ | 0 < s.re} :=
  differentiableOn_GammaR_re_pos.analyticOnNhd isOpen_re_pos

/-- A branch-safe analytic logarithm of `Gammaℝ` on `Re > 0`. -/
private def gammaRLog : ℂ → ℂ :=
  Classical.choose <|
    Aristotle.Standalone.analytic_log_on_halfPlane' 0 Gammaℝ
      analyticOn_GammaR_re_pos
      (fun _ hs => Gammaℝ_ne_zero_of_re_pos hs)

private theorem gammaRLog_analytic :
    AnalyticOnNhd ℂ gammaRLog {s : ℂ | 0 < s.re} :=
  (Classical.choose_spec <|
    Aristotle.Standalone.analytic_log_on_halfPlane' 0 Gammaℝ
      analyticOn_GammaR_re_pos
      (fun _ hs => Gammaℝ_ne_zero_of_re_pos hs)).1

private theorem exp_gammaRLog_eq (s : ℂ) (hs : 0 < s.re) :
    Complex.exp (gammaRLog s) = Gammaℝ s :=
  (Classical.choose_spec <|
    Aristotle.Standalone.analytic_log_on_halfPlane' 0 Gammaℝ
      analyticOn_GammaR_re_pos
      (fun _ hs => Gammaℝ_ne_zero_of_re_pos hs)).2 s hs

private theorem differentiableAt_gammaRLog {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ gammaRLog s :=
  (gammaRLog_analytic s hs).differentiableAt

private theorem deriv_gammaRLog_eq (s : ℂ) (hs : 0 < s.re) :
    deriv gammaRLog s = logDeriv Gammaℝ s := by
  have hdiff : DifferentiableAt ℂ gammaRLog s := differentiableAt_gammaRLog hs
  have hcomp :
      HasDerivAt (fun z => Complex.exp (gammaRLog z))
        (Complex.exp (gammaRLog s) * deriv gammaRLog s) s := by
    simpa using (Complex.hasDerivAt_exp (gammaRLog s)).comp s hdiff.hasDerivAt
  have hEq :
      (fun z => Complex.exp (gammaRLog z)) =ᶠ[𝓝 s] Gammaℝ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    simpa using exp_gammaRLog_eq z hz
  have hGammaR :
      HasDerivAt Gammaℝ (deriv Gammaℝ s) s :=
    (RvMRightEdge.differentiableAt_GammaR s hs).hasDerivAt
  have hmul : Complex.exp (gammaRLog s) * deriv gammaRLog s = deriv Gammaℝ s := by
    exact (hcomp.congr_of_eventuallyEq hEq.symm).unique hGammaR
  have hGammaR_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  rw [logDeriv_apply, eq_div_iff hGammaR_ne]
  simpa [exp_gammaRLog_eq s hs, mul_comm] using hmul

private theorem hasDerivAt_gammaRLog (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt gammaRLog (logDeriv Gammaℝ s) s := by
  simpa [deriv_gammaRLog_eq s hs] using (differentiableAt_gammaRLog hs).hasDerivAt

private theorem hasDerivAt_rvm_vertical_path (σ : ℝ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => (↑σ : ℂ) + ↑t * I) I y := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (↑t : ℂ) * I) (1 * I) y := h1.mul_const I
  have h3 : HasDerivAt (fun _ : ℝ => (↑σ : ℂ)) 0 y := hasDerivAt_const y (↑σ : ℂ)
  convert h3.add h2 using 1
  simp

private theorem hasDerivAt_rvm_horizontal_path (t : ℝ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => (↑u : ℂ) + ↑t * I) 1 x := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun _ : ℝ => (↑t : ℂ) * I) 0 x := hasDerivAt_const x (↑t * I)
  convert h1.add h2 using 1
  simp

/-- On the vertical line `Re(s) = 1/2`, the real part of `logDeriv Gammaℝ`
    matches the smooth theta derivative. -/
private theorem re_logDeriv_GammaR_half_eq_thetaDeriv (t : ℝ) :
    (logDeriv Gammaℝ ((1 / 2 : ℂ) + (↑t : ℂ) * I)).re =
      ThetaDerivAsymptotic.thetaDeriv t := by
  have ht : 0 < (((1 / 2 : ℂ) + (↑t : ℂ) * I)).re := by
    norm_num
  rw [RvMRightEdge.logDeriv_GammaR_eq ((1 / 2 : ℂ) + (↑t : ℂ) * I) ht]
  have hhalf :
      (((1 / 2 : ℂ) + (↑t : ℂ) * I) / 2) = (1 / 4 : ℂ) + I * ((↑t : ℂ) / 2) := by
    ring
  rw [ThetaDerivAsymptotic.thetaDeriv, hhalf, logDeriv_apply]
  simp [Complex.add_re, Complex.mul_re, Complex.log_ofReal_re]
  ring

/-- The branch-safe `Gammaℝ` logarithm on `1/2 + it` is recovered by
    integrating `thetaDeriv`. -/
private theorem gammaRLog_halfLine_im_sub_eq_integral_thetaDeriv (T : ℝ) (hT : 1 ≤ T) :
    (gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im
      - (gammaRLog ((1 / 2 : ℂ) + (1 : ℂ) * I)).im =
      ∫ y in (1 : ℝ)..T, ThetaDerivAsymptotic.thetaDeriv y := by
  let g : ℂ → ℂ := gammaRLog
  let φ : ℝ → ℂ := fun y => (1 / 2 : ℂ) + (↑y : ℂ) * I
  have hline_cont : ContinuousOn
      (fun y : ℝ => logDeriv Gammaℝ (φ y))
      (Set.Icc (1 : ℝ) T) := by
    have hφ : ContinuousOn φ (Set.Icc (1 : ℝ) T) := by
      simpa [φ] using (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
    have hφ_maps : Set.MapsTo φ (Set.Icc (1 : ℝ) T) {s : ℂ | 0 < s.re} := by
      intro y hy
      simp [φ]
    have hnum0 : ContinuousOn (deriv Gammaℝ) {s : ℂ | 0 < s.re} := by
      intro s hs
      exact ((analyticOn_GammaR_re_pos s hs).deriv).continuousAt.continuousWithinAt
    have hden0 : ContinuousOn Gammaℝ {s : ℂ | 0 < s.re} := by
      intro s hs
      exact (RvMRightEdge.differentiableAt_GammaR s hs).continuousAt.continuousWithinAt
    have hnum : ContinuousOn (fun y : ℝ => deriv Gammaℝ (φ y)) (Set.Icc (1 : ℝ) T) :=
      hnum0.comp' hφ hφ_maps
    have hden : ContinuousOn (fun y : ℝ => Gammaℝ (φ y)) (Set.Icc (1 : ℝ) T) :=
      hden0.comp' hφ hφ_maps
    have hne : ∀ y ∈ Set.Icc (1 : ℝ) T, Gammaℝ (φ y) ≠ 0 := by
      intro y hy
      exact Gammaℝ_ne_zero_of_re_pos (by simp [φ])
    simpa [logDeriv_apply, φ] using hnum.div hden hne
  have hline :
      IntervalIntegrable
        (fun y : ℝ => logDeriv Gammaℝ (φ y))
        volume 1 T :=
    hline_cont.intervalIntegrable_of_Icc hT
  have hlineI :
      IntervalIntegrable
        (fun y : ℝ => I * logDeriv Gammaℝ (φ y))
        volume 1 T := by
    simpa [one_mul] using hline.const_mul I
  have hderiv :
      ∀ y ∈ Set.uIcc (1 : ℝ) T,
        HasDerivAt (fun t : ℝ => g (φ t)) (I * logDeriv Gammaℝ (φ y)) y := by
    intro y hy
    have hs : 0 < (φ y).re := by
      simp [φ]
    have hbase : HasDerivAt g (logDeriv Gammaℝ (φ y)) (φ y) := by
      simpa [g] using hasDerivAt_gammaRLog (φ y) hs
    have hφ : HasDerivAt φ I y := by
      simpa [φ] using hasDerivAt_rvm_vertical_path (1 / 2) y
    simpa [Function.comp, φ, mul_comm, mul_left_comm, mul_assoc] using hbase.comp y hφ
  have hFTC :
      ∫ y in (1 : ℝ)..T, I * logDeriv Gammaℝ (φ y) =
        g (φ T) - g (φ 1) := by
    simpa [φ] using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hlineI
  have hmap :
      ∫ y in (1 : ℝ)..T, (I * logDeriv Gammaℝ (φ y)).im
        =
      (∫ y in (1 : ℝ)..T, I * logDeriv Gammaℝ (φ y)).im := by
    simpa using Complex.imCLM.intervalIntegral_comp_comm hlineI
  have hFTC_im := congrArg Complex.im hFTC
  symm
  calc
    ∫ y in (1 : ℝ)..T, ThetaDerivAsymptotic.thetaDeriv y
        = ∫ y in (1 : ℝ)..T, (I * logDeriv Gammaℝ (φ y)).im := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with y hy
            simpa [φ, mul_comm] using (re_logDeriv_GammaR_half_eq_thetaDeriv y).symm
    _ = (∫ y in (1 : ℝ)..T, I * logDeriv Gammaℝ (φ y)).im := hmap
    _ = (g (φ T)).im - (g (φ 1)).im := by
            simpa [Complex.sub_im] using hFTC_im
    _ = (gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
          (gammaRLog ((1 / 2 : ℂ) + (1 : ℂ) * I)).im := by
            simp [g, φ]

/-- Exact integral of the main-term derivative `(1/2) log(t/(2π))` on `[1,T]`. -/
private theorem halfLog_main_term_integral_eq (T : ℝ) (hT : 14 ≤ T) :
    ∫ y in (1 : ℝ)..T, (1 / 2 : ℝ) * Real.log (y / (2 * Real.pi)) =
      (((T / 2) * Real.log (T / (2 * Real.pi)) - T / 2) -
        (((1 : ℝ) / 2) * Real.log (((1 : ℝ) / (2 * Real.pi))) - ((1 : ℝ) / 2))) := by
  have h1T : (1 : ℝ) ≤ T := by
    linarith
  have hcontLog :
      ContinuousOn (fun y : ℝ => Real.log (y / (2 * Real.pi))) (Set.uIcc 1 T) := by
    apply ContinuousOn.log
    · exact (continuous_id.div_const (2 * Real.pi)).continuousOn
    · intro y hy
      have hy_pos : 0 < y := by
        rw [Set.uIcc_of_le h1T] at hy
        linarith [hy.1]
      positivity
  have hint :
      IntervalIntegrable
        (fun y : ℝ => (1 / 2 : ℝ) * Real.log (y / (2 * Real.pi))) volume 1 T := by
    exact ((continuousOn_const.mul hcontLog)).intervalIntegrable
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => (y / 2) * Real.log (y / (2 * Real.pi)) - y / 2)
      (f' := fun y : ℝ => (1 / 2 : ℝ) * Real.log (y / (2 * Real.pi)))
      (fun y hy => by
        have hy_pos : 0 < y := by
          rw [Set.uIcc_of_le h1T] at hy
          linarith [hy.1]
        have hlog :
            HasDerivAt (fun u : ℝ => Real.log (u / (2 * Real.pi))) (1 / y) y := by
          have h1 :
              HasDerivAt (fun u : ℝ => u / (2 * Real.pi)) (1 / (2 * Real.pi)) y := by
            simpa using (hasDerivAt_id y).div_const (2 * Real.pi)
          have hpos : 0 < y / (2 * Real.pi) := by
            positivity
          have hlog' := (Real.hasDerivAt_log hpos.ne').comp y h1
          refine hlog'.congr_deriv ?_
          field_simp [hy_pos.ne', Real.pi_ne_zero]
        have h := ((hasDerivAt_id y).div_const 2).mul hlog
        have h' := h.sub ((hasDerivAt_id y).div_const 2)
        convert h' using 1
        field_simp [hy_pos.ne', Real.pi_ne_zero]
        ring_nf
        simp)
      hint)

/-- The integral of the theta-derivative error term on `[1,T]` is `O(log T)`. -/
private theorem thetaDeriv_error_integral_bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |∫ y in (1 : ℝ)..T,
          (ThetaDerivAsymptotic.thetaDeriv y - (1 / 2 : ℝ) * Real.log (y / (2 * Real.pi)))|
        ≤ C * Real.log T := by
  let thetaErr : ℝ → ℝ := fun y =>
    ThetaDerivAsymptotic.thetaDeriv y - (1 / 2 : ℝ) * Real.log (y / (2 * Real.pi))
  have htheta : thetaErr =O[atTop] (fun y : ℝ => 1 / y) :=
    ThetaDerivAsymptotic.theta_deriv_asymptotic
  obtain ⟨C0, hC0evt⟩ := htheta.bound
  obtain ⟨T0, hT0bound⟩ := Filter.eventually_atTop.mp hC0evt
  let B : ℝ := max 14 (max 1 T0)
  have hB_ge14 : 14 ≤ B := le_max_left _ _
  have hB_ge1 : 1 ≤ B := le_trans (le_max_left 1 T0) (le_max_right 14 (max 1 T0))
  have hB_geT0 : T0 ≤ B := le_trans (le_max_right 1 T0) (le_max_right 14 (max 1 T0))
  have hB_pos : 0 < B := by
    linarith
  have htheta_cont_Icc : ∀ {a b : ℝ}, 0 < a → ContinuousOn thetaErr (Set.Icc a b) := by
    intro a b ha
    refine (HardyThetaSmooth.continuous_thetaDeriv.continuousOn).sub ?_
    refine continuousOn_const.mul ?_
    apply ContinuousOn.log
    · exact (continuous_id.div_const (2 * Real.pi)).continuousOn
    · intro y hy
      have hy_pos : 0 < y := lt_of_lt_of_le ha hy.1
      positivity
  obtain ⟨x, hxmem, hxmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hB_ge1)
    (ContinuousOn.abs (htheta_cont_Icc (a := 1) (b := B) (by norm_num : (0 : ℝ) < 1)))
  let M : ℝ := |thetaErr x|
  have hM_bound : ∀ y ∈ Set.Icc 1 B, |thetaErr y| ≤ M := by
    intro y hy
    exact hxmax hy
  let A : ℝ := M * (B - 1)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, M]
    exact mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hB_ge1)
  have hsmall :
      ∀ T : ℝ, 14 ≤ T → T ≤ B → |∫ y in (1 : ℝ)..T, thetaErr y| ≤ A := by
    intro T hT hTB
    have h1T : 1 ≤ T := by
      linarith
    have hbound : ∀ y ∈ Set.uIoc (1 : ℝ) T, ‖thetaErr y‖ ≤ M := by
      intro y hy
      rw [Real.norm_eq_abs]
      rw [Set.uIoc_of_le h1T] at hy
      exact hM_bound y ⟨le_of_lt hy.1, le_trans hy.2 hTB⟩
    have hnorm :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 : ℝ)) (b := T) hbound
    calc
      |∫ y in (1 : ℝ)..T, thetaErr y| = ‖∫ y in (1 : ℝ)..T, thetaErr y‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ M * |T - 1| := hnorm
      _ = M * (T - 1) := by
            rw [abs_of_nonneg (by linarith)]
      _ ≤ A := by
            dsimp [A]
            gcongr
  have htail :
      ∀ T : ℝ, B ≤ T → |∫ y in B..T, thetaErr y| ≤ |C0| * Real.log T := by
    intro T hBT
    have hT_pos : 0 < T := lt_of_lt_of_le hB_pos hBT
    have hinv_cont : ContinuousOn (fun y : ℝ => 1 / y) (Set.uIcc B T) := by
      simpa [one_div] using
        (continuous_id.continuousOn.inv₀ (fun y hy => by
          rw [Set.uIcc_of_le hBT] at hy
          exact (lt_of_lt_of_le hB_pos hy.1).ne'))
    have hintInv :
        IntervalIntegrable (fun y : ℝ => |C0| * (1 / y)) volume B T := by
      exact ((continuousOn_const.mul hinv_cont)).intervalIntegrable
    have hnorm :=
      intervalIntegral.norm_integral_le_of_norm_le (a := B) (b := T) hBT
        (Filter.Eventually.of_forall (fun y hy => by
          have hy_pos : 0 < y := lt_of_lt_of_le hB_pos (le_of_lt hy.1)
          have hy_T0 : T0 ≤ y := le_trans hB_geT0 (le_of_lt hy.1)
          have hy_bound := hT0bound y hy_T0
          have hy_norm_inv : ‖1 / y‖ = 1 / y := by
            rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hy_pos)]
          calc
            ‖thetaErr y‖ ≤ C0 * ‖1 / y‖ := hy_bound
            _ ≤ |C0| * ‖1 / y‖ := by
                  gcongr
                  exact le_abs_self C0
            _ = |C0| * (1 / y) := by rw [hy_norm_inv]))
        hintInv
    calc
      |∫ y in B..T, thetaErr y| = ‖∫ y in B..T, thetaErr y‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ y in B..T, |C0| * (1 / y) := hnorm
      _ = |C0| * ∫ y in B..T, 1 / y := by
            rw [intervalIntegral.integral_const_mul]
      _ = |C0| * Real.log (T / B) := by
            simpa [one_div] using
              congrArg (fun z : ℝ => |C0| * z) (integral_inv_of_pos hB_pos hT_pos)
      _ ≤ |C0| * Real.log T := by
            have hdiv_le : T / B ≤ T := by
              exact div_le_self (le_of_lt hT_pos) hB_ge1
            have hlog_le : Real.log (T / B) ≤ Real.log T := by
              exact Real.log_le_log (by positivity) hdiv_le
            exact mul_le_mul_of_nonneg_left hlog_le (abs_nonneg C0)
  have hintB : IntervalIntegrable thetaErr volume 1 B := by
    exact (htheta_cont_Icc (a := 1) (b := B) (by norm_num : (0 : ℝ) < 1)).intervalIntegrable_of_Icc
      hB_ge1
  have hlog14_pos : 0 < Real.log 14 := Real.log_pos (by norm_num : (1 : ℝ) < 14)
  refine ⟨|C0| + A / Real.log 14, ?_⟩
  intro T hT
  have hlog14_le : Real.log 14 ≤ Real.log T :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 14) hT
  have hA_absorb : A ≤ (A / Real.log 14) * Real.log T := by
    calc
      A = (A / Real.log 14) * Real.log 14 := by
            field_simp [ne_of_gt hlog14_pos]
      _ ≤ (A / Real.log 14) * Real.log T := by
            gcongr
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  by_cases hTB : T ≤ B
  · have hsmallT := hsmall T hT hTB
    calc
      |∫ y in (1 : ℝ)..T, thetaErr y| ≤ A := hsmallT
      _ ≤ (A / Real.log 14) * Real.log T := hA_absorb
      _ ≤ (|C0| + A / Real.log 14) * Real.log T := by
            nlinarith [abs_nonneg C0, hlogT_nonneg, hA_nonneg]
  · have hBT : B ≤ T := le_of_not_ge hTB
    have hintTail : IntervalIntegrable thetaErr volume B T := by
      exact (htheta_cont_Icc (a := B) (b := T) hB_pos).intervalIntegrable_of_Icc hBT
    have hsplit :
        (∫ y in (1 : ℝ)..B, thetaErr y) + ∫ y in B..T, thetaErr y =
          ∫ y in (1 : ℝ)..T, thetaErr y :=
      intervalIntegral.integral_add_adjacent_intervals hintB hintTail
    have hleft : |∫ y in (1 : ℝ)..B, thetaErr y| ≤ A := hsmall B hB_ge14 le_rfl
    have hright : |∫ y in B..T, thetaErr y| ≤ |C0| * Real.log T := htail T hBT
    calc
      |∫ y in (1 : ℝ)..T, thetaErr y|
          = |(∫ y in (1 : ℝ)..B, thetaErr y) + ∫ y in B..T, thetaErr y| := by
              rw [hsplit]
      _ ≤ |∫ y in (1 : ℝ)..B, thetaErr y| + |∫ y in B..T, thetaErr y| := abs_add_le _ _
      _ ≤ A + |C0| * Real.log T := by
            linarith
      _ ≤ (A / Real.log 14) * Real.log T + |C0| * Real.log T := by
            nlinarith [hA_absorb]
      _ = (|C0| + A / Real.log 14) * Real.log T := by
            ring

/-- On the zero-free half-top segment, the logarithmic derivative of
    `completedRiemannZeta` splits into the `Gammaℝ` and `ζ` pieces. -/
private theorem logDeriv_completedZeta_eq_logDeriv_GammaR_add_logDeriv_zeta
    [ZeroOrdinateLowerBoundHyp] (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
    logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I) =
      logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I) +
        logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I) := by
  let s : ℂ := ((↑x : ℂ) + (↑T : ℂ) * I)
  have hsre : 0 < s.re := by
    dsimp [s]
    linarith [hx.1]
  have hs0 : s ≠ 0 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    linarith
  have hs1 : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    linarith
  have hT1 : 1 ≤ T := by linarith
  have hs_comp_ne : completedRiemannZeta s ≠ 0 := by
    exact completedZeta_ne_zero_on_boundary T hT hT_not_ord _
      (top_edge_mem_rectBoundary T hT1 (by
        constructor
        · linarith [hx.1]
        · exact hx.2))
  have heq :
      completedRiemannZeta =ᶠ[𝓝 s] (Gammaℝ * riemannZeta) := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    refine ⟨{z : ℂ | 0 < z.re}, hopen.mem_nhds hsre, ?_⟩
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0] at hz
      simp at hz
    have hG : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hz
    show completedRiemannZeta z = (Gammaℝ * riemannZeta) z
    simpa [Pi.mul_apply] using RvMRightEdge.completedZeta_eq_GammaR_mul_zeta z hz0 hG
  rw [show logDeriv completedRiemannZeta s = logDeriv (Gammaℝ * riemannZeta) s from by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.eq_of_nhds]]
  have hG_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hsre
  have hzeta_ne : riemannZeta s ≠ 0 := by
    intro hzeta
    have hcomp_zero : completedRiemannZeta s = 0 := by
      rw [RvMRightEdge.completedZeta_eq_GammaR_mul_zeta s hs0 hG_ne, hzeta]
      simp
    exact hs_comp_ne hcomp_zero
  have hG_diff : DifferentiableAt ℂ Gammaℝ s := RvMRightEdge.differentiableAt_GammaR s hsre
  have hzeta_diff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hmul_eq : (Gammaℝ * riemannZeta) = (riemannZeta * Gammaℝ) := by
    ext z
    simp [Pi.mul_apply, mul_comm]
  rw [hmul_eq]
  simpa [Pi.mul_apply, add_comm, add_left_comm, add_assoc] using
    (logDeriv_mul s hzeta_ne hG_ne hzeta_diff hG_diff)

/-- The top half of the completed-zeta logarithmic derivative splits into the
    `Gammaℝ` and `ζ` contributions. -/
private theorem halfTop_zeta_logDeriv_continuousOn
    [ZeroOrdinateLowerBoundHyp] (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    ContinuousOn
      (fun x : ℝ => logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
      (Set.Icc (1 / 2 : ℝ) 2) := by
  let φ : ℝ → ℂ := fun x => (↑x : ℂ) + (↑T : ℂ) * I
  have hφ : ContinuousOn φ (Set.Icc (1 / 2 : ℝ) 2) := by
    simpa [φ] using (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
  have hφ_maps : Set.MapsTo φ (Set.Icc (1 / 2 : ℝ) 2) {s : ℂ | s ≠ 1} := by
    intro x hx h
    have him := congrArg Complex.im h
    simp [φ] at him
    linarith
  have hnum0 : ContinuousOn (deriv riemannZeta) {s : ℂ | s ≠ 1} := by
    intro s hs
    exact (continuousAt_deriv_riemannZeta_ne_one s hs).continuousWithinAt
  have hden0 : ContinuousOn riemannZeta {s : ℂ | s ≠ 1} := by
    intro s hs
    exact (differentiableAt_riemannZeta hs).continuousAt.continuousWithinAt
  have hnum : ContinuousOn (fun x : ℝ => deriv riemannZeta (φ x)) (Set.Icc (1 / 2 : ℝ) 2) :=
    hnum0.comp' hφ hφ_maps
  have hden : ContinuousOn (fun x : ℝ => riemannZeta (φ x)) (Set.Icc (1 / 2 : ℝ) 2) :=
    hden0.comp' hφ hφ_maps
  have hne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta (φ x) ≠ 0 := by
    intro x hx hzeta
    have hφ0 : φ x ≠ 0 := by
      intro h0
      have him := congrArg Complex.im h0
      simp [φ] at him
      linarith
    have hT1 : 1 ≤ T := by linarith
    have hcomp_zero : completedRiemannZeta (φ x) = 0 := by
      rw [RvMRightEdge.completedZeta_eq_GammaR_mul_zeta (φ x) hφ0 (Gammaℝ_ne_zero_of_re_pos (by
        simpa [φ] using (show 0 < x by linarith [hx.1])))]
      simp [hzeta]
    exact completedZeta_ne_zero_on_boundary T hT hT_not_ord _
      (top_edge_mem_rectBoundary T hT1 (by
        constructor
        · linarith [hx.1]
        · exact hx.2)) hcomp_zero
  simpa [logDeriv_apply, φ] using hnum.div hden hne

/-- The top half of the completed-zeta logarithmic derivative splits into the
    `Gammaℝ` and `ζ` contributions. -/
private theorem completedZetaHalfTopContribution_eq_gamma_plus_zeta
    [ZeroOrdinateLowerBoundHyp] (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    -(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
      =
    (-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im)) +
      (-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)) := by
  have hGamma_cont : ContinuousOn
      (fun x : ℝ => logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I))
      (Set.Icc (1 / 2 : ℝ) 2) := by
    let φ : ℝ → ℂ := fun x => (↑x : ℂ) + (↑T : ℂ) * I
    have hφ : ContinuousOn φ (Set.Icc (1 / 2 : ℝ) 2) := by
      simpa [φ] using (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
    have hφ_maps : Set.MapsTo φ (Set.Icc (1 / 2 : ℝ) 2) {s : ℂ | 0 < s.re} := by
      intro x hx
      simp [φ]
      linarith [hx.1]
    have hnum0 : ContinuousOn (deriv Gammaℝ) {s : ℂ | 0 < s.re} := by
      intro s hs
      exact ((analyticOn_GammaR_re_pos s hs).deriv).continuousAt.continuousWithinAt
    have hden0 : ContinuousOn Gammaℝ {s : ℂ | 0 < s.re} := by
      intro s hs
      exact (RvMRightEdge.differentiableAt_GammaR s hs).continuousAt.continuousWithinAt
    have hnum : ContinuousOn (fun x : ℝ => deriv Gammaℝ (φ x)) (Set.Icc (1 / 2 : ℝ) 2) :=
      hnum0.comp' hφ hφ_maps
    have hden : ContinuousOn (fun x : ℝ => Gammaℝ (φ x)) (Set.Icc (1 / 2 : ℝ) 2) :=
      hden0.comp' hφ hφ_maps
    have hne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, Gammaℝ (φ x) ≠ 0 := by
      intro x hx
      exact Gammaℝ_ne_zero_of_re_pos (by simpa [φ] using (show 0 < x by linarith [hx.1]))
    simpa [logDeriv_apply, φ] using hnum.div hden hne
  have hZeta_cont :
      ContinuousOn
        (fun x : ℝ => logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
        (Set.Icc (1 / 2 : ℝ) 2) :=
    halfTop_zeta_logDeriv_continuousOn T hT hT_not_ord
  have hsplit :
      ∫ x in (1 / 2 : ℝ)..2,
          (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im
        =
      (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im) +
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) := by
    have hGamma_int : IntervalIntegrable
        (fun x : ℝ => logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I))
        volume (1 / 2) 2 :=
      hGamma_cont.intervalIntegrable_of_Icc (by norm_num)
    have hZeta_int : IntervalIntegrable
        (fun x : ℝ => logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
        volume (1 / 2) 2 :=
      hZeta_cont.intervalIntegrable_of_Icc (by norm_num)
    have hsum_int : IntervalIntegrable
        (fun x : ℝ =>
          logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I) +
            logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
        volume (1 / 2) 2 :=
      (hGamma_cont.add hZeta_cont).intervalIntegrable_of_Icc (by norm_num)
    have hpoint :
        ∀ x : ℝ,
          x ∈ Set.Icc (1 / 2 : ℝ) 2 →
            logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I) =
              logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I) +
                logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I) := by
      intro x hx
      simpa using
        logDeriv_completedZeta_eq_logDeriv_GammaR_add_logDeriv_zeta T hT hT_not_ord hx
    have hcompleted_re :
        ∫ x in (1 / 2 : ℝ)..2,
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im =
          (∫ x in (1 / 2 : ℝ)..2,
            logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im := by
      have hcompleted_cont : ContinuousOn
          (fun x : ℝ => logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
          (Set.Icc (1 / 2 : ℝ) 2) := by
        refine (completedZeta_top_continuousOn T hT hT_not_ord).mono ?_
        intro x hx
        exact ⟨by linarith [hx.1], hx.2⟩
      have hcompleted_int :
          IntervalIntegrable
            (fun x : ℝ => logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))
            volume (1 / 2) 2 :=
        hcompleted_cont.intervalIntegrable_of_Icc (by norm_num)
      have := Complex.imCLM.intervalIntegral_comp_comm hcompleted_int
      simp only [Complex.imCLM_apply] at this
      exact this
    have hGamma_im :
        ∫ x in (1 / 2 : ℝ)..2,
            (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im =
          (∫ x in (1 / 2 : ℝ)..2,
            logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im := by
      have := Complex.imCLM.intervalIntegral_comp_comm hGamma_int
      simp only [Complex.imCLM_apply] at this
      exact this
    have hZeta_im :
        ∫ x in (1 / 2 : ℝ)..2,
            (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im =
          (∫ x in (1 / 2 : ℝ)..2,
            logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im := by
      have := Complex.imCLM.intervalIntegral_comp_comm hZeta_int
      simp only [Complex.imCLM_apply] at this
      exact this
    calc
      ∫ x in (1 / 2 : ℝ)..2,
          (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im
          = (∫ x in (1 / 2 : ℝ)..2,
              logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im := hcompleted_re
      _ = (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I) +
              logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))).im := by
            apply congrArg Complex.im
            apply intervalIntegral.integral_congr_ae
            filter_upwards with x hx
            have hx' : x ∈ Set.Icc (1 / 2 : ℝ) 2 := by
              have hx'' : x ∈ Set.uIcc (1 / 2 : ℝ) 2 := Set.uIoc_subset_uIcc hx
              rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx''
              exact hx''
            exact hpoint x hx'
      _ = ((∫ x in (1 / 2 : ℝ)..2,
              logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)) +
            (∫ x in (1 / 2 : ℝ)..2,
              logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I))).im := by
            rw [intervalIntegral.integral_add hGamma_int hZeta_int]
      _ = (∫ x in (1 / 2 : ℝ)..2,
            logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im +
          (∫ x in (1 / 2 : ℝ)..2,
            logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im := by
            rw [Complex.add_im]
      _ = (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im) +
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) := by
            rw [← hGamma_im, ← hZeta_im]
  rw [hsplit]
  ring

/-- Exact FTC evaluation of the `Gammaℝ` contribution from the half-top
    segment and the right edge. -/
private theorem halfTopGammaPlusRightEdgeGamma_eq_gammaRLog_endpoint
    (T : ℝ) (hT : 14 ≤ T) :
    (-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im)) +
      completedZetaRightGammaContribution T
      =
    (1 / Real.pi) *
      ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
        (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) := by
  have hT1 : 1 ≤ T := by linarith
  have hright_cont : ContinuousOn
      (fun y : ℝ => logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I))
      (Set.Icc (1 : ℝ) T) := by
    let φ : ℝ → ℂ := fun y => (2 : ℂ) + (↑y : ℂ) * I
    have hφ : ContinuousOn φ (Set.Icc (1 : ℝ) T) := by
      simpa [φ] using (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
    have hφ_maps : Set.MapsTo φ (Set.Icc (1 : ℝ) T) {s : ℂ | 0 < s.re} := by
      intro y hy
      simp [φ]
    have hnum0 : ContinuousOn (deriv Gammaℝ) {s : ℂ | 0 < s.re} := by
      intro s hs
      exact ((analyticOn_GammaR_re_pos s hs).deriv).continuousAt.continuousWithinAt
    have hden0 : ContinuousOn Gammaℝ {s : ℂ | 0 < s.re} := by
      intro s hs
      exact (RvMRightEdge.differentiableAt_GammaR s hs).continuousAt.continuousWithinAt
    have hnum : ContinuousOn (fun y : ℝ => deriv Gammaℝ (φ y)) (Set.Icc (1 : ℝ) T) :=
      hnum0.comp' hφ hφ_maps
    have hden : ContinuousOn (fun y : ℝ => Gammaℝ (φ y)) (Set.Icc (1 : ℝ) T) :=
      hden0.comp' hφ hφ_maps
    have hne : ∀ y ∈ Set.Icc (1 : ℝ) T, Gammaℝ (φ y) ≠ 0 := by
      intro y hy
      exact Gammaℝ_ne_zero_of_re_pos (by simp [φ])
    simpa [logDeriv_apply, φ] using hnum.div hden hne
  have hright :
      IntervalIntegrable
        (fun y : ℝ => logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I))
        volume 1 T :=
    hright_cont.intervalIntegrable_of_Icc hT1
  have htop_cont : ContinuousOn
      (fun x : ℝ => logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I))
      (Set.Icc (1 / 2 : ℝ) 2) := by
    let φ : ℝ → ℂ := fun x => (↑x : ℂ) + (↑T : ℂ) * I
    have hφ : ContinuousOn φ (Set.Icc (1 / 2 : ℝ) 2) := by
      simpa [φ] using (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
    have hφ_maps : Set.MapsTo φ (Set.Icc (1 / 2 : ℝ) 2) {s : ℂ | 0 < s.re} := by
      intro x hx
      simp [φ]
      linarith [hx.1]
    have hnum0 : ContinuousOn (deriv Gammaℝ) {s : ℂ | 0 < s.re} := by
      intro s hs
      exact ((analyticOn_GammaR_re_pos s hs).deriv).continuousAt.continuousWithinAt
    have hden0 : ContinuousOn Gammaℝ {s : ℂ | 0 < s.re} := by
      intro s hs
      exact (RvMRightEdge.differentiableAt_GammaR s hs).continuousAt.continuousWithinAt
    have hnum : ContinuousOn (fun x : ℝ => deriv Gammaℝ (φ x)) (Set.Icc (1 / 2 : ℝ) 2) :=
      hnum0.comp' hφ hφ_maps
    have hden : ContinuousOn (fun x : ℝ => Gammaℝ (φ x)) (Set.Icc (1 / 2 : ℝ) 2) :=
      hden0.comp' hφ hφ_maps
    have hne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, Gammaℝ (φ x) ≠ 0 := by
      intro x hx
      exact Gammaℝ_ne_zero_of_re_pos (by simp [φ]; linarith [hx.1])
    simpa [logDeriv_apply, φ] using hnum.div hden hne
  have htop :
      IntervalIntegrable
        (fun x : ℝ => logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I))
        volume (1 / 2) 2 :=
    htop_cont.intervalIntegrable_of_Icc (by norm_num)
  have hrightFTC :
      ∫ y in (1 : ℝ)..T, I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)
        = gammaRLog ((2 : ℂ) + (↑T : ℂ) * I) - gammaRLog ((2 : ℂ) + (1 : ℂ) * I) := by
    have hrightI :
        IntervalIntegrable
          (fun y : ℝ => I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I))
          volume 1 T := by
      simpa [one_mul] using hright.const_mul I
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => gammaRLog ((2 : ℂ) + (↑y : ℂ) * I))
        (f' := fun y : ℝ => I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I))
        (fun y _hy => by
          have hs : 0 < (((2 : ℂ) + (↑y : ℂ) * I)).re := by norm_num
          exact ((hasDerivAt_gammaRLog (((2 : ℂ) + (↑y : ℂ) * I)) hs).scomp y
            (hasDerivAt_rvm_vertical_path 2 y)).congr_deriv (by
              simp [smul_eq_mul]))
        hrightI)
  have htopFTC :
      ∫ x in (1 / 2 : ℝ)..2, logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)
        = gammaRLog ((2 : ℂ) + (↑T : ℂ) * I) - gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I) := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x : ℝ => gammaRLog ((↑x : ℂ) + (↑T : ℂ) * I))
        (f' := fun x : ℝ => logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I))
        (fun x hx => by
          have hx' : x ∈ Set.Icc (1 / 2 : ℝ) 2 := by
            rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
            exact hx
          have hs : 0 < (((↑x : ℂ) + (↑T : ℂ) * I)).re := by
            simp
            linarith [hx'.1]
          simpa [smul_eq_mul] using
            (hasDerivAt_gammaRLog (((↑x : ℂ) + (↑T : ℂ) * I)) hs).scomp x
              (hasDerivAt_rvm_horizontal_path T x))
        htop)
  have hright_im :
      ∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re
        =
      (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im -
        (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im := by
    have hrightI :
        IntervalIntegrable
          (fun y : ℝ => I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I))
          volume 1 T := by
      simpa [one_mul] using hright.const_mul I
    have hmap :
        ∫ y in (1 : ℝ)..T, (I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).im
          =
        (∫ y in (1 : ℝ)..T, I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).im := by
      simpa using Complex.imCLM.intervalIntegral_comp_comm hrightI
    have hFTC_im := congrArg Complex.im hrightFTC
    calc
      ∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re
          = ∫ y in (1 : ℝ)..T, (I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).im := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards with y
              simp
      _ = (∫ y in (1 : ℝ)..T, I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).im := hmap
      _ = (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im -
            (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im := by
              simpa [Complex.sub_im] using hFTC_im
  have htop_im :
      ∫ x in (1 / 2 : ℝ)..2, (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im
        =
      (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im -
        (gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im := by
    calc
      ∫ x in (1 / 2 : ℝ)..2, (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im
          = (∫ x in (1 / 2 : ℝ)..2, logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im := by
              simpa using Complex.imCLM.intervalIntegral_comp_comm htop
      _ = (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im -
            (gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im := by
              simpa [Complex.sub_im] using congrArg Complex.im htopFTC
  have hrightGamma :
      completedZetaRightGammaContribution T =
        (1 / Real.pi) *
          (∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re) := by
    let g : ℝ → ℂ := fun y =>
      (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
        (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2)
    have hg_eq :
        g = fun y : ℝ => logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I) := by
      ext y
      have hy' : 0 < (((2 : ℂ) + (↑y : ℂ) * I)).re := by norm_num
      simpa [g, add_comm, add_left_comm, add_assoc] using
        (RvMRightEdge.logDeriv_GammaR_eq ((2 : ℂ) + (↑y : ℂ) * I) hy').symm
    have hg_int : IntervalIntegrable g volume 1 T := by
      simpa [hg_eq] using hright
    have hg_re :
        (∫ y in (1 : ℝ)..T, g y).re = ∫ y in (1 : ℝ)..T, (g y).re := by
      simpa [g] using (Complex.reCLM.intervalIntegral_comp_comm hg_int).symm
    have hg_eq_re :
        ∫ y in (1 : ℝ)..T, (g y).re =
          ∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re := by
      simp [hg_eq]
    unfold completedZetaRightGammaContribution
    calc
      (1 / Real.pi) * (∫ y in (1 : ℝ)..T, g y).re
          = (1 / Real.pi) * ∫ y in (1 : ℝ)..T, (g y).re := by
              rw [hg_re]
      _ = (1 / Real.pi) * (∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re) := by
              rw [hg_eq_re]
  calc
    (-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im)) +
      completedZetaRightGammaContribution T
        = (-(1 / Real.pi) *
            (∫ x in (1 / 2 : ℝ)..2,
              (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im)) +
          (1 / Real.pi) *
            (∫ y in (1 : ℝ)..T,
              (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re) := by
          rw [hrightGamma]
    _ = (-(1 / Real.pi) *
            ((gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im -
              (gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im)) +
          (1 / Real.pi) *
            ((gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im -
              (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) := by
          rw [htop_im, hright_im]
    _ = (1 / Real.pi) *
          ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
            (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) := by
          ring

/-- Exact right-edge `Gammaℝ` identity: the vertical contribution is the
    endpoint difference of `gammaRLog` on the line `Re(s)=2`. -/
private theorem completedZetaRightGammaContribution_eq_gammaRLog_right_edge_endpoint
    (T : ℝ) (hT : 14 ≤ T) :
    completedZetaRightGammaContribution T =
      (1 / Real.pi) *
        ((gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im -
          (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) := by
  have hT1 : 1 ≤ T := by linarith
  have hright_cont : ContinuousOn
      (fun y : ℝ => logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I))
      (Set.Icc (1 : ℝ) T) := by
    let φ : ℝ → ℂ := fun y => (2 : ℂ) + (↑y : ℂ) * I
    have hφ : ContinuousOn φ (Set.Icc (1 : ℝ) T) := by
      simpa [φ] using (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
    have hφ_maps : Set.MapsTo φ (Set.Icc (1 : ℝ) T) {s : ℂ | 0 < s.re} := by
      intro y hy
      simp [φ]
    have hnum0 : ContinuousOn (deriv Gammaℝ) {s : ℂ | 0 < s.re} := by
      intro s hs
      exact ((analyticOn_GammaR_re_pos s hs).deriv).continuousAt.continuousWithinAt
    have hden0 : ContinuousOn Gammaℝ {s : ℂ | 0 < s.re} := by
      intro s hs
      exact (RvMRightEdge.differentiableAt_GammaR s hs).continuousAt.continuousWithinAt
    have hnum : ContinuousOn (fun y : ℝ => deriv Gammaℝ (φ y)) (Set.Icc (1 : ℝ) T) :=
      hnum0.comp' hφ hφ_maps
    have hden : ContinuousOn (fun y : ℝ => Gammaℝ (φ y)) (Set.Icc (1 : ℝ) T) :=
      hden0.comp' hφ hφ_maps
    have hne : ∀ y ∈ Set.Icc (1 : ℝ) T, Gammaℝ (φ y) ≠ 0 := by
      intro y hy
      exact Gammaℝ_ne_zero_of_re_pos (by simp [φ])
    simpa [logDeriv_apply, φ] using hnum.div hden hne
  have hright :
      IntervalIntegrable
        (fun y : ℝ => logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I))
        volume 1 T :=
    hright_cont.intervalIntegrable_of_Icc hT1
  have hrightFTC :
      ∫ y in (1 : ℝ)..T, I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)
        = gammaRLog ((2 : ℂ) + (↑T : ℂ) * I) - gammaRLog ((2 : ℂ) + (1 : ℂ) * I) := by
    have hrightI :
        IntervalIntegrable
          (fun y : ℝ => I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I))
          volume 1 T := by
      simpa [one_mul] using hright.const_mul I
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => gammaRLog ((2 : ℂ) + (↑y : ℂ) * I))
        (f' := fun y : ℝ => I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I))
        (fun y _hy => by
          have hs : 0 < (((2 : ℂ) + (↑y : ℂ) * I)).re := by norm_num
          exact ((hasDerivAt_gammaRLog (((2 : ℂ) + (↑y : ℂ) * I)) hs).scomp y
            (hasDerivAt_rvm_vertical_path 2 y)).congr_deriv (by
              simp [smul_eq_mul]))
        hrightI)
  have hright_im :
      ∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re
        =
      (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im -
        (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im := by
    have hrightI :
        IntervalIntegrable
          (fun y : ℝ => I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I))
          volume 1 T := by
      simpa [one_mul] using hright.const_mul I
    have hmap :
        ∫ y in (1 : ℝ)..T, (I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).im
          =
        (∫ y in (1 : ℝ)..T, I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).im := by
      simpa using Complex.imCLM.intervalIntegral_comp_comm hrightI
    have hFTC_im := congrArg Complex.im hrightFTC
    calc
      ∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re
          = ∫ y in (1 : ℝ)..T, (I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).im := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards with y
              simp
      _ = (∫ y in (1 : ℝ)..T, I * logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).im := hmap
      _ = (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im -
            (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im := by
              simpa [Complex.sub_im] using hFTC_im
  have hrightGamma :
      completedZetaRightGammaContribution T =
        (1 / Real.pi) *
          (∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re) := by
    let g : ℝ → ℂ := fun y =>
      (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
        (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2)
    have hg_eq :
        g = fun y : ℝ => logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I) := by
      ext y
      have hy' : 0 < (((2 : ℂ) + (↑y : ℂ) * I)).re := by norm_num
      simpa [g, add_comm, add_left_comm, add_assoc] using
        (RvMRightEdge.logDeriv_GammaR_eq ((2 : ℂ) + (↑y : ℂ) * I) hy').symm
    have hg_int : IntervalIntegrable g volume 1 T := by
      simpa [hg_eq] using hright
    have hg_re :
        (∫ y in (1 : ℝ)..T, g y).re = ∫ y in (1 : ℝ)..T, (g y).re := by
      simpa [g] using (Complex.reCLM.intervalIntegral_comp_comm hg_int).symm
    have hg_eq_re :
        ∫ y in (1 : ℝ)..T, (g y).re =
          ∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re := by
      simp [hg_eq]
    unfold completedZetaRightGammaContribution
    calc
      (1 / Real.pi) * (∫ y in (1 : ℝ)..T, g y).re
          = (1 / Real.pi) * ∫ y in (1 : ℝ)..T, (g y).re := by
              rw [hg_re]
      _ = (1 / Real.pi) * (∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re) := by
              rw [hg_eq_re]
  calc
    completedZetaRightGammaContribution T
        = (1 / Real.pi) *
            (∫ y in (1 : ℝ)..T, (logDeriv Gammaℝ ((2 : ℂ) + (↑y : ℂ) * I)).re) := hrightGamma
    _ = (1 / Real.pi) *
          ((gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im -
            (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) := by
          rw [hright_im]

/-- Exact linear elimination of the half-top `ζ` term in favor of the
    completed half-top contribution, the right-edge `Gammaℝ` term, and the
    `gammaRLog` endpoint expression. -/
private theorem halfTopZeta_eq_completedHalfTopPlusRightGamma_sub_gammaRLog_endpoint
    [ZeroOrdinateLowerBoundHyp] (T : ℝ) (hT : 14 ≤ T) (hT_not_ord : T ∉ zetaZeroOrdinates) :
    -(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
      =
    (-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) +
        completedZetaRightGammaContribution T)
      -
      (1 / Real.pi) *
        ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
          (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) := by
  let zetaTerm : ℝ :=
    -(1 / Real.pi) *
      (∫ x in (1 / 2 : ℝ)..2,
        (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
  let gammaTerm : ℝ :=
    -(1 / Real.pi) *
      (∫ x in (1 / 2 : ℝ)..2,
        (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im)
  let completedTerm : ℝ :=
    -(1 / Real.pi) *
      (∫ x in (1 / 2 : ℝ)..2,
        (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
  let endpointTerm : ℝ :=
    (1 / Real.pi) *
      ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
        (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im)
  have hsplit : completedTerm = gammaTerm + zetaTerm := by
    simpa [completedTerm, gammaTerm, zetaTerm] using
      completedZetaHalfTopContribution_eq_gamma_plus_zeta T hT hT_not_ord
  have hgamma : gammaTerm + completedZetaRightGammaContribution T = endpointTerm := by
    simpa [gammaTerm, endpointTerm] using
      halfTopGammaPlusRightEdgeGamma_eq_gammaRLog_endpoint T hT
  calc
    zetaTerm = completedTerm - gammaTerm := by
      linarith
    _ =
      (completedTerm + completedZetaRightGammaContribution T) -
        (gammaTerm + completedZetaRightGammaContribution T) := by
          ring
    _ = (completedTerm + completedZetaRightGammaContribution T) - endpointTerm := by
          rw [hgamma]
    _ =
      (-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) +
          completedZetaRightGammaContribution T)
        -
        (1 / Real.pi) *
          ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
            (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) := by
              rfl

/-- Honest boundary for the unresolved branch-safe variation of `ζ` along the
    half-top segment `[1/2, 2] + iT`. This is the exact analytic input consumed
    by the downstream contour-evaluation lane. -/
class RvmHalfTopZetaVariationBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)| ≤ C * Real.log T

/-- Reduced half-top zeta leaf after removing the exact `Gammaℝ` contour piece.
    This isolates the top-edge branch-variation problem for `ζ` itself. -/
private theorem rvm_half_top_zeta_variation_bound
    [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)| ≤ C * Real.log T := by
  exact RvmHalfTopZetaVariationBoundHyp.bound

/-- A horizontal primitive of `ζ'/ζ` with `O(log T)` endpoint variation on the
    half-top segment is enough to discharge `RvmHalfTopZetaVariationBoundHyp`. -/
private theorem rvmHalfTopZetaVariationBoundHyp_of_endpoint_primitive_bound
    [ZeroOrdinateLowerBoundHyp]
    (hPrimitive :
      ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
        ∃ F : ℝ → ℂ,
          ContinuousOn F (Set.Icc (1 / 2 : ℝ) 2) ∧
          (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
            HasDerivAt F
              (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) x) ∧
          ‖F 2 - F (1 / 2)‖ ≤ C * Real.log T) :
    RvmHalfTopZetaVariationBoundHyp := by
  refine ⟨?_⟩
  obtain ⟨C, hC⟩ := hPrimitive
  refine ⟨C / Real.pi, ?_⟩
  intro T hT hT_not_ord
  obtain ⟨F, hFcont, hFderiv, hFbound⟩ := hC T hT hT_not_ord
  let f : ℝ → ℂ := fun x =>
    logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)
  have hf_cont : ContinuousOn f (Set.Icc (1 / 2 : ℝ) 2) :=
    halfTop_zeta_logDeriv_continuousOn T hT hT_not_ord
  have hf_int : IntervalIntegrable f volume (1 / 2) 2 :=
    hf_cont.intervalIntegrable_of_Icc (by norm_num)
  have hFTC :
      ∫ x in (1 / 2 : ℝ)..2, f x = F 2 - F (1 / 2) := by
    exact
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hFderiv x (by
          rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
          exact hx))
        hf_int
  have him :
      ∫ x in (1 / 2 : ℝ)..2, (f x).im = (F 2 - F (1 / 2)).im := by
    calc
      ∫ x in (1 / 2 : ℝ)..2, (f x).im = (∫ x in (1 / 2 : ℝ)..2, f x).im := by
          simpa [f] using Complex.imCLM.intervalIntegral_comp_comm hf_int
      _ = (F 2 - F (1 / 2)).im := by rw [hFTC]
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  calc
    |-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)|
        = |-(1 / Real.pi) * (F 2 - F (1 / 2)).im| := by
            rw [show (∫ x in (1 / 2 : ℝ)..2,
                (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) =
                  ∫ x in (1 / 2 : ℝ)..2, (f x).im by rfl,
              him]
    _ = (1 / Real.pi) * |(F 2 - F (1 / 2)).im| := by
          rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
    _ ≤ (1 / Real.pi) * ‖F 2 - F (1 / 2)‖ := by
          gcongr
          exact Complex.abs_im_le_norm _
    _ ≤ (1 / Real.pi) * (C * Real.log T) := by
          gcongr
    _ = (C / Real.pi) * Real.log T := by
          ring

/-- Reduced Gamma endpoint leaf after removing the exact `Gammaℝ` contour
    integral identity. This isolates the branch-safe `gammaRLog` endpoint
    comparison against the explicit Stirling main term. -/
private theorem rvm_gammaRLog_endpoint_main_term_bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) *
          ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
            (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im)
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi)| ≤ C * Real.log T := by
  obtain ⟨Ctheta, htheta⟩ := thetaDeriv_error_integral_bound
  have hlog14_pos : 0 < Real.log 14 := Real.log_pos (by norm_num : (1 : ℝ) < 14)
  let K : ℝ :=
    (1 / Real.pi) *
        (((gammaRLog ((1 / 2 : ℂ) + (1 : ℂ) * I)).im -
            (((1 : ℝ) / 2) * Real.log (((1 : ℝ) / (2 * Real.pi))) - ((1 : ℝ) / 2)) -
            (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im))
      + 1 / 8
  refine ⟨Ctheta / Real.pi + |K| / Real.log 14, ?_⟩
  intro T hT
  have h1T : (1 : ℝ) ≤ T := by
    linarith
  have hthetaFTC := gammaRLog_halfLine_im_sub_eq_integral_thetaDeriv T h1T
  have hmainFTC := halfLog_main_term_integral_eq T hT
  let thetaErrInt : ℝ :=
    ∫ y in (1 : ℝ)..T,
      (ThetaDerivAsymptotic.thetaDeriv y - (1 / 2 : ℝ) * Real.log (y / (2 * Real.pi)))
  have hsplit :
      (1 / Real.pi) *
          ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
            (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im)
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
            - (T / (2 * Real.pi)) * Real.log Real.pi)
      = (1 / Real.pi) * thetaErrInt + K := by
    have hT_pos : 0 < T := by
      linarith
    have hthetaFTC' :
        (gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im =
          (gammaRLog ((1 / 2 : ℂ) + (1 : ℂ) * I)).im +
            ∫ y in (1 : ℝ)..T, ThetaDerivAsymptotic.thetaDeriv y := by
      linarith [hthetaFTC]
    have hmainFTC' :
        (T / 2) * Real.log (T / (2 * Real.pi)) - T / 2 =
          (((1 : ℝ) / 2) * Real.log (((1 : ℝ) / (2 * Real.pi))) - ((1 : ℝ) / 2)) +
            ∫ y in (1 : ℝ)..T, (1 / 2 : ℝ) * Real.log (y / (2 * Real.pi)) := by
      linarith [hmainFTC]
    have hmain_rewrite :
        (1 / Real.pi) *
            ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
          - (T / (2 * Real.pi)) * Real.log Real.pi
        = (1 / Real.pi) * ((T / 2) * Real.log (T / (2 * Real.pi)) - T / 2) - 1 / 8 := by
      calc
        (1 / Real.pi) *
            ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
          - (T / (2 * Real.pi)) * Real.log Real.pi
            = (1 / Real.pi) * ((T / 2) * (Real.log (T / 2) - Real.log Real.pi) - T / 2) - 1 / 8 := by
                field_simp [Real.pi_ne_zero]
                ring
        _ = (1 / Real.pi) * ((T / 2) * Real.log (T / (2 * Real.pi)) - T / 2) - 1 / 8 := by
                rw [ThetaDerivAsymptotic.log_half_sub_log_pi T hT_pos]
    have hcontLog :
        ContinuousOn (fun y : ℝ => Real.log (y / (2 * Real.pi))) (Set.uIcc 1 T) := by
      apply ContinuousOn.log
      · exact (continuous_id.div_const (2 * Real.pi)).continuousOn
      · intro y hy
        rw [Set.uIcc_of_le h1T] at hy
        have hy_pos : 0 < y := by
          linarith [hy.1]
        positivity
    have hsubint :
        (∫ y in (1 : ℝ)..T, ThetaDerivAsymptotic.thetaDeriv y) -
          ∫ y in (1 : ℝ)..T, (1 / 2 : ℝ) * Real.log (y / (2 * Real.pi)) = thetaErrInt := by
      have hthetaInt : IntervalIntegrable ThetaDerivAsymptotic.thetaDeriv volume 1 T :=
        HardyThetaSmooth.thetaDeriv_intervalIntegrable 1 T
      have hmainInt :
          IntervalIntegrable (fun y => (1 / 2 : ℝ) * Real.log (y / (2 * Real.pi))) volume 1 T :=
        ((continuousOn_const.mul hcontLog)).intervalIntegrable
      dsimp [thetaErrInt]
      rw [intervalIntegral.integral_sub hthetaInt hmainInt]
    have hsubint' :
        ∫ y in (1 : ℝ)..T, ThetaDerivAsymptotic.thetaDeriv y =
          thetaErrInt + ∫ y in (1 : ℝ)..T, (1 / 2 : ℝ) * Real.log (y / (2 * Real.pi)) := by
      linarith [hsubint]
    dsimp [thetaErrInt, K]
    rw [hmain_rewrite, hthetaFTC', hmainFTC', hsubint']
    ring
  have htheta_bound :
      |thetaErrInt| ≤ Ctheta * Real.log T := by
    simpa [thetaErrInt] using htheta T hT
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  calc
    |(1 / Real.pi) *
        ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
          (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im)
      - ((1 / Real.pi) *
            ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
          - (T / (2 * Real.pi)) * Real.log Real.pi)|
        = |(1 / Real.pi) * thetaErrInt + K| := by
            rw [hsplit]
    _ ≤ |(1 / Real.pi) * thetaErrInt| + |K| := abs_add_le _ _
    _ ≤ (Ctheta / Real.pi) * Real.log T + |K| := by
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
      have htheta_scaled :
          (1 / Real.pi) * |thetaErrInt| ≤ (Ctheta / Real.pi) * Real.log T := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left htheta_bound (by positivity : 0 ≤ 1 / Real.pi))
      linarith
    _ ≤ (Ctheta / Real.pi + |K| / Real.log 14) * Real.log T := by
          have hK_absorb : |K| ≤ (|K| / Real.log 14) * Real.log T := by
            calc
              |K| = (|K| / Real.log 14) * Real.log 14 := by
                      field_simp [ne_of_gt hlog14_pos]
              _ ≤ (|K| / Real.log 14) * Real.log T := by
                      gcongr
          nlinarith

/-- Direct right-edge `Gammaℝ` main-term theorem, salvaged from the Aristotle
    payload as a theorem-first replacement for the old class-based boundary. -/
theorem completedZetaRightGammaContribution_main_term_bound_relaxed :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |completedZetaRightGammaContribution T -
        ((1 / Real.pi) *
          ((T / 2) * Real.log (T / 2) - T / 2 -
            ((T - 1) / 2) * Real.log Real.pi +
            (Real.log 2 + 1) / 2))| ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := rightEdge_gamma_integral_main_term_explicit
  refine ⟨C / Real.pi, ?_⟩
  intro T hT
  let Iint : ℝ :=
    ∫ y in (1 : ℝ)..T,
      (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)).re +
        ((1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2)).re
  let M : ℝ :=
    (T / 2) * Real.log (T / 2) - T / 2 -
      ((T - 1) / 2) * Real.log Real.pi + (Real.log 2 + 1) / 2
  have hI : |Iint - M| ≤ C * Real.log T := by
    simpa [Iint, M, Complex.add_re, Complex.mul_re] using hC T hT
  have hscaled :
      (1 / Real.pi) * |Iint - M| ≤ (C / Real.pi) * Real.log T := by
    have hmul :=
      mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ (1 / Real.pi : ℝ))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hfinal :
      |(1 / Real.pi) * Iint - ((1 / Real.pi) * M)| ≤ (C / Real.pi) * Real.log T := by
    calc
      |(1 / Real.pi) * Iint - ((1 / Real.pi) * M)|
          = |(1 / Real.pi) * (Iint - M)| := by
              ring
      _ = (1 / Real.pi) * |Iint - M| := by
            rw [abs_mul, abs_of_pos (by positivity : 0 < (1 / Real.pi : ℝ))]
      _ ≤ (C / Real.pi) * Real.log T := hscaled
  have hleft :
      completedZetaRightGammaContribution T = (1 / Real.pi) * Iint := by
    have hT1 : 1 ≤ T := by linarith
    have hgamma_int : IntervalIntegrable
        (fun y : ℝ =>
          (-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
            (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2))
        volume 1 T :=
      (continuousOn_const.add
        (continuousOn_const.mul (rightEdge_gamma_logDeriv_continuousOn T hT1))).intervalIntegrable_of_Icc hT1
    have hre :
        Iint =
          (∫ y in (1 : ℝ)..T,
            ((-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
              (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2))).re :=
      Complex.reCLM.intervalIntegral_comp_comm hgamma_int
    unfold completedZetaRightGammaContribution Iint
    rw [← hre]
  calc
    |completedZetaRightGammaContribution T -
        ((1 / Real.pi) *
          ((T / 2) * Real.log (T / 2) - T / 2 -
            ((T - 1) / 2) * Real.log Real.pi +
            (Real.log 2 + 1) / 2))|
        = |(1 / Real.pi) * Iint - ((1 / Real.pi) * M)| := by
            rw [hleft]
    _ ≤ (C / Real.pi) * Real.log T := hfinal

/-- Exact relaxed-constant theorem for `completedZetaRightGammaContribution`
    in the current main-term normalization. -/
theorem completedZetaRightGammaContribution_main_term_bound_relaxed_exact :
    ∃ C K : ℝ, ∀ T : ℝ, 14 ≤ T →
      |completedZetaRightGammaContribution T -
        (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
            - (T / (2 * Real.pi)) * Real.log Real.pi) + K)| ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := completedZetaRightGammaContribution_main_term_bound_relaxed
  refine ⟨C, ((Real.log 2 + 1) / (2 * Real.pi)) + (Real.log Real.pi) / (2 * Real.pi), ?_⟩
  intro T hT
  have hmain :
      (1 / Real.pi) *
          ((T / 2) * Real.log (T / 2) - T / 2 -
            ((T - 1) / 2) * Real.log Real.pi +
            (Real.log 2 + 1) / 2)
        =
      (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
          - (T / (2 * Real.pi)) * Real.log Real.pi) +
        ((Real.log 2 + 1) / (2 * Real.pi)) + (Real.log Real.pi) / (2 * Real.pi)) := by
    field_simp [Real.pi_ne_zero]
    ring_nf
  have hC' := hC T hT
  convert hC' using 1 <;> rw [hmain] <;> ring_nf

/-- Honest smaller boundary for the combined completed-half-top contribution
    alone. Together with any relaxed-constant right-edge `Gammaℝ` main-term
    theorem for `completedZetaRightGammaContribution`, this recovers the
    bundled contour boundary below. -/
class RvmCompletedHalfTopVariationBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)| ≤ C * Real.log T

/-- Reduced completed-half-top leaf after separating off the right-edge
    `Gammaℝ` main term. -/
private theorem rvm_completedHalfTopVariation_bound
    [RvmCompletedHalfTopVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)| ≤ C * Real.log T := by
  exact RvmCompletedHalfTopVariationBoundHyp.bound

/-- A horizontal primitive of `completedRiemannZeta`'s logarithmic derivative
    with `O(log T)` endpoint variation on the half-top segment is enough to
    discharge `RvmCompletedHalfTopVariationBoundHyp`. -/
private theorem rvmCompletedHalfTopVariationBoundHyp_of_endpoint_primitive_bound
    [ZeroOrdinateLowerBoundHyp]
    (hPrimitive :
      ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
        ∃ F : ℝ → ℂ,
          ContinuousOn F (Set.Icc (1 / 2 : ℝ) 2) ∧
          (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
            HasDerivAt F
              (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) x) ∧
          ‖F 2 - F (1 / 2)‖ ≤ C * Real.log T) :
    RvmCompletedHalfTopVariationBoundHyp := by
  refine ⟨?_⟩
  obtain ⟨C, hC⟩ := hPrimitive
  refine ⟨C / Real.pi, ?_⟩
  intro T hT hT_not_ord
  obtain ⟨F, hFcont, hFderiv, hFbound⟩ := hC T hT hT_not_ord
  let f : ℝ → ℂ := fun x =>
    logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)
  have hf_cont : ContinuousOn f (Set.Icc (1 / 2 : ℝ) 2) := by
    refine (completedZeta_top_continuousOn T hT hT_not_ord).mono ?_
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hf_int : IntervalIntegrable f volume (1 / 2) 2 :=
    hf_cont.intervalIntegrable_of_Icc (by norm_num)
  have hFTC :
      ∫ x in (1 / 2 : ℝ)..2, f x = F 2 - F (1 / 2) := by
    exact
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hFderiv x (by
          rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
          exact hx))
        hf_int
  have him :
      ∫ x in (1 / 2 : ℝ)..2, (f x).im = (F 2 - F (1 / 2)).im := by
    calc
      ∫ x in (1 / 2 : ℝ)..2, (f x).im = (∫ x in (1 / 2 : ℝ)..2, f x).im := by
          simpa [f] using Complex.imCLM.intervalIntegral_comp_comm hf_int
      _ = (F 2 - F (1 / 2)).im := by rw [hFTC]
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  calc
    |-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)|
        = |-(1 / Real.pi) * (F 2 - F (1 / 2)).im| := by
            rw [show (∫ x in (1 / 2 : ℝ)..2,
                (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) =
                  ∫ x in (1 / 2 : ℝ)..2, (f x).im by rfl,
              him]
    _ = (1 / Real.pi) * |(F 2 - F (1 / 2)).im| := by
          rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
    _ ≤ (1 / Real.pi) * ‖F 2 - F (1 / 2)‖ := by
          gcongr
          exact Complex.abs_im_le_norm _
    _ ≤ (1 / Real.pi) * (C * Real.log T) := by
          gcongr
    _ = (C / Real.pi) * Real.log T := by
          ring

/-- Minimal completed-half-top boundary now exposed in the RvM lane: a
    horizontal primitive of `logDeriv completedRiemannZeta` on the half-top
    segment with `O(log T)` endpoint variation. -/
class RvmCompletedHalfTopEndpointPrimitiveBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      ∃ F : ℝ → ℂ,
        ContinuousOn F (Set.Icc (1 / 2 : ℝ) 2) ∧
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
          HasDerivAt F
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) x) ∧
        ‖F 2 - F (1 / 2)‖ ≤ C * Real.log T

/-- Honest smaller completed-half-top boundary: only the imaginary part of
    the endpoint variation is controlled. This is the theorem-first surface the
    downstream contour recombination actually consumes. -/
class RvmCompletedHalfTopEndpointPrimitiveImBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      ∃ F : ℝ → ℂ,
        ContinuousOn F (Set.Icc (1 / 2 : ℝ) 2) ∧
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
          HasDerivAt F
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) x) ∧
        |(F 2 - F (1 / 2)).im| ≤ C * Real.log T

/-- Reduced completed-half-top endpoint-primitive leaf. -/
private theorem rvm_completedHalfTop_endpoint_primitive_bound
    [RvmCompletedHalfTopEndpointPrimitiveBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      ∃ F : ℝ → ℂ,
        ContinuousOn F (Set.Icc (1 / 2 : ℝ) 2) ∧
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
          HasDerivAt F
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) x) ∧
        ‖F 2 - F (1 / 2)‖ ≤ C * Real.log T := by
  exact RvmCompletedHalfTopEndpointPrimitiveBoundHyp.bound

/-- The im-part endpoint primitive bound implies the completed half-top
    variation bound, which is the actual active downstream surface. -/
private theorem rvmCompletedHalfTopVariationBoundHyp_of_endpoint_primitive_im_bound
    [ZeroOrdinateLowerBoundHyp]
    (hPrimitive :
      ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
        ∃ F : ℝ → ℂ,
          ContinuousOn F (Set.Icc (1 / 2 : ℝ) 2) ∧
          (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
            HasDerivAt F
              (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)) x) ∧
          |(F 2 - F (1 / 2)).im| ≤ C * Real.log T) :
    RvmCompletedHalfTopVariationBoundHyp := by
  refine ⟨?_⟩
  obtain ⟨C, hC⟩ := hPrimitive
  refine ⟨C / Real.pi, ?_⟩
  intro T hT hT_not_ord
  obtain ⟨F, hFcont, hFderiv, hFbound⟩ := hC T hT hT_not_ord
  let f : ℝ → ℂ := fun x =>
    logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)
  have hf_cont : ContinuousOn f (Set.Icc (1 / 2 : ℝ) 2) := by
    refine (completedZeta_top_continuousOn T hT hT_not_ord).mono ?_
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hf_int : IntervalIntegrable f volume (1 / 2) 2 :=
    hf_cont.intervalIntegrable_of_Icc (by norm_num)
  have hFTC :
      ∫ x in (1 / 2 : ℝ)..2, f x = F 2 - F (1 / 2) := by
    exact
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hFderiv x (by
          rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
          exact hx))
        hf_int
  have him :
      ∫ x in (1 / 2 : ℝ)..2, (f x).im = (F 2 - F (1 / 2)).im := by
    calc
      ∫ x in (1 / 2 : ℝ)..2, (f x).im = (∫ x in (1 / 2 : ℝ)..2, f x).im := by
          simpa [f] using Complex.imCLM.intervalIntegral_comp_comm hf_int
      _ = (F 2 - F (1 / 2)).im := by rw [hFTC]
  calc
    |-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)|
        = |-(1 / Real.pi) * (F 2 - F (1 / 2)).im| := by
            rw [show (∫ x in (1 / 2 : ℝ)..2,
                (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) =
                  ∫ x in (1 / 2 : ℝ)..2, (f x).im by rfl,
              him]
    _ = (1 / Real.pi) * |(F 2 - F (1 / 2)).im| := by
          rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
    _ ≤ (1 / Real.pi) * (C * Real.log T) := by
          gcongr
    _ = (C / Real.pi) * Real.log T := by
          ring

/-- The im-part endpoint primitive class directly discharges the completed
    half-top variation bound. -/
instance (priority := 100)
    [ZeroOrdinateLowerBoundHyp] [RvmCompletedHalfTopEndpointPrimitiveImBoundHyp] :
    RvmCompletedHalfTopVariationBoundHyp := by
  exact
    rvmCompletedHalfTopVariationBoundHyp_of_endpoint_primitive_im_bound
      RvmCompletedHalfTopEndpointPrimitiveImBoundHyp.bound

/-- Honest bundled boundary for the combined completed-half-top contribution
    and right-edge `Gammaℝ` term after subtracting the explicit Stirling main
    term. This remains the internal downstream wrapper, but the theorem-first
    boundary in this file has been reduced further to
    `RvmCompletedHalfTopVariationBoundHyp` and
    `RvmGammaRLogRightEdgeRelaxedMainTermBoundHyp`. -/
class RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp : Prop where
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) +
          completedZetaRightGammaContribution T)
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi)| ≤ C * Real.log T

/-- A relaxed-constant right-edge `Gammaℝ` main-term theorem is enough to turn
    a pure completed-half-top `O(log T)` bound into the bundled completed-top
    plus right-edge Gamma comparison used downstream. -/
private theorem
    rvmCompletedHalfTopPlusRightGammaMainTermBoundHyp_of_completedHalfTopVariation_and_rightGamma_relaxed_main_term_bound
    [RvmCompletedHalfTopVariationBoundHyp]
    (hRightGamma :
      ∃ Cg K : ℝ, ∀ T : ℝ, 14 ≤ T →
        |completedZetaRightGammaContribution T
          - (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
              - (T / (2 * Real.pi)) * Real.log Real.pi) + K)| ≤ Cg * Real.log T) :
    RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp := by
  refine ⟨?_⟩
  obtain ⟨Cc, hCc⟩ := rvm_completedHalfTopVariation_bound
  obtain ⟨Cg, K, hCg⟩ := hRightGamma
  have hlog14_pos : 0 < Real.log 14 := Real.log_pos (by norm_num : (1 : ℝ) < 14)
  refine ⟨Cc + Cg + |K + 1 / 8| / Real.log 14, ?_⟩
  intro T hT hT_not_ord
  let completedTerm : ℝ :=
    -(1 / Real.pi) *
      (∫ x in (1 / 2 : ℝ)..2,
        (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
  let baseTerm : ℝ :=
    (1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
      - (T / (2 * Real.pi)) * Real.log Real.pi
  let gammaErr : ℝ :=
    completedZetaRightGammaContribution T - (baseTerm + K)
  let mainTerm : ℝ :=
    (1 / Real.pi) *
        ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
      - (T / (2 * Real.pi)) * Real.log Real.pi
  have hmain : mainTerm = baseTerm - 1 / 8 := by
    dsimp [mainTerm, baseTerm]
    field_simp [Real.pi_ne_zero]
    ring
  have hsplit :
      (completedTerm + completedZetaRightGammaContribution T) - mainTerm
        = completedTerm + gammaErr + (K + 1 / 8) := by
    rw [hmain]
    dsimp [gammaErr]
    ring
  have hcompleted : |completedTerm| ≤ Cc * Real.log T := hCc T hT hT_not_ord
  have hgamma : |gammaErr| ≤ Cg * Real.log T := by
    simpa [gammaErr, baseTerm] using hCg T hT
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hK_absorb : |K + 1 / 8| ≤ (|K + 1 / 8| / Real.log 14) * Real.log T := by
    calc
      |K + 1 / 8| = (|K + 1 / 8| / Real.log 14) * Real.log 14 := by
          field_simp [ne_of_gt hlog14_pos]
      _ ≤ (|K + 1 / 8| / Real.log 14) * Real.log T := by
          gcongr
  calc
    |(completedTerm + completedZetaRightGammaContribution T) - mainTerm|
        = |completedTerm + gammaErr + (K + 1 / 8)| := by rw [hsplit]
    _ ≤ |completedTerm + gammaErr| + |K + 1 / 8| := by
          simpa [add_assoc] using abs_add_le (completedTerm + gammaErr) (K + 1 / 8)
    _ ≤ (|completedTerm| + |gammaErr|) + |K + 1 / 8| := by
          linarith [abs_add_le completedTerm gammaErr]
    _ ≤ Cc * Real.log T + Cg * Real.log T + |K + 1 / 8| := by
          linarith
    _ ≤ Cc * Real.log T + Cg * Real.log T
          + (|K + 1 / 8| / Real.log 14) * Real.log T := by
            gcongr
    _ = (Cc + Cg + |K + 1 / 8| / Real.log 14) * Real.log T := by
          ring

/-- Minimal right-edge Gamma boundary now exposed in the RvM lane: a
    relaxed-constant asymptotic for `gammaRLog` on the line `Re(s)=2`. -/
class RvmGammaRLogRightEdgeRelaxedMainTermBoundHyp : Prop where
  bound :
    ∃ C K : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) * (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im
        - (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
            - (T / (2 * Real.pi)) * Real.log Real.pi) + K)| ≤ C * Real.log T

/-- The direct right-edge `Gammaℝ` main-term theorem already implies the
    reduced `gammaRLog` endpoint asymptotic on `Re(s)=2`. -/
private theorem
    gammaRLog_right_edge_relaxed_main_term_bound_of_completedZetaRightGammaContribution_relaxed_main_term :
    ∃ C K : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) * (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im
        - (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
            - (T / (2 * Real.pi)) * Real.log Real.pi) + K)| ≤ C * Real.log T := by
  obtain ⟨C, K, hK⟩ := completedZetaRightGammaContribution_main_term_bound_relaxed_exact
  refine ⟨C, K + (1 / Real.pi) * (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im, ?_⟩
  intro T hT
  calc
    |(1 / Real.pi) * (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im
        - (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
            - (T / (2 * Real.pi)) * Real.log Real.pi) +
            (K + (1 / Real.pi) * (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im))|
        =
      |completedZetaRightGammaContribution T
        - (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
            - (T / (2 * Real.pi)) * Real.log Real.pi) + K)| := by
            rw [completedZetaRightGammaContribution_eq_gammaRLog_right_edge_endpoint T hT]
            ring
    _ ≤ C * Real.log T := hK T hT

instance (priority := 100) : RvmGammaRLogRightEdgeRelaxedMainTermBoundHyp where
  bound := gammaRLog_right_edge_relaxed_main_term_bound_of_completedZetaRightGammaContribution_relaxed_main_term

/-- Reduced right-edge `gammaRLog` leaf. -/
private theorem rvm_gammaRLog_right_edge_relaxed_main_term_bound
    [RvmGammaRLogRightEdgeRelaxedMainTermBoundHyp] :
    ∃ C K : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) * (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im
        - (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
            - (T / (2 * Real.pi)) * Real.log Real.pi) + K)| ≤ C * Real.log T := by
  exact RvmGammaRLogRightEdgeRelaxedMainTermBoundHyp.bound

/-- Canonical right-edge `gammaRLog` asymptotics along `Re(s)=2` imply the
    relaxed-constant theorem for `completedZetaRightGammaContribution`. -/
private theorem
    completedZetaRightGammaContribution_relaxed_main_term_bound_of_gammaRLog_right_edge_relaxed_main_term
    [RvmGammaRLogRightEdgeRelaxedMainTermBoundHyp] :
    ∃ Cg Kg : ℝ, ∀ T : ℝ, 14 ≤ T →
      |completedZetaRightGammaContribution T
        - (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
            - (T / (2 * Real.pi)) * Real.log Real.pi) + Kg)| ≤ Cg * Real.log T := by
  obtain ⟨C, K, hK⟩ := rvm_gammaRLog_right_edge_relaxed_main_term_bound
  refine ⟨C, K - (1 / Real.pi) * (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im, ?_⟩
  intro T hT
  calc
    |completedZetaRightGammaContribution T
        - (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
            - (T / (2 * Real.pi)) * Real.log Real.pi) +
            (K - (1 / Real.pi) * (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im))|
        =
      |(1 / Real.pi) * (gammaRLog ((2 : ℂ) + (↑T : ℂ) * I)).im
        - (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
            - (T / (2 * Real.pi)) * Real.log Real.pi) + K)| := by
            rw [completedZetaRightGammaContribution_eq_gammaRLog_right_edge_endpoint T hT]
            ring
    _ ≤ C * Real.log T := hK T hT

/-- The sharper theorem-first surface on the right edge is a relaxed-constant
    `gammaRLog` asymptotic on `Re(s)=2`; combined with the pure completed-half-
    top boundary, it recovers the current bundled completed-top/right-Gamma
    surface. -/
private theorem
    rvmCompletedHalfTopPlusRightGammaMainTermBoundHyp_of_completedHalfTopEndpointPrimitive_and_gammaRLog_right_edge_relaxed_main_term
    [ZeroOrdinateLowerBoundHyp]
    [RvmCompletedHalfTopEndpointPrimitiveBoundHyp]
    [RvmGammaRLogRightEdgeRelaxedMainTermBoundHyp] :
    RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp := by
  letI : RvmCompletedHalfTopVariationBoundHyp :=
    rvmCompletedHalfTopVariationBoundHyp_of_endpoint_primitive_bound
      rvm_completedHalfTop_endpoint_primitive_bound
  exact
    rvmCompletedHalfTopPlusRightGammaMainTermBoundHyp_of_completedHalfTopVariation_and_rightGamma_relaxed_main_term_bound
      completedZetaRightGammaContribution_relaxed_main_term_bound_of_gammaRLog_right_edge_relaxed_main_term

private theorem
    rvmCompletedHalfTopPlusRightGammaMainTermBoundHyp_of_completedHalfTopVariation_and_gammaRLog_right_edge_relaxed_main_term
    [RvmCompletedHalfTopVariationBoundHyp]
    [RvmGammaRLogRightEdgeRelaxedMainTermBoundHyp] :
    RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp := by
  exact
    rvmCompletedHalfTopPlusRightGammaMainTermBoundHyp_of_completedHalfTopVariation_and_rightGamma_relaxed_main_term_bound
      completedZetaRightGammaContribution_relaxed_main_term_bound_of_gammaRLog_right_edge_relaxed_main_term

instance (priority := 100)
    [RvmCompletedHalfTopVariationBoundHyp]
    [RvmGammaRLogRightEdgeRelaxedMainTermBoundHyp] :
    RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp := by
  exact
    rvmCompletedHalfTopPlusRightGammaMainTermBoundHyp_of_completedHalfTopVariation_and_gammaRLog_right_edge_relaxed_main_term

/-- Reduced combined main-term leaf after eliminating the half-top `ζ`
    contribution in favor of the completed half-top term. -/
private theorem rvm_completedHalfTopPlusRightGamma_main_term_bound
    [RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) +
          completedZetaRightGammaContribution T)
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi)| ≤ C * Real.log T := by
  exact RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp.bound

/-- If both the combined completed-half-top/right-`Gammaℝ` term and the
    `gammaRLog` endpoint term satisfy matching `O(log T)` main-term
    comparisons, then the isolated half-top `ζ` variation does as well. -/
private theorem rvmHalfTopZetaVariationBoundHyp_of_mainTerm_comparison_bounds
    [ZeroOrdinateLowerBoundHyp]
    (hCompleted :
      ∃ Cc : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
        |(-(1 / Real.pi) *
            (∫ x in (1 / 2 : ℝ)..2,
              (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) +
            completedZetaRightGammaContribution T)
          - ((1 / Real.pi) *
                ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
             - (T / (2 * Real.pi)) * Real.log Real.pi)| ≤ Cc * Real.log T)
    (hGamma :
      ∃ Cg : ℝ, ∀ T : ℝ, 14 ≤ T →
        |(1 / Real.pi) *
            ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
              (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im)
          - ((1 / Real.pi) *
                ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
             - (T / (2 * Real.pi)) * Real.log Real.pi)| ≤ Cg * Real.log T) :
    RvmHalfTopZetaVariationBoundHyp := by
  refine ⟨?_⟩
  obtain ⟨Cc, hCc⟩ := hCompleted
  obtain ⟨Cg, hCg⟩ := hGamma
  refine ⟨Cc + Cg, ?_⟩
  intro T hT hT_not_ord
  let zetaTerm : ℝ :=
    -(1 / Real.pi) *
      (∫ x in (1 / 2 : ℝ)..2,
        (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
  let mainTerm : ℝ :=
    (1 / Real.pi) *
        ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
      - (T / (2 * Real.pi)) * Real.log Real.pi
  let completedErr : ℝ :=
    (-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) +
        completedZetaRightGammaContribution T) - mainTerm
  let gammaErr : ℝ :=
    (1 / Real.pi) *
      ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
        (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) - mainTerm
  have hsplit : zetaTerm = completedErr - gammaErr := by
    dsimp [zetaTerm, completedErr, gammaErr, mainTerm]
    rw [halfTopZeta_eq_completedHalfTopPlusRightGamma_sub_gammaRLog_endpoint T hT hT_not_ord]
    ring
  calc
    |zetaTerm| = |completedErr - gammaErr| := by rw [hsplit]
    _ ≤ |completedErr| + |gammaErr| := by
          simpa [sub_eq_add_neg] using abs_add_le completedErr (-gammaErr)
    _ ≤ Cc * Real.log T + Cg * Real.log T := by
          linarith [hCc T hT hT_not_ord, hCg T hT]
    _ = (Cc + Cg) * Real.log T := by
          ring

/-- The already-proved `gammaRLog` endpoint/main-term comparison combines with
    any matching `O(log T)` bound on the completed half-top plus right-edge
    `Gammaℝ` term to produce `RvmHalfTopZetaVariationBoundHyp`. -/
private theorem rvmHalfTopZetaVariationBoundHyp_of_completedHalfTopPlusRightGamma_main_term_bound
    [ZeroOrdinateLowerBoundHyp]
    (hCompleted :
      ∃ Cc : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
        |(-(1 / Real.pi) *
            (∫ x in (1 / 2 : ℝ)..2,
              (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im) +
            completedZetaRightGammaContribution T)
          - ((1 / Real.pi) *
                ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
             - (T / (2 * Real.pi)) * Real.log Real.pi)| ≤ Cc * Real.log T) :
    RvmHalfTopZetaVariationBoundHyp := by
  exact
    rvmHalfTopZetaVariationBoundHyp_of_mainTerm_comparison_bounds
      hCompleted rvm_gammaRLog_endpoint_main_term_bound

instance (priority := 100) [ZeroOrdinateLowerBoundHyp]
    [RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp] :
    RvmHalfTopZetaVariationBoundHyp := by
  exact
    rvmHalfTopZetaVariationBoundHyp_of_completedHalfTopPlusRightGamma_main_term_bound
      rvm_completedHalfTopPlusRightGamma_main_term_bound

/-- Minimal half-top/right-edge wrapper that keeps the current theorem-first
    boundary exposed only through the endpoint primitive plus the relaxed right-
    edge `gammaRLog` theorem. -/
private theorem
    rvmCompletedHalfTopPlusRightGammaMainTermBoundHyp_of_completedHalfTopEndpointPrimitive_and_rightGamma_relaxed_main_term_bound
    [ZeroOrdinateLowerBoundHyp]
    [RvmCompletedHalfTopEndpointPrimitiveImBoundHyp]
    (hRightGamma :
      ∃ Cg K : ℝ, ∀ T : ℝ, 14 ≤ T →
        |completedZetaRightGammaContribution T
          - (((1 / Real.pi) * ((T / 2) * Real.log (T / 2) - T / 2)
              - (T / (2 * Real.pi)) * Real.log Real.pi) + K)| ≤ Cg * Real.log T) :
    RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp := by
  letI : RvmCompletedHalfTopVariationBoundHyp := by infer_instance
  exact
    rvmCompletedHalfTopPlusRightGammaMainTermBoundHyp_of_completedHalfTopVariation_and_rightGamma_relaxed_main_term_bound
      hRightGamma

/-- The two theorem-first surfaces now exposed in the file already recover the
    half-top `ζ` variation boundary: a primitive with `O(log T)` endpoint
    variation for the completed half-top term, and a relaxed-constant
    `gammaRLog` asymptotic on the right edge. -/
private theorem
    rvmHalfTopZetaVariationBoundHyp_of_completedHalfTopEndpointPrimitive_and_gammaRLog_right_edge_relaxed_main_term
    [ZeroOrdinateLowerBoundHyp]
    [RvmCompletedHalfTopEndpointPrimitiveImBoundHyp]
    [RvmGammaRLogRightEdgeRelaxedMainTermBoundHyp] :
    RvmHalfTopZetaVariationBoundHyp := by
  letI : RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp := by
    infer_instance
  exact
    rvmHalfTopZetaVariationBoundHyp_of_completedHalfTopPlusRightGamma_main_term_bound
      rvm_completedHalfTopPlusRightGamma_main_term_bound

/-- The direct right-edge theorem now also supports the half-top zeta
    variation boundary without routing through the `gammaRLog` class. -/
private theorem
    rvmHalfTopZetaVariationBoundHyp_of_completedHalfTopEndpointPrimitive_and_completedZetaRightGamma_relaxed_main_term
    [ZeroOrdinateLowerBoundHyp]
    [RvmCompletedHalfTopEndpointPrimitiveImBoundHyp] :
    RvmHalfTopZetaVariationBoundHyp := by
  letI : RvmCompletedHalfTopPlusRightGammaMainTermBoundHyp := by
    infer_instance
  exact
    rvmHalfTopZetaVariationBoundHyp_of_completedHalfTopPlusRightGamma_main_term_bound
      rvm_completedHalfTopPlusRightGamma_main_term_bound

/-- Reduced contour leaf after removing the exact `Gammaℝ` contour piece.
    The remaining blockers are now separated into the half-top zeta branch
    variation and the `gammaRLog` endpoint/main-term comparison. -/
private theorem rvm_half_top_zeta_plus_gammaRLog_endpoint_main_term_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
        + (1 / Real.pi) *
            ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
              (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im)
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi)| ≤ C * Real.log T := by
  obtain ⟨Czeta, hzeta⟩ := rvm_half_top_zeta_variation_bound
  obtain ⟨Cgamma, hgamma⟩ := rvm_gammaRLog_endpoint_main_term_bound
  refine ⟨Czeta + Cgamma, ?_⟩
  intro T hT hT_not_ord
  let zetaErr : ℝ :=
    -(1 / Real.pi) *
      (∫ x in (1 / 2 : ℝ)..2,
        (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
  let gammaErr : ℝ :=
    (1 / Real.pi) *
      ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
        (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im)
      - ((1 / Real.pi) *
            ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
          - (T / (2 * Real.pi)) * Real.log Real.pi)
  have hsplit :
      -(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
        + (1 / Real.pi) *
            ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
              (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im)
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi)
      = zetaErr + gammaErr := by
    simp [zetaErr, gammaErr]
    ring
  calc
    |-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
      + (1 / Real.pi) *
          ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
            (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im)
      - ((1 / Real.pi) *
            ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
         - (T / (2 * Real.pi)) * Real.log Real.pi)|
        = |zetaErr + gammaErr| := by rw [hsplit]
    _ ≤ |zetaErr| + |gammaErr| := abs_add_le _ _
    _ ≤ Czeta * Real.log T + Cgamma * Real.log T := by
          gcongr
          · exact hzeta T hT hT_not_ord
          · exact hgamma T hT
    _ = (Czeta + Cgamma) * Real.log T := by ring

/-- Smaller contour leaf after folding the top edge to the half-top segment
    `[1/2, 2]`. The remaining blocker is now a branch-safe argument-variation
    statement on this half-top segment together with the right-edge Gamma term. -/
private theorem rvm_completedZeta_half_top_plus_gamma_right_edge_core_main_term_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
        + completedZetaRightGammaContribution T
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi)| ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := rvm_half_top_zeta_plus_gammaRLog_endpoint_main_term_bound
  refine ⟨C, ?_⟩
  intro T hT hT_not_ord
  have hsplit :=
    completedZetaHalfTopContribution_eq_gamma_plus_zeta T hT hT_not_ord
  have hgamma :=
    halfTopGammaPlusRightEdgeGamma_eq_gammaRLog_endpoint T hT
  let Z : ℝ :=
    -(1 / Real.pi) *
      (∫ x in (1 / 2 : ℝ)..2,
        (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
  let G : ℝ :=
    -(1 / Real.pi) *
      (∫ x in (1 / 2 : ℝ)..2,
        (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im)
  let M : ℝ :=
    ((1 / Real.pi) *
        ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
      - (T / (2 * Real.pi)) * Real.log Real.pi)
  have hrearrange1 :
      (G + Z) + completedZetaRightGammaContribution T - M =
        Z + ((G + completedZetaRightGammaContribution T) - M) := by
    dsimp [G, Z, M]
    ring
  have hrearrange2 :
      Z + ((1 / Real.pi) *
            ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
              (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) - M)
        =
      Z + (1 / Real.pi) *
            ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
              (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) - M := by
    dsimp [Z, M]
    ring
  calc
    |-(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv completedRiemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
      + completedZetaRightGammaContribution T
      - ((1 / Real.pi) *
            ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
         - (T / (2 * Real.pi)) * Real.log Real.pi)|
        =
      |((-(1 / Real.pi) *
            (∫ x in (1 / 2 : ℝ)..2,
              (logDeriv Gammaℝ ((↑x : ℂ) + (↑T : ℂ) * I)).im)) +
          (-(1 / Real.pi) *
            (∫ x in (1 / 2 : ℝ)..2,
              (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im))) +
          completedZetaRightGammaContribution T
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi)| := by
            rw [hsplit]
    _ =
      |Z + ((G + completedZetaRightGammaContribution T) - M)| := by
            rw [hrearrange1]
    _ =
      |Z + ((1 / Real.pi) *
            ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
              (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im) - M)| := by
            rw [hgamma]
    _ =
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv riemannZeta ((↑x : ℂ) + (↑T : ℂ) * I)).im)
        + (1 / Real.pi) *
            ((gammaRLog ((1 / 2 : ℂ) + (↑T : ℂ) * I)).im -
              (gammaRLog ((2 : ℂ) + (1 : ℂ) * I)).im)
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi)| := by
            rw [hrearrange2]
    _ ≤ C * Real.log T := hC T hT hT_not_ord

/-- Smaller contour leaf after peeling off the bounded right-edge ζ term,
    the bounded critical-line argument term, and the constant `1`. -/
private theorem rvm_completedZeta_top_plus_gamma_right_edge_core_main_term_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(completedZetaTopContribution T).re
        + completedZetaRightGammaContribution T
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi)| ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := rvm_completedZeta_half_top_plus_gamma_right_edge_core_main_term_bound
  refine ⟨C, ?_⟩
  intro T hT hT_not_ord
  rw [completedZetaTopContribution_re_eq_half_top_imIntegral T hT hT_not_ord]
  simpa using hC T hT hT_not_ord

/-- Wrapper restoring the bounded critical-line argument term and constant `1`
    on top of the smaller Gamma-plus-top-edge main-term leaf. -/
private theorem rvm_completedZeta_top_plus_gamma_right_edge_main_term_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(completedZetaTopContribution T).re
        + completedZetaRightGammaContribution T
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨Ccore, hcore⟩ := rvm_completedZeta_top_plus_gamma_right_edge_core_main_term_bound
  have hlog14_pos : 0 < Real.log 14 := Real.log_pos (by norm_num : (1 : ℝ) < 14)
  have harg_one :
      ∀ T : ℝ, 14 ≤ T →
        |(1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T)) + 1|
          ≤ (2 / Real.log 14) * Real.log T := by
    intro T hT
    have harg :
        |(1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
      calc
        (1 / Real.pi) * |Complex.arg (riemannZeta (1 / 2 + I * ↑T))|
            ≤ (1 / Real.pi) * Real.pi := by
                gcongr
                exact Complex.abs_arg_le_pi _
        _ = 1 := by
              field_simp [Real.pi_ne_zero]
    have hbase :
        |(1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T)) + 1| ≤ 2 := by
      calc
        |(1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T)) + 1|
            ≤ |(1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))| + |1| := by
                simpa using
                  abs_add_le
                    ((1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))) 1
        _ ≤ 1 + 1 := by
              linarith
        _ = 2 := by ring
    have hlog_mono : Real.log 14 ≤ Real.log T :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 14) hT
    have hcoeff_nonneg : 0 ≤ 2 / Real.log 14 := by
      positivity
    calc
      |(1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T)) + 1|
          ≤ 2 := hbase
      _ = (2 / Real.log 14) * Real.log 14 := by
            field_simp [ne_of_gt hlog14_pos]
      _ ≤ (2 / Real.log 14) * Real.log T := by
            gcongr
  refine ⟨Ccore + 2 / Real.log 14, ?_⟩
  intro T hT hT_not_ord
  let coreErr : ℝ :=
    (completedZetaTopContribution T).re
      + completedZetaRightGammaContribution T
      - ((1 / Real.pi) *
            ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
         - (T / (2 * Real.pi)) * Real.log Real.pi)
  let argErr : ℝ :=
    (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T)) + 1
  have hsplit :
      (completedZetaTopContribution T).re
        + completedZetaRightGammaContribution T
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)
      = coreErr - argErr := by
    simp [coreErr, argErr]
    ring_nf
  have htriangle : |coreErr - argErr| ≤ |coreErr| + |argErr| := by
    calc
      |coreErr - argErr| = |coreErr + (-argErr)| := by ring_nf
      _ ≤ |coreErr| + |-argErr| := abs_add_le _ _
      _ = |coreErr| + |argErr| := by rw [abs_neg]
  calc
    |(completedZetaTopContribution T).re
        + completedZetaRightGammaContribution T
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)|
        = |coreErr - argErr| := by
            rw [hsplit]
    _ ≤ |coreErr| + |argErr| := htriangle
    _ ≤ Ccore * Real.log T + (2 / Real.log 14) * Real.log T := by
          linarith [hcore T hT hT_not_ord, harg_one T hT]
    _ = (Ccore + 2 / Real.log 14) * Real.log T := by
          ring

/-- Smaller contour leaf after peeling off the bounded right-edge ζ term and
    separating the proved Stirling-approximation replacement for the Gamma main
    term. -/
private theorem rvm_completedZeta_top_plus_gamma_right_edge_formula_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(completedZetaTopContribution T).re
        + completedZetaRightGammaContribution T
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨Cmain, hmain⟩ := rvm_completedZeta_top_plus_gamma_right_edge_main_term_bound
  have hstirling :
      (fun T : ℝ =>
        (1 / Real.pi) *
          ((stirlingApprox T).im -
            ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)))
        =O[atTop] (fun T : ℝ => Real.log T) :=
    (stirling_im_approx.const_mul_left (1 / Real.pi)).trans isBigO_inv_of_log
  obtain ⟨Cstir0, hCstir0⟩ := hstirling.bound
  obtain ⟨Tstir, hTstir_bound⟩ := Filter.eventually_atTop.mp hCstir0
  let B : ℝ := max 14 Tstir
  let stirErr : ℝ → ℝ := fun T =>
    (1 / Real.pi) *
      ((stirlingApprox T).im -
        ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8))
  have hstir_large : ∀ T : ℝ, B ≤ T → |stirErr T| ≤ Cstir0 * Real.log T := by
    intro T hT
    have hTstir : Tstir ≤ T := le_trans (le_max_right _ _) hT
    have hbound := hTstir_bound T hTstir
    have hlogT_nonneg : 0 ≤ Real.log T := by
      apply Real.log_nonneg
      have : (14 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
      linarith
    simpa [stirErr, Real.norm_eq_abs, abs_of_nonneg hlogT_nonneg] using hbound
  have hB_ge14 : 14 ≤ B := le_max_left _ _
  have hlog14_pos : 0 < Real.log 14 := Real.log_pos (by norm_num : (1 : ℝ) < 14)
  have hstir_cont :
      ContinuousOn stirErr (Set.Icc 14 B) := by
    have hmain_cont :
        ContinuousOn
          (fun T : ℝ => (T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
          (Set.Icc 14 B) := by
      have hlog :
          ContinuousOn (fun T : ℝ => Real.log (T / 2)) (Set.Icc 14 B) := by
        refine ContinuousOn.comp Real.continuousOn_log (continuousOn_id.div_const 2) ?_
        intro T hT
        have : 0 < T / 2 := by linarith [hT.1]
        exact ne_of_gt this
      exact ((continuousOn_id.div_const 2).mul hlog).sub
        (continuousOn_id.div_const 2) |>.sub continuousOn_const
    have hstir_im_cont_global : Continuous (fun t : ℝ => (stirlingApprox t).im) := by
      apply Complex.continuous_im.comp
      unfold stirlingApprox
      have hs : Continuous (fun t : ℝ => (1/4 : ℂ) + I * ↑t / 2) := by
        fun_prop
      have hlog : Continuous (fun t : ℝ => Complex.log ((1/4 : ℂ) + I * ↑t / 2)) := by
        apply Continuous.clog hs
        intro t
        left
        simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      exact ((hs.sub continuous_const).mul hlog).sub hs |>.add continuous_const
    have hstir_im_cont : ContinuousOn (fun T : ℝ => (stirlingApprox T).im) (Set.Icc 14 B) :=
      hstir_im_cont_global.continuousOn
    exact continuousOn_const.mul (hstir_im_cont.sub hmain_cont)
  obtain ⟨Mstir, hMstir⟩ := (isCompact_Icc : IsCompact (Set.Icc 14 B)).exists_bound_of_continuousOn hstir_cont
  let Cstir : ℝ := max Cstir0 (Mstir / Real.log 14)
  have hCstir_nonneg : 0 ≤ Cstir := by
    have h14bound : ‖stirErr 14‖ ≤ Mstir := hMstir 14 ⟨le_rfl, hB_ge14⟩
    have hMstir_nonneg : 0 ≤ Mstir := le_trans (norm_nonneg _) h14bound
    have hratio_nonneg : 0 ≤ Mstir / Real.log 14 := by
      exact div_nonneg hMstir_nonneg hlog14_pos.le
    exact le_trans hratio_nonneg (le_max_right _ _)
  have hstir_small : ∀ T : ℝ, 14 ≤ T → T ≤ B → |stirErr T| ≤ Cstir * Real.log T := by
    intro T hT hTB
    have habs : |stirErr T| ≤ Mstir := by
      simpa [Real.norm_eq_abs] using hMstir T ⟨hT, hTB⟩
    have hlog_mono : Real.log 14 ≤ Real.log T := Real.log_le_log (by norm_num : (0 : ℝ) < 14) hT
    have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have h14bound : ‖stirErr 14‖ ≤ Mstir := hMstir 14 ⟨le_rfl, hB_ge14⟩
    have hMstir_nonneg : 0 ≤ Mstir := le_trans (norm_nonneg _) h14bound
    have hratio_nonneg : 0 ≤ Mstir / Real.log 14 := by
      exact div_nonneg hMstir_nonneg hlog14_pos.le
    have hcoeff :
        Mstir ≤ (Mstir / Real.log 14) * Real.log T := by
      calc
        Mstir = (Mstir / Real.log 14) * Real.log 14 := by
          field_simp [ne_of_gt hlog14_pos]
        _ ≤ (Mstir / Real.log 14) * Real.log T := by
          exact mul_le_mul_of_nonneg_left hlog_mono hratio_nonneg
    calc
      |stirErr T| ≤ Mstir := habs
      _ ≤ (Mstir / Real.log 14) * Real.log T := hcoeff
      _ ≤ Cstir * Real.log T := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hlogT_nonneg
  have hstir_all : ∀ T : ℝ, 14 ≤ T → |stirErr T| ≤ Cstir * Real.log T := by
    intro T hT
    by_cases hTB : T ≤ B
    · exact hstir_small T hT hTB
    · have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      exact le_trans (hstir_large T (le_of_not_ge hTB))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hlogT_nonneg)
  refine ⟨Cmain + Cstir, ?_⟩
  intro T hT hT_not_ord
  have hsplit :
      (completedZetaTopContribution T).re
        + completedZetaRightGammaContribution T
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)
      =
      ((completedZetaTopContribution T).re
        + completedZetaRightGammaContribution T
        - ((1 / Real.pi) *
              ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1))
        - stirErr T := by
    simp [stirErr]
    ring
  calc
    |(completedZetaTopContribution T).re
        + completedZetaRightGammaContribution T
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)|
        = |((completedZetaTopContribution T).re
            + completedZetaRightGammaContribution T
            - ((1 / Real.pi) *
                  ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
               - (T / (2 * Real.pi)) * Real.log Real.pi
               + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
               + 1))
            - stirErr T| := by
            rw [hsplit]
    _ ≤ |(completedZetaTopContribution T).re
            + completedZetaRightGammaContribution T
            - ((1 / Real.pi) *
                  ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
               - (T / (2 * Real.pi)) * Real.log Real.pi
              + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
               + 1)| + |stirErr T| := by
          simpa [sub_eq_add_neg] using abs_add_le
            ((completedZetaTopContribution T).re
              + completedZetaRightGammaContribution T
              - ((1 / Real.pi) *
                    ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)
                 - (T / (2 * Real.pi)) * Real.log Real.pi
                 + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
                 + 1))
            (-stirErr T)
    _ ≤ Cmain * Real.log T + Cstir * Real.log T := by
          linarith [hmain T hT hT_not_ord, hstir_all T hT]
    _ = (Cmain + Cstir) * Real.log T := by ring

/-- Reduced contour leaf after eliminating the left edge by reflection. -/
private theorem rvm_completedZeta_top_plus_right_edge_formula_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(completedZetaTopContribution T).re
        + (1 / Real.pi) *
            (∫ y in (1 : ℝ)..T,
              logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨Ccore, hcore⟩ := rvm_completedZeta_top_plus_gamma_right_edge_formula_bound
  obtain ⟨Czeta, hzeta⟩ := completedZetaRightZetaContribution_bound
  refine ⟨Ccore + Czeta, ?_⟩
  intro T hT hT_not_ord
  have hright_int := completedZeta_right_intervalIntegrable T hT hT_not_ord
  have hright_re :
      ∫ y in (1 : ℝ)..T,
          (logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re =
        (∫ y in (1 : ℝ)..T,
          logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hright_int
    simp only [Complex.reCLM_apply] at this
    exact this
  have hsplit :
      (1 / Real.pi) *
        (∫ y in (1 : ℝ)..T,
          logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re =
      completedZetaRightGammaContribution T + completedZetaRightZetaContribution T := by
    rw [← hright_re]
    exact completedZetaRightContribution_eq_gamma_plus_zeta T hT
  have hsplit' :
      (completedZetaTopContribution T).re
        + (1 / Real.pi) *
            (∫ y in (1 : ℝ)..T,
              logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)
      =
      ((completedZetaTopContribution T).re
        + completedZetaRightGammaContribution T
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)) + completedZetaRightZetaContribution T := by
    let mainTerm : ℝ :=
      (1 / Real.pi) * (stirlingApprox T).im
        - (T / (2 * Real.pi)) * Real.log Real.pi
        + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
        + 1
    have hrewrite :
        (completedZetaTopContribution T).re
          + (1 / Real.pi) *
              (∫ y in (1 : ℝ)..T,
                logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re
          - mainTerm
        =
        (completedZetaTopContribution T).re
          + (completedZetaRightGammaContribution T + completedZetaRightZetaContribution T)
          - mainTerm := by
      exact congrArg (fun x =>
        (completedZetaTopContribution T).re + x - mainTerm) hsplit
    calc
      (completedZetaTopContribution T).re
          + (1 / Real.pi) *
              (∫ y in (1 : ℝ)..T,
                logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re
          - ((1 / Real.pi) * (stirlingApprox T).im
             - (T / (2 * Real.pi)) * Real.log Real.pi
             + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
             + 1)
          =
          (completedZetaTopContribution T).re
            + (completedZetaRightGammaContribution T + completedZetaRightZetaContribution T)
            - ((1 / Real.pi) * (stirlingApprox T).im
               - (T / (2 * Real.pi)) * Real.log Real.pi
               + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
               + 1) := by
            simpa [mainTerm] using hrewrite
      _ =
          ((completedZetaTopContribution T).re
            + completedZetaRightGammaContribution T
            - ((1 / Real.pi) * (stirlingApprox T).im
               - (T / (2 * Real.pi)) * Real.log Real.pi
               + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
               + 1)) + completedZetaRightZetaContribution T := by
            ring
  calc
    |(completedZetaTopContribution T).re
        + (1 / Real.pi) *
            (∫ y in (1 : ℝ)..T,
              logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)|
        = |((completedZetaTopContribution T).re
            + completedZetaRightGammaContribution T
            - ((1 / Real.pi) * (stirlingApprox T).im
               - (T / (2 * Real.pi)) * Real.log Real.pi
               + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
               + 1)) + completedZetaRightZetaContribution T| := by
            rw [hsplit']
    _ ≤ |(completedZetaTopContribution T).re
            + completedZetaRightGammaContribution T
            - ((1 / Real.pi) * (stirlingApprox T).im
               - (T / (2 * Real.pi)) * Real.log Real.pi
               + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
               + 1)| + |completedZetaRightZetaContribution T| := abs_add_le _ _
    _ ≤ Ccore * Real.log T + Czeta * Real.log T := by
          gcongr
          · exact hcore T hT hT_not_ord
          · exact hzeta T hT
    _ = (Ccore + Czeta) * Real.log T := by ring

/-- Smaller contour-evaluation leaf: after peeling off the fixed bottom edge,
    the remaining analytic content is the top/right/left boundary contribution. -/
private theorem rvm_completedZeta_upper_three_edges_formula_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(completedZetaUpperThreeContribution T).re
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := rvm_completedZeta_top_plus_right_edge_formula_bound
  refine ⟨C, ?_⟩
  intro T hT hT_not_ord
  have hsplit := congrArg Complex.re (completedZetaUpperThreeContribution_eq_top_add_side T)
  have hside := completedZetaSideContribution_re_eq_rightEdgeReal T hT hT_not_ord
  calc
    |(completedZetaUpperThreeContribution T).re
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)|
        = |(completedZetaTopContribution T).re
            + (1 / Real.pi) *
               (∫ y in (1 : ℝ)..T,
                  logDeriv completedRiemannZeta ((2 : ℂ) + (↑y : ℂ) * I)).re
            - ((1 / Real.pi) * (stirlingApprox T).im
               - (T / (2 * Real.pi)) * Real.log Real.pi
               + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
               + 1)| := by
            rw [hsplit, Complex.add_re, hside]
    _ ≤ C * Real.log T := hC T hT hT_not_ord

/-- Reduced contour-evaluation wrapper after removing the `RiemannXiAlt` pole
    terms by contour linearity and the fixed bottom-edge contribution. -/
private theorem rvm_completedZeta_logIntegralRect_formula_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(logIntegralRect completedRiemannZeta (-1) 2 1 T).re
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨Cbot, hbot⟩ := completedZeta_bottomContribution_bound
  obtain ⟨Ccore, hcore⟩ := rvm_completedZeta_upper_three_edges_formula_bound
  refine ⟨Cbot + Ccore, ?_⟩
  intro T hT hT_not_ord
  have hsplit :=
    congrArg Complex.re (logIntegralRect_completedZeta_eq_bottom_plus_upperThree T)
  calc
    |(logIntegralRect completedRiemannZeta (-1) 2 1 T).re
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)|
        = |completedZetaBottomContribution.re +
            ((completedZetaUpperThreeContribution T).re
              - ((1 / Real.pi) * (stirlingApprox T).im
                  - (T / (2 * Real.pi)) * Real.log Real.pi
                  + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
                  + 1))| := by
            rw [hsplit, Complex.add_re]
            ring
    _ ≤ |completedZetaBottomContribution.re| +
          |(completedZetaUpperThreeContribution T).re
              - ((1 / Real.pi) * (stirlingApprox T).im
                  - (T / (2 * Real.pi)) * Real.log Real.pi
                  + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
                  + 1)| := abs_add_le _ _
    _ ≤ Cbot * Real.log T + Ccore * Real.log T := by
          gcongr
          · exact hbot T hT
          · exact hcore T hT hT_not_ord
    _ = (Cbot + Ccore) * Real.log T := by ring

/-- The original xi-form contour statement is now a wrapper around the
    completed-zeta contour statement. -/
private theorem rvm_logIntegralRect_formula_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(logIntegralRect RiemannXiAlt (-1) 2 1 T).re
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := rvm_completedZeta_logIntegralRect_formula_bound
  refine ⟨C, ?_⟩
  intro T hT hT_not_ord
  have hEq := xi_logIntegralRect_eq_completedZeta T hT hT_not_ord
  calc
    |(logIntegralRect RiemannXiAlt (-1) 2 1 T).re
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)|
        = |(logIntegralRect completedRiemannZeta (-1) 2 1 T).re
            - ((1 / Real.pi) * (stirlingApprox T).im
               - (T / (2 * Real.pi)) * Real.log Real.pi
               + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
               + 1)| := by rw [hEq]
    _ ≤ C * Real.log T := hC T hT hT_not_ord

/-- The multiplicity-counted RvM decomposition at generic `T`.

    This now reduces to the completed-zeta contour-evaluation bound; the
    multiplicity-counted argument-principle bridge to `Nmult` and the xi-to-Λ
    contour linearity step are both proved locally above. -/
private theorem rvm_Nmult_formula_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(Nmult T : ℝ)
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := rvm_logIntegralRect_formula_bound
  refine ⟨C, ?_⟩
  intro T hT hT_not_ord
  have hlog := xi_logIntegralRect_eq_Nmult T hT hT_not_ord
  calc
    |(Nmult T : ℝ)
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)|
        = |(logIntegralRect RiemannXiAlt (-1) 2 1 T).re
            - ((1 / Real.pi) * (stirlingApprox T).im
               - (T / (2 * Real.pi)) * Real.log Real.pi
               + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
               + 1)| := by
            rw [hlog]
            simp
    _ ≤ C * Real.log T := hC T hT hT_not_ord

/-- Compatibility input reduced to the explicit `ξ'` rectangle zero-count
    boundary exposed in `DistinctMultiplicityCompatibility.lean`. -/
private theorem rvm_commonZeroMass_compatibility_input_bound
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  exact commonZeroMass_bound_of_xiDerivZeroCountRectMultBoundFrom14Hyp

/-- Reduced compatibility wrapper after moving the distinct-vs-multiplicity
    issue onto the exact common-zero multiplicity sum. -/
private theorem rvm_distinct_mult_compatibility_bound
    [ZeroOrdinateLowerBoundHyp] [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(N T : ℝ) - (Nmult T : ℝ)| ≤ C * Real.log T := by
  exact (distinct_mult_compatibility_bound_iff_commonZeroMass_bound 14).2
    rvm_commonZeroMass_compatibility_input_bound

/-- The legacy distinct-count RvM decomposition is now a compatibility wrapper
    around the multiplicity-counted lane plus the `N` versus `Nmult` error term.

    Reference: Titchmarsh §9.3-9.4, Montgomery-Vaughan Theorem 14.5. -/
private theorem rvm_N_formula_bound
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp]
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(N T : ℝ)
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨Cmult, hmult⟩ := rvm_Nmult_formula_bound
  obtain ⟨Ccompat, hcompat⟩ := rvm_distinct_mult_compatibility_bound
  refine ⟨Cmult + Ccompat, ?_⟩
  intro T hT hT_not_ord
  have hmultT := hmult T hT hT_not_ord
  have hcompatT := hcompat T hT
  have hlog_nonneg : 0 ≤ Real.log T := le_of_lt (Real.log_pos (by linarith))
  calc
    |(N T : ℝ)
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
           + 1)|
        = |((N T : ℝ) - (Nmult T : ℝ)) +
            ((Nmult T : ℝ)
              - ((1 / Real.pi) * (stirlingApprox T).im
                 - (T / (2 * Real.pi)) * Real.log Real.pi
                 + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
                 + 1))| := by ring
    _ ≤ |(N T : ℝ) - (Nmult T : ℝ)| +
          |(Nmult T : ℝ)
            - ((1 / Real.pi) * (stirlingApprox T).im
               - (T / (2 * Real.pi)) * Real.log Real.pi
               + (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + I * ↑T))
               + 1)| := abs_add_le _ _
    _ ≤ Ccompat * Real.log T + Cmult * Real.log T := by linarith
    _ = (Cmult + Ccompat) * Real.log T := by ring

/-! ### Assembly: Combining argument principle with contour evaluation -/

/-- For T ≥ 14 not a zero ordinate, N(T) equals the RvM expression up to O(log T).
    Proof: directly from `rvm_N_formula_bound`. -/
private theorem rvm_at_generic_T
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp]
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(N T : ℝ)
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  exact rvm_N_formula_bound

/-- For any T and ε > 0, there exists T' ∈ (T, T+ε) not a zero ordinate,
    with no zero ordinate in (T, T'] (so N(T') = N(T)). -/
private theorem exists_right_gap (T ε : ℝ) (hε : 0 < ε) :
    ∃ T' ∈ Set.Ioo T (T + ε), T' ∉ zetaZeroOrdinates ∧
      ∀ γ ∈ zetaZeroOrdinates, γ ≤ T ∨ T' < γ := by
  -- The zero ordinates in (T, T+ε) form a finite set
  have hfin : (zetaZeroOrdinates ∩ Set.Ioo T (T + ε)).Finite := by
    apply Set.Finite.subset (Set.Finite.image _ (finite_zeros_le (T + ε)))
    intro γ ⟨hγ_mem, hγ_range⟩
    obtain ⟨z, hzpos, rfl⟩ := hγ_mem
    exact ⟨z, ⟨hzpos, le_of_lt hγ_range.2⟩, rfl⟩
  by_cases h : (zetaZeroOrdinates ∩ Set.Ioo T (T + ε)).Nonempty
  · -- There are ordinates in (T, T+ε). Find the minimum.
    let F := hfin.toFinset
    have hF_nonempty : F.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
    let m := F.min' hF_nonempty
    have hm_mem : m ∈ zetaZeroOrdinates ∩ Set.Ioo T (T + ε) :=
      hfin.mem_toFinset.mp (Finset.min'_mem F hF_nonempty)
    have hm_min : ∀ x ∈ F, m ≤ x := fun x hx => Finset.min'_le F x hx
    obtain ⟨_, hm_lo, hm_hi⟩ := hm_mem
    -- Pick T' = (T + m) / 2, which is in (T, m) ⊆ (T, T+ε) with no ordinate in (T, T']
    refine ⟨(T + m) / 2, ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · intro hmem
      have : (T + m) / 2 ∈ zetaZeroOrdinates ∩ Set.Ioo T (T + ε) :=
        ⟨hmem, by constructor <;> linarith⟩
      have := hm_min _ (hfin.mem_toFinset.mpr this)
      linarith
    · intro γ hγ
      by_cases hγ_range : γ ∈ Set.Ioo T (T + ε)
      · have hγ_F : γ ∈ F := hfin.mem_toFinset.mpr ⟨hγ, hγ_range⟩
        have := hm_min γ hγ_F
        right; linarith
      · simp only [Set.mem_Ioo, not_and_or, not_lt] at hγ_range
        rcases hγ_range with h | h
        · exact Or.inl h
        · right; linarith
  · -- No ordinates in (T, T+ε). Pick T' = T + ε/2.
    refine ⟨T + ε / 2, ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · intro hmem
      exact h ⟨T + ε / 2, hmem, by constructor <;> linarith⟩
    · intro γ hγ
      by_cases hle : γ ≤ T
      · exact Or.inl hle
      · push_neg at hle
        have : γ ∉ Set.Ioo T (T + ε) := by
          intro hmem; exact h ⟨γ, hγ, hmem⟩
        simp only [Set.mem_Ioo, not_and_or, not_lt] at this
        rcases this with h' | h'
        · exact absurd hle (not_lt.mpr h')
        · right; linarith

/-- When no ordinate lies in (T, T'], the zero counting function is constant. -/
private theorem N_eq_of_no_ordinate_between {T T' : ℝ} (hle : T ≤ T')
    (h_no_ord : ∀ γ ∈ zetaZeroOrdinates, γ ≤ T ∨ T' < γ) :
    N T' = N T := by
  show (zerosUpTo T').ncard = (zerosUpTo T).ncard
  congr 1
  show zetaNontrivialZerosPos ∩ {s : ℂ | s.im ≤ T'} =
       zetaNontrivialZerosPos ∩ {s : ℂ | s.im ≤ T}
  ext s
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hpos, him⟩
    refine ⟨hpos, ?_⟩
    have hord : s.im ∈ zetaZeroOrdinates := ⟨s, hpos, rfl⟩
    rcases h_no_ord s.im hord with h | h
    · exact h
    · linarith
  · rintro ⟨hpos, him⟩
    exact ⟨hpos, by linarith⟩

/-- When no ordinate lies in `(T, T']`, the multiplicity-counted zero counting
    function is constant as well. -/
private theorem Nmult_eq_of_no_ordinate_between {T T' : ℝ} (hle : T ≤ T')
    (h_no_ord : ∀ γ ∈ zetaZeroOrdinates, γ ≤ T ∨ T' < γ) :
    Nmult T' = Nmult T := by
  have hzeros : zerosUpTo T' = zerosUpTo T := by
    ext s
    simp only [zerosUpTo, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hpos, him⟩
      refine ⟨hpos, ?_⟩
      have hord : s.im ∈ zetaZeroOrdinates := ⟨s, hpos, rfl⟩
      rcases h_no_ord s.im hord with h | h
      · exact h
      · linarith
    · rintro ⟨hpos, him⟩
      exact ⟨hpos, le_trans him hle⟩
  have hfinset :
      (finite_zeros_le T').toFinset = (finite_zeros_le T).toFinset := by
    ext s
    simp [Set.Finite.mem_toFinset, hzeros]
  unfold zeroCountingFunctionMult
  rw [hfinset]

/-- The "continuous part" of the RvM formula (everything except the arg term). -/
private def rvmContinuousPart (T : ℝ) : ℝ :=
  (1 / Real.pi) * (stirlingApprox T).im
    - (T / (2 * Real.pi)) * Real.log Real.pi + 1

/-- The stirling approx imaginary part is continuous. -/
private theorem continuous_stirlingApprox_im :
    Continuous (fun t : ℝ => (stirlingApprox t).im) := by
  apply Complex.continuous_im.comp
  unfold stirlingApprox
  have hs : Continuous (fun t : ℝ => (1/4 : ℂ) + I * ↑t / 2) := by fun_prop
  have hlog : Continuous (fun t : ℝ => Complex.log ((1/4 : ℂ) + I * ↑t / 2)) := by
    apply Continuous.clog hs
    intro t; left
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  exact ((hs.sub continuous_const).mul hlog).sub hs |>.add continuous_const

/-- The continuous part is continuous. -/
private theorem continuous_rvmContinuousPart : Continuous rvmContinuousPart := by
  unfold rvmContinuousPart
  have h1 : Continuous (fun t : ℝ => (1 / Real.pi) * (stirlingApprox t).im) :=
    continuous_const.mul continuous_stirlingApprox_im
  have h2 : Continuous (fun t : ℝ => (t / (2 * Real.pi)) * Real.log Real.pi) := by
    fun_prop
  exact (h1.sub h2).add continuous_const

/-- Extension from non-ordinate T to all T.

    Proof strategy: for any T, find T' > T arbitrarily close, not an ordinate,
    with N(T') = N(T) (right-continuity). Apply rvm_at_generic_T at T'.
    The "continuous part" G of the formula satisfies G(T') → G(T).
    The "arg part" H is bounded by 1. Use le_of_forall_pos_le_add. -/
private theorem rvm_extend_to_all_T
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp]
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀,
      |(N T : ℝ)
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨C₀', hC₀'⟩ := rvm_at_generic_T
  set C₀ := max C₀' 0
  have hC₀_nn : 0 ≤ C₀ := le_max_right _ _
  have hC₀ : ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(N T : ℝ) - ((1 / Real.pi) * (stirlingApprox T).im -
        (T / (2 * Real.pi)) * Real.log Real.pi +
        (1 / Real.pi) * (riemannZeta (1 / 2 + I * ↑T)).arg + 1)| ≤ C₀ * Real.log T := by
    intro T hT hT_ord
    calc _ ≤ C₀' * Real.log T := hC₀' T hT hT_ord
      _ ≤ C₀ * Real.log T := by
        apply mul_le_mul_of_nonneg_right (le_max_left _ _)
        exact le_of_lt (Real.log_pos (by linarith))
  refine ⟨2 * C₀ + 1, max 14 (Real.exp 2), fun T hT => ?_⟩
  have hT14 : 14 ≤ T := le_trans (le_max_left _ _) hT
  have hTe2 : Real.exp 2 ≤ T := le_trans (le_max_right _ _) hT
  have hT_pos : 0 < T := lt_of_lt_of_le (by positivity) hTe2
  have hlog_ge2 : 2 ≤ Real.log T := by
    rw [show (2 : ℝ) = Real.log (Real.exp 2) from (Real.log_exp 2).symm]
    exact Real.log_le_log (Real.exp_pos 2) hTe2
  have hlog_pos : 0 < Real.log T := by linarith
  -- Decompose F(T) = G(T) + H(T) where G is continuous and |H| ≤ 1
  set G := rvmContinuousPart with hG_def
  set H : ℝ → ℝ := fun T => (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
  -- The full formula is G(T) + H(T)
  have hF_eq : ∀ t : ℝ,
      (1 / Real.pi) * (stirlingApprox t).im
        - (t / (2 * Real.pi)) * Real.log Real.pi
        + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑t)) + 1
      = G t + H t := by
    intro t; show _ = rvmContinuousPart t + H t; unfold rvmContinuousPart; ring
  -- |H(t)| ≤ 1 for all t
  have hH_bound : ∀ t : ℝ, |H t| ≤ 1 := by
    intro t
    show |((1 : ℝ) / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑t))| ≤ 1
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
    calc (1 / Real.pi) * |Complex.arg (riemannZeta (1/2 + I * ↑t))|
        ≤ (1 / Real.pi) * Real.pi := by
          gcongr; exact Complex.abs_arg_le_pi _
      _ = 1 := by field_simp
  -- G is continuous
  have hG_cont : Continuous G := continuous_rvmContinuousPart
  -- For any δ > 0, bound |N(T) - F(T)| ≤ 2C₀ · log(T) + 2 + δ
  suffices h : ∀ δ > 0, |(N T : ℝ) - (G T + H T)| ≤ 2 * C₀ * Real.log T + 2 + δ by
    have hle : |(N T : ℝ) - (G T + H T)| ≤ 2 * C₀ * Real.log T + 2 := by
      apply le_of_forall_pos_le_add
      intro ε hε; linarith [h ε hε]
    rw [hF_eq T]
    calc |(N T : ℝ) - (G T + H T)| ≤ 2 * C₀ * Real.log T + 2 := hle
      _ ≤ 2 * C₀ * Real.log T + Real.log T := by linarith
      _ = (2 * C₀ + 1) * Real.log T := by ring
  intro δ hδ
  -- By continuity of G at T, there exists ε > 0 such that |G(T') - G(T)| < δ for |T' - T| < ε
  have hG_cont_at : ContinuousAt G T := hG_cont.continuousAt
  rw [Metric.continuousAt_iff] at hG_cont_at
  obtain ⟨ε₀, hε₀_pos, hε₀⟩ := hG_cont_at δ hδ
  -- Find T' ∈ (T, T + min(ε₀, 1)) not an ordinate with N(T') = N(T)
  set ε := min ε₀ 1 with hε_def
  have hε_pos : 0 < ε := lt_min hε₀_pos one_pos
  obtain ⟨T', ⟨hT'_lo, hT'_hi⟩, hT'_not_ord, hT'_gap⟩ := exists_right_gap T ε hε_pos
  -- N(T') = N(T) since no ordinate lies in (T, T']
  have hN_eq : N T' = N T := N_eq_of_no_ordinate_between (le_of_lt hT'_lo) hT'_gap
  -- T' ≥ 14
  have hT'14 : 14 ≤ T' := by linarith
  -- T' < T + 1
  have hT'_lt_T1 : T' < T + 1 := by
    have : ε ≤ 1 := min_le_right ε₀ 1
    linarith
  -- Apply rvm_at_generic_T at T'
  have hbound := hC₀ T' hT'14 hT'_not_ord
  -- Rewrite using N(T') = N(T)
  rw [hN_eq] at hbound
  rw [hF_eq T'] at hbound
  -- log(T') ≤ log(T + 1) ≤ 2 · log(T)
  have hlog_T' : Real.log T' ≤ 2 * Real.log T := by
    have : Real.log T' ≤ Real.log (T + 1) :=
      Real.log_le_log (by linarith) (le_of_lt hT'_lt_T1)
    have : Real.log (T + 1) ≤ Real.log (T * T) := by
      apply Real.log_le_log (by linarith)
      nlinarith
    calc Real.log T' ≤ Real.log (T * T) := by linarith
      _ = Real.log T + Real.log T := Real.log_mul (ne_of_gt hT_pos) (ne_of_gt hT_pos)
      _ = 2 * Real.log T := by ring
  -- |H(T') - H(T)| ≤ 2
  have hH_diff : |H T' - H T| ≤ 2 := by
    have h1 : |H T' - H T| ≤ |H T'| + |H T| := by
      have := abs_sub_le (H T') 0 (H T); simp at this; linarith
    linarith [hH_bound T', hH_bound T]
  -- |G(T') - G(T)| < δ
  have hG_diff : |G T' - G T| < δ := by
    have hdist : dist T' T < ε₀ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      calc T' - T < ε := by linarith
        _ ≤ ε₀ := min_le_left _ _
    have := hε₀ hdist
    rwa [Real.dist_eq] at this
  -- Triangle inequality
  calc |(N T : ℝ) - (G T + H T)|
      = |((N T : ℝ) - (G T' + H T')) + ((G T' - G T) + (H T' - H T))| := by ring_nf
    _ ≤ |(N T : ℝ) - (G T' + H T')| + |(G T' - G T) + (H T' - H T)| := abs_add_le _ _
    _ ≤ |(N T : ℝ) - (G T' + H T')| + |G T' - G T| + |H T' - H T| := by
        linarith [abs_add_le (G T' - G T) (H T' - H T)]
    _ ≤ C₀ * Real.log T' + δ + 2 := by linarith [hG_diff]
    _ ≤ C₀ * (2 * Real.log T) + δ + 2 := by
        have : C₀ * Real.log T' ≤ C₀ * (2 * Real.log T) :=
          mul_le_mul_of_nonneg_left hlog_T' hC₀_nn
        linarith
    _ = 2 * C₀ * Real.log T + 2 + δ := by ring

theorem rvm_decomposition_bounded
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp]
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    (fun T : ℝ => (N T : ℝ)
      - ((1 / Real.pi) * (stirlingApprox T).im
         - (T / (2 * Real.pi)) * Real.log Real.pi
         + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
         + 1)) =O[atTop] (fun T : ℝ => Real.log T) := by
  obtain ⟨C, T₀, hCT⟩ := rvm_extend_to_all_T
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max T₀ (Real.exp 1))] with T hT
  have hT_ge : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT_exp : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hlog_pos : 0 < Real.log T :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < Real.exp 1) hT_exp)
  have hbound := hCT T hT_ge
  rw [show ‖(fun T : ℝ => (↑(N T) : ℝ) - (1 / Real.pi * (stirlingApprox T).im -
      T / (2 * Real.pi) * Real.log Real.pi +
      1 / Real.pi * (riemannZeta (1 / 2 + I * ↑T)).arg + 1)) T‖ =
      |↑(N T) - (1 / Real.pi * (stirlingApprox T).im -
      T / (2 * Real.pi) * Real.log Real.pi +
      1 / Real.pi * (riemannZeta (1 / 2 + I * ↑T)).arg + 1)| from Real.norm_eq_abs _]
  rw [show ‖(fun T : ℝ => Real.log T) T‖ = |Real.log T| from Real.norm_eq_abs _]
  rw [abs_of_pos hlog_pos]
  exact hbound

/-- The RvM formula as a pointwise bound.

    Composes four proved results:
    (1) `rvm_decomposition_bounded`: N(T) = Stirling + S(T) + 1 + O(log T) [sorry]
    (2) `stirling_im_approx`: Im(stirlingApprox) = main formula + O(1/T) [proved]
    (3) `backlund_ST_bound`: S(T) = O(log T) [proved]
    (4) `rvm_stirling_algebra`: algebraic identity [proved]

    All error terms are absorbed into O(log T). -/
private theorem contour_integral_gives_rvm
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp]
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀,
      |(N T : ℝ) - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi))
        - T / (2 * Real.pi))| ≤ C * Real.log T := by
  have h_decomp := rvm_decomposition_bounded
  have h_stirling := stirling_im_approx
  have h_ST := backlund_ST_bound
  have h_combined : (fun T : ℝ => (N T : ℝ)
    - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi))
        - T / (2 * Real.pi))) =O[atTop] (fun T : ℝ => Real.log T) := by
    have hA := h_decomp
    have hB : (fun T : ℝ => (1 / Real.pi) * ((stirlingApprox T).im
      - ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8))) =O[atTop]
        (fun T : ℝ => Real.log T) :=
      (h_stirling.const_mul_left (1 / Real.pi)).trans isBigO_inv_of_log
    have hD : (fun T : ℝ => (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T)))
        =O[atTop] (fun T : ℝ => Real.log T) :=
      h_ST.const_mul_left (1 / Real.pi)
    have h78 : (fun _ : ℝ => (7 : ℝ) / 8) =O[atTop] (fun T : ℝ => Real.log T) :=
      (isBigO_one_of_log.const_mul_left (7 / 8)).congr_left (fun _ => by ring)
    have hcongr : (fun T : ℝ =>
        ((N T : ℝ)
          - ((1 / Real.pi) * (stirlingApprox T).im
             - (T / (2 * Real.pi)) * Real.log Real.pi
             + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
             + 1))
        + ((1 / Real.pi) * ((stirlingApprox T).im
          - ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)))
        + ((1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T)))
        + (7 / 8 : ℝ))
      =ᶠ[atTop] (fun T : ℝ => (N T : ℝ)
        - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with T hT
      have halg := rvm_stirling_algebra T hT
      linarith
    exact (hA.add hB |>.add hD |>.add h78).congr' hcongr (Eventually.of_forall fun _ => rfl)
  rw [Asymptotics.isBigO_iff] at h_combined
  obtain ⟨C, hC⟩ := h_combined
  rw [Filter.Eventually, Filter.mem_atTop_sets] at hC
  obtain ⟨T₀, hT₀⟩ := hC
  refine ⟨C, max T₀ (Real.exp 1), fun T hT => ?_⟩
  have hT_ge : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT_exp : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hlog_pos : 0 < Real.log T :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < Real.exp 1) hT_exp)
  have hbound : ‖(N T : ℝ)
    - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))‖
    ≤ C * ‖Real.log T‖ := hT₀ T hT_ge
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hbound
  calc |(N T : ℝ)
        - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))|
      ≤ C * |Real.log T| := hbound
    _ = C * Real.log T := by rw [abs_of_pos hlog_pos]

/-- For `T ≥ 14` not a zero ordinate, `Nmult(T)` equals the RvM expression up
    to `O(log T)`. -/
private theorem rvm_at_generic_T_mult
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(Nmult T : ℝ)
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  exact rvm_Nmult_formula_bound

/-- Extension from non-ordinate `T` to all `T` for the multiplicity-counted
    RvM formula. -/
private theorem rvm_extend_to_all_T_mult
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀,
      |(Nmult T : ℝ)
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨C₀', hC₀'⟩ := rvm_at_generic_T_mult
  set C₀ := max C₀' 0
  have hC₀_nn : 0 ≤ C₀ := le_max_right _ _
  have hC₀ : ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(Nmult T : ℝ) - ((1 / Real.pi) * (stirlingApprox T).im -
        (T / (2 * Real.pi)) * Real.log Real.pi +
        (1 / Real.pi) * (riemannZeta (1 / 2 + I * ↑T)).arg + 1)| ≤ C₀ * Real.log T := by
    intro T hT hT_ord
    calc _ ≤ C₀' * Real.log T := hC₀' T hT hT_ord
      _ ≤ C₀ * Real.log T := by
        apply mul_le_mul_of_nonneg_right (le_max_left _ _)
        exact le_of_lt (Real.log_pos (by linarith))
  refine ⟨2 * C₀ + 1, max 14 (Real.exp 2), fun T hT => ?_⟩
  have hT14 : 14 ≤ T := le_trans (le_max_left _ _) hT
  have hTe2 : Real.exp 2 ≤ T := le_trans (le_max_right _ _) hT
  have hT_pos : 0 < T := lt_of_lt_of_le (by positivity) hTe2
  have hlog_ge2 : 2 ≤ Real.log T := by
    rw [show (2 : ℝ) = Real.log (Real.exp 2) from (Real.log_exp 2).symm]
    exact Real.log_le_log (Real.exp_pos 2) hTe2
  have hlog_pos : 0 < Real.log T := by linarith
  set G := rvmContinuousPart with hG_def
  set H : ℝ → ℝ := fun T => (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
  have hF_eq : ∀ t : ℝ,
      (1 / Real.pi) * (stirlingApprox t).im
        - (t / (2 * Real.pi)) * Real.log Real.pi
        + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑t)) + 1
      = G t + H t := by
    intro t; show _ = rvmContinuousPart t + H t; unfold rvmContinuousPart; ring
  have hH_bound : ∀ t : ℝ, |H t| ≤ 1 := by
    intro t
    show |((1 : ℝ) / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑t))| ≤ 1
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
    calc (1 / Real.pi) * |Complex.arg (riemannZeta (1/2 + I * ↑t))|
        ≤ (1 / Real.pi) * Real.pi := by
          gcongr; exact Complex.abs_arg_le_pi _
      _ = 1 := by field_simp
  have hG_cont : Continuous G := continuous_rvmContinuousPart
  suffices h : ∀ δ > 0, |(Nmult T : ℝ) - (G T + H T)| ≤ 2 * C₀ * Real.log T + 2 + δ by
    have hle : |(Nmult T : ℝ) - (G T + H T)| ≤ 2 * C₀ * Real.log T + 2 := by
      apply le_of_forall_pos_le_add
      intro ε hε; linarith [h ε hε]
    rw [hF_eq T]
    calc |(Nmult T : ℝ) - (G T + H T)| ≤ 2 * C₀ * Real.log T + 2 := hle
      _ ≤ 2 * C₀ * Real.log T + Real.log T := by linarith
      _ = (2 * C₀ + 1) * Real.log T := by ring
  intro δ hδ
  have hG_cont_at : ContinuousAt G T := hG_cont.continuousAt
  rw [Metric.continuousAt_iff] at hG_cont_at
  obtain ⟨ε₀, hε₀_pos, hε₀⟩ := hG_cont_at δ hδ
  set ε := min ε₀ 1 with hε_def
  have hε_pos : 0 < ε := lt_min hε₀_pos one_pos
  obtain ⟨T', ⟨hT'_lo, hT'_hi⟩, hT'_not_ord, hT'_gap⟩ := exists_right_gap T ε hε_pos
  have hN_eq : Nmult T' = Nmult T :=
    Nmult_eq_of_no_ordinate_between (le_of_lt hT'_lo) hT'_gap
  have hT'14 : 14 ≤ T' := by linarith
  have hT'_lt_T1 : T' < T + 1 := by
    have : ε ≤ 1 := min_le_right ε₀ 1
    linarith
  have hbound := hC₀ T' hT'14 hT'_not_ord
  rw [hN_eq] at hbound
  rw [hF_eq T'] at hbound
  have hlog_T' : Real.log T' ≤ 2 * Real.log T := by
    have : Real.log T' ≤ Real.log (T + 1) :=
      Real.log_le_log (by linarith) (le_of_lt hT'_lt_T1)
    have : Real.log (T + 1) ≤ Real.log (T * T) := by
      apply Real.log_le_log (by linarith)
      nlinarith
    calc Real.log T' ≤ Real.log (T * T) := by linarith
      _ = Real.log T + Real.log T := Real.log_mul (ne_of_gt hT_pos) (ne_of_gt hT_pos)
      _ = 2 * Real.log T := by ring
  have hH_diff : |H T' - H T| ≤ 2 := by
    have h1 : |H T' - H T| ≤ |H T'| + |H T| := by
      have := abs_sub_le (H T') 0 (H T); simp at this; linarith
    linarith [hH_bound T', hH_bound T]
  have hG_diff : |G T' - G T| < δ := by
    have hdist : dist T' T < ε₀ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      calc T' - T < ε := by linarith
        _ ≤ ε₀ := min_le_left _ _
    have := hε₀ hdist
    rwa [Real.dist_eq] at this
  calc |(Nmult T : ℝ) - (G T + H T)|
      = |((Nmult T : ℝ) - (G T' + H T')) + ((G T' - G T) + (H T' - H T))| := by ring_nf
    _ ≤ |(Nmult T : ℝ) - (G T' + H T')| + |(G T' - G T) + (H T' - H T)| := abs_add_le _ _
    _ ≤ |(Nmult T : ℝ) - (G T' + H T')| + |G T' - G T| + |H T' - H T| := by
        linarith [abs_add_le (G T' - G T) (H T' - H T)]
    _ ≤ C₀ * Real.log T' + δ + 2 := by linarith [hG_diff]
    _ ≤ C₀ * (2 * Real.log T) + δ + 2 := by
        have : C₀ * Real.log T' ≤ C₀ * (2 * Real.log T) :=
          mul_le_mul_of_nonneg_left hlog_T' hC₀_nn
        linarith
    _ = 2 * C₀ * Real.log T + 2 + δ := by ring

theorem rvm_decomposition_bounded_mult
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    (fun T : ℝ => (Nmult T : ℝ)
      - ((1 / Real.pi) * (stirlingApprox T).im
         - (T / (2 * Real.pi)) * Real.log Real.pi
         + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
         + 1)) =O[atTop] (fun T : ℝ => Real.log T) := by
  obtain ⟨C, T₀, hCT⟩ := rvm_extend_to_all_T_mult
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max T₀ (Real.exp 1))] with T hT
  have hT_ge : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT_exp : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hlog_pos : 0 < Real.log T :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < Real.exp 1) hT_exp)
  have hbound := hCT T hT_ge
  rw [show ‖(fun T : ℝ => (↑(Nmult T) : ℝ) - (1 / Real.pi * (stirlingApprox T).im -
      T / (2 * Real.pi) * Real.log Real.pi +
      1 / Real.pi * (riemannZeta (1 / 2 + I * ↑T)).arg + 1)) T‖ =
      |↑(Nmult T) - (1 / Real.pi * (stirlingApprox T).im -
      T / (2 * Real.pi) * Real.log Real.pi +
      1 / Real.pi * (riemannZeta (1 / 2 + I * ↑T)).arg + 1)| from Real.norm_eq_abs _]
  rw [show ‖(fun T : ℝ => Real.log T) T‖ = |Real.log T| from Real.norm_eq_abs _]
  rw [abs_of_pos hlog_pos]
  exact hbound

/-- Multiplicity-counted Riemann-von Mangoldt bound derived from the contour
    decomposition, Stirling, and Backlund's bound on `S(T)`. -/
private theorem contour_integral_gives_rvm_mult
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀,
      |(Nmult T : ℝ) - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi))
        - T / (2 * Real.pi))| ≤ C * Real.log T := by
  have h_decomp := rvm_decomposition_bounded_mult
  have h_stirling := stirling_im_approx
  have h_ST := backlund_ST_bound
  have h_combined : (fun T : ℝ => (Nmult T : ℝ)
    - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi))
        - T / (2 * Real.pi))) =O[atTop] (fun T : ℝ => Real.log T) := by
    have hA := h_decomp
    have hB : (fun T : ℝ => (1 / Real.pi) * ((stirlingApprox T).im
      - ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8))) =O[atTop]
        (fun T : ℝ => Real.log T) :=
      (h_stirling.const_mul_left (1 / Real.pi)).trans isBigO_inv_of_log
    have hD : (fun T : ℝ => (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T)))
        =O[atTop] (fun T : ℝ => Real.log T) :=
      h_ST.const_mul_left (1 / Real.pi)
    have h78 : (fun _ : ℝ => (7 : ℝ) / 8) =O[atTop] (fun T : ℝ => Real.log T) :=
      (isBigO_one_of_log.const_mul_left (7 / 8)).congr_left (fun _ => by ring)
    have hcongr : (fun T : ℝ =>
        ((Nmult T : ℝ)
          - ((1 / Real.pi) * (stirlingApprox T).im
             - (T / (2 * Real.pi)) * Real.log Real.pi
             + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
             + 1))
        + ((1 / Real.pi) * ((stirlingApprox T).im
          - ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8)))
        + ((1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T)))
        + (7 / 8 : ℝ))
      =ᶠ[atTop] (fun T : ℝ => (Nmult T : ℝ)
        - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with T hT
      have halg := rvm_stirling_algebra T hT
      linarith
    exact (hA.add hB |>.add hD |>.add h78).congr' hcongr (Eventually.of_forall fun _ => rfl)
  rw [Asymptotics.isBigO_iff] at h_combined
  obtain ⟨C, hC⟩ := h_combined
  rw [Filter.Eventually, Filter.mem_atTop_sets] at hC
  obtain ⟨T₀, hT₀⟩ := hC
  refine ⟨C, max T₀ (Real.exp 1), fun T hT => ?_⟩
  have hT_ge : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT_exp : Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hlog_pos : 0 < Real.log T :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < Real.exp 1) hT_exp)
  have hbound : ‖(Nmult T : ℝ)
    - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))‖
    ≤ C * ‖Real.log T‖ := hT₀ T hT_ge
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hbound
  calc |(Nmult T : ℝ)
        - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))|
      ≤ C * |Real.log T| := hbound
    _ = C * Real.log T := by rw [abs_of_pos hlog_pos]

/-- **Multiplicity-counted Riemann-von Mangoldt formula (explicit bound form).**

    This is the standard contour-theoretic statement: the zero count on the left
    is taken with multiplicity. Requires the explicit half-top zeta variation
    boundary `RvmHalfTopZetaVariationBoundHyp`. -/
theorem riemann_von_mangoldt_explicit_mult
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀,
      |(Nmult T : ℝ) - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) + T / (2 * Real.pi)|
        ≤ C * Real.log T := by
  obtain ⟨C, T₀, hCT⟩ := contour_integral_gives_rvm_mult
  exact ⟨C, T₀, fun T hT => by
    have := hCT T hT
    convert this using 2
    ring⟩

/-- Export the multiplicity-counted explicit RvM hypothesis from this file. -/
instance rvm_mult_explicit_hyp
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp] :
    ZeroCountingMultRvmExplicitHyp where
  bound := by
    simpa using riemann_von_mangoldt_explicit_mult

/-- **Riemann-von Mangoldt formula (explicit bound form).**
    There exist constants C, T₀ such that for all T ≥ T₀:
      |N(T) - (T/2π) log(T/2π) + T/2π| ≤ C · log T

    Proved from `contour_integral_gives_rvm` via a `ring` rewrite.
    Requires `RvmHalfTopZetaVariationBoundHyp` for the remaining half-top zeta
    branch-variation input, in addition to the `ξ'` compatibility boundary.

    References: Titchmarsh, "Theory of the Riemann Zeta Function", Thm 9.4. -/
theorem riemann_von_mangoldt_explicit
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp]
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀,
      |(N T : ℝ) - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) + T / (2 * Real.pi)|
        ≤ C * Real.log T := by
  obtain ⟨C, T₀, hCT⟩ := contour_integral_gives_rvm
  exact ⟨C, T₀, fun T hT => by
    have := hCT T hT
    convert this using 2
    ring⟩

/-- Provide `ZeroCountingRvmExplicitHyp` from the legacy distinct-count
    compatibility wrapper.
    This automatically triggers the instance chain:
      `ZeroCountingRvmExplicitHyp` → `ZeroCountingAsymptoticHyp`
        → `ZeroCountingMainTermHyp` → `ZeroCountingLowerBoundHyp`
    Requires `ZeroOrdinateLowerBoundHyp` for the bottom-edge restriction
    `Im > 1`, `RvmHalfTopZetaVariationBoundHyp` for the remaining half-top zeta
    branch-variation input, and `XiDerivZeroCountRectMultBoundFrom14Hyp` for
    the distinct-vs-multiplicity compatibility input. -/
instance rvm_explicit_hyp
    [ZeroOrdinateLowerBoundHyp] [RvmHalfTopZetaVariationBoundHyp]
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ZeroCountingRvmExplicitHyp where
  bound := riemann_von_mangoldt_explicit

end ZetaZeros
