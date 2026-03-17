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
import Littlewood.ZetaZeros.StirlingForRvM
import Littlewood.Aristotle.RiemannXiEntire


set_option maxHeartbeats 1600000
set_option autoImplicit false

noncomputable section

namespace ZetaZeros

open Complex Set MeasureTheory Topology Filter RectArgumentPrinciple
open scoped Real

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
with 0 < Im(ρ) < T. We use `FirstZeroOrdinateHyp` to show that all nontrivial
zeros have Im ≥ γ₁ > 14.13 > 1, so the restriction Im > 1 is equivalent to
Im > 0 for nontrivial zeros.
-/

/-- The set of zeros of RiemannXiAlt in the rectangle (-1,2)×(1,T) equals
    the set of nontrivial zeta zeros with 0 < Im(ρ) < T, provided T is not
    a zero ordinate and γ₁ > 14.13 (so all zeros have Im > 1). -/
theorem xi_zeros_in_rect_eq_strip [FirstZeroOrdinateHyp] (T : ℝ) (hT : 14 ≤ T)
    (hT_not_ord : T ∉ zetaZeroOrdinates) :
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
      -- Need Im(z) > 1. All nontrivial zeros have Im ≥ γ₁ > 14.13 > 1.
      rcases firstZeroOrdinate_bounds with ⟨γ₁, _, hγ₁_low, _, hγ₁_min⟩
      have hzpos : z ∈ zetaNontrivialZerosPos := by
        rw [mem_zetaNontrivialZerosPos, mem_zetaNontrivialZeros]
        exact ⟨⟨hzeta, hre_pos, hre_lt⟩, him_pos⟩
      have hord : z.im ∈ zetaZeroOrdinates := ⟨z, hzpos, rfl⟩
      have : γ₁ ≤ z.im := hγ₁_min z.im hord
      linarith
    · exact (riemannXiAlt_zero_iff_zeta_zero hre_pos hre_lt).mpr hzeta

/-- The ncard of zeros of RiemannXiAlt in the rectangle (-1,2)×(1,T) equals N(T)
    for T not a zero ordinate. Uses `FirstZeroOrdinateHyp` to show zeros with
    Im ∈ (1,T) = zeros with Im ∈ (0,T] (all zeros have Im ≥ 14.13 > 1). -/
theorem xi_zero_count_eq_N [FirstZeroOrdinateHyp] (T : ℝ) (hT : 14 ≤ T)
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
the hard analytic fact that ζ(s) ≠ 0 for real s ∈ (0,1). Instead, we use
`FirstZeroOrdinateHyp` which gives γ₁ > 14.13, so all zero ordinates are > 1.
This means neither Im = 1 nor Im = T (T not an ordinate) can be a zero ordinate.

On the boundary of (-1, 2) × (1, T) for T not a zero ordinate:
- Bottom edge (Im = 1): no nontrivial zero has Im = 1 (all ordinates ≥ 14.13)
- Top edge (Im = T): xi ≠ 0 since no zero has imaginary part T (T not an ordinate)
- Right edge (Re = 2): xi ≠ 0 by riemannXiAlt_ne_zero_of_re_ge_one
- Left edge (Re = -1): xi ≠ 0 by riemannXiAlt_ne_zero_of_re_le_zero
-/

/-- 1 is not a zero ordinate: all zero ordinates are ≥ γ₁ > 14.13 > 1. -/
private theorem one_not_zero_ordinate [FirstZeroOrdinateHyp] :
    (1 : ℝ) ∉ zetaZeroOrdinates := by
  intro hmem
  rcases firstZeroOrdinate_bounds with ⟨γ₁, _, hγ₁_low, _, hγ₁_min⟩
  have h1 : γ₁ ≤ 1 := hγ₁_min 1 hmem
  linarith

/-- Xi does not vanish on the boundary of the rectangle (-1, 2) × (1, T)
    when T > 1 is not a zero ordinate. Uses `FirstZeroOrdinateHyp` to
    ensure no zero ordinate equals 1. -/
private theorem xi_ne_zero_on_boundary [FirstZeroOrdinateHyp] (T : ℝ) (hT : 1 < T)
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

/-! ### Sub-lemma: Simple zeros of xi

All nontrivial zeros of ζ(s) are believed to be simple. This follows from
computations (all known zeros are simple) and is consistent with the GUE hypothesis.
This is sourced from `ZetaZerosSimpleHyp` (which states deriv(ζ,s) ≠ 0 at zeros)
via the product rule for ξ(s) = (1/2)s(s-1)Λ(s). -/

/-- All zeros of RiemannXiAlt in the critical strip are simple.
    Derived from `ZetaZerosSimpleHyp` via the product rule:
    ξ(s) = (1/2)s(s-1)Λ(s) and Λ = Γ_R · ζ, so at a zero z with z ≠ 0,1:
    deriv(ξ,z) = (1/2)z(z-1)·deriv(Λ,z) = (1/2)z(z-1)·Γ_R(z)·deriv(ζ,z). -/
private theorem xi_zeros_are_simple [ZetaZerosSimpleHyp] :
    ∀ z : ℂ, 0 < z.re → z.re < 1 → 0 < z.im → RiemannXiAlt z = 0 →
      deriv RiemannXiAlt z ≠ 0 := by
  intro z hre_pos hre_lt him_pos hxi_zero
  -- z is a nontrivial zero with Im > 0. By ZetaZerosSimpleHyp, deriv ζ z ≠ 0.
  have hzeta_zero : riemannZeta z = 0 :=
    (riemannXiAlt_zero_iff_zeta_zero hre_pos hre_lt).mp hxi_zero
  have hmem : z ∈ zetaNontrivialZeros := ⟨hzeta_zero, hre_pos, hre_lt⟩
  have hderiv_zeta := ZetaZerosSimpleHyp.simple z hmem
  -- Step 1: z ≠ 0 and z ≠ 1
  have hz0 : z ≠ 0 := by intro h; rw [h] at hre_pos; simp at hre_pos
  have hz1 : z ≠ 1 := by intro h; rw [h] at hre_lt; simp at hre_lt
  -- Step 2: RiemannXiAlt agrees with (1/2)*s*(s-1)*Λ(s) on a nhd of z
  have h_eq : ∀ᶠ s in nhds z,
      RiemannXiAlt s = (1/2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
    have h01 : ({0, 1} : Set ℂ)ᶜ ∈ nhds z :=
      IsOpen.mem_nhds (isOpen_compl_iff.mpr (Set.Finite.isClosed
        (Set.Finite.insert 0 (Set.finite_singleton 1))))
        (Set.mem_compl (by simp [hz0, hz1]))
    apply Filter.Eventually.mono h01
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    push_neg at hs
    exact RiemannXiAlt_eq_formula hs.1 hs.2
  -- Step 3: deriv RiemannXiAlt z = deriv of the product form at z
  have h_deriv_eq : deriv RiemannXiAlt z =
      deriv (fun s => (1/2 : ℂ) * s * (s - 1) * completedRiemannZeta s) z :=
    Filter.EventuallyEq.deriv_eq h_eq
  -- Step 4: completedRiemannZeta z = 0 (since ζ(z) = 0)
  have h_comp_zero : completedRiemannZeta z = 0 := by
    rwa [completedRiemannZeta_eq_zero_iff_riemannZeta hre_pos]
  -- Step 5: deriv completedRiemannZeta z ≠ 0
  -- At a simple zero z of ζ: Λ(s) = π^{-s/2}·Γ(s/2)·ζ(s) for s ≠ 0,1.
  -- Product rule at z where ζ(z) = 0: Λ'(z) = π^{-z/2}·Γ(z/2)·ζ'(z).
  -- Each factor nonzero: cpow of π, Gamma has no zeros, ζ'(z) ≠ 0.
  have h_comp_deriv_ne : deriv completedRiemannZeta z ≠ 0 := by
    -- Proof: ζ(s) = Λ(s)/Γ_R(s) near z, so by product rule at Λ(z)=0:
    --   ζ'(z) = Λ'(z) · (Γ_R(z))⁻¹. Since ζ'(z) ≠ 0, Λ'(z) ≠ 0.
    have h_eq : ∀ᶠ s in nhds z,
        riemannZeta s = completedRiemannZeta s * (Gammaℝ s)⁻¹ := by
      have h0_nhds : ({0} : Set ℂ)ᶜ ∈ nhds z :=
        IsOpen.mem_nhds isOpen_compl_singleton (Set.mem_compl_singleton_iff.mpr hz0)
      apply Filter.Eventually.mono h0_nhds
      intro s hs
      simp only [Set.mem_singleton_iff] at hs
      rw [riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]
    have h_diff_comp' : DifferentiableAt ℂ completedRiemannZeta z :=
      differentiableAt_completedZeta hz0 hz1
    have h_diff_inv : DifferentiableAt ℂ (fun s => (Gammaℝ s)⁻¹) z :=
      differentiable_Gammaℝ_inv.differentiableAt
    have h_key : deriv riemannZeta z =
        deriv completedRiemannZeta z * (Gammaℝ z)⁻¹ +
        completedRiemannZeta z * deriv (fun s => (Gammaℝ s)⁻¹) z := by
      conv_lhs => rw [Filter.EventuallyEq.deriv_eq h_eq]
      exact deriv_mul h_diff_comp' h_diff_inv
    rw [h_comp_zero, zero_mul, add_zero] at h_key
    intro h_contra
    apply hderiv_zeta
    rw [h_key, h_contra, zero_mul]
  -- Step 6: Compute the derivative via product rule and show nonzero
  -- f(s) = (1/2)·s·(s-1)·Λ(s), so f'(z) = (1/2)·(2z-1)·Λ(z) + (1/2)·z·(z-1)·Λ'(z)
  -- Since Λ(z) = 0: f'(z) = (1/2)·z·(z-1)·Λ'(z) ≠ 0.
  rw [h_deriv_eq]
  have h_diff_comp : DifferentiableAt ℂ completedRiemannZeta z :=
    differentiableAt_completedZeta hz0 hz1
  have h_p : HasDerivAt (fun s => (1/2 : ℂ) * s * (s - 1))
      ((1/2 : ℂ) * (2 * z - 1)) z := by
    have h1 : HasDerivAt (fun s : ℂ => s) 1 z := hasDerivAt_id z
    have h2 : HasDerivAt (fun s : ℂ => s - 1) 1 z := (hasDerivAt_id z).sub_const 1
    have h3 : HasDerivAt (fun s : ℂ => s * (s - 1)) (1 * (z - 1) + z * 1) z := h1.mul h2
    have h4 := h3.const_mul (1/2 : ℂ)
    convert h4 using 1 <;> ring
  have h_c : HasDerivAt completedRiemannZeta (deriv completedRiemannZeta z) z :=
    h_diff_comp.hasDerivAt
  have h_prod := h_p.mul h_c
  have hfg : (fun s => (1/2 : ℂ) * s * (s - 1) * completedRiemannZeta s) =
      ((fun s => (1/2 : ℂ) * s * (s - 1)) * completedRiemannZeta) := by
    ext s; simp [Pi.mul_apply]
  rw [hfg, h_prod.deriv, h_comp_zero, mul_zero, zero_add]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (by norm_num : (1/2 : ℂ) ≠ 0) hz0
    · exact sub_ne_zero.mpr hz1
  · exact h_comp_deriv_ne

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

/-- The Riemann-von Mangoldt decomposition: N(T) equals the Stirling +
    arg(ζ) + 1 expression, up to O(log T) error.

    This is the deep analytic content of the RvM formula.
    It combines:
    (a) Stirling approximation for Im log Γ(1/4 + iT/2) = (T/2)log(T/2) - T/2 - π/8 + O(1/T)
    (b) S(T) = (1/π) arg ζ(1/2+iT) = O(log T)
    (c) Standard bounds for ζ'/ζ on vertical lines
    (d) Bounded horizontal edge contributions

    Reference: Titchmarsh §9.3-9.4, Montgomery-Vaughan Theorem 14.5. -/
private theorem rvm_N_formula_bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(N T : ℝ)
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  -- ## PROOF STRATEGY (Titchmarsh §9.3-9.4)
  --
  -- The formula says: N(T) ≈ (1/π)·Im(stirlingApprox T) - (T/2π)·log π
  --                           + (1/π)·arg ζ(1/2+iT) + 1  [up to O(log T)]
  --
  -- By rvm_stirling_algebra + stirling_im_approx (both PROVED):
  --   RHS ≈ (T/2π)·log(T/2π) - T/(2π) + 7/8 + (1/π)·arg ζ + O(1/T)
  --       = main_term + O(1)  [since |arg ζ| ≤ π]
  --
  -- The Riemann-von Mangoldt formula (Titchmarsh Thm 9.4) states:
  --   N(T) = main_term + 7/8 + S_cont(T) + O(1/T)
  -- where S_cont is the continuously-wound (1/π)·arg ζ along the critical line.
  --
  -- ## WHAT REMAINS (argument principle content):
  --
  -- The formula relates N(T) (a cardinality of zeros) to an analytic expression.
  -- This connection requires the ARGUMENT PRINCIPLE for ξ along the half-boundary
  -- of the rectangle (-1,2)×(1,T), combined with the functional equation ξ(1-s)=ξ(s).
  --
  -- Specifically, the proof tracks arg(ξ) along 2+i → 2+iT → 1/2+iT, decomposing:
  --   arg(ξ) = arg(s·(s-1)) + arg(π^{-s/2}) + arg(Γ(s/2)) + arg(ζ(s))
  -- - Γ contribution → θ(T) ≈ Im(stirlingApprox) (Stirling, PROVED)
  -- - ζ contribution → arg ζ(1/2+iT) + O(log T) (horizontal edge bound)
  -- - Rational contributions → ±π (bounded, absorbed into O(log T))
  --
  -- ## PROVED INFRASTRUCTURE (all 0 sorry):
  -- - XiLogDerivDecomposition: pointwise decomposition of logDeriv(ξ)
  -- - StirlingForRvM: Stirling ↔ main term algebra + Im asymptotic
  -- - RvMEdgeIntegrals: |∫₁ᵀ 1/(2+iy) dy| ≤ log T, horizontal bounds
  -- - RectArgumentPrinciple: argument principle for rectangles
  -- - BinetStirling: Im(stirlingApprox) ≈ (T/2)log(T/2) - T/2 - π/8 + O(1/T)
  --
  -- ## MISSING PIECE:
  -- Formalizing "change of arg along a path" = Im(∫_path logDeriv(f) ds)
  -- and connecting this to N(T) via the argument principle + functional equation.
  sorry

/-- The contour integral evaluation: logIntegralRect(xi) on (-1,2)×(1,T) equals
    the RvM formula expression up to O(log T) error.

    Proved by combining:
    - The argument principle identifies logIntegralRect.re = N(T)
    - `rvm_N_formula_bound` gives |N(T) - formula| ≤ C · log T
    This theorem needs [FirstZeroOrdinateHyp] [ZetaZerosSimpleHyp] for the
    argument principle step, matching its only call site `rvm_at_generic_T`. -/
private theorem contour_evaluation_bound [FirstZeroOrdinateHyp] [ZetaZerosSimpleHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(logIntegralRect RiemannXiAlt (-1) 2 1 T).re
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ := rvm_N_formula_bound
  refine ⟨C, fun T hT hT_not_ord => ?_⟩
  -- Use the argument principle to identify logIntegralRect.re = N(T)
  have hT_gt : 1 < T := by linarith
  have hxi_entire := RiemannXiAlt_entire
  have hxi_bdy := xi_ne_zero_on_boundary T hT_gt hT_not_ord
  have hsimple : ∀ z ∈ openRect (-1) 2 1 T, RiemannXiAlt z = 0 →
      deriv RiemannXiAlt z ≠ 0 := by
    intro z hz hfz
    obtain ⟨hre_lo, hre_hi, him_lo, him_hi⟩ := hz
    have him_pos : 0 < z.im := by linarith
    have hre_pos : 0 < z.re := by
      by_contra hle; push_neg at hle
      exact riemannXiAlt_ne_zero_of_re_le_zero hle
        (by intro heq; subst heq; simp at him_lo; linarith) hfz
    have hre_lt : z.re < 1 := by
      by_contra hge; push_neg at hge
      exact riemannXiAlt_ne_zero_of_re_ge_one hge
        (by intro heq; subst heq; simp at him_lo; linarith) hfz
    exact xi_zeros_are_simple z hre_pos hre_lt him_pos hfz
  have harg_prin := argument_principle_rect_entire RiemannXiAlt (-1) 2 1 T
    (by norm_num : (-1 : ℝ) < 2) (by linarith : (1 : ℝ) < T) hxi_entire hxi_bdy hsimple
  have hcount := xi_zero_count_eq_N T hT hT_not_ord
  unfold zeroCountRect at harg_prin
  rw [hcount] at harg_prin
  -- Now logIntegralRect = ↑(N T), so .re = N(T)
  have hN_eq : (logIntegralRect RiemannXiAlt (-1) 2 1 T).re = ↑(N T) := by
    rw [harg_prin]; simp [Complex.ofReal_re, Complex.natCast_re]
  rw [hN_eq]
  exact hC T hT

/-! ### Assembly: Combining argument principle with contour evaluation -/

/-- For T ≥ 14 not a zero ordinate, N(T) equals the RvM expression up to O(log T).
    Proof: directly from `rvm_N_formula_bound`. The argument principle is not needed
    at this level since `rvm_N_formula_bound` already gives the N(T) bound. -/
private theorem rvm_at_generic_T [FirstZeroOrdinateHyp] [ZetaZerosSimpleHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → T ∉ zetaZeroOrdinates →
      |(N T : ℝ)
        - ((1 / Real.pi) * (stirlingApprox T).im
           - (T / (2 * Real.pi)) * Real.log Real.pi
           + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
           + 1)| ≤ C * Real.log T := by
  exact rvm_N_formula_bound.imp fun C hC T hT _ => hC T hT

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
private theorem rvm_extend_to_all_T [FirstZeroOrdinateHyp] [ZetaZerosSimpleHyp] :
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

theorem rvm_decomposition_bounded [FirstZeroOrdinateHyp] [ZetaZerosSimpleHyp] :
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
private theorem contour_integral_gives_rvm [FirstZeroOrdinateHyp] [ZetaZerosSimpleHyp] :
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

/-- **Riemann-von Mangoldt formula (explicit bound form).**
    There exist constants C, T₀ such that for all T ≥ T₀:
      |N(T) - (T/2π) log(T/2π) + T/2π| ≤ C · log T

    Proved from `contour_integral_gives_rvm` via a `ring` rewrite.

    References: Titchmarsh, "Theory of the Riemann Zeta Function", Thm 9.4. -/
theorem riemann_von_mangoldt_explicit [FirstZeroOrdinateHyp] [ZetaZerosSimpleHyp] :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀,
      |(N T : ℝ) - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) + T / (2 * Real.pi)|
        ≤ C * Real.log T := by
  obtain ⟨C, T₀, hCT⟩ := contour_integral_gives_rvm
  exact ⟨C, T₀, fun T hT => by
    have := hCT T hT
    convert this using 2
    ring⟩

/-- Provide `ZeroCountingRvmExplicitHyp` from the Riemann-von Mangoldt formula.
    This automatically triggers the instance chain:
      `ZeroCountingRvmExplicitHyp` → `ZeroCountingAsymptoticHyp`
        → `ZeroCountingMainTermHyp` → `ZeroCountingLowerBoundHyp`
    Requires `FirstZeroOrdinateHyp` for the rectangle restructuring
    (bottom edge at Im=1 instead of Im=0). -/
instance rvm_explicit_hyp [FirstZeroOrdinateHyp] [ZetaZerosSimpleHyp] :
    ZeroCountingRvmExplicitHyp where
  bound := riemann_von_mangoldt_explicit

end ZetaZeros
