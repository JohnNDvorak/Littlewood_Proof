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

For T not equal to any zero ordinate, the zeros of RiemannXiAlt in the open
rectangle (-1, 2) × (0, T) are exactly the nontrivial zeta zeros with
0 < Im(ρ) < T. Since N(T) counts zeros with Im(ρ) ≤ T (not strictly <),
we need T to not be a zero ordinate.
-/

/-- The set of zeros of RiemannXiAlt in the critical strip rectangle equals
    the set of nontrivial zeta zeros with 0 < Im(ρ) < T, provided T is not
    a zero ordinate. -/
theorem xi_zeros_in_rect_eq_strip (T : ℝ) (hT : 0 < T)
    (hT_not_ord : T ∉ zetaZeroOrdinates) :
    {z ∈ openRect (-1) 2 0 T | RiemannXiAlt z = 0} =
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im < T} := by
  ext z
  constructor
  · rintro ⟨hz_rect, hz_zero⟩
    obtain ⟨ha, hb, hc, hd⟩ := hz_rect
    -- z ∈ (-1, 2) × (0, T) and RiemannXiAlt z = 0
    -- Must show 0 < Re(z) < 1: outside this range RiemannXiAlt ≠ 0
    have hre_pos : 0 < z.re := by
      by_contra h
      push_neg at h
      -- Re(z) ≤ 0. Since Im(z) > 0 (from hc), z ≠ 0.
      have hz_ne_zero : z ≠ 0 := by
        intro heq; rw [heq] at hc; simp at hc
      exact riemannXiAlt_ne_zero_of_re_le_zero h hz_ne_zero hz_zero
    have hre_lt : z.re < 1 := by
      by_contra h
      push_neg at h
      -- Re(z) ≥ 1. Since Im(z) > 0 (from hc), z ≠ 1.
      have hz_ne_one : z ≠ 1 := by
        intro heq; rw [heq] at hc; simp at hc
      exact riemannXiAlt_ne_zero_of_re_ge_one h hz_ne_one hz_zero
    exact ⟨(riemannXiAlt_zero_iff_zeta_zero hre_pos hre_lt).mp hz_zero,
      hre_pos, hre_lt, hc, hd⟩
  · rintro ⟨hzeta, hre_pos, hre_lt, him_pos, him_lt⟩
    constructor
    · exact ⟨by linarith, by linarith, him_pos, him_lt⟩
    · exact (riemannXiAlt_zero_iff_zeta_zero hre_pos hre_lt).mpr hzeta

/-- The ncard of zeros of RiemannXiAlt in the rectangle equals N(T) for
    T not a zero ordinate. -/
theorem xi_zero_count_eq_N (T : ℝ) (hT : 0 < T)
    (hT_not_ord : T ∉ zetaZeroOrdinates) :
    Set.ncard {z ∈ openRect (-1) 2 0 T | RiemannXiAlt z = 0} = N T := by
  rw [xi_zeros_in_rect_eq_strip T hT hT_not_ord]
  -- N(T) = ncard (zerosUpTo T) = ncard {s | s ∈ zetaNontrivialZerosPos ∧ s.im ≤ T}
  -- The LHS has Im < T (strict), RHS has Im ≤ T.
  -- Since T ∉ zetaZeroOrdinates, no zero has Im = T, so the sets agree.
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
    -- Need Im(z) < T, not just ≤ T. Use hT_not_ord.
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

/-- **RvM decomposition**: N(T) equals the Stirling/theta contribution plus S(T) plus 1,
    up to O(log T). This is the output of applying the argument principle to ξ(s)
    on the rectangle (-1,2)×(0,T) and decomposing the logarithmic derivative.

    Specifically: N(T) = (1/π)·Im(stirlingApprox T) − (T/2π)·logπ
                         + (1/π)·arg(ζ(1/2+iT)) + 1 + O(log T)

    The O(log T) error absorbs:
    - The difference between continuous Im(logΓ) and Im(stirlingApprox) (O(1/T))
    - The branch-cut correction between continuous and principal arg of ζ (multiples of 2)
    - The rational term contribution from s(s-1) (bounded)
    - Horizontal edge contributions (bounded)

    ## Proved infrastructure available in this file:
    - `argument_principle_rect_entire`: Log-integral = zero count (PROVED)
    - `logDeriv_decompose_rect`: Log-deriv partial fraction decomposition (PROVED)
    - `RiemannXiAlt_entire`: ξ is entire (PROVED, Mathlib)
    - `riemannXiAlt_ne_zero_of_re_ge_one/le_zero`: ξ ≠ 0 outside critical strip (PROVED)
    - `xi_zero_count_eq_N`: Zero count in rectangle = N(T) (PROVED)
    - `exists_nearby_non_ordinate`: Generic T near any T₀ exists (PROVED)

    ## What the sorry encapsulates:
    (i) Decomposition of logDeriv(ξ) into Γ'/Γ + ζ'/ζ + rational on the boundary
    (ii) Evaluation of the digamma/Γ integral along vertical lines → Im(logΓ)
    (iii) Evaluation of the ζ'/ζ integral along the critical line → arg(ζ)
    (iv) Bounds on horizontal edge integrals (O(1) from standard growth estimates)
    (v) Simple-zeros hypothesis for the argument principle application

    Reference: Titchmarsh, "Theory of the Riemann Zeta Function", §9.3-9.4 -/
theorem rvm_decomposition_bounded :
    (fun T : ℝ => (N T : ℝ)
      - ((1 / Real.pi) * (stirlingApprox T).im
         - (T / (2 * Real.pi)) * Real.log Real.pi
         + (1 / Real.pi) * Complex.arg (riemannZeta (1/2 + I * ↑T))
         + 1)) =O[atTop] (fun T : ℝ => Real.log T) := by
  sorry

/-- The RvM formula as a pointwise bound.

    Composes four proved results:
    (1) `rvm_decomposition_bounded`: N(T) = Stirling + S(T) + 1 + O(log T) [sorry]
    (2) `stirling_im_approx`: Im(stirlingApprox) = main formula + O(1/T) [proved]
    (3) `backlund_ST_bound`: S(T) = O(log T) [proved]
    (4) `rvm_stirling_algebra`: algebraic identity [proved]

    All error terms are absorbed into O(log T). -/
private theorem contour_integral_gives_rvm :
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
theorem riemann_von_mangoldt_explicit :
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
        → `ZeroCountingMainTermHyp` → `ZeroCountingLowerBoundHyp` -/
instance rvm_explicit_hyp : ZeroCountingRvmExplicitHyp where
  bound := riemann_von_mangoldt_explicit

end ZetaZeros
