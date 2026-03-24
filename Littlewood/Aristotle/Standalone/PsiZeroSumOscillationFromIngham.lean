/-
Proof of PsiZeroSumOscillationHyp (B5b) from ExplicitFormulaPsiGeneralHyp (B5a)
via Landau's indirect argument.

## Mathematical Strategy (Landau 1905 / Ingham 1932)

Given the general truncated explicit formula (B5a) with variable truncation T:
  |ψ(x) - x + Σ_{|γ|≤T} Re(x^ρ/ρ)| ≤ C · (√x · (log T)²/√T + (log x)²)

To show: under RH, ψ(x) - x is unbounded in both directions relative to √x.

Proof by contradiction for the positive direction:
1. Assume ψ(x) - x ≤ M√x for all x ≥ x₀ (bounded above)
2. From B5a at T=x: -∑_{|γ|≤x} Re(x^ρ/ρ) ≤ M√x + K(log x)²
3. The Mellin/Stieltjes transform ∫₁^∞ (M√x - (ψ(x)-x)) x^{-s-1} dx
   converges for Re(s) > 1/2
4. This makes ζ'/ζ + 1/(s-1) + M/(s-1/2) holomorphic for Re(s) > 1/2
5. But under RH, ζ has zeros at 1/2+iγ (infinitely many by Hardy),
   so ζ'/ζ has poles at those points — contradiction

The negative direction is symmetric.

## Lean Formalization

The Landau-Ingham contradiction via Mellin transforms is deferred. The proof
uses a sorry for the key analytic number theory fact: under RH with infinitely
many critical-line zeros, ψ(x)-x cannot be bounded above (or below) by any
multiple of √x for all large x.

## References

- Landau, E. (1905). "Über einen Satz von Tschebyschef." Math. Ann. 61.
- Ingham, A. E. (1932). The Distribution of Prime Numbers, Chapter V.
- Montgomery-Vaughan (2007). Multiplicative Number Theory I, §15.2.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.Aristotle.ZetaLogDerivInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Classical

namespace Aristotle.Standalone.PsiZeroSumOscillationFromIngham

open Filter Complex Topology
open GrowthDomination
open Aristotle.DirichletPhaseAlignment (ZerosBelow CriticalZeros)
open Aristotle.Standalone.RHPsiWitnessFromZeroSum (psiMainTerm)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open ZetaZeros

-- ============================================================
-- Infrastructure: positive-imaginary-part zeros (PROVED)
-- ============================================================

/-- The subset of ZerosBelow T with strictly positive imaginary part. -/
def PositiveImZerosBelow (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => 0 < ρ.im)

lemma positiveImZerosBelow_sub (T : ℝ) :
    PositiveImZerosBelow T ⊆ ZerosBelow T :=
  Finset.filter_subset _ _

lemma positiveImZerosBelow_re_half (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ ρ ∈ PositiveImZerosBelow T, ρ.re = 1 / 2 := by
  intro ρ hρ
  have hρ_mem : ρ ∈ ZerosBelow T := positiveImZerosBelow_sub T hρ
  have hρ_crit : ρ ∈ CriticalZeros := by
    simp only [ZerosBelow] at hρ_mem
    split_ifs at hρ_mem with hfin
    · exact ((hfin.mem_toFinset).mp hρ_mem).1
    · simp at hρ_mem
  exact hRH ρ hρ_crit

-- ============================================================
-- Proved: Re(I/ρ) ≤ 1/‖ρ‖ for nonzero ρ
-- ============================================================

/-- For any nonzero ρ, Re(I/ρ) ≤ 1/‖ρ‖.
Proof: |Re(z)| ≤ ‖z‖ and ‖I/ρ‖ = 1/‖ρ‖. -/
lemma re_I_div_le_inv_norm (ρ : ℂ) (_hρ : ρ ≠ 0) :
    (I / ρ).re ≤ 1 / ‖ρ‖ := by
  calc (I / ρ).re ≤ ‖I / ρ‖ := le_trans (le_abs_self _) (abs_re_le_norm _)
    _ = ‖I‖ / ‖ρ‖ := by rw [norm_div]
    _ = 1 / ‖ρ‖ := by rw [Complex.norm_I]

-- ============================================================
-- Key analytic fact: Landau-Ingham unbounded oscillation
-- ============================================================

-- ============================================================
-- Phase alignment infrastructure for explicit formula approach
-- ============================================================

open Aristotle.DirichletPhaseAlignment
  (exists_large_x_phases_aligned_to_target bound_real_part_of_sum_shifted
   bound_real_part_of_sum_shifted_upper)

/-- For γ ≥ 1: γ/(1/4+γ²) ≥ 1/(2γ).
Comparison lemma: γ/(1/4+γ²) ≥ γ/(γ+γ²) = 1/(1+γ) ≥ 1/(2γ) for γ ≥ 1.
Key for reducing divergence of ∑ γ/(1/4+γ²) to divergence of ∑ 1/γ. -/
lemma gamma_div_bound (γ : ℝ) (hγ : γ ≥ 1) :
    γ / (1/4 + γ ^ 2) ≥ 1 / (2 * γ) := by
  rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg γ]

/-- Deep input: divergence of the positive-imaginary weighted zero sum under RH. -/
class CriticalZeroSumDivergesHyp : Prop where
  proof :
    ∀ (hRH : ZetaZeros.RiemannHypothesis) (M : ℝ), ∃ T : ℝ, T ≥ 2 ∧
      M ≤ ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2)

/-- **Atomic sorry (B5b leaf)**: Under RH, ∑_{0<γ≤T} γ/(1/4+γ²) → ∞ as T → ∞.

This is the divergence of the weighted sum over positive zeta zero ordinates.
The weight γ/(1/4+γ²) ≈ 1/γ for large γ, so this diverges at the same rate as
the harmonic sum ∑ 1/γ over zero ordinates.

**Proof outline** (not yet formalized):
(1) Riemann-von Mangoldt: N(T) = (T/2π)log(T/2π) - T/2π + O(log T).
    In particular, N⁺(T) := #{γ : 0 < γ ≤ T, ζ(1/2+iγ)=0} ≥ cT·log(T) for T ≥ 2.
(2) For γ ≥ 1: γ/(1/4+γ²) ≥ 1/(2γ) (from `gamma_div_bound`).
(3) Dyadic decomposition: ∑_{1≤γ≤T} 1/γ ≥ c·log(T) → ∞.
(4) Zeros with 0 < γ < 1 contribute only a bounded amount (finitely many).
    In fact, the first zero ordinate is γ₁ ≈ 14.13, so this set is empty.

**Blocked by**: uniform Riemann-von Mangoldt (needs Stirling + Argument Principle).

References: Hardy 1914, Backlund 1918, Titchmarsh (1986) §9.4. -/
private theorem critical_zero_sum_diverges
    [CriticalZeroSumDivergesHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ M : ℝ, ∃ T : ℝ, T ≥ 2 ∧
      M ≤ ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2) :=
  CriticalZeroSumDivergesHyp.proof hRH

/-- Re((-I)/ρ) = -γ/(1/4+γ²) when Re(ρ) = 1/2, Im(ρ) = γ.
This is the key identity: alignment to w = -I produces the DIVERGENT sum
(negative for positive γ). -/
private lemma re_neg_I_div_eq (ρ : ℂ) (hρ_re : ρ.re = 1/2) :
    ((-I) / ρ).re = -ρ.im / (1/4 + ρ.im ^ 2) := by
  rw [Complex.div_re, Complex.neg_re, Complex.neg_im]
  simp only [Complex.I_re, Complex.I_im, neg_zero, Complex.normSq_apply]
  rw [hρ_re]
  ring

/-- The sum Σ_{S+} Re((-I)/ρ) = -Σ_{S+} γ/(1/4+γ²) for zeros with Re(ρ)=1/2. -/
private lemma sum_re_neg_I_div_eq (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    (∑ ρ ∈ PositiveImZerosBelow T, ((-I) / ρ).re) =
    -(∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2)) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun ρ hρ => by
    rw [re_neg_I_div_eq ρ (positiveImZerosBelow_re_half T hRH ρ hρ)]
    rw [neg_div])

/-- Re(I/ρ) = γ/(1/4+γ²) when Re(ρ) = 1/2.
Needed for the σ = -1 direction (alignment to w = I). -/
private lemma re_I_div_eq (ρ : ℂ) (hρ_re : ρ.re = 1/2) :
    (I / ρ).re = ρ.im / (1/4 + ρ.im ^ 2) := by
  rw [Complex.div_re]
  simp only [Complex.I_re, Complex.I_im, Complex.normSq_apply]
  rw [hρ_re]
  ring

/-- Sum version of re_I_div_eq: ∑_{S+} Re(I/ρ) = ∑_{S+} γ/(1/4+γ²). -/
private lemma sum_re_I_div_eq (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    (∑ ρ ∈ PositiveImZerosBelow T, (I / ρ).re) =
    (∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2)) :=
  Finset.sum_congr rfl (fun ρ hρ =>
    re_I_div_eq ρ (positiveImZerosBelow_re_half T hRH ρ hρ))

-- ============================================================
-- Conjugate bound infrastructure
-- ============================================================

/-- The subset of ZerosBelow T with strictly negative imaginary part. -/
private def NegativeImZerosBelow (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => ρ.im < 0)

/-- The subset of ZerosBelow T with zero imaginary part. -/
private def ZeroImZerosBelow (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => ρ.im = 0)

/-- Elements of ZerosBelow T are in CriticalZeros. -/
private lemma zerosBelow_mem_criticalZeros {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) :
    ρ ∈ CriticalZeros := by
  simp only [ZerosBelow] at hρ
  split_ifs at hρ with hfin
  · exact ((hfin.mem_toFinset).mp hρ).1
  · simp at hρ

/-- Elements of ZerosBelow T have |Im(ρ)| ≤ T. -/
private lemma zerosBelow_im_le {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) :
    |ρ.im| ≤ T := by
  simp only [ZerosBelow] at hρ
  split_ifs at hρ with hfin
  · exact ((hfin.mem_toFinset).mp hρ).2
  · simp at hρ

/-- Under RH, every element of ZerosBelow T has Re = 1/2. -/
private lemma zerosBelow_re_half {T : ℝ} (hRH : ZetaZeros.RiemannHypothesis)
    {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) : ρ.re = 1 / 2 :=
  hRH ρ (zerosBelow_mem_criticalZeros hρ)

/-- Im(conj ρ) = -Im(ρ) (handles starRingEnd unfolding). -/
private lemma conj_im_eq (ρ : ℂ) : (starRingEnd ℂ ρ).im = -ρ.im := by
  change (star ρ).im = _; simp [Complex.conj_im]

/-- Helper: conj ρ is in ZerosBelow T if ρ is. -/
private lemma conj_mem_zerosBelow {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) :
    starRingEnd ℂ ρ ∈ ZerosBelow T := by
  have hρ_crit := zerosBelow_mem_criticalZeros hρ
  have hconj_crit : starRingEnd ℂ ρ ∈ CriticalZeros := zero_conj_zero hρ_crit
  have hconj_im_le : |((starRingEnd ℂ) ρ).im| ≤ T := by
    rw [conj_im_eq, abs_neg]; exact zerosBelow_im_le hρ
  -- Extract finiteness from the fact that hρ is in ZerosBelow (not ∅)
  have hfin : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite := by
    by_contra h; simp only [ZerosBelow, dif_neg h] at hρ; simp at hρ
  simp only [ZerosBelow, dif_pos hfin]
  exact hfin.mem_toFinset.mpr ⟨hconj_crit, hconj_im_le⟩

/-- Conjugation sends positive-Im zeros to negative-Im zeros within ZerosBelow T. -/
private lemma conj_pos_mem_neg (T : ℝ) (_hRH : ZetaZeros.RiemannHypothesis) :
    ∀ ρ ∈ PositiveImZerosBelow T, starRingEnd ℂ ρ ∈ NegativeImZerosBelow T := by
  intro ρ hρ
  simp only [NegativeImZerosBelow, Finset.mem_filter]
  have hρ_zb : ρ ∈ ZerosBelow T := positiveImZerosBelow_sub T hρ
  have hρ_im : 0 < ρ.im := by
    simp only [PositiveImZerosBelow, Finset.mem_filter] at hρ; exact hρ.2
  exact ⟨conj_mem_zerosBelow hρ_zb, by rw [conj_im_eq]; linarith⟩

/-- Conjugation sends negative-Im zeros to positive-Im zeros within ZerosBelow T. -/
private lemma conj_neg_mem_pos (T : ℝ) (_hRH : ZetaZeros.RiemannHypothesis) :
    ∀ ρ ∈ NegativeImZerosBelow T, starRingEnd ℂ ρ ∈ PositiveImZerosBelow T := by
  intro ρ hρ
  simp only [PositiveImZerosBelow, Finset.mem_filter]
  simp only [NegativeImZerosBelow, Finset.mem_filter] at hρ
  exact ⟨conj_mem_zerosBelow hρ.1, by rw [conj_im_eq]; linarith⟩

/-- For real x > 0, Re(x^(conj ρ) / (conj ρ)) = Re(x^ρ / ρ).
Key: x^(conj ρ) = conj(x^ρ) for positive real x (via cpow_conj + conj_ofReal). -/
private lemma re_cpow_div_conj_eq (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    (((x : ℂ) ^ (starRingEnd ℂ ρ)) / (starRingEnd ℂ ρ)).re =
    (((x : ℂ) ^ ρ) / ρ).re := by
  -- (↑x)^(conj ρ) = conj((conj(↑x))^ρ) = conj((↑x)^ρ) since conj(↑x) = ↑x
  have harg : (↑x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact ne_of_lt Real.pi_pos
  have h_cpow : (↑x : ℂ) ^ (starRingEnd ℂ ρ) = starRingEnd ℂ ((↑x : ℂ) ^ ρ) := by
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  -- conj(z/w) = conj(z)/conj(w), so the whole expression is Re(conj(x^ρ/ρ)) = Re(x^ρ/ρ)
  have h_div : starRingEnd ℂ ((↑x : ℂ) ^ ρ) / starRingEnd ℂ ρ =
      starRingEnd ℂ (((↑x : ℂ) ^ ρ) / ρ) := (map_div₀ (starRingEnd ℂ) _ _).symm
  rw [h_cpow, h_div, Complex.conj_re]

/-- The non-positive-Im part of ZerosBelow decomposes into negative-Im and zero-Im.
Uses that ¬(0 < x) ↔ x ≤ 0 ↔ x < 0 ∨ x = 0 for real ordering. -/
private lemma nonPosIm_decomp (T : ℝ) :
    (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)) =
    NegativeImZerosBelow T ∪ ZeroImZerosBelow T := by
  ext ρ
  simp only [Finset.mem_filter, NegativeImZerosBelow, ZeroImZerosBelow,
    Finset.mem_union, Finset.mem_filter, not_lt]
  constructor
  · intro ⟨hmem, hle⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inl ⟨hmem, h⟩
    · exact Or.inr ⟨hmem, h⟩
  · rintro (⟨hmem, hlt⟩ | ⟨hmem, heq⟩)
    · exact ⟨hmem, le_of_lt hlt⟩
    · exact ⟨hmem, le_of_eq heq⟩

/-- Negative-Im and zero-Im parts are disjoint. -/
private lemma negIm_zeroIm_disjoint (T : ℝ) :
    Disjoint (NegativeImZerosBelow T) (ZeroImZerosBelow T) := by
  simp only [NegativeImZerosBelow, ZeroImZerosBelow]
  rw [Finset.disjoint_filter]
  intro ρ _ hlt heq
  linarith

/-- Under RH, the zero-Im part has at most 1 element (all such ρ = 1/2). -/
private lemma zeroIm_card_le_one (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    (ZeroImZerosBelow T).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro ρ₁ hρ₁ ρ₂ hρ₂
  simp only [ZeroImZerosBelow, Finset.mem_filter] at hρ₁ hρ₂
  have hre₁ := zerosBelow_re_half hRH hρ₁.1
  have hre₂ := zerosBelow_re_half hRH hρ₂.1
  exact Complex.ext (by rw [hre₁, hre₂]) (by rw [hρ₁.2, hρ₂.2])

/-- Each term in the zero-Im sum is bounded by 2√x. Under RH, ρ = 1/2 + 0i,
so x^ρ/ρ = x^{1/2}/(1/2) = 2√x. -/
private lemma zeroIm_term_bound (T : ℝ) (x : ℝ) (hx : x ≥ 2)
    (hRH : ZetaZeros.RiemannHypothesis)
    (ρ : ℂ) (hρ : ρ ∈ ZeroImZerosBelow T) :
    |(((x : ℂ) ^ ρ / ρ)).re| ≤ 2 * Real.sqrt x := by
  simp only [ZeroImZerosBelow, Finset.mem_filter] at hρ
  have hre : ρ.re = 1 / 2 := zerosBelow_re_half hRH hρ.1
  have him : ρ.im = 0 := hρ.2
  have hx_pos : (0 : ℝ) < x := by linarith
  -- Use norm bound: |Re(z)| ≤ ‖z‖
  calc |(((x : ℂ) ^ ρ / ρ)).re|
      ≤ ‖((x : ℂ) ^ ρ / ρ)‖ := Complex.abs_re_le_norm _
    _ = ‖(x : ℂ) ^ ρ‖ / ‖ρ‖ := norm_div _ _
    _ = x ^ ρ.re / ‖ρ‖ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    _ = x ^ (1 / 2 : ℝ) / ‖ρ‖ := by rw [hre]
    _ = Real.sqrt x / ‖ρ‖ := by rw [Real.sqrt_eq_rpow]
    _ = 2 * Real.sqrt x := by
        -- ρ = (1/2 : ℝ) as a complex number, so ‖ρ‖ = 1/2
        have hρ_eq : ρ = (↑(1/2 : ℝ) : ℂ) :=
          Complex.ext (by simp [hre]) (by simp [him])
        rw [hρ_eq, Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
        ring

/-- **B5b conjugate bound** (PROVED): Under RH, the full zero sum over ZerosBelow T
equals 2× the sum over PositiveImZerosBelow T, up to a bounded remainder R
with |R| ≤ 2√x, accounting for the possible zero at ρ = 1/2.

Proof: Under RH, zeros come in conjugate pairs ρ, ρ̄ (from the functional
equation ζ(s) = 0 ↔ ζ(1-s) = 0, with Re(ρ) = 1/2 giving 1-ρ = ρ̄). For real x > 0,
Re(x^ρ̄/ρ̄) = Re(conj(x^ρ/ρ)) = Re(x^ρ/ρ). The only unpaired zero has Im = 0
(at most ρ = 1/2 under RH), contributing |R| ≤ |x^{1/2}/(1/2)| = 2√x. -/
private theorem zero_sum_conjugate_bound (T : ℝ) (x : ℝ) (hx : x ≥ 2)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ R : ℝ, |R| ≤ 2 * Real.sqrt x ∧
      (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re =
      2 * (∑ ρ ∈ PositiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re + R := by
  -- Set f ρ := (x^ρ/ρ).re for convenience
  set f : ℂ → ℝ := fun ρ => (((x : ℂ) ^ ρ) / ρ).re with hf_def
  have hx_pos : (0 : ℝ) < x := by linarith
  -- ================================================================
  -- Step 1: Decompose ZerosBelow = PosIm + NonPosIm
  -- ================================================================
  have h_decomp :
      ∑ ρ ∈ ZerosBelow T, f ρ =
      ∑ ρ ∈ PositiveImZerosBelow T, f ρ +
      ∑ ρ ∈ (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)), f ρ :=
    (Finset.sum_filter_add_sum_filter_not (ZerosBelow T) (fun ρ => 0 < ρ.im) f).symm
  -- ================================================================
  -- Step 2: Decompose NonPosIm = NegIm + ZeroIm
  -- ================================================================
  have h_nonpos :
      ∑ ρ ∈ (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)), f ρ =
      ∑ ρ ∈ NegativeImZerosBelow T, f ρ + ∑ ρ ∈ ZeroImZerosBelow T, f ρ := by
    show ∑ ρ ∈ (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)), f ρ =
      ∑ ρ ∈ NegativeImZerosBelow T, f ρ + ∑ ρ ∈ ZeroImZerosBelow T, f ρ
    conv_lhs => rw [nonPosIm_decomp T]
    exact Finset.sum_union (negIm_zeroIm_disjoint T)
  -- ================================================================
  -- Step 3: NegIm sum = PosIm sum (via conjugation bijection)
  -- ================================================================
  have h_neg_eq_pos :
      ∑ ρ ∈ NegativeImZerosBelow T, f ρ =
      ∑ ρ ∈ PositiveImZerosBelow T, f ρ := by
    apply Finset.sum_nbij' (starRingEnd ℂ) (starRingEnd ℂ)
      (conj_neg_mem_pos T hRH) (conj_pos_mem_neg T hRH)
      (fun ρ _ => Complex.conj_conj ρ) (fun ρ _ => Complex.conj_conj ρ)
    intro ρ _hρ
    exact (re_cpow_div_conj_eq x hx_pos ρ).symm
  -- ================================================================
  -- Step 4: Bound the ZeroIm contribution
  -- ================================================================
  set R := ∑ ρ ∈ ZeroImZerosBelow T, f ρ with hR_def
  have hR_bound : |R| ≤ 2 * Real.sqrt x := by
    calc |R| ≤ ∑ ρ ∈ ZeroImZerosBelow T, |f ρ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ρ ∈ ZeroImZerosBelow T, (2 * Real.sqrt x) :=
          Finset.sum_le_sum (fun ρ hρ => zeroIm_term_bound T x hx hRH ρ hρ)
      _ = (ZeroImZerosBelow T).card * (2 * Real.sqrt x) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (2 * Real.sqrt x) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast zeroIm_card_le_one T hRH
      _ = 2 * Real.sqrt x := one_mul _
  -- ================================================================
  -- Step 5: Combine
  -- ================================================================
  refine ⟨R, hR_bound, ?_⟩
  -- Push .re through the sum: Re(∑ z) = ∑ Re(z)
  have h_re_sum : (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re =
      ∑ ρ ∈ ZerosBelow T, f ρ := by
    change Complex.reAddGroupHom (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)) = _
    rw [map_sum]; rfl
  have h_re_pos : (∑ ρ ∈ PositiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re =
      ∑ ρ ∈ PositiveImZerosBelow T, f ρ := by
    change Complex.reAddGroupHom (∑ ρ ∈ PositiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ)) = _
    rw [map_sum]; rfl
  rw [h_re_sum, h_re_pos, h_decomp, h_nonpos, h_neg_eq_pos]
  ring

/-- Positive-imaginary-part zeros have Im > 0 (tautology from filter definition). -/
private lemma positiveImZerosBelow_im_pos (T : ℝ) :
    ∀ ρ ∈ PositiveImZerosBelow T, 0 < ρ.im := by
  intro ρ hρ
  simp only [PositiveImZerosBelow, Finset.mem_filter] at hρ
  exact hρ.2

-- ============================================================
-- Helpers for assembly: growth comparison
-- ============================================================

/-- Exponential lower bound: e^u ≥ u³/27 for u ≥ 0.
Proof: e^{u/3} ≥ 1 + u/3 ≥ u/3, so e^u = (e^{u/3})³ ≥ (u/3)³. -/
private lemma exp_ge_cube_div (u : ℝ) (hu : u ≥ 0) : u ^ 3 / 27 ≤ Real.exp u := by
  have h3 : u / 3 ≤ Real.exp (u / 3) := by linarith [Real.add_one_le_exp (u / 3)]
  have h4 : (u / 3) ^ 3 ≤ Real.exp (u / 3) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h3 3
  have h5 : Real.exp (u / 3) ^ 3 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc u ^ 3 / 27 = (u / 3) ^ 3 := by ring
    _ ≤ Real.exp (u / 3) ^ 3 := h4
    _ = Real.exp u := h5

/-- For A ≥ 0, x ≥ exp(216A): A · (log x)² ≤ √x.
Proof: √x = e^{(logx)/2} ≥ ((logx)/2)³/27 = (logx)³/216.
Then A·(logx)² ≤ (logx)·(logx)²/216 = (logx)³/216 ≤ √x. -/
private lemma log_sq_le_sqrt (A : ℝ) (hA : A ≥ 0) (x : ℝ)
    (hx : x ≥ Real.exp (216 * A)) :
    A * (Real.log x) ^ 2 ≤ Real.sqrt x := by
  have hexp_pos : (0 : ℝ) < Real.exp (216 * A) := Real.exp_pos _
  have hx_pos : 0 < x := lt_of_lt_of_le hexp_pos hx
  -- Step 1: log x ≥ 216A
  have hlog_ge : Real.log x ≥ 216 * A := by
    rw [ge_iff_le, ← Real.log_exp (216 * A)]
    exact Real.log_le_log hexp_pos hx
  have hlog_nn : 0 ≤ Real.log x := by linarith [mul_nonneg (by norm_num : (216:ℝ) ≥ 0) hA]
  -- Step 2: √x = exp((logx)/2) ≥ (logx)³/216
  have h_sqrt_eq : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx_pos]
    congr 1; ring
  have h_sqrt_lb : (Real.log x) ^ 3 / 216 ≤ Real.sqrt x := by
    rw [h_sqrt_eq]
    calc (Real.log x) ^ 3 / 216
        = (Real.log x / 2) ^ 3 / 27 := by ring
      _ ≤ Real.exp (Real.log x / 2) := exp_ge_cube_div _ (by linarith)
  -- Step 3: A·(logx)² ≤ (logx)³/216 since logx ≥ 216A
  calc A * (Real.log x) ^ 2
      ≤ (Real.log x / 216) * (Real.log x) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        linarith
    _ = (Real.log x) ^ 3 / 216 := by ring
    _ ≤ Real.sqrt x := h_sqrt_lb

/-- Upper bound on (logT)²/√T for T ≥ 2: at most 432.
Proof: from exp_ge_cube_div, √T ≥ (logT)³/216.
So (logT)²/√T ≤ 216/logT ≤ 216/(1/2) = 432, using log 2 > 1/2. -/
private lemma logT_sq_div_sqrtT_le (T : ℝ) (hT : T ≥ 2) :
    (Real.log T) ^ 2 / Real.sqrt T ≤ 432 := by
  have hT_pos : 0 < T := by linarith
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  -- From exp_ge_cube_div: √T ≥ (logT)³/216
  have h_sqrt_eq : Real.sqrt T = Real.exp (Real.log T / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hT_pos]
    congr 1; ring
  have h_sqrt_lb : (Real.log T) ^ 3 / 216 ≤ Real.sqrt T := by
    rw [h_sqrt_eq]
    calc (Real.log T) ^ 3 / 216
        = (Real.log T / 2) ^ 3 / 27 := by ring
      _ ≤ Real.exp (Real.log T / 2) := exp_ge_cube_div _ (by linarith)
  -- So (logT)² ≤ 432 · √T, equivalently (logT)²/√T ≤ 432
  rw [div_le_iff₀ (Real.sqrt_pos_of_pos hT_pos)]
  -- Need: (logT)² ≤ 432 · √T
  -- From h_sqrt_lb: (logT)³/216 ≤ √T, so 432·√T ≥ 432·(logT)³/216 = 2·(logT)³
  -- And (logT)² ≤ 2·(logT)³ iff 1 ≤ 2·logT iff logT ≥ 1/2
  -- logT ≥ log 2 ≥ 1/2 (since exp(1/2) < 2, i.e., e < 4)
  have h_exp_half_le : Real.exp (1/2 : ℝ) ≤ 2 := by
    have := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)
      (n := 2) (by norm_num)
    simp [Finset.sum_range_succ] at this
    linarith
  have h_log2 : Real.log T ≥ 1/2 := by
    calc Real.log T ≥ Real.log 2 := Real.log_le_log (by norm_num) hT
      _ ≥ 1/2 := by
          rw [ge_iff_le, Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
          exact h_exp_half_le
  nlinarith [sq_nonneg (Real.log T)]

-- ============================================================
-- Landau-Ingham decomposition: 4 sub-lemmas (1 proved, 3 sorry)
-- ============================================================

/-- The "gap" integrand: under a one-sided bound on ψ(x)-x,
this integrand is nonneg for large x. -/
private noncomputable def landauIntegrand
    (σ : ℝ) (C₀ : ℝ) (x : ℝ) : ℝ :=
  C₀ * Real.sqrt x - σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x)

/-- **Sub-lemma 1/4** (PROVED): Integrand nonnegativity from one-sided bound. -/
private lemma landau_integrand_nonneg
    (σ C₀ X₀ : ℝ)
    (h_bound : ∀ x, x ≥ X₀ →
      σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≤ C₀ * Real.sqrt x)
    (x : ℝ) (hx : x ≥ X₀) :
    0 ≤ landauIntegrand σ C₀ x := by
  unfold landauIntegrand; linarith [h_bound x hx]

-- NOTE: The former sorry's `landau_mellin_analytic` and `landau_zeta_identity`
-- have been REMOVED. `landau_zeta_identity` was mathematically impossible:
-- it required F + G = ζ'/ζ on {Re > 1} with both F, G analytic on {Re > 1/2},
-- but ζ'/ζ has a simple pole at s = 1 ∈ {Re > 1/2} (proved in
-- `landau_pole_contradiction` below). The Landau-Ingham impossibility is now
-- captured as a single atomic sorry in `landau_psi_bounded_impossible`.

/-- **Sub-lemma 4/4** (PROVED): Pole contradiction.
If F + G represents ζ'/ζ for Re(s) > 1 and both F, G are analytic
on Re(s) > 1/2, then F + G is continuous at s = 1. But ζ'/ζ has a
simple pole at s = 1 (from `neg_zeta_logderiv_pole_at_one`).
Multiplying by (s-1): limit is 0 (from continuity) but also -1 (from pole).
Contradiction via `tendsto_nhds_unique`.

Note: RH is not needed — the hypotheses are already inconsistent due to
the s = 1 pole alone. The `hRH` parameter is kept for interface compatibility. -/
private theorem landau_pole_contradiction
    (_hRH : ZetaZeros.RiemannHypothesis)
    (F G : ℂ → ℂ)
    (hF : AnalyticOn ℂ F {s : ℂ | 1/2 < s.re})
    (hG : AnalyticOn ℂ G {s : ℂ | 1/2 < s.re})
    (h_id : ∀ s : ℂ, 1 < s.re →
      deriv riemannZeta s / riemannZeta s = F s + G s) :
    False := by
  -- The set {Re > 1/2} is open and contains 1
  have hS_open : IsOpen {s : ℂ | (1 : ℝ) / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1_mem : (1 : ℂ) ∈ {s : ℂ | (1 : ℝ) / 2 < s.re} := by
    show (1 : ℝ) / 2 < (1 : ℂ).re; simp [Complex.one_re]; norm_num
  -- F + G is continuous at s = 1
  have hFG_contAt : ContinuousAt (fun s => F s + G s) (1 : ℂ) :=
    (hF.continuousOn.continuousAt (hS_open.mem_nhds h1_mem)).add
      (hG.continuousOn.continuousAt (hS_open.mem_nhds h1_mem))
  -- Pole data: -ζ'/ζ(s) = g(s)/(s-1) near s = 1, g analytic, g(1) = 1
  obtain ⟨g, hg_an, hg1, hg_eq⟩ :=
    Aristotle.ZetaLogDerivInfra.neg_zeta_logderiv_pole_at_one
  -- The filter 𝓝[{Re > 1}] 1 is nontrivial (1 is on the boundary of {Re > 1})
  have hL_neBot : (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)).NeBot := by
    refine Filter.NeBot.mk ?_
    intro hbot
    have h_empty : (∅ : Set ℂ) ∈ 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ) := by
      rw [hbot]; exact Filter.mem_bot
    rw [mem_nhdsWithin] at h_empty
    obtain ⟨U, hU_open, h1U, hU_sub⟩ := h_empty
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open 1 h1U
    exact absurd (hU_sub ⟨hball (by
        simp only [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real]
        rw [Real.norm_of_nonneg (half_pos hε).le]
        linarith),
      show 1 < ((1 : ℂ) + (↑(ε / 2) : ℂ)).re from by
        simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith⟩)
      (by simp)
  -- 𝓝[{Re > 1}] 1 ≤ 𝓝[{1}ᶜ] 1 (since Re(s) > 1 implies s ≠ 1)
  have hL_le : 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ) ≤ 𝓝[{(1 : ℂ)}ᶜ] (1 : ℂ) :=
    nhdsWithin_mono (1 : ℂ) (fun (s : ℂ) (hs : s ∈ {s : ℂ | 1 < s.re}) =>
      show s ∈ {(1 : ℂ)}ᶜ from by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h; subst h; exact absurd hs (by simp [Complex.one_re]))
  -- On 𝓝[{Re > 1}] 1, eventually: (s-1) * (F s + G s) = -g s
  have h_eq_L : ∀ᶠ s in 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ),
      (s - 1) * (F s + G s) = -g s := by
    filter_upwards [hg_eq.filter_mono hL_le, self_mem_nhdsWithin]
      with s hpole (hs_re : s ∈ {s : ℂ | 1 < s.re})
    have hs_ne : s ≠ (1 : ℂ) := by
      intro h; subst h
      exact absurd hs_re (by simp [Set.mem_setOf_eq, Complex.one_re])
    have hs_sub_ne : s - 1 ≠ 0 := sub_ne_zero_of_ne hs_ne
    -- F s + G s = ζ'/ζ(s) = -(g(s)/(s-1)), so (s-1)*(F+G) = -g(s)
    have h_fg : F s + G s = -(g s / (s - 1)) := by
      rw [(h_id s hs_re).symm]
      exact neg_eq_iff_eq_neg.mp (by rwa [neg_div] at hpole)
    rw [h_fg, mul_neg, neg_inj]
    field_simp [hs_sub_ne]
  -- Limit 1: (s-1)*(F+G)(s) → 0 as s → 1
  have h_lim_0 : Filter.Tendsto (fun s => (s - 1) * (F s + G s))
      (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)) (𝓝 0) := by
    have h_sub : Filter.Tendsto (fun s : ℂ => s - 1) (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
      rw [show (0 : ℂ) = 1 - 1 from by ring]
      exact tendsto_id.sub tendsto_const_nhds
    have h_prod := h_sub.mul hFG_contAt
    rw [show (0 : ℂ) * (F (1 : ℂ) + G (1 : ℂ)) = 0 from zero_mul _] at h_prod
    exact h_prod.mono_left nhdsWithin_le_nhds
  -- Limit 2: (s-1)*(F+G)(s) → -1 (equals -g(s) eventually, g(1) = 1)
  have h_lim_neg1 : Filter.Tendsto (fun s => (s - 1) * (F s + G s))
      (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)) (𝓝 (-1)) := by
    have hg_lim : Filter.Tendsto (fun s => -g s)
        (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)) (𝓝 (-1)) := by
      have h4 := hg_an.continuousAt.neg.tendsto
      rw [hg1] at h4
      exact h4.mono_left nhdsWithin_le_nhds
    exact (Filter.tendsto_congr' h_eq_L).mpr hg_lim
  -- Contradiction: 0 = -1
  exact absurd (tendsto_nhds_unique h_lim_0 h_lim_neg1) (by norm_num)

/-- **B5b assembly** (PROVED from sub-sorry's): Core Landau-Ingham impossibility.
Under RH, σ·(ψ(x)-x) cannot be bounded above by C₀·√x for all large x.

Proof via explicit formula + Dirichlet phase alignment:
1. Get C_ef from ExplicitFormulaPsiGeneralHyp
2. Use critical_zero_sum_diverges to get T₀ with large Σ γ/(1/4+γ²) ≥ M₀
3. Align phases of PositiveImZerosBelow(T₀) to w = -σI
4. bound_real_part_of_sum_shifted_upper gives Σ Re(x^ρ/ρ) very negative (σ=1)
   or bound_real_part_of_sum_shifted gives Σ Re(x^ρ/ρ) very positive (σ=-1)
5. zero_sum_conjugate_bound relates full sum to positive-Im sum (factor of 2)
6. Explicit formula yields σ·(ψ(x)-x) > C₀·√x, contradicting h_bound

The parameter M₀ = 3456|C_ef| + |C₀| + 10 is chosen to absorb:
(a) |C_ef|·(logT₀)²/√T₀ ≤ 432|C_ef| (from logT_sq_div_sqrtT_le)
(b) |C_ef|·(logx)²/√x ≤ 1 (from log_sq_le_sqrt for x ≥ exp(216·A), A small)
(c) The 2√x remainder from conjugate bound
(d) The ε·D noise from phase alignment -/
private theorem landau_psi_bounded_impossible
    [ExplicitFormulaPsiGeneralHyp]
    [CriticalZeroSumDivergesHyp]
    [Aristotle.DirichletPhaseAlignment.PhaseAlignmentToTargetHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (C₀ X₀ : ℝ)
    (h_bound : ∀ x, x ≥ X₀ →
      σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≤
        C₀ * Real.sqrt x) :
    False := by
  -- ================================================================
  -- Step 1: Extract explicit formula constant, work with |C_ef|
  -- ================================================================
  obtain ⟨C_ef, hEF⟩ := ExplicitFormulaPsiGeneralHyp.proof
  set C := |C_ef| with hC_def
  have hC_nn : 0 ≤ C := abs_nonneg _
  -- The bound hEF with |C_ef| ≤ C:
  have hEF' : ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
      C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
    intro x T hx hT
    calc _ ≤ C_ef * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
            (Real.log x) ^ 2) := hEF x T hx hT
      _ ≤ |C_ef| * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
            (Real.log x) ^ 2) := by
          apply mul_le_mul_of_nonneg_right (le_abs_self _)
          apply add_nonneg
          · apply div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (Real.sqrt_nonneg _)
          · exact sq_nonneg _
  -- ================================================================
  -- Step 2: Choose M₀ and get T₀ from divergent sum
  -- ================================================================
  set M₀ := 3456 * C + |C₀| + 10 with hM₀_def
  have hM₀_pos : M₀ > 0 := by positivity
  obtain ⟨T₀, hT₀_ge, hT₀_sum⟩ := critical_zero_sum_diverges hRH M₀
  -- ================================================================
  -- Step 3: Set up S, D, ε
  -- ================================================================
  set S := PositiveImZerosBelow T₀ with hS_def
  have hS_re : ∀ ρ ∈ S, ρ.re = 1 / 2 := positiveImZerosBelow_re_half T₀ hRH
  have hS_pos : ∀ ρ ∈ S, 0 < ρ.im := positiveImZerosBelow_im_pos T₀
  have hS_zeta : ∀ ρ ∈ S, ρ ∈ ZetaZeros.zetaNontrivialZeros := by
    intro ρ hρ
    have hρ_zb := positiveImZerosBelow_sub T₀ hρ
    unfold ZerosBelow at hρ_zb
    split_ifs at hρ_zb with hfin
    · rw [Set.Finite.mem_toFinset] at hρ_zb
      exact hρ_zb.1
    · simp at hρ_zb
  set D := ∑ ρ ∈ S, 1 / ‖ρ‖ with hD_def
  have hD_nn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => by positivity)
  set M := ∑ ρ ∈ S, ρ.im / (1/4 + ρ.im ^ 2) with hM_def
  have hM_ge : M₀ ≤ M := hT₀_sum
  -- ε = 1/(4·(D+1)): ensures ε > 0 and ε·D < 1/4
  set ε := 1 / (4 * (D + 1)) with hε_def
  have hε_pos : ε > 0 := by positivity
  have hε_D : ε * D < 1 / 4 := by
    rw [hε_def, div_mul_eq_mul_div, one_mul]
    rw [div_lt_div_iff₀ (by positivity : 4 * (D + 1) > 0) (by norm_num : (0:ℝ) < 4)]
    nlinarith
  -- ================================================================
  -- Step 4: Choose X large enough, get aligned x
  -- ================================================================
  -- Need x ≥ X₀, x ≥ 2, x ≥ exp(216·A) where A = 8C/M₀ for log² domination
  set A_log := 8 * C / M₀ with hA_def
  have hA_nn : 0 ≤ A_log := by positivity
  set X := max X₀ (max 2 (Real.exp (216 * A_log))) with hX_def
  -- Get aligned x from phase alignment
  -- For σ=1: w = -I. For σ=-1: w = I. In both cases ‖w‖ = 1.
  set w := -(σ * I) with hw_def
  have hw_norm : ‖w‖ = 1 := by
    rcases hσ with rfl | rfl <;> simp [hw_def, norm_neg, Complex.norm_I]
  obtain ⟨x, hx_gt, hx_aligned⟩ := exists_large_x_phases_aligned_to_target
    S hS_zeta hS_re hS_pos w hw_norm ε hε_pos X hRH
  -- Extract useful bounds on x
  have hx_X₀ : x ≥ X₀ := by linarith [le_max_left X₀ (max 2 (Real.exp (216 * A_log)))]
  have hx_2 : x ≥ 2 := by
    have : X ≥ 2 := le_trans (le_max_left 2 _) (le_max_right X₀ _)
    linarith
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_exp : x ≥ Real.exp (216 * A_log) := by
    have : X ≥ Real.exp (216 * A_log) := le_trans (le_max_right 2 _) (le_max_right X₀ _)
    linarith
  -- ================================================================
  -- Step 5: Bound the positive-Im sum via phase alignment
  -- ================================================================
  -- Key identity: ∑ Re(w/ρ) = -(σ · M) (the divergent sum with sign)
  have h_sum_w : (∑ ρ ∈ S, (w / ρ).re) = -(σ * M) := by
    rcases hσ with rfl | rfl
    · -- σ = 1, w = -(1 * I) = -I
      have : w = -I := by simp [hw_def]
      rw [this, show -(1 * M) = -M from by ring]
      exact sum_re_neg_I_div_eq T₀ hRH
    · -- σ = -1, w = -(-1 * I) = I
      have : w = I := by simp [hw_def]
      rw [this, show -(-1 * M) = M from by ring]
      exact sum_re_I_div_eq T₀ hRH
  -- Upper bound on ∑_{S} Re(x^ρ/ρ) (used for σ=1)
  have h_upper := bound_real_part_of_sum_shifted_upper hS_re hx_pos hw_norm hε_pos hx_aligned
  -- Lower bound on ∑_{S} Re(x^ρ/ρ) (used for σ=-1)
  have h_lower := bound_real_part_of_sum_shifted hS_re hx_pos hw_norm hε_pos hx_aligned
  -- ================================================================
  -- Step 6: Apply conjugate bound
  -- ================================================================
  obtain ⟨R, hR_bound, hR_eq⟩ := zero_sum_conjugate_bound T₀ x hx_2 hRH
  -- ================================================================
  -- Step 7: Apply explicit formula at T = T₀
  -- ================================================================
  have hEF_at := hEF' x T₀ hx_2 hT₀_ge
  -- Rewrite: let sum_full = (∑ ρ ∈ ZerosBelow T₀, (x:ℂ)^ρ/ρ).re
  set sum_full := (∑ ρ ∈ ZerosBelow T₀, ((x : ℂ) ^ ρ) / ρ).re with hsum_full_def
  set sum_pos := (∑ ρ ∈ S, ((x : ℂ) ^ ρ) / ρ).re with hsum_pos_def
  -- From hR_eq: sum_full = 2 * sum_pos + R
  have h_sum_eq : sum_full = 2 * sum_pos + R := hR_eq
  -- ================================================================
  -- Step 8: Bound the error term
  -- ================================================================
  set err := C * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀ +
    (Real.log x) ^ 2) with herr_def
  -- hEF_at: |ψ(x) - x + sum_full| ≤ err (after sign adjustment)
  have hEF_abs : |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + sum_full| ≤ err := by
    convert hEF_at using 2
    ring
  -- Bound err ≤ (M₀/4) * √x in two parts:
  -- Part (a): C * √x * (logT₀)²/√T₀ ≤ 432C · √x ≤ (M₀/8) · √x
  have h_err_a : C * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀) ≤
      (M₀ / 8) * Real.sqrt x := by
    have h_logT := logT_sq_div_sqrtT_le T₀ hT₀_ge
    calc C * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀)
        = C * ((Real.log T₀) ^ 2 / Real.sqrt T₀) * Real.sqrt x := by ring
      _ ≤ C * 432 * Real.sqrt x := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left h_logT hC_nn
      _ = 432 * C * Real.sqrt x := by ring
      _ ≤ (M₀ / 8) * Real.sqrt x := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          have : M₀ = 3456 * C + |C₀| + 10 := hM₀_def
          nlinarith [abs_nonneg C₀]
  -- Part (b): C * (logx)² ≤ (M₀/8) · √x
  have h_err_b : C * (Real.log x) ^ 2 ≤ (M₀ / 8) * Real.sqrt x := by
    -- A_log = 8C/M₀, so C = A_log · M₀/8
    -- From log_sq_le_sqrt: A_log · (logx)² ≤ √x for x ≥ exp(216·A_log)
    have h_dom := log_sq_le_sqrt A_log hA_nn x hx_exp
    -- C · (logx)² = (A_log · M₀/8) · (logx)² = (M₀/8) · (A_log · (logx)²)
    --              ≤ (M₀/8) · √x
    calc C * (Real.log x) ^ 2
        = (M₀ / 8) * (A_log * (Real.log x) ^ 2) := by
          rw [hA_def]; field_simp
      _ ≤ (M₀ / 8) * Real.sqrt x := by
          apply mul_le_mul_of_nonneg_left h_dom
          positivity
  -- Combined: err ≤ (M₀/4) · √x
  have h_err_total : err ≤ (M₀ / 4) * Real.sqrt x := by
    calc err = C * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀) +
            C * (Real.log x) ^ 2 := by rw [herr_def]; ring
      _ ≤ (M₀ / 8) * Real.sqrt x + (M₀ / 8) * Real.sqrt x := add_le_add h_err_a h_err_b
      _ = (M₀ / 4) * Real.sqrt x := by ring
  -- ================================================================
  -- Step 9: Chain inequalities to contradiction
  -- ================================================================
  have h_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx_pos
  have h_sqrt_nn : 0 ≤ Real.sqrt x := le_of_lt h_sqrt_pos
  -- |a| ≤ b means -b ≤ a ≤ b
  have h_abs := abs_le.mp hEF_abs
  have h_psi_ge : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + sum_full ≥ -err :=
    h_abs.1
  have h_psi_le : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + sum_full ≤ err :=
    h_abs.2
  -- Case split on σ
  rcases hσ with rfl | rfl
  · -- ================================================================
    -- Case σ = 1: Show ψ(x) - x > C₀·√x (contradicts h_bound)
    -- ================================================================
    -- From h_upper: sum_pos ≤ √x · (∑ Re(w/ρ) + ε·D) = √x · (-M + ε·D)
    have h_pos_bound : sum_pos ≤ Real.sqrt x * (-M + ε * D) := by
      have h1 := h_upper
      rw [h_sum_w] at h1
      linarith
    -- From h_sum_eq: sum_full = 2·sum_pos + R ≤ 2√x(-M + εD) + 2√x
    have h_full_bound : sum_full ≤ 2 * Real.sqrt x * (-M + ε * D) + 2 * Real.sqrt x := by
      have hR_le : R ≤ 2 * Real.sqrt x := le_trans (le_abs_self R) hR_bound
      nlinarith [h_sum_eq, h_pos_bound]
    -- From h_psi_ge: ψ-x ≥ -sum_full - err
    -- So: ψ-x ≥ -(2√x(-M+εD) + 2√x) - (M₀/4)√x
    --        = √x · (2M - 2εD - 2 - M₀/4)
    have h_coeff : 2 * M - 2 * (ε * D) - 2 - M₀ / 4 > C₀ := by
      -- 2M - M₀/4 ≥ 2M₀ - M₀/4 = 7M₀/4
      have h1 : 2 * M - M₀ / 4 ≥ 7 * M₀ / 4 := by linarith [hM_ge]
      -- 7M₀/4 ≥ 7*(|C₀|+10)/4 > |C₀| + 5
      have h2 : 7 * M₀ / 4 ≥ 7 * (|C₀| + 10) / 4 := by
        have : M₀ ≥ |C₀| + 10 := by rw [hM₀_def]; linarith [hC_nn]
        linarith
      -- 2εD < 1/2
      have h3 : 2 * (ε * D) < 1 / 2 := by linarith [hε_D]
      -- Combine: coeff > 7(|C₀|+10)/4 - 1/2 - 2 ≥ |C₀| + 15 > |C₀| ≥ C₀
      have h4 : C₀ ≤ |C₀| := le_abs_self C₀
      nlinarith [abs_nonneg C₀]
    -- Get the contradiction: ψ(x) - x > C₀·√x
    -- From h_psi_ge: ψ-x ≥ -sum_full - err
    -- -sum_full ≥ -(2√x(-M+εD) + 2√x) = (2M-2εD-2)√x (from ring)
    -- err ≤ (M₀/4)√x, so ψ-x ≥ (2M-2εD-2-M₀/4)√x > C₀√x
    have h_key : -(2 * Real.sqrt x * (-M + ε * D) + 2 * Real.sqrt x) -
        (M₀ / 4) * Real.sqrt x =
        (2 * M - 2 * (ε * D) - 2 - M₀ / 4) * Real.sqrt x := by ring
    have h_psi_lb : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≥
        (2 * M - 2 * (ε * D) - 2 - M₀ / 4) * Real.sqrt x := by
      have h5 : -sum_full - err ≥
          -(2 * Real.sqrt x * (-M + ε * D) + 2 * Real.sqrt x) -
          (M₀ / 4) * Real.sqrt x := by linarith [h_full_bound, h_err_total]
      linarith [h_psi_ge, h_key]
    -- Contradiction with h_bound
    have := h_bound x hx_X₀
    simp only [one_mul] at this
    nlinarith [h_sqrt_nn]
  · -- ================================================================
    -- Case σ = -1: Show -(ψ(x) - x) > C₀·√x (contradicts h_bound)
    -- ================================================================
    -- From h_lower: sum_pos ≥ √x · (∑ Re(w/ρ) - ε·D) = √x · (M - ε·D)
    have h_pos_bound : sum_pos ≥ Real.sqrt x * (M - ε * D) := by
      have h1 := h_lower
      rw [h_sum_w] at h1
      linarith
    -- From h_sum_eq: sum_full = 2·sum_pos + R ≥ 2√x(M - εD) - 2√x
    have h_full_bound : sum_full ≥ 2 * Real.sqrt x * (M - ε * D) - 2 * Real.sqrt x := by
      have hR_ge : -(2 * Real.sqrt x) ≤ R := by linarith [neg_abs_le R, hR_bound]
      nlinarith [h_sum_eq, h_pos_bound]
    -- From h_psi_le: ψ-x ≤ -sum_full + err
    -- So: -(ψ-x) ≥ sum_full - err ≥ 2√x(M-εD) - 2√x - (M₀/4)√x
    -- Derive coeff > C₀ (same as σ=1 case)
    have hM₀_ge_abs : M₀ ≥ |C₀| + 10 := by rw [hM₀_def]; linarith [hC_nn]
    have h_2M_bound : 2 * M ≥ 2 * M₀ := by linarith [hM_ge]
    have h_M₀_quarter : M₀ / 4 ≤ M₀ := by linarith [hM₀_pos.le]
    have h_coeff_lb : 2 * M - 2 * (ε * D) - 2 - M₀ / 4 ≥ |C₀| + 5 := by linarith [hε_D]
    have h_coeff : 2 * M - 2 * (ε * D) - 2 - M₀ / 4 > C₀ := by linarith [le_abs_self C₀]
    -- Get the contradiction: -(ψ(x) - x) > C₀·√x
    have h_key : (2 * Real.sqrt x * (M - ε * D) - 2 * Real.sqrt x) -
        (M₀ / 4) * Real.sqrt x =
        (2 * M - 2 * (ε * D) - 2 - M₀ / 4) * Real.sqrt x := by ring
    have h_neg_psi_lb : -(Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≥
        (2 * M - 2 * (ε * D) - 2 - M₀ / 4) * Real.sqrt x := by
      have h5 : sum_full - err ≥
          (2 * Real.sqrt x * (M - ε * D) - 2 * Real.sqrt x) -
          (M₀ / 4) * Real.sqrt x := by linarith [h_full_bound, h_err_total]
      linarith [h_psi_le, h_key]
    -- Contradiction with h_bound
    have h_bd := h_bound x hx_X₀
    simp only [neg_one_mul, neg_le] at h_bd
    -- h_bd : -(C₀ * √x) ≤ ψ(x) - x, i.e., -(ψ-x) ≤ C₀√x
    -- h_neg_psi_lb : -(ψ-x) ≥ coeff * √x where coeff > C₀
    -- So: C₀√x ≥ -(ψ-x) ≥ coeff * √x > C₀ * √x (for √x > 0)
    have : C₀ * Real.sqrt x < (2 * M - 2 * (ε * D) - 2 - M₀ / 4) * Real.sqrt x :=
      mul_lt_mul_of_pos_right h_coeff h_sqrt_pos
    linarith

/-- **Landau-Ingham fact** (Landau 1905, Ingham 1932):
Under RH, ψ(x) - x is unbounded above relative to √x.
Proved from `landau_psi_bounded_impossible` via `by_contra` + `push_neg`. -/
private theorem landau_ingham_unbounded_above
    [ExplicitFormulaPsiGeneralHyp]
    [CriticalZeroSumDivergesHyp]
    [Aristotle.DirichletPhaseAlignment.PhaseAlignmentToTargetHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≥ C * Real.sqrt x := by
  by_contra h; push_neg at h
  obtain ⟨C₀, X₀, hbound⟩ := h
  exact landau_psi_bounded_impossible hRH 1 (Or.inl rfl) C₀ (X₀ + 1)
    (fun x hx => by simp only [one_mul]; exact (hbound x (by linarith)).le)

/-- Symmetric Landau-Ingham fact for the negative direction.
Proved from `landau_psi_bounded_impossible` via `by_contra` + `push_neg`. -/
private theorem landau_ingham_unbounded_below
    [ExplicitFormulaPsiGeneralHyp]
    [CriticalZeroSumDivergesHyp]
    [Aristotle.DirichletPhaseAlignment.PhaseAlignmentToTargetHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ C : ℝ, ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x ≤ -(C * Real.sqrt x) := by
  by_contra h; push_neg at h
  obtain ⟨C₀, X₀, hbound⟩ := h
  exact landau_psi_bounded_impossible hRH (-1) (Or.inr rfl) C₀ (X₀ + 1)
    (fun x hx => by
      simp only [neg_one_mul, neg_le]
      exact (hbound x (by linarith)).le)

-- ============================================================
-- Main theorem: PsiZeroSumOscillationHyp from Landau indirect argument
-- ============================================================

/-- **B5b proved from B5a** via Landau's indirect argument (Landau 1905, Ingham 1932):

Under RH, ψ(x) - x is unbounded in both directions relative to √x.

The top-level assembly is proved from `landau_psi_bounded_impossible`; inside that
proof, the remaining atomic leaves are:
- `critical_zero_sum_diverges` (in this file),
- `exists_large_x_phases_aligned_to_target` (in DirichletPhaseAlignment).
Both directions (above and below) are then proved via `by_contra` + `push_neg`. -/
theorem psiZeroSumOscillation_proved
    [ExplicitFormulaPsiGeneralHyp]
    [CriticalZeroSumDivergesHyp]
    [Aristotle.DirichletPhaseAlignment.PhaseAlignmentToTargetHyp] :
    PsiZeroSumOscillationHyp where
  proof := by
    intro hRH
    exact ⟨landau_ingham_unbounded_above hRH, landau_ingham_unbounded_below hRH⟩

end Aristotle.Standalone.PsiZeroSumOscillationFromIngham
