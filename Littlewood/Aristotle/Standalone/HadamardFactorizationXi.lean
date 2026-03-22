/-
  Hadamard Factorization for ξ(s) and the Partial Fraction of ζ'/ζ

  This file isolates the genuine xi/Hadamard input behind the `ζ'/ζ` bound.
  The relevant entire function is the corrected xi function
    `RiemannXiAlt(s) = (1 / 2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)`,
  not `completedRiemannZeta₀` itself.

  The architecture is intentionally split:
  1. `HadamardXiCore` is the minimal xi partial-fraction input actually used
     downstream.
  2. `HadamardXiHyp` adds optional metadata about the chosen zero enumeration.
  3. `logDeriv_completedRiemannZeta_partial_fraction` constructively transfers
     the xi partial fraction to the completed zeta log-derivative.
  4. `neg_zeta_logDeriv_partial_fraction` is then a pure algebraic wrapper once
     the standard completed-zeta logarithmic derivative split is supplied.
-/

import Mathlib
import Littlewood.Aristotle.RiemannXiEntire
import Littlewood.Aristotle.Standalone.WeierstrassElementaryFactors

set_option maxHeartbeats 800000
set_option autoImplicit false

open Complex Topology Filter

noncomputable section

namespace HadamardXi

/-! ## The Hadamard constant and zero sum -/

/-- Minimal Hadamard-style xi input actually consumed by the partial-fraction
    lane. The key identity lives on `RiemannXiAlt`, the entire xi function. -/
class HadamardXiCore where
  /-- The Hadamard constant B_ξ. -/
  B : ℂ
  /-- An enumeration of the nontrivial zeros. -/
  zeros : ℕ → ℂ
  /-- Zero density: Σ 1 / |ρ|² converges. -/
  summable_inv_sq : Summable (fun n => 1 / ‖zeros n‖ ^ 2)
  /-- The xi partial fraction: away from the enumerated zeros,
      `logDeriv RiemannXiAlt` is the Hadamard constant plus the zero sum. -/
  logDeriv_xi_eq : ∀ (s : ℂ), (∀ n, s ≠ zeros n) →
    HasSum (fun n => 1 / (s - zeros n) + 1 / zeros n)
      (logDeriv RiemannXiAlt s - B)

/-- Optional geometric metadata about the chosen zero enumeration. This is
    separate from `HadamardXiCore` because the downstream `ζ'/ζ` lane only
    consumes the xi partial-fraction identity itself. -/
class HadamardXiHyp extends HadamardXiCore where
  /-- Each zero lies in the critical strip. -/
  zeros_in_strip : ∀ n, 0 < (zeros n).re ∧ (zeros n).re < 1
  /-- The zeros are nonzero. -/
  zeros_ne_zero : ∀ n, zeros n ≠ 0

/-- A constructive canonical-product package for `RiemannXiAlt`. This is
stronger than the downstream `HadamardXiCore` leaf: instead of assuming the
partial-fraction identity outright, it asks for locally uniform convergence of
the genus-1 Hadamard partial products to `RiemannXiAlt`, plus nonvanishing away
from the enumerated zeros. -/
class HadamardXiCanonicalProduct where
  /-- The Hadamard constant in the exponential prefactor. -/
  B : ℂ
  /-- The nontrivial zeros used in the genus-1 product. -/
  zeros : ℕ → ℂ
  /-- The nonzero leading constant in the canonical product. -/
  xi0 : ℂ
  /-- The leading constant is nonzero. -/
  xi0_ne_zero : xi0 ≠ 0
  /-- The genus-1 convergence input. -/
  summable_inv_sq : Summable (fun n => 1 / ‖zeros n‖ ^ 2)
  /-- Each listed zero is nonzero, so the shifted elementary factors are the
      usual `E₁(s / ρ)`. -/
  zeros_ne_zero : ∀ n, zeros n ≠ 0
  /-- The genus-1 Hadamard partial products converge locally uniformly to
      `RiemannXiAlt` on all of `ℂ`. -/
  partialProducts_tendsto :
    TendstoLocallyUniformlyOn (fun N s =>
      xi0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
      RiemannXiAlt atTop Set.univ
  /-- Away from the listed zeros, the limiting xi function is nonvanishing. -/
  xi_nonzero_of_not_mem : ∀ s, (∀ n, s ≠ zeros n) → RiemannXiAlt s ≠ 0

/-- The bare locally uniform convergence input for a normalized xi canonical
product. This isolates the entire-function factorization statement from the
separate arithmetic obligations on the chosen factor locations. -/
class HadamardXiCanonicalProductData where
  /-- The Hadamard constant in the exponential prefactor. -/
  B : ℂ
  /-- The factor locations used in the genus-1 product. -/
  zeros : ℕ → ℂ

/-- The actual locally uniform convergence theorem for the normalized xi
canonical partial products attached to a chosen `B` and zero sequence. -/
abbrev HadamardXiPartialProductsTendstoHyp (B : ℂ) (zeros : ℕ → ℂ) : Prop :=
  TendstoLocallyUniformlyOn (fun N s =>
    RiemannXiAlt 0 * (Complex.exp (B * s) *
      ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
    RiemannXiAlt atTop Set.univ

/-- Class wrapper around the local-uniform convergence proposition for the
normalized xi partial products. -/
class HadamardXiPartialProductsTendsto (B : ℂ) (zeros : ℕ → ℂ) : Prop where
  /-- The normalized genus-1 Hadamard partial products converge locally
      uniformly to `RiemannXiAlt`. -/
  partialProducts_tendsto : HadamardXiPartialProductsTendstoHyp B zeros

/-- Bundled wrapper for the bare xi canonical-product convergence input. The
honest leaves are now `HadamardXiCanonicalProductData` and
`HadamardXiPartialProductsTendsto`. -/
class HadamardXiCanonicalProductConvergence where
  /-- The Hadamard constant in the exponential prefactor. -/
  B : ℂ
  /-- The factor locations used in the genus-1 product. -/
  zeros : ℕ → ℂ
  /-- The normalized genus-1 Hadamard partial products converge locally
      uniformly to `RiemannXiAlt`. -/
  partialProducts_tendsto :
    TendstoLocallyUniformlyOn (fun N s =>
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
      RiemannXiAlt atTop Set.univ

/-- The chosen factor locations are genuinely nonzero centers `ρ`, so the
shifted elementary factor `E₁(s / ρ)` vanishes at `s = ρ`. -/
abbrev HadamardXiFactorCentersHyp (zeros : ℕ → ℂ) : Prop :=
  ∀ n, zeros n ≠ 0

/-- Class wrapper around the nonzero-factor-centers hypothesis. -/
class HadamardXiFactorCenters (zeros : ℕ → ℂ) : Prop where
  /-- Each factor location is nonzero. -/
  zeros_ne_zero : HadamardXiFactorCentersHyp zeros

/-- The genus-1 convergence estimate needed to control the Hadamard termwise
logarithmic derivative. This is kept separate from the actual product
convergence statement. -/
abbrev HadamardXiSummableInvSqHyp (zeros : ℕ → ℂ) : Prop :=
  Summable (fun n => 1 / ‖zeros n‖ ^ 2)

/-- Class wrapper around the inverse-square summability hypothesis. -/
class HadamardXiSummableInvSq (zeros : ℕ → ℂ) : Prop where
  /-- The genus-1 convergence input. -/
  summable_inv_sq : HadamardXiSummableInvSqHyp zeros

/-- The pure canonical-product convergence package for `RiemannXiAlt`, before
adding any completeness statement about the xi zero set. This now packages the
three independent inputs: locally uniform convergence, nonzero factor centers,
and the inverse-square summability needed for the log-derivative series. -/
class HadamardXiCanonicalProductApprox where
  /-- The Hadamard constant in the exponential prefactor. -/
  B : ℂ
  /-- The factor locations used in the genus-1 product. -/
  zeros : ℕ → ℂ
  /-- The genus-1 convergence input. -/
  summable_inv_sq : Summable (fun n => 1 / ‖zeros n‖ ^ 2)
  /-- Each factor location is nonzero, so `E₁(s / ρ)` is genuinely centered at
      `ρ`. -/
  zeros_ne_zero : ∀ n, zeros n ≠ 0
  /-- The normalized genus-1 Hadamard partial products converge locally
      uniformly to `RiemannXiAlt`. -/
  partialProducts_tendsto :
    TendstoLocallyUniformlyOn (fun N s =>
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
      RiemannXiAlt atTop Set.univ

/-- The theorem-first Hadamard boundary now lives on the xi lane: the three
pure canonical-product inputs needed before the constructive zero-set bridge.
This is the honest minimal external leaf on the current path. Once these are
supplied, completeness of the xi zero set is recovered below from the product
itself, so no separate zero-cover hypothesis is needed on the main path. -/
abbrev HadamardXiApproxHyp (B : ℂ) (zeros : ℕ → ℂ) : Prop :=
  HadamardXiPartialProductsTendstoHyp B zeros ∧
    HadamardXiFactorCentersHyp zeros ∧
    HadamardXiSummableInvSqHyp zeros

/-- The local xi-side zero-exhaustion proposition for a chosen sequence of
factor locations. This is convenient inside the xi canonical-product lane, but
the external target is the strip-form zeta coverage proposition below. -/
abbrev HadamardXiCompleteXi (zeros : ℕ → ℂ) : Prop :=
  ∀ s, RiemannXiAlt s = 0 → ∃ n, s = zeros n

/-- The external zero-exhaustion proposition most natural from the zeta side:
the chosen sequence lists every critical-strip zero of `riemannZeta`. The xi
zero cover is recovered locally from the bridge lemmas below. -/
abbrev HadamardXiCompleteCriticalStrip (zeros : ℕ → ℂ) : Prop :=
  ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → ∃ n, s = zeros n

/-- Legacy theorem-first external bundle. The live Hadamard boundary is now
`HadamardXiApproxHyp`; this wrapper keeps the older strip-coverage add-on
available without putting it back on the main xi factorization path. -/
abbrev HadamardXiExternalHyp (B : ℂ) (zeros : ℕ → ℂ) : Prop :=
  HadamardXiApproxHyp B zeros ∧ HadamardXiCompleteCriticalStrip zeros

/-- Class wrapper around `HadamardXiCompleteXi`. This stays available for
typeclass plumbing, but the unbundled proposition is the primary leaf. -/
class HadamardXiZeroCover (zeros : ℕ → ℂ) : Prop where
  /-- Every zero of `RiemannXiAlt` is listed. -/
  xi_complete : HadamardXiCompleteXi zeros

/-- Class wrapper around the external strip-form zero coverage proposition. -/
class HadamardXiCriticalStripCover (zeros : ℕ → ℂ) : Prop where
  /-- Every critical-strip zeta zero is listed. -/
  complete : HadamardXiCompleteCriticalStrip zeros

/-- A zero-cover package stated directly for the entire xi function. This is a
more natural upstream surface for a generic Hadamard theorem on
`RiemannXiAlt`: the canonical product data plus the assertion that every xi zero
appears in the chosen sequence. The zeta-strip cover is then a wrapper via the
elementary xi/zeta bridge proved below. -/
class HadamardXiCanonicalProductXiCover where
  /-- The Hadamard constant in the exponential prefactor. -/
  B : ℂ
  /-- The nontrivial zeros used in the genus-1 product. -/
  zeros : ℕ → ℂ
  /-- The genus-1 convergence input. -/
  summable_inv_sq : Summable (fun n => 1 / ‖zeros n‖ ^ 2)
  /-- Each listed factor location is nonzero, so `E₁(s / ρ)` really has its
      simple zero at `s = ρ`. -/
  zeros_ne_zero : ∀ n, zeros n ≠ 0
  /-- The genus-1 Hadamard partial products with the correct xi normalization at
      `0` converge locally uniformly to `RiemannXiAlt`. -/
  partialProducts_tendsto :
    TendstoLocallyUniformlyOn (fun N s =>
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
      RiemannXiAlt atTop Set.univ
  /-- Every zero of `RiemannXiAlt` is listed. -/
  xi_complete : HadamardXiCompleteXi zeros

/-- A still smaller upstream package: the canonical-product data includes only
the nonzero factor locations together with coverage of all critical-strip zeta
zeros. The fact that each listed point is itself a critical-strip zero is
derived constructively from the locally uniform convergence, because the partial
products eventually vanish at that point. -/
class HadamardXiCanonicalProductCriticalCover where
  /-- The Hadamard constant in the exponential prefactor. -/
  B : ℂ
  /-- The nontrivial zeros used in the genus-1 product. -/
  zeros : ℕ → ℂ
  /-- The genus-1 convergence input. -/
  summable_inv_sq : Summable (fun n => 1 / ‖zeros n‖ ^ 2)
  /-- Each listed factor location is nonzero, so `E₁(s / ρ)` really has its
      simple zero at `s = ρ`. -/
  zeros_ne_zero : ∀ n, zeros n ≠ 0
  /-- The genus-1 Hadamard partial products with the correct xi normalization at
      `0` converge locally uniformly to `RiemannXiAlt`. -/
  partialProducts_tendsto :
    TendstoLocallyUniformlyOn (fun N s =>
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
      RiemannXiAlt atTop Set.univ
  /-- Every critical-strip zeta zero is listed. -/
  complete :
    ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → ∃ n, s = zeros n

/-- A smaller constructive upstream package: the genus-1 product converges to
`RiemannXiAlt`, and the chosen sequence is exactly an enumeration of the
critical-strip zeros of `riemannZeta`. The xi zero-set description is then
derived from the standard bridge `RiemannXiAlt = (1/2) s(s-1) Λ(s)` together
with the fact that `RiemannXiAlt` has no zeros outside `0 < Re(s) < 1`. -/
class HadamardXiCanonicalProductCriticalZeros where
  /-- The Hadamard constant in the exponential prefactor. -/
  B : ℂ
  /-- The nontrivial zeros used in the genus-1 product. -/
  zeros : ℕ → ℂ
  /-- The genus-1 convergence input. -/
  summable_inv_sq : Summable (fun n => 1 / ‖zeros n‖ ^ 2)
  /-- The genus-1 Hadamard partial products with the correct xi normalization at
      `0` converge locally uniformly to `RiemannXiAlt`. -/
  partialProducts_tendsto :
    TendstoLocallyUniformlyOn (fun N s =>
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
      RiemannXiAlt atTop Set.univ
  /-- Every listed point is a nontrivial zeta zero in the critical strip. -/
  zeros_spec : ∀ n, riemannZeta (zeros n) = 0 ∧ 0 < (zeros n).re ∧ (zeros n).re < 1
  /-- Every critical-strip zeta zero is listed. -/
  complete :
    ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → ∃ n, s = zeros n

/-- A narrower canonical-product package: the leading constant is fixed to the
actual xi value at `0`, and the remaining zero data is packaged as an exact
zero-set description for `RiemannXiAlt`. This is sufficient to build
`HadamardXiCanonicalProduct`. -/
class HadamardXiCanonicalProductZeroSet where
  /-- The Hadamard constant in the exponential prefactor. -/
  B : ℂ
  /-- The nontrivial zeros used in the genus-1 product. -/
  zeros : ℕ → ℂ
  /-- The genus-1 convergence input. -/
  summable_inv_sq : Summable (fun n => 1 / ‖zeros n‖ ^ 2)
  /-- The genus-1 Hadamard partial products with the correct xi normalization at
      `0` converge locally uniformly to `RiemannXiAlt`. -/
  partialProducts_tendsto :
    TendstoLocallyUniformlyOn (fun N s =>
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
      RiemannXiAlt atTop Set.univ
  /-- Exact zero-set description for the chosen enumeration. -/
  zero_iff : ∀ s, RiemannXiAlt s = 0 ↔ ∃ n, s = zeros n

private theorem RiemannXiAlt_zero_value : RiemannXiAlt 0 = (1 / 2 : ℂ) := by
  simp [RiemannXiAlt]

private theorem RiemannXiAlt_zero_ne_zero : RiemannXiAlt 0 ≠ 0 := by
  rw [RiemannXiAlt_zero_value]
  norm_num

private theorem RiemannXiAlt_one_value : RiemannXiAlt 1 = (1 / 2 : ℂ) := by
  simp [RiemannXiAlt]

private theorem RiemannXiAlt_one_ne_zero : RiemannXiAlt 1 ≠ 0 := by
  rw [RiemannXiAlt_one_value]
  norm_num

private theorem completedRiemannZeta_eq_zero_iff_riemannZeta_of_re_pos {s : ℂ}
    (hs : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hzeta := riemannZeta_def_of_ne_zero (s := s) hs0
  constructor
  · intro h
    rw [hzeta, h, zero_div]
  · intro h
    have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
    have hzeta_mul : riemannZeta s * Gammaℝ s = completedRiemannZeta s := by
      have hzeta' := congrArg (fun z => z * Gammaℝ s) hzeta
      simpa [div_eq_mul_inv, mul_assoc, hGamma] using hzeta'
    have : riemannZeta s * Gammaℝ s = 0 := by
      simp [h]
    simpa [hzeta_mul] using this

private theorem RiemannXiAlt_zero_iff_riemannZeta_zero_of_mem_strip {s : ℂ}
    (hre_pos : 0 < s.re) (hre_lt : s.re < 1) :
    RiemannXiAlt s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hre_pos
    simp at hre_pos
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hre_lt
    simp at hre_lt
  rw [RiemannXiAlt_eq_formula hs0 hs1]
  have hprod : ((1 / 2 : ℂ) * s * (s - 1)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) hs0)
      (sub_ne_zero.mpr hs1)
  constructor
  · intro h
    have hcomp : completedRiemannZeta s = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hprod
      · exact h'
    exact (completedRiemannZeta_eq_zero_iff_riemannZeta_of_re_pos hre_pos).mp hcomp
  · intro hzeta
    have hcomp : completedRiemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta_of_re_pos hre_pos).mpr hzeta
    rw [hcomp]
    ring

private theorem RiemannXiAlt_ne_zero_of_re_ge_one {s : ℂ} (hre : 1 ≤ s.re) (hs1 : s ≠ 1) :
    RiemannXiAlt s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst h
    norm_num at hre
  rw [RiemannXiAlt_eq_formula hs0 hs1]
  intro h
  have hprod : ((1 / 2 : ℂ) * s * (s - 1)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) hs0)
      (sub_ne_zero.mpr hs1)
  have hcomp : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hprod
    · exact h'
  have hzeta := (completedRiemannZeta_eq_zero_iff_riemannZeta_of_re_pos (by linarith)).mp hcomp
  exact riemannZeta_ne_zero_of_one_le_re hre hzeta

private theorem RiemannXiAlt_one_sub (s : ℂ) : RiemannXiAlt (1 - s) = RiemannXiAlt s := by
  unfold RiemannXiAlt
  rw [completedRiemannZeta₀_one_sub]
  ring

private theorem RiemannXiAlt_ne_zero_of_re_le_zero {s : ℂ} (hre : s.re ≤ 0) (hs0 : s ≠ 0) :
    RiemannXiAlt s ≠ 0 := by
  rw [← RiemannXiAlt_one_sub]
  apply RiemannXiAlt_ne_zero_of_re_ge_one
  · simp [Complex.sub_re, Complex.one_re]
    linarith
  · intro h
    have hre_eq : (1 - s).re = 1 := by simp [h]
    have him_eq : (1 - s).im = 0 := by simp [h]
    have hs_re : s.re = 0 := by
      simp [Complex.sub_re, Complex.one_re] at hre_eq
      linarith
    have hs_im : s.im = 0 := by
      simp [Complex.sub_im, Complex.one_im] at him_eq
      linarith
    exact hs0 (Complex.ext hs_re hs_im)

private theorem RiemannXiAlt_zero_re_in_strip {s : ℂ} (hxi : RiemannXiAlt s = 0) :
    0 < s.re ∧ s.re < 1 := by
  have hs0 : s ≠ 0 := by
    intro h
    exact RiemannXiAlt_zero_ne_zero <| by simpa [h] using hxi
  have hs1 : s ≠ 1 := by
    intro h
    exact RiemannXiAlt_one_ne_zero <| by simpa [h] using hxi
  have hre_pos : 0 < s.re := by
    by_contra hre
    push_neg at hre
    exact (RiemannXiAlt_ne_zero_of_re_le_zero hre hs0) hxi
  have hre_lt : s.re < 1 := by
    by_contra hre
    push_neg at hre
    exact (RiemannXiAlt_ne_zero_of_re_ge_one hre hs1) hxi
  exact ⟨hre_pos, hre_lt⟩

/-- The clean xi-side completeness statement derived from critical-strip zeta
coverage. This is the local xi-side bridge from the external strip-form zero
coverage proposition. -/
theorem hadamardXi_complete_xi {zeros : ℕ → ℂ}
    (hcomplete : HadamardXiCompleteCriticalStrip zeros) :
    HadamardXiCompleteXi zeros := by
  intro s hxi
  rcases RiemannXiAlt_zero_re_in_strip hxi with ⟨hre_pos, hre_lt⟩
  have hzeta : riemannZeta s = 0 :=
    (RiemannXiAlt_zero_iff_riemannZeta_zero_of_mem_strip hre_pos hre_lt).mp hxi
  exact hcomplete s hzeta hre_pos hre_lt

/-- Xi-side completeness recovers the external strip-form coverage proposition
via the xi/zeta zero bridge on `0 < Re(s) < 1`. -/
theorem hadamardXi_complete_critical_strip {zeros : ℕ → ℂ}
    (hxi_complete : HadamardXiCompleteXi zeros) :
    HadamardXiCompleteCriticalStrip zeros := by
  intro s hzeta hre_pos hre_lt
  have hxi : RiemannXiAlt s = 0 :=
    (RiemannXiAlt_zero_iff_riemannZeta_zero_of_mem_strip hre_pos hre_lt).mpr hzeta
  exact hxi_complete s hxi

/-- Convenience alias expressing the strip-cover wrapper as a theorem builder. -/
theorem hadamardXi_criticalStripCover_of_complete_xi {zeros : ℕ → ℂ}
    (hxi_complete : HadamardXiCompleteXi zeros) :
    HadamardXiCompleteCriticalStrip zeros :=
  hadamardXi_complete_critical_strip hxi_complete

/-- Package the primary xi-completeness proposition as the typeclass wrapper
used elsewhere in the file. -/
def hadamardXi_zeroCover_of_complete_xi {zeros : ℕ → ℂ}
    (hxi_complete : HadamardXiCompleteXi zeros) : HadamardXiZeroCover zeros where
  xi_complete := hxi_complete

/-- Package the external strip-form zero coverage proposition directly as the
xi zero-cover wrapper. -/
def hadamardXi_zeroCover_of_complete_critical_strip {zeros : ℕ → ℂ}
    (hcomplete : HadamardXiCompleteCriticalStrip zeros) : HadamardXiZeroCover zeros :=
  hadamardXi_zeroCover_of_complete_xi (hadamardXi_complete_xi hcomplete)

/-- Package the external strip-form zero coverage proposition as its wrapper
class. -/
def hadamardXi_criticalStripCover_of_complete_critical_strip {zeros : ℕ → ℂ}
    (hcomplete : HadamardXiCompleteCriticalStrip zeros) :
    HadamardXiCriticalStripCover zeros where
  complete := hcomplete

/-- Package the local-uniform convergence proposition as its typeclass wrapper. -/
def hadamardXi_partialProductsTendsto_of_hyp {B : ℂ} {zeros : ℕ → ℂ}
    (htend : HadamardXiPartialProductsTendstoHyp B zeros) :
    HadamardXiPartialProductsTendsto B zeros where
  partialProducts_tendsto := htend

/-- Package the nonzero-factor-centers proposition as its typeclass wrapper. -/
def hadamardXi_factorCenters_of_hyp {zeros : ℕ → ℂ}
    (hzeros : HadamardXiFactorCentersHyp zeros) : HadamardXiFactorCenters zeros where
  zeros_ne_zero := hzeros

/-- Package the inverse-square summability proposition as its typeclass
wrapper. -/
def hadamardXi_summableInvSq_of_hyp {zeros : ℕ → ℂ}
    (hsq : HadamardXiSummableInvSqHyp zeros) : HadamardXiSummableInvSq zeros where
  summable_inv_sq := hsq

/-- Package the live theorem-first Hadamard approximation surface as the
bundled approximation wrapper. -/
def hadamardXi_approx_of_approxHyp (B : ℂ) (zeros : ℕ → ℂ)
    (h : HadamardXiApproxHyp B zeros) : HadamardXiCanonicalProductApprox :=
  { B := B
    zeros := zeros
    summable_inv_sq := h.2.2
    zeros_ne_zero := h.2.1
    partialProducts_tendsto := h.1 }

/-- Extract the live theorem-first Hadamard approximation surface from the
bundled approximation wrapper. -/
theorem hadamardXi_approxHyp_of_approx (h : HadamardXiCanonicalProductApprox) :
    HadamardXiApproxHyp h.B h.zeros :=
  ⟨h.partialProducts_tendsto, h.zeros_ne_zero, h.summable_inv_sq⟩

/-- Extract the local-uniform convergence proposition from its wrapper class. -/
theorem hadamardXi_partialProductsTendsto_hyp_of_instance {B : ℂ} {zeros : ℕ → ℂ}
    (h : HadamardXiPartialProductsTendsto B zeros) :
    HadamardXiPartialProductsTendstoHyp B zeros :=
  h.partialProducts_tendsto

/-- Extract the nonzero-factor-centers proposition from its wrapper class. -/
theorem hadamardXi_factorCenters_hyp_of_instance {zeros : ℕ → ℂ}
    (h : HadamardXiFactorCenters zeros) : HadamardXiFactorCentersHyp zeros :=
  h.zeros_ne_zero

/-- Extract the inverse-square summability proposition from its wrapper class. -/
theorem hadamardXi_summableInvSq_hyp_of_instance {zeros : ℕ → ℂ}
    (h : HadamardXiSummableInvSq zeros) : HadamardXiSummableInvSqHyp zeros :=
  h.summable_inv_sq

/-- Extract the local-uniform convergence proposition from the live theorem-first
Hadamard approximation surface. -/
theorem hadamardXi_partialProductsTendsto_hyp_of_approxHyp {B : ℂ} {zeros : ℕ → ℂ}
    (h : HadamardXiApproxHyp B zeros) : HadamardXiPartialProductsTendstoHyp B zeros :=
  h.1

/-- Extract the nonzero-factor-centers proposition from the live theorem-first
Hadamard approximation surface. -/
theorem hadamardXi_factorCenters_hyp_of_approxHyp {B : ℂ} {zeros : ℕ → ℂ}
    (h : HadamardXiApproxHyp B zeros) : HadamardXiFactorCentersHyp zeros :=
  h.2.1

/-- Extract the inverse-square summability proposition from the live theorem-first
Hadamard approximation surface. -/
theorem hadamardXi_summableInvSq_hyp_of_approxHyp {B : ℂ} {zeros : ℕ → ℂ}
    (h : HadamardXiApproxHyp B zeros) : HadamardXiSummableInvSqHyp zeros :=
  h.2.2

/-- Extract the live theorem-first Hadamard approximation surface from the
legacy external bundle. -/
theorem hadamardXi_approxHyp_of_externalHyp {B : ℂ} {zeros : ℕ → ℂ}
    (h : HadamardXiExternalHyp B zeros) : HadamardXiApproxHyp B zeros :=
  h.1

/-- Extract the local-uniform convergence proposition from the legacy
theorem-first external Hadamard package. -/
theorem hadamardXi_partialProductsTendsto_hyp_of_externalHyp {B : ℂ} {zeros : ℕ → ℂ}
    (h : HadamardXiExternalHyp B zeros) : HadamardXiPartialProductsTendstoHyp B zeros :=
  hadamardXi_partialProductsTendsto_hyp_of_approxHyp (hadamardXi_approxHyp_of_externalHyp h)

/-- Extract the nonzero-factor-centers proposition from the legacy theorem-first
external Hadamard package. -/
theorem hadamardXi_factorCenters_hyp_of_externalHyp {B : ℂ} {zeros : ℕ → ℂ}
    (h : HadamardXiExternalHyp B zeros) : HadamardXiFactorCentersHyp zeros :=
  hadamardXi_factorCenters_hyp_of_approxHyp (hadamardXi_approxHyp_of_externalHyp h)

/-- Extract the inverse-square summability proposition from the legacy
theorem-first external Hadamard package. -/
theorem hadamardXi_summableInvSq_hyp_of_externalHyp {B : ℂ} {zeros : ℕ → ℂ}
    (h : HadamardXiExternalHyp B zeros) : HadamardXiSummableInvSqHyp zeros :=
  hadamardXi_summableInvSq_hyp_of_approxHyp (hadamardXi_approxHyp_of_externalHyp h)

/-- Extract the primary external strip-form zero coverage proposition from the
legacy theorem-first external Hadamard package. -/
theorem hadamardXi_complete_critical_strip_of_externalHyp {B : ℂ} {zeros : ℕ → ℂ}
    (h : HadamardXiExternalHyp B zeros) : HadamardXiCompleteCriticalStrip zeros :=
  h.2

/-- Extract the primary xi-completeness proposition from the wrapper class. -/
theorem hadamardXi_complete_xi_of_zeroCover {zeros : ℕ → ℂ}
    (hzero : HadamardXiZeroCover zeros) : HadamardXiCompleteXi zeros :=
  hzero.xi_complete

/-- Extract the primary external strip-form zero-coverage proposition from the
xi zero-cover wrapper. This keeps `HadamardXiZeroCover` secondary to the
strip-form target. -/
theorem hadamardXi_complete_critical_strip_of_zeroCover {zeros : ℕ → ℂ}
    (hzero : HadamardXiZeroCover zeros) : HadamardXiCompleteCriticalStrip zeros :=
  hadamardXi_complete_critical_strip hzero.xi_complete

instance (priority := 100) {zeros : ℕ → ℂ} [h : HadamardXiCriticalStripCover zeros] :
    HadamardXiZeroCover zeros :=
  hadamardXi_zeroCover_of_complete_critical_strip h.complete

private theorem RiemannXiAlt_zero_of_listed_zero_of_partialProducts
    (B : ℂ) (zeros : ℕ → ℂ) (hzeros : ∀ n, zeros n ≠ 0)
    (hprod : TendstoLocallyUniformlyOn (fun N s =>
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏ m ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros m) s))
      RiemannXiAlt atTop Set.univ)
    (n : ℕ) :
    RiemannXiAlt (zeros n) = 0 := by
  let F : ℕ → ℂ := fun N =>
    RiemannXiAlt 0 * (Complex.exp (B * zeros n) *
      ∏ m ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros m) (zeros n))
  have hF_tendsto : Tendsto F atTop (𝓝 (RiemannXiAlt (zeros n))) := by
    simpa [F] using hprod.tendsto_at (Set.mem_univ (zeros n))
  have hF_eq_zero : ∀ᶠ N in atTop, F N = 0 := by
    filter_upwards [Filter.eventually_ge_atTop (n + 1)] with N hN
    have hn_mem : n ∈ Finset.range N := by
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self n) hN)
    have hfactor_zero :
        WeierstrassFactors.epShifted 1 (zeros n) (zeros n) = 0 := by
      simpa using WeierstrassFactors.epShifted_at_a 1 (a := zeros n) (hzeros n)
    have hprod_zero :
        ∏ m ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros m) (zeros n) = 0 := by
      rw [Finset.prod_eq_zero_iff]
      exact ⟨n, hn_mem, hfactor_zero⟩
    simp [F, hprod_zero]
  have hF_zero_tendsto : Tendsto F atTop (𝓝 (0 : ℂ)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    exact hF_eq_zero.mono fun _ hN => hN.symm
  exact tendsto_nhds_unique hF_tendsto hF_zero_tendsto

instance (priority := 100) [h : HadamardXiCanonicalProductData]
    [htend : HadamardXiPartialProductsTendsto h.B h.zeros] :
    HadamardXiCanonicalProductConvergence where
  B := h.B
  zeros := h.zeros
  partialProducts_tendsto := htend.partialProducts_tendsto

/-- Direct theorem-first packaging of the canonical-product approximation from
explicit `B`, `zeros`, and the three remaining non-coverage hypotheses. -/
def hadamardXi_approx_of_external_input (B : ℂ) (zeros : ℕ → ℂ)
    (htend : HadamardXiPartialProductsTendstoHyp B zeros)
    (hsq : HadamardXiSummableInvSqHyp zeros)
    (hzeros : HadamardXiFactorCentersHyp zeros) :
    HadamardXiCanonicalProductApprox where
  B := B
  zeros := zeros
  summable_inv_sq := hsq
  zeros_ne_zero := hzeros
  partialProducts_tendsto := htend

/-- Direct theorem-first packaging of the canonical-product approximation from
the exact external Hadamard package. -/
def hadamardXi_approx_of_externalHyp (B : ℂ) (zeros : ℕ → ℂ)
    (h : HadamardXiExternalHyp B zeros) : HadamardXiCanonicalProductApprox :=
  hadamardXi_approx_of_approxHyp B zeros (hadamardXi_approxHyp_of_externalHyp h)

/-- Recover the exact external Hadamard package from an approximation together
with strip-form zero coverage. -/
theorem hadamardXi_externalHyp_of_approx (h : HadamardXiCanonicalProductApprox)
    (hcomplete : HadamardXiCompleteCriticalStrip h.zeros) :
    HadamardXiExternalHyp h.B h.zeros :=
  ⟨hadamardXi_approxHyp_of_approx h, hcomplete⟩

/-- Extract the local-uniform convergence proposition from the approximation
wrapper. -/
theorem hadamardXi_partialProductsTendsto_hyp_of_approx (h : HadamardXiCanonicalProductApprox) :
    HadamardXiPartialProductsTendstoHyp h.B h.zeros :=
  h.partialProducts_tendsto

/-- Extract the nonzero-factor-centers proposition from the approximation
wrapper. -/
theorem hadamardXi_factorCenters_hyp_of_approx (h : HadamardXiCanonicalProductApprox) :
    HadamardXiFactorCentersHyp h.zeros :=
  h.zeros_ne_zero

/-- Extract the inverse-square summability proposition from the approximation
wrapper. -/
theorem hadamardXi_summableInvSq_hyp_of_approx (h : HadamardXiCanonicalProductApprox) :
    HadamardXiSummableInvSqHyp h.zeros :=
  h.summable_inv_sq

instance (priority := 100) [h : HadamardXiCanonicalProductData]
    [htend : HadamardXiPartialProductsTendsto h.B h.zeros]
    [hsq : HadamardXiSummableInvSq h.zeros] [hzeros : HadamardXiFactorCenters h.zeros] :
    HadamardXiCanonicalProductApprox :=
  hadamardXi_approx_of_external_input h.B h.zeros
    htend.partialProducts_tendsto hsq.summable_inv_sq hzeros.zeros_ne_zero

/-- Package the canonical-product approximation together with the primary
xi-side completeness proposition into the bundled xi-cover class. -/
def hadamardXi_xiCover_of_complete_xi (h : HadamardXiCanonicalProductApprox)
    (hxi_complete : HadamardXiCompleteXi h.zeros) :
    HadamardXiCanonicalProductXiCover where
  B := h.B
  zeros := h.zeros
  summable_inv_sq := h.summable_inv_sq
  zeros_ne_zero := h.zeros_ne_zero
  partialProducts_tendsto := h.partialProducts_tendsto
  xi_complete := hxi_complete

/-- External packaging theorem: canonical-product approximation together with
critical-strip zeta coverage yields the bundled xi-cover class. The local
xi-side completeness proof is supplied by `hadamardXi_complete_xi`. -/
def hadamardXi_xiCover_of_complete_critical_strip (h : HadamardXiCanonicalProductApprox)
    (hcomplete : HadamardXiCompleteCriticalStrip h.zeros) :
    HadamardXiCanonicalProductXiCover :=
  hadamardXi_xiCover_of_complete_xi h (hadamardXi_complete_xi hcomplete)

/-- Fully external packaging theorem: explicit `B`, explicit zero sequence, the
three canonical-product hypotheses, and strip-form zeta zero coverage together
yield the bundled xi-cover class. -/
def hadamardXi_xiCover_of_external_input (B : ℂ) (zeros : ℕ → ℂ)
    (htend : HadamardXiPartialProductsTendstoHyp B zeros)
    (hsq : HadamardXiSummableInvSqHyp zeros)
    (hzeros : HadamardXiFactorCentersHyp zeros)
    (hcomplete : HadamardXiCompleteCriticalStrip zeros) :
    HadamardXiCanonicalProductXiCover :=
  hadamardXi_xiCover_of_complete_critical_strip
    (hadamardXi_approx_of_external_input B zeros htend hsq hzeros) hcomplete

/-- Fully external theorem-first packaging of the bundled xi-cover class from
the exact external Hadamard package. -/
def hadamardXi_xiCover_of_externalHyp (B : ℂ) (zeros : ℕ → ℂ)
    (h : HadamardXiExternalHyp B zeros) : HadamardXiCanonicalProductXiCover :=
  hadamardXi_xiCover_of_complete_critical_strip
    (hadamardXi_approx_of_externalHyp B zeros h)
    (hadamardXi_complete_critical_strip_of_externalHyp h)

/-- Recover the approximation wrapper from the larger xi-cover bundle. -/
def hadamardXi_approx_of_xiCover (h : HadamardXiCanonicalProductXiCover) :
    HadamardXiCanonicalProductApprox :=
  hadamardXi_approx_of_external_input h.B h.zeros
    h.partialProducts_tendsto h.summable_inv_sq h.zeros_ne_zero

/-- Extract xi-side completeness from the larger xi-cover bundle. -/
theorem hadamardXi_complete_xi_of_xiCover (h : HadamardXiCanonicalProductXiCover) :
    HadamardXiCompleteXi h.zeros :=
  h.xi_complete

/-- Extract the primary external strip-form zero-coverage proposition from the
larger xi-cover bundle. -/
theorem hadamardXi_complete_critical_strip_of_xiCover (h : HadamardXiCanonicalProductXiCover) :
    HadamardXiCompleteCriticalStrip h.zeros :=
  hadamardXi_complete_critical_strip h.xi_complete

/-- Recover the exact external Hadamard package from the larger xi-cover
bundle. This keeps `HadamardXiCanonicalProductXiCover` secondary to the
theorem-first external target. -/
theorem hadamardXi_externalHyp_of_xiCover (h : HadamardXiCanonicalProductXiCover) :
    HadamardXiExternalHyp h.B h.zeros :=
  hadamardXi_externalHyp_of_approx
    (hadamardXi_approx_of_xiCover h)
    (hadamardXi_complete_critical_strip_of_xiCover h)

instance (priority := 100) [h : HadamardXiCanonicalProductApprox]
    [hz : HadamardXiZeroCover h.zeros] :
    HadamardXiCanonicalProductXiCover :=
  hadamardXi_xiCover_of_complete_xi h hz.xi_complete

instance (priority := 100) [h : HadamardXiCanonicalProductXiCover] :
    HadamardXiCanonicalProductCriticalCover where
  B := h.B
  zeros := h.zeros
  summable_inv_sq := h.summable_inv_sq
  zeros_ne_zero := h.zeros_ne_zero
  partialProducts_tendsto := h.partialProducts_tendsto
  complete := by
    intro s hzeta hre_pos hre_lt
    have hxi : RiemannXiAlt s = 0 :=
      (RiemannXiAlt_zero_iff_riemannZeta_zero_of_mem_strip hre_pos hre_lt).mpr hzeta
    exact h.xi_complete s hxi

instance (priority := 100) [h : HadamardXiCanonicalProductCriticalCover] :
    HadamardXiCanonicalProductCriticalZeros where
  B := h.B
  zeros := h.zeros
  summable_inv_sq := h.summable_inv_sq
  partialProducts_tendsto := h.partialProducts_tendsto
  zeros_spec := by
    intro n
    have hxi_zero : RiemannXiAlt (h.zeros n) = 0 :=
      RiemannXiAlt_zero_of_listed_zero_of_partialProducts h.B h.zeros h.zeros_ne_zero
        h.partialProducts_tendsto n
    rcases RiemannXiAlt_zero_re_in_strip hxi_zero with ⟨hre_pos, hre_lt⟩
    exact
      ⟨(RiemannXiAlt_zero_iff_riemannZeta_zero_of_mem_strip hre_pos hre_lt).mp hxi_zero,
        hre_pos, hre_lt⟩
  complete := h.complete

instance (priority := 100) [h : HadamardXiCanonicalProductCriticalZeros] :
    HadamardXiCanonicalProductZeroSet where
  B := h.B
  zeros := h.zeros
  summable_inv_sq := h.summable_inv_sq
  partialProducts_tendsto := h.partialProducts_tendsto
  zero_iff := by
    intro s
    constructor
    · intro hxi
      rcases RiemannXiAlt_zero_re_in_strip hxi with ⟨hre_pos, hre_lt⟩
      have hzeta : riemannZeta s = 0 :=
        (RiemannXiAlt_zero_iff_riemannZeta_zero_of_mem_strip hre_pos hre_lt).mp hxi
      exact h.complete s hzeta hre_pos hre_lt
    · rintro ⟨n, rfl⟩
      rcases h.zeros_spec n with ⟨hzeta, hre_pos, hre_lt⟩
      exact (RiemannXiAlt_zero_iff_riemannZeta_zero_of_mem_strip hre_pos hre_lt).mpr hzeta

instance (priority := 100) [h : HadamardXiCanonicalProductZeroSet] :
    HadamardXiCanonicalProduct where
  B := h.B
  zeros := h.zeros
  xi0 := RiemannXiAlt 0
  xi0_ne_zero := RiemannXiAlt_zero_ne_zero
  summable_inv_sq := h.summable_inv_sq
  zeros_ne_zero := by
    intro n hzero
    have hxi_zero : RiemannXiAlt (h.zeros n) = 0 :=
      (h.zero_iff (h.zeros n)).2 ⟨n, rfl⟩
    exact RiemannXiAlt_zero_ne_zero <| by simpa [hzero] using hxi_zero
  partialProducts_tendsto := h.partialProducts_tendsto
  xi_nonzero_of_not_mem := by
    intro s hs_ne hzero
    rcases (h.zero_iff s).1 hzero with ⟨n, rfl⟩
    exact hs_ne n rfl

private def hadamardTerm (zeros : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  1 / (s - zeros n) + 1 / zeros n

private def xiFactor (zeros : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
  WeierstrassFactors.epShifted 1 (zeros n)

private def xiPartialProduct (xi0 B : ℂ) (zeros : ℕ → ℂ) (N : ℕ) : ℂ → ℂ :=
  fun s => xi0 * (Complex.exp (B * s) * ∏ n ∈ Finset.range N, xiFactor zeros n s)

private theorem hadamardTerm_eq_fraction (s ρ : ℂ) (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    1 / (s - ρ) + 1 / ρ = s / ((s - ρ) * ρ) := by
  field_simp [hρ, sub_ne_zero.mpr hsρ]
  ring

private theorem xiFactor_ne_zero (ρ s : ℂ) (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    WeierstrassFactors.epShifted 1 ρ s ≠ 0 := by
  rw [WeierstrassFactors.ep_one_shifted]
  intro h
  rw [mul_eq_zero] at h
  rcases h with hlin | hexp
  · apply hsρ
    have hdiv : s / ρ = (1 : ℂ) := (sub_eq_zero.mp hlin).symm
    simpa using (div_eq_iff hρ).mp hdiv
  · exact (exp_ne_zero _).elim hexp

private theorem logDeriv_one_sub_div_const (ρ s : ℂ) (hρ : ρ ≠ 0) (_hsρ : s ≠ ρ) :
    logDeriv (fun z : ℂ => 1 - z / ρ) s = 1 / (s - ρ) := by
  have hfun : (fun z : ℂ => 1 - z / ρ) = fun z => (ρ - z) * ρ⁻¹ := by
    ext z
    field_simp [hρ]
  calc
    logDeriv (fun z : ℂ => 1 - z / ρ) s
        = logDeriv (fun z : ℂ => (ρ - z) * ρ⁻¹) s := by
            simp [hfun]
    _ = logDeriv (fun z : ℂ => ρ - z) s := by
          simpa [mul_comm] using
            (logDeriv_mul_const (x := s) (f := fun z : ℂ => ρ - z) (a := ρ⁻¹)
              (inv_ne_zero hρ))
    _ = 1 / (s - ρ) := by
          simp only [logDeriv_apply]
          have hder : deriv (fun z : ℂ => ρ - z) s = (-1 : ℂ) := by
            simpa using (deriv_const_sub (f := fun z : ℂ => z) (c := ρ) (x := s))
          rw [hder]
          rw [show ρ - s = -(s - ρ) by ring, div_neg, neg_div]
          simp

private theorem logDeriv_exp_div_const (ρ s : ℂ) :
    logDeriv (fun z : ℂ => Complex.exp (z / ρ)) s = 1 / ρ := by
  simpa [Function.comp, Complex.LogDeriv_exp] using
    (logDeriv_comp
      (f := Complex.exp) (g := fun z : ℂ => z / ρ)
      Complex.differentiableAt_exp
      (differentiableAt_id.div_const ρ))

private theorem logDeriv_xiFactor (ρ s : ℂ) (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    logDeriv (WeierstrassFactors.epShifted 1 ρ) s = 1 / (s - ρ) + 1 / ρ := by
  have hfun : WeierstrassFactors.epShifted 1 ρ = fun z : ℂ =>
      (1 - z / ρ) * Complex.exp (z / ρ) := by
    ext z
    rw [WeierstrassFactors.ep_one_shifted]
  rw [hfun]
  have hlin_ne : (1 : ℂ) - s / ρ ≠ 0 := by
    intro h
    apply hsρ
    have hdiv : s / ρ = (1 : ℂ) := (sub_eq_zero.mp h).symm
    simpa using (div_eq_iff hρ).mp hdiv
  calc
    logDeriv (fun z : ℂ => (1 - z / ρ) * Complex.exp (z / ρ)) s
        = logDeriv (fun z : ℂ => 1 - z / ρ) s
            + logDeriv (fun z : ℂ => Complex.exp (z / ρ)) s := by
              simpa [Pi.mul_apply] using
                (logDeriv_mul (x := s)
                  (f := fun z : ℂ => 1 - z / ρ)
                  (g := fun z : ℂ => Complex.exp (z / ρ))
                  hlin_ne (exp_ne_zero _)
                  ((differentiableAt_const 1).sub (differentiableAt_id.div_const ρ))
                  (Complex.differentiableAt_exp.comp s (differentiableAt_id.div_const ρ)))
    _ = 1 / (s - ρ) + 1 / ρ := by
          rw [logDeriv_one_sub_div_const ρ s hρ hsρ, logDeriv_exp_div_const]

private theorem logDeriv_exp_mul_const (B s : ℂ) :
    logDeriv (fun z : ℂ => Complex.exp (B * z)) s = B := by
  have hlin : DifferentiableAt ℂ (fun z : ℂ => B * z) s := by
    simpa [one_mul] using
      ((differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) s).const_mul B)
  rw [logDeriv_apply, deriv_cexp hlin]
  rw [deriv_const_mul_field (x := s) (v := fun z : ℂ => z) B]
  simp

private theorem eventually_norm_ge_two_mul (zeros : ℕ → ℂ)
    (hzeros : ∀ n, zeros n ≠ 0)
    (hsq : Summable (fun n => 1 / ‖zeros n‖ ^ 2)) (s : ℂ) :
    ∀ᶠ n in atTop, 2 * ‖s‖ ≤ ‖zeros n‖ := by
  by_cases hs0 : s = 0
  · subst hs0
    exact Filter.Eventually.of_forall fun _ => by simp
  · have hsnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    have hε : 0 < (1 / (4 * ‖s‖ ^ 2 : ℝ)) := by positivity
    have htend : Tendsto (fun n => 1 / ‖zeros n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa [Nat.cofinite_eq_atTop] using hsq.tendsto_cofinite_zero
    filter_upwards [htend (Iio_mem_nhds hε)] with n hn
    have hsq_pos : 0 < ‖zeros n‖ ^ 2 := by
      have : 0 < ‖zeros n‖ := norm_pos_iff.mpr (hzeros n)
      positivity
    have hlt_sq : 4 * ‖s‖ ^ 2 < ‖zeros n‖ ^ 2 := by
      exact (one_div_lt_one_div hsq_pos (by positivity)).mp hn
    by_contra hsmall
    push_neg at hsmall
    have hsq_le : ‖zeros n‖ ^ 2 ≤ 4 * ‖s‖ ^ 2 := by
      have hpow : ‖zeros n‖ ^ 2 ≤ (2 * ‖s‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg (zeros n)) hsmall.le 2
      nlinarith [hpow]
    linarith

private theorem hadamardTerm_norm_le (s ρ : ℂ) (hρ : ρ ≠ 0) (hsρ : s ≠ ρ)
    (hlarge : 2 * ‖s‖ ≤ ‖ρ‖) :
    ‖1 / (s - ρ) + 1 / ρ‖ ≤ (2 * ‖s‖) * (1 / ‖ρ‖ ^ 2) := by
  have hsub : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
    have hrev : ‖ρ‖ - ‖s‖ ≤ ‖ρ - s‖ := norm_sub_norm_le ρ s
    have hhalf : ‖ρ‖ / 2 ≤ ‖ρ‖ - ‖s‖ := by nlinarith
    exact hhalf.trans <| by simpa [norm_sub_rev] using hrev
  have hρnorm : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr hρ
  calc
    ‖1 / (s - ρ) + 1 / ρ‖ = ‖s / ((s - ρ) * ρ)‖ := by
      rw [hadamardTerm_eq_fraction s ρ hρ hsρ]
    _ = ‖s‖ / (‖s - ρ‖ * ‖ρ‖) := by
      rw [norm_div, norm_mul]
    _ ≤ ‖s‖ / ((‖ρ‖ / 2) * ‖ρ‖) := by
      apply div_le_div_of_nonneg_left (norm_nonneg s)
      · positivity
      · exact mul_le_mul_of_nonneg_right hsub (norm_nonneg ρ)
    _ = (2 * ‖s‖) * (1 / ‖ρ‖ ^ 2) := by
      field_simp [hρnorm]
      

private theorem summable_hadamardTerms_of_summable_inv_sq (zeros : ℕ → ℂ)
    (hzeros : ∀ n, zeros n ≠ 0)
    (hsq : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (s : ℂ) (hs_ne : ∀ n, s ≠ zeros n) :
    Summable (fun n => hadamardTerm zeros s n) := by
  apply Summable.of_norm_bounded_eventually_nat
    (g := fun n => (2 * ‖s‖) * (1 / ‖zeros n‖ ^ 2))
  · exact hsq.mul_left (2 * ‖s‖)
  · filter_upwards [eventually_norm_ge_two_mul zeros hzeros hsq s] with n hn
    simpa [hadamardTerm] using hadamardTerm_norm_le s (zeros n) (hzeros n) (hs_ne n) hn

/-- The shifted genus-1 factors differ from `1` by a summable norm series. -/
private theorem summable_norm_sub_one_epShifted (zeros : ℕ → ℂ)
    (hzeros : ∀ n, zeros n ≠ 0)
    (hsq : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (s : ℂ) :
    Summable (fun n => ‖WeierstrassFactors.epShifted 1 (zeros n) s - 1‖) := by
  have hbound :
      ∀ᶠ n in atTop,
        ‖WeierstrassFactors.epShifted 1 (zeros n) s - 1‖ ≤
          3 * ‖s‖ ^ 2 * (1 / ‖zeros n‖ ^ 2) := by
    have hsmall : ∀ᶠ n in atTop, ‖s / zeros n‖ ≤ 1 / 2 := by
      filter_upwards [eventually_norm_ge_two_mul zeros hzeros hsq s] with n hn
      rw [norm_div]
      have hnorm_pos : 0 < ‖zeros n‖ := norm_pos_iff.mpr (hzeros n)
      have hhalf : ‖s‖ ≤ ‖zeros n‖ / 2 := by nlinarith
      calc
        ‖s‖ / ‖zeros n‖ ≤ (‖zeros n‖ / 2) / ‖zeros n‖ := by
          exact div_le_div_of_nonneg_right hhalf hnorm_pos.le
        _ = 1 / 2 := by
          field_simp [hnorm_pos.ne']
    filter_upwards [hsmall] with n hn
    calc
      ‖WeierstrassFactors.epShifted 1 (zeros n) s - 1‖
          = ‖1 - WeierstrassFactors.epShifted 1 (zeros n) s‖ := by
              rw [norm_sub_rev]
      _ ≤ 3 * ‖s / zeros n‖ ^ 2 := WeierstrassFactors.norm_one_sub_ep_one_shifted_le hn
      _ = 3 * (‖s‖ ^ 2 * (1 / ‖zeros n‖ ^ 2)) := by
            rw [norm_div, div_eq_mul_inv, mul_pow]
            ring
      _ = 3 * ‖s‖ ^ 2 * (1 / ‖zeros n‖ ^ 2) := by ring
  have hsummable :
      Summable (fun n => 3 * ‖s‖ ^ 2 * (1 / ‖zeros n‖ ^ 2)) := by
    exact hsq.mul_left _
  rw [← summable_nat_add_iff (Classical.choose (Filter.eventually_atTop.mp hbound))] at hsummable ⊢
  exact Summable.of_nonneg_of_le
    (fun n => norm_nonneg _)
    (fun n =>
      Classical.choose_spec (Filter.eventually_atTop.mp hbound) _ (Nat.le_add_left _ _))
    hsummable

/-- The shifted genus-1 product is multipliable at each fixed `s`. -/
private theorem multipliable_epShifted (zeros : ℕ → ℂ)
    (hzeros : ∀ n, zeros n ≠ 0)
    (hsq : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (s : ℂ) :
    Multipliable (fun n => WeierstrassFactors.epShifted 1 (zeros n) s) := by
  let f : ℕ → ℂ := fun n => WeierstrassFactors.epShifted 1 (zeros n) s - 1
  have hf : Summable (fun n => ‖f n‖) := by
    simpa [f] using summable_norm_sub_one_epShifted zeros hzeros hsq s
  convert multipliable_one_add_of_summable hf using 1
  ext n
  simp [f]

/-- The finite products converge to the unordered product. -/
private theorem tendsto_prod_epShifted (zeros : ℕ → ℂ)
    (hzeros : ∀ n, zeros n ≠ 0)
    (hsq : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (s : ℂ) :
    Tendsto (fun N => ∏ k ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros k) s)
      atTop (𝓝 (∏' n, WeierstrassFactors.epShifted 1 (zeros n) s)) :=
  (multipliable_epShifted zeros hzeros hsq s).hasProd.tendsto_prod_nat

/-- Away from the listed zeros, the convergent genus-1 product is nonzero. -/
private theorem tprod_epShifted_ne_zero (zeros : ℕ → ℂ)
    (hzeros : ∀ n, zeros n ≠ 0)
    (hsq : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (s : ℂ) (hs_ne : ∀ n, s ≠ zeros n) :
    ∏' n, WeierstrassFactors.epShifted 1 (zeros n) s ≠ 0 := by
  let f : ℕ → ℂ := fun n => WeierstrassFactors.epShifted 1 (zeros n) s - 1
  have hf : ∀ n, 1 + f n ≠ 0 := by
    intro n
    simpa [f] using xiFactor_ne_zero (zeros n) s (hzeros n) (hs_ne n)
  have hsumm : Summable (fun n => ‖f n‖) := by
    simpa [f] using summable_norm_sub_one_epShifted zeros hzeros hsq s
  simpa [f] using tprod_one_add_ne_zero_of_summable hf hsumm

/-- Local-uniform convergence of the normalized partial products identifies
`RiemannXiAlt` with the corresponding infinite genus-1 product. -/
private theorem RiemannXiAlt_eq_tprod (B : ℂ) (zeros : ℕ → ℂ)
    (hzeros : ∀ n, zeros n ≠ 0)
    (hsq : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hprod : TendstoLocallyUniformlyOn (fun N s =>
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
      RiemannXiAlt atTop Set.univ)
    (s : ℂ) :
    RiemannXiAlt s =
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏' n, WeierstrassFactors.epShifted 1 (zeros n) s) := by
  refine tendsto_nhds_unique (hprod.tendsto_at (Set.mem_univ s)) ?_
  refine Tendsto.mul tendsto_const_nhds ?_
  convert Tendsto.mul tendsto_const_nhds (tendsto_prod_epShifted zeros hzeros hsq s) using 1

/-- Product convergence forces `RiemannXiAlt` to be nonzero away from the
listed zeros. -/
private theorem xi_ne_zero_of_not_listed (B : ℂ) (zeros : ℕ → ℂ)
    (hzeros : ∀ n, zeros n ≠ 0)
    (hsq : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hprod : TendstoLocallyUniformlyOn (fun N s =>
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
      RiemannXiAlt atTop Set.univ)
    (s : ℂ) (hs_ne : ∀ n, s ≠ zeros n) :
    RiemannXiAlt s ≠ 0 := by
  rw [RiemannXiAlt_eq_tprod B zeros hzeros hsq hprod s]
  exact mul_ne_zero RiemannXiAlt_zero_ne_zero
    (mul_ne_zero (exp_ne_zero _)
      (tprod_epShifted_ne_zero zeros hzeros hsq s hs_ne))

/-- The normalized genus-1 product data already determines the exact zero set
of `RiemannXiAlt`: listed points are zeros by eventual vanishing of the finite
products, and away from the listed points the convergent infinite product is
nonzero. -/
def HadamardXiCanonicalProductZeroSet_of_product_and_summability
    (B : ℂ) (zeros : ℕ → ℂ)
    (hzeros : ∀ n, zeros n ≠ 0)
    (hsq : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hprod : TendstoLocallyUniformlyOn (fun N s =>
      RiemannXiAlt 0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, WeierstrassFactors.epShifted 1 (zeros n) s))
      RiemannXiAlt atTop Set.univ) :
    HadamardXiCanonicalProductZeroSet where
  B := B
  zeros := zeros
  summable_inv_sq := hsq
  partialProducts_tendsto := hprod
  zero_iff s := by
    constructor
    · intro hxi
      by_contra hs_listed
      push_neg at hs_listed
      exact (xi_ne_zero_of_not_listed B zeros hzeros hsq hprod s hs_listed) hxi
    · rintro ⟨n, rfl⟩
      exact RiemannXiAlt_zero_of_listed_zero_of_partialProducts B zeros hzeros hprod n

/-- Package the current theorem-first approximation surface as an exact xi
zero-set package. This removes the old external zero-cover field from the
critical Hadamard path. -/
def hadamardXi_zeroSet_of_approx (h : HadamardXiCanonicalProductApprox) :
    HadamardXiCanonicalProductZeroSet :=
  HadamardXiCanonicalProductZeroSet_of_product_and_summability
    h.B h.zeros h.zeros_ne_zero h.summable_inv_sq h.partialProducts_tendsto

/-- The current theorem-first Hadamard approximation surface already implies
xi-side completeness, via the exact zero-set bridge derived from the canonical
product itself. -/
theorem hadamardXi_complete_xi_of_approx (h : HadamardXiCanonicalProductApprox) :
    HadamardXiCompleteXi h.zeros := by
  intro s hxi
  exact (hadamardXi_zeroSet_of_approx h).zero_iff s |>.mp hxi

/-- The approximation surface also implies the primary strip-form zero
coverage proposition, because xi-completeness now follows constructively from
the canonical product. -/
theorem hadamardXi_complete_critical_strip_of_approx (h : HadamardXiCanonicalProductApprox) :
    HadamardXiCompleteCriticalStrip h.zeros :=
  hadamardXi_complete_critical_strip (hadamardXi_complete_xi_of_approx h)

/-- Package the approximation surface directly as the bundled xi-cover class.
This is now constructive and does not need any extra zero-coverage input. -/
def hadamardXi_xiCover_of_approx (h : HadamardXiCanonicalProductApprox) :
    HadamardXiCanonicalProductXiCover :=
  hadamardXi_xiCover_of_complete_xi h (hadamardXi_complete_xi_of_approx h)

/-- Direct theorem-first packaging of the bundled xi-cover class from the live
Hadamard approximation surface. -/
def hadamardXi_xiCover_of_approxHyp (B : ℂ) (zeros : ℕ → ℂ)
    (h : HadamardXiApproxHyp B zeros) : HadamardXiCanonicalProductXiCover :=
  hadamardXi_xiCover_of_approx (hadamardXi_approx_of_approxHyp B zeros h)

/-- Fully external theorem-first packaging of the bundled xi-cover class from
the live Hadamard approximation inputs. -/
def hadamardXi_xiCover_of_approx_input (B : ℂ) (zeros : ℕ → ℂ)
    (htend : HadamardXiPartialProductsTendstoHyp B zeros)
    (hsq : HadamardXiSummableInvSqHyp zeros)
    (hzeros : HadamardXiFactorCentersHyp zeros) :
    HadamardXiCanonicalProductXiCover :=
  hadamardXi_xiCover_of_approxHyp B zeros ⟨htend, hzeros, hsq⟩

instance (priority := 100) [h : HadamardXiCanonicalProductApprox] :
    HadamardXiCanonicalProductZeroSet :=
  hadamardXi_zeroSet_of_approx h

private theorem differentiable_xiFiniteProduct (zeros : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (fun z : ℂ => ∏ n ∈ Finset.range N, xiFactor zeros n z) := by
  intro z
  convert
    (DifferentiableAt.finset_prod
      (u := Finset.range N) (f := fun n => xiFactor zeros n) ?_) using 1
  · ext w
    simp
  intro n hn
  simpa [xiFactor] using (WeierstrassFactors.differentiable_epShifted 1 (zeros n) z)

private theorem differentiable_xiPartialProduct (xi0 B : ℂ) (zeros : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (xiPartialProduct xi0 B zeros N) := by
  intro z
  unfold xiPartialProduct
  have hlin : DifferentiableAt ℂ (fun w : ℂ => B * w) z := by
    simpa [one_mul] using
      ((differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ => w) z).const_mul B)
  exact
    ((Complex.differentiableAt_exp.comp z hlin).mul
      (differentiable_xiFiniteProduct zeros N z)).const_mul xi0

private theorem logDeriv_xiPartialProduct (xi0 B : ℂ) (hxi0 : xi0 ≠ 0)
    (zeros : ℕ → ℂ) (hzeros : ∀ n, zeros n ≠ 0)
    (s : ℂ) (hs_ne : ∀ n, s ≠ zeros n) (N : ℕ) :
    logDeriv (xiPartialProduct xi0 B zeros N) s =
      B + ∑ n ∈ Finset.range N, hadamardTerm zeros s n := by
  unfold xiPartialProduct
  have hprod_ne : ∏ n ∈ Finset.range N, xiFactor zeros n s ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro n hn
    exact xiFactor_ne_zero (zeros n) s (hzeros n) (hs_ne n)
  have hprod_diff : DifferentiableAt ℂ (fun z => ∏ n ∈ Finset.range N, xiFactor zeros n z) s := by
    exact differentiable_xiFiniteProduct zeros N s
  calc
    logDeriv (fun s => xi0 * (Complex.exp (B * s) *
        ∏ n ∈ Finset.range N, xiFactor zeros n s)) s
        = logDeriv (fun s => Complex.exp (B * s) *
            ∏ n ∈ Finset.range N, xiFactor zeros n s) s := by
              simpa using
                (logDeriv_const_mul
                  (f := fun z : ℂ => Complex.exp (B * z) *
                    ∏ n ∈ Finset.range N, xiFactor zeros n z)
                  s xi0 hxi0)
    _ = logDeriv (fun z : ℂ => Complex.exp (B * z)) s
          + logDeriv (fun z => ∏ n ∈ Finset.range N, xiFactor zeros n z) s := by
            simpa [Pi.mul_apply] using
              (logDeriv_mul (x := s)
                (f := fun z : ℂ => Complex.exp (B * z))
                (g := fun z => ∏ n ∈ Finset.range N, xiFactor zeros n z)
                (exp_ne_zero _) hprod_ne
                (by
                  have hlin : DifferentiableAt ℂ (fun z : ℂ => B * z) s := by
                    simpa [one_mul] using
                      ((differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) s).const_mul B)
                  exact Complex.differentiableAt_exp.comp s hlin)
                hprod_diff)
    _ = B + ∑ n ∈ Finset.range N, hadamardTerm zeros s n := by
          rw [logDeriv_exp_mul_const]
          rw [logDeriv_prod (Finset.range N) (xiFactor zeros) s]
          · congr 1
            refine Finset.sum_congr rfl ?_
            intro n hn
            simpa [hadamardTerm, xiFactor] using
              logDeriv_xiFactor (zeros n) s (hzeros n) (hs_ne n)
          · intro n hn
            exact xiFactor_ne_zero (zeros n) s (hzeros n) (hs_ne n)
          · intro n hn
            exact (WeierstrassFactors.differentiable_epShifted 1 (zeros n) s)

/-- Canonical-product convergence of genus-1 xi partial products implies the
Hadamard partial-fraction identity for `logDeriv RiemannXiAlt`. -/
theorem logDeriv_xi_eq_of_canonicalProduct (B xi0 : ℂ) (hxi0 : xi0 ≠ 0)
    (zeros : ℕ → ℂ) (hzeros : ∀ n, zeros n ≠ 0)
    (hsq : Summable (fun n => 1 / ‖zeros n‖ ^ 2))
    (hprod : TendstoLocallyUniformlyOn (xiPartialProduct xi0 B zeros) RiemannXiAlt atTop Set.univ)
    (hxi_ne : ∀ s, (∀ n, s ≠ zeros n) → RiemannXiAlt s ≠ 0)
    (s : ℂ) (hs_ne : ∀ n, s ≠ zeros n) :
    HasSum (fun n => hadamardTerm zeros s n) (logDeriv RiemannXiAlt s - B) := by
  have hsumm : Summable (fun n => hadamardTerm zeros s n) :=
    summable_hadamardTerms_of_summable_inv_sq zeros hzeros hsq s hs_ne
  refine (hsumm.hasSum_iff_tendsto_nat).2 ?_
  have hlog :
      Tendsto (fun N : ℕ => logDeriv (xiPartialProduct xi0 B zeros N) s) atTop
        (𝓝 (logDeriv RiemannXiAlt s)) := by
    simpa using
      (Complex.logDeriv_tendsto isOpen_univ ⟨s, Set.mem_univ s⟩ hprod
        (Filter.Eventually.of_forall fun N =>
          (differentiable_xiPartialProduct xi0 B zeros N).differentiableOn)
        (hxi_ne s hs_ne))
  have hsum_plus :
      Tendsto (fun N : ℕ => B + ∑ n ∈ Finset.range N, hadamardTerm zeros s n) atTop
        (𝓝 (logDeriv RiemannXiAlt s)) := by
    exact hlog.congr' <| Filter.Eventually.of_forall fun N =>
      logDeriv_xiPartialProduct xi0 B hxi0 zeros hzeros s hs_ne N
  have hsum :
      Tendsto (fun N : ℕ => (B + ∑ n ∈ Finset.range N, hadamardTerm zeros s n) - B) atTop
        (𝓝 (logDeriv RiemannXiAlt s - B)) := by
    exact hsum_plus.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => B) atTop (𝓝 B))
  convert hsum using 1
  ext N
  ring

instance (priority := 100) [h : HadamardXiCanonicalProduct] : HadamardXiCore where
  B := h.B
  zeros := h.zeros
  summable_inv_sq := h.summable_inv_sq
  logDeriv_xi_eq := by
    intro s hs_ne
    simpa [hadamardTerm] using
      logDeriv_xi_eq_of_canonicalProduct h.B h.xi0 h.xi0_ne_zero
        h.zeros h.zeros_ne_zero h.summable_inv_sq h.partialProducts_tendsto
        h.xi_nonzero_of_not_mem s hs_ne

/-- Package the larger xi-cover bundle directly as the downstream xi core. This
keeps `HadamardXiCanonicalProductXiCover` secondary to the theorem-first
external inputs. -/
def hadamardXi_core_of_xiCover (h : HadamardXiCanonicalProductXiCover) :
    HadamardXiCore := by
  letI : HadamardXiCanonicalProductXiCover := h
  exact inferInstance

/-- The approximation package alone already yields the downstream xi core,
through the derived exact zero-set package. -/
def hadamardXi_core_of_approx (h : HadamardXiCanonicalProductApprox) :
    HadamardXiCore := by
  letI : HadamardXiCanonicalProductApprox := h
  exact inferInstance

/-- Direct theorem-first route from the live Hadamard approximation surface to
the downstream xi core. -/
def hadamardXi_core_of_approxHyp (B : ℂ) (zeros : ℕ → ℂ)
    (h : HadamardXiApproxHyp B zeros) : HadamardXiCore :=
  hadamardXi_core_of_approx (hadamardXi_approx_of_approxHyp B zeros h)

/-- Fully external theorem-first route from the live Hadamard approximation
inputs straight to the downstream xi core. -/
def hadamardXi_core_of_approx_input (B : ℂ) (zeros : ℕ → ℂ)
    (htend : HadamardXiPartialProductsTendstoHyp B zeros)
    (hsq : HadamardXiSummableInvSqHyp zeros)
    (hzeros : HadamardXiFactorCentersHyp zeros) :
    HadamardXiCore :=
  hadamardXi_core_of_approxHyp B zeros ⟨htend, hzeros, hsq⟩

/-- External packaging theorem straight to the downstream xi core from a
canonical-product approximation plus strip-form zeta zero coverage. This keeps
the intermediate xi-cover bundles optional for callers. -/
def hadamardXi_core_of_complete_critical_strip (h : HadamardXiCanonicalProductApprox)
    (_hcomplete : HadamardXiCompleteCriticalStrip h.zeros) : HadamardXiCore :=
  hadamardXi_core_of_approx h

/-- Fully external theorem-first packaging straight to the downstream xi core:
explicit `B`, explicit zero sequence, the three analytic hypotheses, and
strip-form zeta zero coverage are sufficient. -/
def hadamardXi_core_of_external_input (B : ℂ) (zeros : ℕ → ℂ)
    (htend : HadamardXiPartialProductsTendstoHyp B zeros)
    (hsq : HadamardXiSummableInvSqHyp zeros)
    (hzeros : HadamardXiFactorCentersHyp zeros)
    (_hcomplete : HadamardXiCompleteCriticalStrip zeros) :
    HadamardXiCore :=
  hadamardXi_core_of_approx_input B zeros htend hsq hzeros

/-- Fully external theorem-first packaging straight to the downstream xi core
from the exact external Hadamard package. -/
def hadamardXi_core_of_externalHyp (B : ℂ) (zeros : ℕ → ℂ)
    (h : HadamardXiExternalHyp B zeros) : HadamardXiCore :=
  hadamardXi_core_of_approx (hadamardXi_approx_of_externalHyp B zeros h)

/-! ## Convergence of the zero sum -/

section

variable [h : HadamardXiCore]

/-- The Hadamard zero sum converges away from the enumerated zeros. -/
theorem summable_hadamard_terms (s : ℂ) (hs_ne : ∀ n, s ≠ h.zeros n) :
    Summable (fun n => 1 / (s - h.zeros n) + 1 / h.zeros n) :=
  (h.logDeriv_xi_eq s hs_ne).summable

/-- The zero sum as a function of `s`. -/
def zeroSum (s : ℂ) : ℂ :=
  ∑' n, (1 / (s - h.zeros n) + 1 / h.zeros n)

/-- `logDeriv RiemannXiAlt` is the Hadamard constant plus the zero sum. -/
theorem logDeriv_xi_partial_fraction (s : ℂ) (hs_ne : ∀ n, s ≠ h.zeros n) :
    logDeriv RiemannXiAlt s = h.B + zeroSum s := by
  unfold zeroSum
  have hhs := h.logDeriv_xi_eq s hs_ne
  rw [hhs.tsum_eq]
  ring

end

/-- `logDeriv` of `z * (z - 1)` is the sum of the two simple poles. -/
private lemma logDeriv_id_mul_sub_one (s : ℂ) (hs0 : s ≠ 0) (hs1 : s - 1 ≠ 0) :
    logDeriv (fun z => z * (z - 1)) s = 1 / s + 1 / (s - 1) := by
  have hfun : (fun z : ℂ => z * (z - 1)) = (fun z => z ^ 2 - z) := by
    ext z
    ring
  rw [hfun]
  simp only [logDeriv_apply]
  rw [show s ^ 2 - s = s * (s - 1) by ring]
  have h := (hasDerivAt_pow 2 s).sub (hasDerivAt_id s)
  have heq : ((fun z : ℂ => z ^ 2) - (fun z => z)) =ᶠ[nhds s] (fun z => z ^ 2 - z) := by
    filter_upwards with z
    simp [Pi.sub_apply]
  rw [((heq.hasDerivAt_iff).mp h).deriv]
  simp [pow_one]
  field_simp
  ring

/-! ## From logDeriv(ξ) to logDeriv(completed ζ)

Away from `s = 0, 1`, `RiemannXiAlt` agrees locally with
`(1 / 2) * s * (s - 1) * completedRiemannZeta`, so its logarithmic derivative
splits into the simple-pole part and `logDeriv completedRiemannZeta`.
-/

/-- Local bridge from `RiemannXiAlt` to the completed zeta logarithmic derivative. -/
private theorem logDeriv_RiemannXiAlt_eq_inv_add_logDeriv_completed (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hcomp : completedRiemannZeta s ≠ 0) :
    logDeriv RiemannXiAlt s =
      1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h_at_s : RiemannXiAlt s = (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s) := by
    simpa [mul_assoc] using RiemannXiAlt_eq_formula hs0 hs1
  have h_nhds : RiemannXiAlt =ᶠ[nhds s]
      (fun z : ℂ => (1 / 2 : ℂ) * (z * (z - 1) * completedRiemannZeta z)) := by
    refine Filter.Eventually.mono
      (IsOpen.mem_nhds (isOpen_ne.inter isOpen_ne) ⟨hs0, hs1⟩) ?_
    intro z hz
    simpa [mul_assoc] using RiemannXiAlt_eq_formula hz.1 hz.2
  have hlogderiv_eq : logDeriv RiemannXiAlt s =
      logDeriv (fun z : ℂ => (1 / 2 : ℂ) * (z * (z - 1) * completedRiemannZeta z)) s := by
    simp only [logDeriv_apply, h_at_s, Filter.EventuallyEq.deriv_eq h_nhds]
  calc
    logDeriv RiemannXiAlt s
        = logDeriv (fun z : ℂ => (1 / 2 : ℂ) * (z * (z - 1) * completedRiemannZeta z)) s :=
          hlogderiv_eq
    _ = logDeriv (fun z : ℂ => z * (z - 1) * completedRiemannZeta z) s := by
          simpa using
            (logDeriv_const_mul
              (f := fun z : ℂ => z * (z - 1) * completedRiemannZeta z)
              s (1 / 2 : ℂ) (by norm_num))
    _ = logDeriv (fun z : ℂ => z * (z - 1)) s + logDeriv completedRiemannZeta s := by
          simpa [Pi.mul_apply] using
            (logDeriv_mul (x := s)
              (f := fun z : ℂ => z * (z - 1))
              (g := completedRiemannZeta)
              (mul_ne_zero hs0 hs1') hcomp
              (differentiableAt_id.mul (differentiableAt_id.sub_const 1))
              (differentiableAt_completedZeta hs0 hs1))
    _ = 1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
          rw [logDeriv_id_mul_sub_one s hs0 hs1']

section

variable [h : HadamardXiCore]

/-- The xi Hadamard input implies the completed-zeta partial fraction. -/
theorem logDeriv_completedRiemannZeta_partial_fraction (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hcomp : completedRiemannZeta s ≠ 0)
    (hs_ne : ∀ n, s ≠ h.zeros n) :
    logDeriv completedRiemannZeta s =
      h.B + zeroSum s - 1 / s - 1 / (s - 1) := by
  have hxi := logDeriv_xi_partial_fraction s hs_ne
  have hsplit := logDeriv_RiemannXiAlt_eq_inv_add_logDeriv_completed s hs0 hs1 hcomp
  rw [hxi] at hsplit
  rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
  simpa [add_assoc, add_left_comm, add_comm] using hsplit.symm

/-- The partial fraction constant for `-ζ'/ζ`, combining the Hadamard constant
    with the explicit `π` term. -/
def zetaLogDerivConst : ℂ := -h.B - (1 / 2) * Complex.log (↑Real.pi)

/-- **Partial fraction of `-ζ'/ζ`**: once the standard completed-zeta
    logarithmic derivative split is supplied, the xi Hadamard input gives the
    usual zero-sum expansion for `-ζ'/ζ`. -/
theorem neg_zeta_logDeriv_partial_fraction
    (s : ℂ) (hs_re : 1 < s.re) (hcomp : completedRiemannZeta s ≠ 0)
    (hs_ne : ∀ n, s ≠ h.zeros n)
    (completed_decomp : logDeriv completedRiemannZeta s =
      -(1 / 2) * Complex.log (↑Real.pi) +
        (1 / 2) * logDeriv Complex.Gamma (s / 2) + logDeriv riemannZeta s) :
    -logDeriv riemannZeta s =
      1 / s + 1 / (s - 1) - h.B - zeroSum s
      - (1 / 2) * Complex.log (↑Real.pi)
      + (1 / 2) * logDeriv Complex.Gamma (s / 2) := by
  have hs0 : s ≠ 0 := by
    intro heq
    subst heq
    exact absurd hs_re (by norm_num [Complex.zero_re])
  have hs1 : s ≠ 1 := by
    intro heq
    subst heq
    exact absurd hs_re (by norm_num [Complex.one_re])
  have hcompleted :=
    logDeriv_completedRiemannZeta_partial_fraction s hs0 hs1 hcomp hs_ne
  rw [hcompleted] at completed_decomp
  have hzeta : logDeriv riemannZeta s =
      (h.B + zeroSum s - 1 / s - 1 / (s - 1)) -
        (-(1 / 2) * Complex.log (↑Real.pi)) -
        ((1 / 2) * logDeriv Complex.Gamma (s / 2)) := by
    rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
    simpa [add_assoc, add_left_comm, add_comm] using completed_decomp.symm
  have hneg := congrArg Neg.neg hzeta
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg

end

/-! ## Deriving `HadamardXiHyp` from upstream canonical-product classes

The key insight: `HadamardXiCanonicalProductApprox` already yields
`HadamardXiCore` via the existing instance chain, and the strip metadata
(`zeros_in_strip`) follows constructively from the canonical product
convergence.  Each listed zero must be a zero of `RiemannXiAlt` (by
eventual vanishing of the partial products), and all zeros of `RiemannXiAlt`
lie in the critical strip (proved above as `RiemannXiAlt_zero_re_in_strip`).
-/

/-- **Hadamard Xi Hypothesis from xi-cover package.** -/
instance (priority := 100) [h : HadamardXiCanonicalProductXiCover] : HadamardXiHyp where
  toHadamardXiCore := inferInstance
  zeros_in_strip := fun n =>
    RiemannXiAlt_zero_re_in_strip
      (RiemannXiAlt_zero_of_listed_zero_of_partialProducts h.B h.zeros h.zeros_ne_zero
        h.partialProducts_tendsto n)
  zeros_ne_zero := h.zeros_ne_zero

/-- **Hadamard Xi Hypothesis from critical-cover package.** -/
instance (priority := 100) [h : HadamardXiCanonicalProductCriticalCover] : HadamardXiHyp where
  toHadamardXiCore := inferInstance
  zeros_in_strip := fun n =>
    RiemannXiAlt_zero_re_in_strip
      (RiemannXiAlt_zero_of_listed_zero_of_partialProducts h.B h.zeros h.zeros_ne_zero
        h.partialProducts_tendsto n)
  zeros_ne_zero := h.zeros_ne_zero

end HadamardXi
