/-
Classical Littlewood Key Lemma — hypothesis surface

This file packages the classical Littlewood route to `ψ(x) - x = Ω±(√x)`
without the inhomogeneous phase-alignment hypothesis. The core objects are:

1. the multiplicity-weighted Abel sum over positive zeta zeros,
2. the diagonal lower bound on that sum,
3. the resulting key lemma, and
4. the Phragmén-Lindelöf bridge from one-sided ψ-bounds back to the Abel sum.

Unlike the Ingham-style route, this classical surface only needs the
homogeneous Kronecker input `w = 1`.
-/

import Mathlib
import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.Basic.ChebyshevFunctions
import Littlewood.CoreLemmas.DirichletApproximation
import Littlewood.ZetaZeros.ZeroCountingMultiplicity

set_option maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

open Real Filter Topology Asymptotics
open scoped Real BigOperators

namespace Littlewood.Classical

open ZetaZeros

/-! ## Zero-sum surface -/

/-- Distinct positive-imaginary zeta zeros up to height `T`. Multiplicity is
attached separately via `zeroMultiplicity`. -/
noncomputable def positiveImZerosBelow (T : ℝ) : Finset ℂ :=
  (finite_zeros_le T).toFinset

/-- Multiplicity of a zeta zero, encoded by analytic order. -/
noncomputable def zeroMultiplicity (ρ : ℂ) : ℕ :=
  (analyticOrderAt riemannZeta ρ).toNat

/-- Littlewood's Abel kernel attached to a zero ordinate. -/
noncomputable def abelWeightedZeroKernel (ξ η : ℝ) (ρ : ℂ) : ℝ :=
  (Real.sin (ρ.im * η) / ρ.im) * Real.exp (-(ρ.im * ξ))

/-- The Abel-weighted zero sum truncated at height `T`, counting zeros with
multiplicity. -/
noncomputable def abelWeightedZeroSumUpTo (T ξ η : ℝ) : ℝ :=
  ∑ ρ ∈ positiveImZerosBelow T, (zeroMultiplicity ρ : ℝ) * abelWeightedZeroKernel ξ η ρ

/-- The classical Abel-weighted zero sum on the truncation scale `T = 1 / ξ`. -/
noncomputable def abelWeightedZeroSum (ξ η : ℝ) : ℝ :=
  abelWeightedZeroSumUpTo (1 / ξ) ξ η

/-- Complex Abel function truncated at height `T`:
`f_T(z) = ∑ m(ρ) * exp (-ρ.im * z) / ρ.im`. -/
noncomputable def complexAbelSumUpTo (T : ℝ) (z : ℂ) : ℂ :=
  ∑ ρ ∈ positiveImZerosBelow T,
    (zeroMultiplicity ρ : ℂ) * (Complex.exp (-((ρ.im : ℂ) * z)) / (ρ.im : ℂ))

/-- Canonical finite holomorphic Abel function used by the PL bridge. -/
noncomputable def complexAbelFun (T : ℝ) (z : ℂ) : ℂ :=
  ∑ ρ ∈ positiveImZerosBelow T,
    (zeroMultiplicity ρ : ℂ) * (Complex.exp (-((ρ.im : ℂ) * z)) / (ρ.im : ℂ))

private lemma abelWeightedZeroKernel_neg_eta (ξ η : ℝ) (ρ : ℂ) :
    abelWeightedZeroKernel ξ (-η) ρ = -abelWeightedZeroKernel ξ η ρ := by
  unfold abelWeightedZeroKernel
  rw [mul_neg, Real.sin_neg, neg_div, neg_mul]

/-- The truncated Abel-weighted zero sum is odd in the vertical parameter `η`. -/
theorem abelWeightedZeroSumUpTo_neg_eta (T ξ η : ℝ) :
    abelWeightedZeroSumUpTo T ξ (-η) = -abelWeightedZeroSumUpTo T ξ η := by
  unfold abelWeightedZeroSumUpTo
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  rw [abelWeightedZeroKernel_neg_eta, mul_neg]

/-- The scale-specialized Abel-weighted zero sum is odd in `η`. -/
theorem abelWeightedZeroSum_neg_eta (ξ η : ℝ) :
    abelWeightedZeroSum ξ (-η) = -abelWeightedZeroSum ξ η := by
  simp [abelWeightedZeroSum, abelWeightedZeroSumUpTo_neg_eta]

private lemma complexAbelTrigBundle_re (a : ℝ) :
    (Complex.cos (a : ℂ) + Complex.sin (a : ℂ) * Complex.I).re = Real.cos a := by
  rw [Complex.add_re, Complex.mul_re]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]

private lemma complexAbelTrigBundle_im (a : ℝ) :
    (Complex.cos (a : ℂ) + Complex.sin (a : ℂ) * Complex.I).im = Real.sin a := by
  rw [Complex.add_im, Complex.mul_im]
  simp [Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]

private lemma abelWeightedZeroKernel_eq_neg_im_complexAbelTerm (ξ η : ℝ) (ρ : ℂ) :
    abelWeightedZeroKernel ξ η ρ =
      -(Complex.exp (-((ρ.im : ℂ) * ((ξ : ℂ) + (η : ℂ) * Complex.I))) / (ρ.im : ℂ)).im := by
  unfold abelWeightedZeroKernel
  have hre :
      (-((ρ.im : ℂ) * ((ξ : ℂ) + (η : ℂ) * Complex.I))).re = -(ρ.im * ξ) := by
    simp [Complex.mul_re, Complex.mul_im]
  have him :
      (-((ρ.im : ℂ) * ((ξ : ℂ) + (η : ℂ) * Complex.I))).im = -(ρ.im * η) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos, hre, him, Complex.div_ofReal_im, Complex.mul_im]
  rw [Complex.exp_ofReal_re, Complex.exp_ofReal_im,
    complexAbelTrigBundle_re (-(ρ.im * η)), complexAbelTrigBundle_im (-(ρ.im * η))]
  simp [Real.sin_neg]
  ring

private lemma weighted_neg_im_complexAbelTerm (ξ η : ℝ) (ρ : ℂ) :
    -(((zeroMultiplicity ρ : ℂ) *
        (Complex.exp (-((ρ.im : ℂ) * ((ξ : ℂ) + (η : ℂ) * Complex.I))) / (ρ.im : ℂ))).im)
      = (zeroMultiplicity ρ : ℝ) * abelWeightedZeroKernel ξ η ρ := by
  rw [Complex.mul_im]
  simp [abelWeightedZeroKernel_eq_neg_im_complexAbelTerm, mul_comm]

theorem abelWeightedZeroSumUpTo_eq_neg_im_complexAbelSumUpTo (T ξ η : ℝ) :
    abelWeightedZeroSumUpTo T ξ η =
      -(complexAbelSumUpTo T ((ξ : ℂ) + (η : ℂ) * Complex.I)).im := by
  unfold abelWeightedZeroSumUpTo complexAbelSumUpTo
  rw [Complex.im_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  simpa using (weighted_neg_im_complexAbelTerm ξ η ρ).symm

theorem abelWeightedZeroSum_eq_neg_im_complexAbel (ξ η : ℝ) (hξ : 0 < ξ) :
    abelWeightedZeroSum ξ η =
      -(complexAbelSumUpTo (1 / ξ) ((ξ : ℂ) + (η : ℂ) * Complex.I)).im := by
  have _hTpos : 0 < 1 / ξ := one_div_pos.mpr hξ
  simpa [abelWeightedZeroSum] using
    abelWeightedZeroSumUpTo_eq_neg_im_complexAbelSumUpTo (1 / ξ) ξ η

theorem abelWeightedZeroSumUpTo_eq_neg_im_complexAbelFun (T ξ η : ℝ) :
    abelWeightedZeroSumUpTo T ξ η =
      -(complexAbelFun T ((ξ : ℂ) + (η : ℂ) * Complex.I)).im := by
  simpa [complexAbelFun, complexAbelSumUpTo] using
    abelWeightedZeroSumUpTo_eq_neg_im_complexAbelSumUpTo T ξ η

theorem abelWeightedZeroSum_eq_neg_im_complexAbelFun (ξ η : ℝ) (hξ : 0 < ξ) :
    abelWeightedZeroSum ξ η =
      -(complexAbelFun (1 / ξ) ((ξ : ℂ) + (η : ℂ) * Complex.I)).im := by
  simpa [complexAbelFun, complexAbelSumUpTo] using
    abelWeightedZeroSum_eq_neg_im_complexAbel ξ η hξ

/-- Multiplicity-weighted truncated explicit formula on the Abel surface.

This is the classical explicit formula for `ψ`, with zeros counted with
multiplicity, rewritten at `x = exp η` against the sine-kernel surface used by
`abelWeightedZeroSumUpTo`. -/
class MultWeightedExplicitFormulaPsiHyp : Prop where
  approx :
    ∃ C > 0, ∀ η T : ℝ, η ≥ 2 → T ≥ 2 →
      |chebyshevPsi (Real.exp η) - Real.exp η +
          2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η|
        ≤ C * (Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) + η ^ 2)

theorem multWeightedExplicitFormulaPsi_bound
    [MultWeightedExplicitFormulaPsiHyp] :
    ∃ C > 0, ∀ η T : ℝ, η ≥ 2 → T ≥ 2 →
      |chebyshevPsi (Real.exp η) - Real.exp η +
          2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η|
        ≤ C * (Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) + η ^ 2) := by
  simpa using MultWeightedExplicitFormulaPsiHyp.approx

/-- Normalized multiplicity-weighted explicit formula:
`abelWeightedZeroSumUpTo T 0 η` differs from the rescaled `ψ(e^η)-e^η` term by
the normalized explicit-formula error. -/
theorem explicit_formula_to_abel_sum_normalized
    [MultWeightedExplicitFormulaPsiHyp] (T η : ℝ) (hη : η ≥ 2) (hT : T ≥ 2) :
    ∃ C > 0,
      |abelWeightedZeroSumUpTo T 0 η -
          (-(chebyshevPsi (Real.exp η) - Real.exp η) / (2 * Real.exp (η / 2)))|
        ≤ C * ((Real.log T) ^ 2 / Real.sqrt T + 1 + η ^ 2 / Real.exp (η / 2)) := by
  obtain ⟨C0, hC0_pos, hbound⟩ := multWeightedExplicitFormulaPsi_bound
  let C : ℝ := C0 / 2
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hExp_pos : 0 < Real.exp (η / 2) := Real.exp_pos (η / 2)
  have hExp_ne : Real.exp (η / 2) ≠ 0 := hExp_pos.ne'
  have hdenom_pos : 0 < 2 * Real.exp (η / 2) := by positivity
  have hsqrtT_pos : 0 < Real.sqrt T := by
    have hT_pos : 0 < T := by linarith
    exact Real.sqrt_pos_of_pos hT_pos
  have hsqrtT_ne : Real.sqrt T ≠ 0 := hsqrtT_pos.ne'
  refine ⟨C, hC_pos, ?_⟩
  have hmain := hbound η T hη hT
  have hrewrite :
      abelWeightedZeroSumUpTo T 0 η -
          (-(chebyshevPsi (Real.exp η) - Real.exp η) / (2 * Real.exp (η / 2))) =
        (chebyshevPsi (Real.exp η) - Real.exp η +
            2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η) /
          (2 * Real.exp (η / 2)) := by
    field_simp [hExp_ne]
    ring
  rw [hrewrite, abs_div, abs_of_pos hdenom_pos]
  calc
    |chebyshevPsi (Real.exp η) - Real.exp η +
        2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η| /
        (2 * Real.exp (η / 2))
      ≤ (C0 * (Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) + η ^ 2)) /
          (2 * Real.exp (η / 2)) := by
            exact div_le_div_of_nonneg_right hmain hdenom_pos.le
    _ = C * ((Real.log T) ^ 2 / Real.sqrt T + 1 + η ^ 2 / Real.exp (η / 2)) := by
          field_simp [C, hExp_ne, hsqrtT_ne]
          ring

/-- Fixed-parameter comparison theorem requested for the multiplicity-weighted
surface. This packages the normalized bound above into the coarse `O(1)` form
used when only `(T, η)` are fixed. -/
theorem explicit_formula_to_abel_sum_approx
    [MultWeightedExplicitFormulaPsiHyp] (T η : ℝ) (hη : η ≥ 2) (hT : T ≥ 2) :
    ∃ C : ℝ,
      |abelWeightedZeroSumUpTo T 0 η -
          (-(chebyshevPsi (Real.exp η) - Real.exp η) / (2 * Real.exp (η / 2)))|
        ≤ C := by
  obtain ⟨C, _, hbound⟩ := explicit_formula_to_abel_sum_normalized T η hη hT
  exact ⟨C * ((Real.log T) ^ 2 / Real.sqrt T + 1 + η ^ 2 / Real.exp (η / 2)), hbound⟩

private lemma critical_sine_bridge_coeff_norm_le (γ : ℝ) (hγ : 0 < γ) :
    ‖(((((1 / 2 : ℂ) + (γ : ℂ) * Complex.I)⁻¹) + Complex.I / (γ : ℂ)))‖ ≤
      1 / (2 * γ ^ 2) := by
  have hre :
      (((((1 / 2 : ℂ) + (γ : ℂ) * Complex.I)⁻¹) + Complex.I / (γ : ℂ))).re
        = 1 / (2 * (1 / 4 + γ ^ 2)) := by
    rw [Complex.add_re, Complex.inv_re, Complex.div_re]
    simp [Complex.normSq_apply]
    ring
  have him :
      (((((1 / 2 : ℂ) + (γ : ℂ) * Complex.I)⁻¹) + Complex.I / (γ : ℂ))).im
        = 1 / (4 * γ * (1 / 4 + γ ^ 2)) := by
    have hγne : γ ≠ 0 := hγ.ne'
    rw [Complex.add_im, Complex.inv_im, Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp [hγne]
    ring
  rw [Complex.norm_def, Complex.normSq_apply, hre, him]
  have hsq :
      (1 / (2 * (1 / 4 + γ ^ 2))) ^ 2 + (1 / (4 * γ * (1 / 4 + γ ^ 2))) ^ 2
        = (1 / (2 * γ ^ 2)) ^ 2 * (γ ^ 2 / (1 / 4 + γ ^ 2)) := by
    field_simp [hγ.ne']
    ring
  have hsq' :
      1 / (2 * (1 / 4 + γ ^ 2)) * (1 / (2 * (1 / 4 + γ ^ 2))) +
          1 / (4 * γ * (1 / 4 + γ ^ 2)) * (1 / (4 * γ * (1 / 4 + γ ^ 2)))
        = (1 / (2 * γ ^ 2)) ^ 2 * (γ ^ 2 / (1 / 4 + γ ^ 2)) := by
    simpa [pow_two] using hsq
  rw [hsq']
  refine Real.sqrt_le_iff.mpr ?_
  constructor
  · positivity
  · have hfrac : γ ^ 2 / (1 / 4 + γ ^ 2) ≤ 1 := by
      have hpos : 0 < 1 / 4 + γ ^ 2 := by positivity
      rw [div_le_iff₀ hpos]
      nlinarith [sq_nonneg γ]
    have hsqnonneg : 0 ≤ (1 / (2 * γ ^ 2)) ^ 2 := by positivity
    nlinarith

/-- Scalar bridge from the explicit-formula term on the critical line to the
Abel kernel `sin (γ η) / γ`, with a summable `O(γ⁻²)` error. -/
theorem re_cpow_div_rho_approx (γ η : ℝ) (hγ : 1 < γ) :
    abs ((((Real.exp η : ℂ) ^ ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) /
        ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I)).re)
        - Real.exp (η / 2) * Real.sin (γ * η) / γ)
      ≤ Real.exp (η / 2) / (2 * γ ^ 2) := by
  have hγ_pos : 0 < γ := lt_trans zero_lt_one hγ
  let ρ : ℂ := (1 / 2 : ℂ) + (γ : ℂ) * Complex.I
  let u : ℂ := Complex.exp (((γ * η : ℂ)) * Complex.I)
  have hlog : Complex.log (Real.exp η : ℂ) = (η : ℂ) := by
    have h1 : Complex.log (Real.exp η : ℂ) = ((Real.log (Real.exp η) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_log (le_of_lt (Real.exp_pos η))]
    rw [h1]
    simp
  have hexp_arg :
      Complex.log (Real.exp η : ℂ) * ρ =
        ((η / 2 : ℝ) : ℂ) + ((γ * η : ℝ) : ℂ) * Complex.I := by
    rw [hlog]
    simp [ρ]
    ring
  have hpow : ((Real.exp η : ℂ) ^ ρ) = (Real.exp (η / 2) : ℂ) * u := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos η).ne'),
      hexp_arg, Complex.exp_add]
    have hphase : Complex.exp ((((γ * η : ℝ) : ℂ)) * Complex.I) = u := by
      unfold u
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [hphase]
    simp
  have hinner : (((-Complex.I / (γ : ℂ)) * u).re) = Real.sin (γ * η) / γ := by
    unfold u
    rw [Complex.mul_re, Complex.div_re, Complex.exp_re, Complex.exp_im]
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring
  have htarget_re :
      (((Real.exp (η / 2) : ℂ) * ((-Complex.I / (γ : ℂ)) * u)).re)
        = Real.exp (η / 2) * Real.sin (γ * η) / γ := by
    have hA_re : ((Real.exp (η / 2) : ℂ)).re = Real.exp (η / 2) := by
      change (Complex.exp (((η / 2 : ℝ) : ℂ))).re = Real.exp (η / 2)
      rw [Complex.exp_re]
      simp
    have hA_im : ((Real.exp (η / 2) : ℂ)).im = 0 := by
      rw [show (Real.exp (η / 2) : ℂ) = Complex.exp (((η / 2 : ℝ) : ℂ)) by simp]
      rw [Complex.exp_im]
      simp
    rw [Complex.mul_re, hA_re, hA_im, hinner]
    ring
  have hdiff :
      ((Real.exp η : ℂ) ^ ρ / ρ) - ((Real.exp (η / 2) : ℂ) * ((-Complex.I / (γ : ℂ)) * u))
        = (Real.exp (η / 2) : ℂ) * u * (ρ⁻¹ + Complex.I / (γ : ℂ)) := by
    rw [hpow]
    simp [ρ, u, div_eq_mul_inv]
    ring
  have hu : ‖u‖ = 1 := by
    unfold u
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (γ * η)
  calc
    abs ((((Real.exp η : ℂ) ^ ρ / ρ).re) - Real.exp (η / 2) * Real.sin (γ * η) / γ)
      = abs ((((Real.exp η : ℂ) ^ ρ / ρ) -
          ((Real.exp (η / 2) : ℂ) * ((-Complex.I / (γ : ℂ)) * u))).re) := by
            rw [Complex.sub_re, htarget_re]
    _ ≤ ‖((Real.exp η : ℂ) ^ ρ / ρ) - ((Real.exp (η / 2) : ℂ) * ((-Complex.I / (γ : ℂ)) * u))‖ :=
          Complex.abs_re_le_norm _
    _ = ‖(Real.exp (η / 2) : ℂ) * u * (ρ⁻¹ + Complex.I / (γ : ℂ))‖ := by
          rw [hdiff]
    _ = Real.exp (η / 2) * ‖u‖ * ‖ρ⁻¹ + Complex.I / (γ : ℂ)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real]
          simp [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    _ = Real.exp (η / 2) * ‖ρ⁻¹ + Complex.I / (γ : ℂ)‖ := by
          rw [hu, mul_one]
    _ ≤ Real.exp (η / 2) / (2 * γ ^ 2) := by
          simpa [ρ, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
            mul_le_mul_of_nonneg_left
              (critical_sine_bridge_coeff_norm_le γ hγ_pos)
              (Real.exp_pos _).le

theorem complexAbelSumUpTo_differentiable (T : ℝ) :
    Differentiable ℂ (complexAbelSumUpTo T) := by
  simpa [complexAbelSumUpTo] using
    (Differentiable.fun_sum
      (u := positiveImZerosBelow T)
      (𝕜 := ℂ)
      (A := fun ρ => fun z : ℂ =>
        (zeroMultiplicity ρ : ℂ) * (Complex.exp (-((ρ.im : ℂ) * z)) / (ρ.im : ℂ)))
      (by
        intro ρ hρ
        have hExp : Differentiable ℂ (fun z : ℂ => Complex.exp ((-(ρ.im : ℂ)) * z)) :=
          Complex.differentiable_exp.comp (differentiable_id.const_mul (-(ρ.im : ℂ)))
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, neg_mul] using
          (hExp.const_mul ((zeroMultiplicity ρ : ℂ) * (ρ.im : ℂ)⁻¹))))

theorem complexAbelFun_differentiable (T : ℝ) :
    Differentiable ℂ (complexAbelFun T) := by
  simpa [complexAbelFun, complexAbelSumUpTo] using
    complexAbelSumUpTo_differentiable T

theorem complexAbelSumUpTo_diffContOnCl (T a b : ℝ) :
    DiffContOnCl ℂ (complexAbelSumUpTo T) (Complex.re ⁻¹' Set.Ioo a b) := by
  exact (complexAbelSumUpTo_differentiable T).diffContOnCl

theorem complexAbelFun_diffContOnCl (T a b : ℝ) :
    DiffContOnCl ℂ (complexAbelFun T) (Complex.re ⁻¹' Set.Ioo a b) := by
  exact (complexAbelFun_differentiable T).diffContOnCl

lemma mem_positiveImZerosBelow {T : ℝ} {ρ : ℂ} :
    ρ ∈ positiveImZerosBelow T ↔ ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
  simp [positiveImZerosBelow, zerosUpTo, Set.Finite.mem_toFinset]

lemma positiveImZerosBelow_im_pos {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow T) : 0 < ρ.im := by
  rcases mem_positiveImZerosBelow.mp hρ with ⟨hρ_pos, _⟩
  exact (mem_zetaNontrivialZerosPos.mp hρ_pos).2

lemma positiveImZerosBelow_im_le {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow T) : ρ.im ≤ T := by
  exact (mem_positiveImZerosBelow.mp hρ).2

lemma card_positiveImZerosBelow (T : ℝ) :
    (positiveImZerosBelow T).card = N T := by
  rw [positiveImZerosBelow, ← zeroCountingFunction_eq_finset_card]

lemma sum_zeroMultiplicity_positiveImZerosBelow (T : ℝ) :
    ∑ ρ ∈ positiveImZerosBelow T, zeroMultiplicity ρ = Nmult T := by
  simpa [positiveImZerosBelow, zeroMultiplicity] using
    (zeroCountingFunctionMult_eq_sum T).symm

lemma positiveImZerosBelow_eq_empty_of_nonpos {T : ℝ} (hT : T ≤ 0) :
    positiveImZerosBelow T = ∅ := by
  ext ρ
  constructor
  · intro hρ
    exfalso
    rcases mem_positiveImZerosBelow.mp hρ with ⟨hρ_pos, hρ_le⟩
    rcases mem_zetaNontrivialZerosPos.mp hρ_pos with ⟨_, hρ_im_pos⟩
    linarith
  · intro hρ
    simp at hρ

lemma abelWeightedZeroSumUpTo_eq_zero_of_nonpos {T ξ η : ℝ} (hT : T ≤ 0) :
    abelWeightedZeroSumUpTo T ξ η = 0 := by
  simp [abelWeightedZeroSumUpTo, positiveImZerosBelow_eq_empty_of_nonpos hT]

lemma sum_zeroMultiplicity_positiveImZerosBelow_real (T : ℝ) :
    ∑ ρ ∈ positiveImZerosBelow T, (zeroMultiplicity ρ : ℝ) = (Nmult T : ℝ) := by
  exact_mod_cast sum_zeroMultiplicity_positiveImZerosBelow T

private theorem zeroCountingFunctionMult_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    Nmult T₁ ≤ Nmult T₂ := by
  classical
  rw [zeroCountingFunctionMult_eq_sum, zeroCountingFunctionMult_eq_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    ((finite_zeros_le T₁).toFinset_mono (zerosUpTo_subset_of_le h)) ?_
  intro ρ _ _
  exact Nat.zero_le _

lemma abelWeightedZeroKernel_diag_lower {ξ : ℝ} (hξ : 0 < ξ) {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow (1 / ξ)) :
    ξ / 2 * Real.exp (-1) ≤ abelWeightedZeroKernel ξ ξ ρ := by
  have hγ_pos : 0 < ρ.im := positiveImZerosBelow_im_pos hρ
  have hγ_le : ρ.im ≤ 1 / ξ := positiveImZerosBelow_im_le hρ
  have hprod_pos : 0 < ρ.im * ξ := mul_pos hγ_pos hξ
  have hprod_le : ρ.im * ξ ≤ 1 := by
    have hmul : ρ.im * ξ ≤ (1 / ξ) * ξ := mul_le_mul_of_nonneg_right hγ_le hξ.le
    have hright : (1 / ξ) * ξ = 1 := by
      exact one_div_mul_cancel hξ.ne'
    exact hmul.trans_eq hright
  have hsin_gt :
      ρ.im * ξ - (ρ.im * ξ) ^ 3 / 4 < Real.sin (ρ.im * ξ) :=
    Real.sin_gt_sub_cube hprod_pos hprod_le
  have hsin_lower : ρ.im * ξ / 2 ≤ Real.sin (ρ.im * ξ) := by
    have hsq_le : (ρ.im * ξ) ^ 2 ≤ 1 := by
      nlinarith [hprod_pos.le, hprod_le]
    have haux : ρ.im * ξ / 2 ≤ ρ.im * ξ - (ρ.im * ξ) ^ 3 / 4 := by
      nlinarith [hprod_pos.le, hsq_le]
    exact le_of_lt (lt_of_le_of_lt haux hsin_gt)
  have hratio :
      ξ / 2 ≤ Real.sin (ρ.im * ξ) / ρ.im := by
    rw [le_div_iff₀ hγ_pos]
    nlinarith
  have hratio_nonneg : 0 ≤ Real.sin (ρ.im * ξ) / ρ.im := by
    exact le_trans (by positivity) hratio
  have hexp :
      Real.exp (-1) ≤ Real.exp (-(ρ.im * ξ)) := by
    exact Real.exp_le_exp.mpr (by linarith [hprod_le])
  have hmul :=
    mul_le_mul hratio hexp (by positivity) hratio_nonneg
  simpa [abelWeightedZeroKernel, mul_comm, mul_left_comm, mul_assoc] using hmul

private lemma positiveImZerosBelow_im_gt_one [ZeroOrdinateLowerBoundHyp]
    {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ positiveImZerosBelow T) : (1 : ℝ) < ρ.im := by
  rcases mem_positiveImZerosBelow.mp hρ with ⟨hρ_pos, _⟩
  exact zero_ord_lower_bound ρ hρ_pos

private lemma complexAbelSummand_norm_le_on_real
    [ZeroOrdinateLowerBoundHyp]
    {T ξ : ℝ} (hξ : 0 < ξ) {ρ : ℂ} (hρ : ρ ∈ positiveImZerosBelow T) :
    ‖(zeroMultiplicity ρ : ℂ) * (Complex.exp (-((ρ.im : ℂ) * (ξ : ℂ))) / (ρ.im : ℂ))‖
      ≤ (zeroMultiplicity ρ : ℝ) * Real.exp (-ξ) := by
  have hγ_pos : 0 < ρ.im := positiveImZerosBelow_im_pos hρ
  have hγ_gt_one : (1 : ℝ) < ρ.im := positiveImZerosBelow_im_gt_one hρ
  have hmult_nonneg : 0 ≤ (zeroMultiplicity ρ : ℝ) := by
    exact_mod_cast Nat.zero_le (zeroMultiplicity ρ)
  have hnorm :
      ‖(zeroMultiplicity ρ : ℂ) * (Complex.exp (-((ρ.im : ℂ) * (ξ : ℂ))) / (ρ.im : ℂ))‖
        = (zeroMultiplicity ρ : ℝ) * (Real.exp (-(ρ.im * ξ)) / ρ.im) := by
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_exp, Complex.norm_real]
    simp [Real.norm_eq_abs, abs_of_nonneg, hγ_pos.le]
  rw [hnorm]
  have hdiv_le :
      Real.exp (-(ρ.im * ξ)) / ρ.im ≤ Real.exp (-(ρ.im * ξ)) := by
    rw [div_le_iff₀ hγ_pos]
    nlinarith [Real.exp_pos (-(ρ.im * ξ)), le_of_lt hγ_gt_one]
  have hexp_le : Real.exp (-(ρ.im * ξ)) ≤ Real.exp (-ξ) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hξ, le_of_lt hγ_gt_one]
  calc
    (zeroMultiplicity ρ : ℝ) * (Real.exp (-(ρ.im * ξ)) / ρ.im)
      ≤ (zeroMultiplicity ρ : ℝ) * Real.exp (-(ρ.im * ξ)) := by
          exact mul_le_mul_of_nonneg_left hdiv_le hmult_nonneg
    _ ≤ (zeroMultiplicity ρ : ℝ) * Real.exp (-ξ) := by
          exact mul_le_mul_of_nonneg_left hexp_le hmult_nonneg

theorem complexAbelSumUpTo_norm_le_on_real
    [ZeroOrdinateLowerBoundHyp]
    (T ξ : ℝ) (hξ : 0 < ξ) :
    ‖complexAbelSumUpTo T (ξ : ℂ)‖ ≤ (Nmult T : ℝ) * Real.exp (-ξ) := by
  unfold complexAbelSumUpTo
  calc
    ‖∑ ρ ∈ positiveImZerosBelow T,
        (zeroMultiplicity ρ : ℂ) * (Complex.exp (-((ρ.im : ℂ) * (ξ : ℂ))) / (ρ.im : ℂ))‖
      ≤ ∑ ρ ∈ positiveImZerosBelow T,
          ‖(zeroMultiplicity ρ : ℂ) * (Complex.exp (-((ρ.im : ℂ) * (ξ : ℂ))) / (ρ.im : ℂ))‖ := by
            exact norm_sum_le _ _
    _ ≤ ∑ ρ ∈ positiveImZerosBelow T, (zeroMultiplicity ρ : ℝ) * Real.exp (-ξ) := by
          refine Finset.sum_le_sum ?_
          intro ρ hρ
          exact complexAbelSummand_norm_le_on_real hξ hρ
    _ = (∑ ρ ∈ positiveImZerosBelow T, (zeroMultiplicity ρ : ℝ)) * Real.exp (-ξ) := by
          rw [← Finset.sum_mul]
    _ = (Nmult T : ℝ) * Real.exp (-ξ) := by
          rw [sum_zeroMultiplicity_positiveImZerosBelow_real]

theorem complexAbelFun_norm_le_on_real
    [ZeroOrdinateLowerBoundHyp]
    (T ξ : ℝ) (hξ : 0 < ξ) :
    ‖complexAbelFun T (ξ : ℂ)‖ ≤ (Nmult T : ℝ) * Real.exp (-ξ) := by
  simpa [complexAbelFun, complexAbelSumUpTo] using
    complexAbelSumUpTo_norm_le_on_real T ξ hξ

theorem complexAbelFun_norm_le_on_real_ray
    [ZeroOrdinateLowerBoundHyp]
    (T ξ₀ ξ : ℝ) (hξ₀ : 0 < ξ₀) (hξ : ξ₀ ≤ ξ) :
    ‖complexAbelFun T (ξ : ℂ)‖ ≤ (Nmult T : ℝ) * Real.exp (-ξ₀) := by
  have hξ_pos : 0 < ξ := lt_of_lt_of_le hξ₀ hξ
  have hbase := complexAbelFun_norm_le_on_real T ξ hξ_pos
  have hexp : Real.exp (-ξ) ≤ Real.exp (-ξ₀) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hN_nonneg : 0 ≤ (Nmult T : ℝ) := by
    exact_mod_cast Nat.zero_le (Nmult T)
  exact hbase.trans (mul_le_mul_of_nonneg_left hexp hN_nonneg)

private lemma positiveImZerosBelow_eq_empty_of_le_one
    [ZeroOrdinateLowerBoundHyp] {T : ℝ} (hT : T ≤ 1) :
    positiveImZerosBelow T = ∅ := by
  ext ρ
  constructor
  · intro hρ
    exfalso
    have hγ_gt_one : (1 : ℝ) < ρ.im := positiveImZerosBelow_im_gt_one hρ
    have hγ_le : ρ.im ≤ T := positiveImZerosBelow_im_le hρ
    linarith
  · intro hρ
    simp at hρ

private lemma complexAbelSummand_norm_le_at_one
    [ZeroOrdinateLowerBoundHyp]
    {T η : ℝ} {ρ : ℂ} (hρ : ρ ∈ positiveImZerosBelow T) :
    ‖(zeroMultiplicity ρ : ℂ) *
        (Complex.exp (-((ρ.im : ℂ) * ((1 : ℂ) + (η : ℂ) * Complex.I))) / (ρ.im : ℂ))‖
      ≤ (zeroMultiplicity ρ : ℝ) * Real.exp (-(Nat.floor ρ.im : ℝ)) := by
  have hγ_pos : 0 < ρ.im := positiveImZerosBelow_im_pos hρ
  have hγ_gt_one : (1 : ℝ) < ρ.im := positiveImZerosBelow_im_gt_one hρ
  have hmult_nonneg : 0 ≤ (zeroMultiplicity ρ : ℝ) := by
    exact_mod_cast Nat.zero_le (zeroMultiplicity ρ)
  have hnorm :
      ‖(zeroMultiplicity ρ : ℂ) *
          (Complex.exp (-((ρ.im : ℂ) * ((1 : ℂ) + (η : ℂ) * Complex.I))) / (ρ.im : ℂ))‖
        = (zeroMultiplicity ρ : ℝ) * (Real.exp (-ρ.im) / ρ.im) := by
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_exp, Complex.norm_real]
    simp [Real.norm_eq_abs, abs_of_nonneg, hγ_pos.le, Complex.mul_re, Complex.mul_im]
  rw [hnorm]
  have hdiv_le : Real.exp (-ρ.im) / ρ.im ≤ Real.exp (-ρ.im) := by
    rw [div_le_iff₀ hγ_pos]
    nlinarith [Real.exp_pos (-ρ.im), le_of_lt hγ_gt_one]
  have hfloor_le : ((Nat.floor ρ.im : ℕ) : ℝ) ≤ ρ.im := Nat.floor_le hγ_pos.le
  have hexp_le : Real.exp (-ρ.im) ≤ Real.exp (-(Nat.floor ρ.im : ℝ)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc
    (zeroMultiplicity ρ : ℝ) * (Real.exp (-ρ.im) / ρ.im)
        ≤ (zeroMultiplicity ρ : ℝ) * Real.exp (-ρ.im) := by
          exact mul_le_mul_of_nonneg_left hdiv_le hmult_nonneg
    _ ≤ (zeroMultiplicity ρ : ℝ) * Real.exp (-(Nat.floor ρ.im : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hexp_le hmult_nonneg

private theorem zeroCountingFunctionMult_quadratic_bound
    [ZeroCountingMultRvmExplicitHyp] :
    ∃ A > 0, ∀ T ≥ 1, (Nmult T : ℝ) ≤ A * T ^ 2 := by
  rcases zeroCountingFunctionMult_rvm_explicit_hyp with ⟨C, T0, hC⟩
  let C0 : ℝ := max C 0
  let Tcut : ℝ := max T0 1
  let A0 : ℝ := 1 / (4 * Real.pi ^ 2) + C0
  let A : ℝ := max A0 (Nmult Tcut : ℝ)
  have hC0_nonneg : 0 ≤ C0 := le_max_right _ _
  have hA0_pos : 0 < A0 := by
    unfold A0
    positivity
  have hA_pos : 0 < A := lt_of_lt_of_le hA0_pos (le_max_left _ _)
  refine ⟨A, hA_pos, ?_⟩
  intro T hT
  by_cases hlarge : Tcut ≤ T
  · have hT0 : T0 ≤ T := le_trans (le_max_left _ _) hlarge
    have hT_nonneg : 0 ≤ T := by linarith
    have hErr :
        |(Nmult T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
          ≤ C0 * Real.log T := by
      have hbase := hC T hT0
      have hlog_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT
      have hC_le : C * Real.log T ≤ C0 * Real.log T := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlog_nonneg
      exact hbase.trans hC_le
    have hupper :
        (Nmult T : ℝ) ≤ (T / (2 * π)) * Real.log (T / (2 * π)) + C0 * Real.log T := by
      have hright := (abs_le.mp hErr).2
      have haux :
          (Nmult T : ℝ) ≤
            (T / (2 * π)) * Real.log (T / (2 * π)) - T / (2 * π) + C0 * Real.log T := by
        linarith
      have hdrop :
          (T / (2 * π)) * Real.log (T / (2 * π)) - T / (2 * π) + C0 * Real.log T
            ≤ (T / (2 * π)) * Real.log (T / (2 * π)) + C0 * Real.log T := by
        have hTdiv_nonneg : 0 ≤ T / (2 * π) := by positivity
        linarith
      exact haux.trans hdrop
    have hmain_sq :
        (T / (2 * π)) * Real.log (T / (2 * π)) ≤ (1 / (4 * Real.pi ^ 2)) * T ^ 2 := by
      have hratio_nonneg : 0 ≤ T / (2 * π) := by positivity
      have hlog_le : Real.log (T / (2 * π)) ≤ T / (2 * π) := Real.log_le_self hratio_nonneg
      have hmul := mul_le_mul_of_nonneg_left hlog_le hratio_nonneg
      have hsq :
          (T / (2 * π)) * (T / (2 * π)) = (1 / (4 * Real.pi ^ 2)) * T ^ 2 := by
        field_simp [Real.pi_ne_zero]
        ring
      exact hmul.trans_eq hsq
    have hlog_sq : Real.log T ≤ T ^ 2 := by
      calc
        Real.log T ≤ T := Real.log_le_self (by linarith)
        _ ≤ T ^ 2 := by nlinarith
    have hC_sq : C0 * Real.log T ≤ C0 * T ^ 2 := by
      exact mul_le_mul_of_nonneg_left hlog_sq hC0_nonneg
    have hA0_sq :
        (T / (2 * π)) * Real.log (T / (2 * π)) + C0 * Real.log T ≤ A0 * T ^ 2 := by
      calc
        (T / (2 * π)) * Real.log (T / (2 * π)) + C0 * Real.log T
            ≤ (1 / (4 * Real.pi ^ 2)) * T ^ 2 + C0 * T ^ 2 := by
              exact add_le_add hmain_sq hC_sq
        _ = A0 * T ^ 2 := by
              unfold A0
              ring
    calc
      (Nmult T : ℝ) ≤ A0 * T ^ 2 := hupper.trans hA0_sq
      _ ≤ A * T ^ 2 := by
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg T)
  · have hsmall : T ≤ Tcut := le_of_not_ge hlarge
    have hmono : (Nmult T : ℝ) ≤ (Nmult Tcut : ℝ) := by
      exact_mod_cast zeroCountingFunctionMult_mono hsmall
    have hTsq_ge_one : 1 ≤ T ^ 2 := by
      nlinarith
    have hcut_nonneg : 0 ≤ (Nmult Tcut : ℝ) := by
      exact_mod_cast Nat.zero_le (Nmult Tcut)
    calc
      (Nmult T : ℝ) ≤ (Nmult Tcut : ℝ) := hmono
      _ ≤ (Nmult Tcut : ℝ) * T ^ 2 := by
            simpa [one_mul] using
              (mul_le_mul_of_nonneg_left hTsq_ge_one hcut_nonneg)
      _ ≤ A * T ^ 2 := by
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg T)

/-- On the right boundary `Re z = 1`, the complex Abel function is uniformly
bounded independently of the truncation `T` and the imaginary part `η`. -/
theorem complexAbelFun_norm_le_at_one
    [ZeroOrdinateLowerBoundHyp] [ZeroCountingMultRvmExplicitHyp] :
    ∃ M : ℝ, ∀ (T η : ℝ), ‖complexAbelFun T ((1 : ℂ) + (η : ℂ) * Complex.I)‖ ≤ M := by
  classical
  obtain ⟨A, hA_pos, hA⟩ := zeroCountingFunctionMult_quadratic_bound
  let majorant : ℕ → ℝ := fun j =>
    A * (((j + 1 : ℕ) : ℝ) ^ 2) * Real.exp (-(j : ℝ))
  have hs_base : Summable (fun j : ℕ => (j : ℝ) ^ 2 * Real.exp (-(j : ℝ))) := by
    simpa using (Real.summable_pow_mul_exp_neg_nat_mul 2 zero_lt_one)
  have hs_shift : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-((j + 1 : ℕ) : ℝ))) := by
    simpa using (_root_.summable_nat_add_iff 1).2 hs_base
  have hs_core : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ) ^ 2) * Real.exp (-(j : ℝ))) := by
    refine hs_shift.mul_left (Real.exp 1) |>.congr ?_
    intro j
    calc
      Real.exp 1 * ((((j + 1 : ℕ) : ℝ) ^ 2) * Real.exp (-((j + 1 : ℕ) : ℝ)))
          = (((j + 1 : ℕ) : ℝ) ^ 2) * (Real.exp 1 * Real.exp (-((j + 1 : ℕ) : ℝ))) := by ring
      _ = (((j + 1 : ℕ) : ℝ) ^ 2) * Real.exp (-(j : ℝ)) := by
            congr 1
            rw [← Real.exp_add]
            norm_num
  have hs_majorant : Summable majorant := by
    simpa [majorant, mul_assoc, mul_left_comm, mul_comm] using hs_core.mul_left A
  have hM_nonneg : 0 ≤ ∑' j, majorant j := by
    exact tsum_nonneg (fun j => by positivity)
  refine ⟨∑' j, majorant j, ?_⟩
  intro T η
  by_cases hT : T ≤ 1
  · have hempty : positiveImZerosBelow T = ∅ := positiveImZerosBelow_eq_empty_of_le_one hT
    simpa [complexAbelFun, hempty] using hM_nonneg
  · have hT_one : 1 < T := lt_of_not_ge hT
    let n : ℕ := Nat.floor T + 1
    have hmaps :
        ∀ ρ ∈ positiveImZerosBelow T, Nat.floor ρ.im ∈ Finset.range n := by
      intro ρ hρ
      apply Finset.mem_range.mpr
      have hfloor_le : Nat.floor ρ.im ≤ Nat.floor T := Nat.floor_le_floor (positiveImZerosBelow_im_le hρ)
      exact lt_of_le_of_lt hfloor_le (Nat.lt_succ_self _)
    have hdecomp :
        ∑ ρ ∈ positiveImZerosBelow T,
          (zeroMultiplicity ρ : ℝ) * Real.exp (-(Nat.floor ρ.im : ℝ))
          =
        ∑ j ∈ Finset.range n,
          ∑ ρ ∈ positiveImZerosBelow T with Nat.floor ρ.im = j,
            (zeroMultiplicity ρ : ℝ) * Real.exp (-(Nat.floor ρ.im : ℝ)) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (s := positiveImZerosBelow T) (t := Finset.range n)
        (g := fun ρ => Nat.floor ρ.im) hmaps
        (f := fun ρ => (zeroMultiplicity ρ : ℝ) * Real.exp (-(Nat.floor ρ.im : ℝ)))
    have hfiber_subset :
        ∀ j ∈ Finset.range n,
          (positiveImZerosBelow T).filter (fun ρ => Nat.floor ρ.im = j)
            ⊆ positiveImZerosBelow (j + 1) := by
      intro j hj ρ hρ
      rw [Finset.mem_filter] at hρ
      rcases mem_positiveImZerosBelow.mp hρ.1 with ⟨hρ_zero, hρT⟩
      have hρ_le : ρ.im ≤ (j + 1 : ℝ) := by
        exact le_of_lt (by simpa [hρ.2] using (Nat.lt_floor_add_one ρ.im))
      exact mem_positiveImZerosBelow.mpr ⟨hρ_zero, hρ_le⟩
    have hfiber_count :
        ∀ j ∈ Finset.range n,
          ∑ ρ ∈ (positiveImZerosBelow T).filter (fun ρ => Nat.floor ρ.im = j),
            (zeroMultiplicity ρ : ℝ)
            ≤ (Nmult (j + 1) : ℝ) := by
      intro j hj
      calc
        ∑ ρ ∈ (positiveImZerosBelow T).filter (fun ρ => Nat.floor ρ.im = j),
            (zeroMultiplicity ρ : ℝ)
            ≤ ∑ ρ ∈ positiveImZerosBelow (j + 1), (zeroMultiplicity ρ : ℝ) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (hfiber_subset j hj) ?_
              intro ρ _ _
              positivity
        _ = (Nmult (j + 1) : ℝ) := by
              rw [sum_zeroMultiplicity_positiveImZerosBelow_real]
    calc
      ‖complexAbelFun T ((1 : ℂ) + (η : ℂ) * Complex.I)‖
          = ‖∑ ρ ∈ positiveImZerosBelow T,
                (zeroMultiplicity ρ : ℂ) *
                  (Complex.exp (-((ρ.im : ℂ) * ((1 : ℂ) + (η : ℂ) * Complex.I))) / (ρ.im : ℂ))‖ := by
                simp [complexAbelFun]
      _ ≤ ∑ ρ ∈ positiveImZerosBelow T,
            ‖(zeroMultiplicity ρ : ℂ) *
                (Complex.exp (-((ρ.im : ℂ) * ((1 : ℂ) + (η : ℂ) * Complex.I))) / (ρ.im : ℂ))‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ ρ ∈ positiveImZerosBelow T,
            (zeroMultiplicity ρ : ℝ) * Real.exp (-(Nat.floor ρ.im : ℝ)) := by
              refine Finset.sum_le_sum ?_
              intro ρ hρ
              exact complexAbelSummand_norm_le_at_one hρ
      _ = ∑ j ∈ Finset.range n,
            ∑ ρ ∈ positiveImZerosBelow T with Nat.floor ρ.im = j,
              (zeroMultiplicity ρ : ℝ) * Real.exp (-(Nat.floor ρ.im : ℝ)) := hdecomp
      _ = ∑ j ∈ Finset.range n,
            (∑ ρ ∈ (positiveImZerosBelow T).filter (fun ρ => Nat.floor ρ.im = j),
                (zeroMultiplicity ρ : ℝ)) * Real.exp (-(j : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              calc
                ∑ ρ ∈ positiveImZerosBelow T with Nat.floor ρ.im = j,
                    (zeroMultiplicity ρ : ℝ) * Real.exp (-(Nat.floor ρ.im : ℝ))
                    =
                    ∑ ρ ∈ positiveImZerosBelow T with Nat.floor ρ.im = j,
                      (zeroMultiplicity ρ : ℝ) * Real.exp (-(j : ℝ)) := by
                        refine Finset.sum_congr rfl ?_
                        intro ρ hρ
                        rw [Finset.mem_filter] at hρ
                        simp [hρ.2]
                _ =
                    (∑ ρ ∈ (positiveImZerosBelow T).filter (fun ρ => Nat.floor ρ.im = j),
                      (zeroMultiplicity ρ : ℝ)) * Real.exp (-(j : ℝ)) := by
                        simpa using
                          (Finset.sum_mul
                            (s := (positiveImZerosBelow T).filter (fun ρ => Nat.floor ρ.im = j))
                            (f := fun ρ => (zeroMultiplicity ρ : ℝ))
                            (a := Real.exp (-(j : ℝ)))).symm
      _ ≤ ∑ j ∈ Finset.range n, majorant j := by
              refine Finset.sum_le_sum ?_
              intro j hj
              have hcount := hfiber_count j hj
              have hexp_nonneg : 0 ≤ Real.exp (-(j : ℝ)) := by positivity
              have hAj : (Nmult (j + 1 : ℝ) : ℝ) ≤ A * (j + 1 : ℝ) ^ 2 := by
                exact hA (j + 1 : ℝ) (by
                  exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
              calc
                (∑ ρ ∈ (positiveImZerosBelow T).filter (fun ρ => Nat.floor ρ.im = j),
                    (zeroMultiplicity ρ : ℝ)) * Real.exp (-(j : ℝ))
                    ≤ (Nmult (j + 1 : ℝ) : ℝ) * Real.exp (-(j : ℝ)) := by
                      exact mul_le_mul_of_nonneg_right hcount hexp_nonneg
                _ ≤ (A * (j + 1 : ℝ) ^ 2) * Real.exp (-(j : ℝ)) := by
                      exact mul_le_mul_of_nonneg_right hAj hexp_nonneg
                _ = majorant j := by
                      simp [majorant, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ ∑' j, majorant j := by
            exact hs_majorant.sum_le_tsum _ (by intro j hj; positivity)

theorem complexAbelFun_norm_le_at_re_one
    [ZeroOrdinateLowerBoundHyp] [ZeroCountingMultRvmExplicitHyp] :
    ∃ M : ℝ, ∀ (T η : ℝ), T ≥ 0 →
      ‖complexAbelFun T ((1 : ℂ) + (η : ℂ) * Complex.I)‖ ≤ M := by
  obtain ⟨M, hM⟩ := complexAbelFun_norm_le_at_one
  exact ⟨M, fun T η _ => hM T η⟩

private lemma diagonal_sum_controls_Nmult
    {ξ : ℝ} (hξ : 0 < ξ) :
    ((Nmult (1 / ξ) : ℝ) * (ξ / 2 * Real.exp (-1))) ≤ abelWeightedZeroSum ξ ξ := by
  calc
    (Nmult (1 / ξ) : ℝ) * (ξ / 2 * Real.exp (-1))
        = ∑ ρ ∈ positiveImZerosBelow (1 / ξ),
            (zeroMultiplicity ρ : ℝ) * (ξ / 2 * Real.exp (-1)) := by
            rw [← sum_zeroMultiplicity_positiveImZerosBelow_real (1 / ξ), Finset.sum_mul]
    _ ≤ ∑ ρ ∈ positiveImZerosBelow (1 / ξ),
          (zeroMultiplicity ρ : ℝ) * abelWeightedZeroKernel ξ ξ ρ := by
            refine Finset.sum_le_sum ?_
            intro ρ hρ
            exact mul_le_mul_of_nonneg_left
              (abelWeightedZeroKernel_diag_lower hξ hρ)
              (by positivity)
    _ = abelWeightedZeroSum ξ ξ := rfl

private lemma Nmult_le_diagonal_sum_scale
    {ξ : ℝ} (hξ : 0 < ξ) :
    (Nmult (1 / ξ) : ℝ) ≤ (2 * Real.exp 1 / ξ) * abelWeightedZeroSum ξ ξ := by
  have hbase := diagonal_sum_controls_Nmult hξ
  have hmul :
      (2 * Real.exp 1 / ξ) * ((Nmult (1 / ξ) : ℝ) * (ξ / 2 * Real.exp (-1)))
        ≤ (2 * Real.exp 1 / ξ) * abelWeightedZeroSum ξ ξ := by
    exact mul_le_mul_of_nonneg_left hbase (by positivity)
  have hcoeff :
      (2 * Real.exp 1 / ξ) * (ξ / 2 * Real.exp (-1)) = 1 := by
    field_simp [hξ.ne']
    rw [show Real.exp 1 * Real.exp (-1) = Real.exp (1 + (-1)) by rw [← Real.exp_add]]
    norm_num
  have hleft :
      (2 * Real.exp 1 / ξ) * ((Nmult (1 / ξ) : ℝ) * (ξ / 2 * Real.exp (-1)))
        = (Nmult (1 / ξ) : ℝ) := by
    calc
      (2 * Real.exp 1 / ξ) * ((Nmult (1 / ξ) : ℝ) * (ξ / 2 * Real.exp (-1)))
          = (Nmult (1 / ξ) : ℝ) * ((2 * Real.exp 1 / ξ) * (ξ / 2 * Real.exp (-1))) := by
              ring
      _ = (Nmult (1 / ξ) : ℝ) := by rw [hcoeff, mul_one]
  calc
    (Nmult (1 / ξ) : ℝ)
        = (2 * Real.exp 1 / ξ) * ((Nmult (1 / ξ) : ℝ) * (ξ / 2 * Real.exp (-1))) := hleft.symm
    _ ≤ (2 * Real.exp 1 / ξ) * abelWeightedZeroSum ξ ξ := hmul

private lemma bounded_simultaneous_near_period_finset
    (S : Finset ℂ) {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) :
    ∃ t > L, ∃ M : ℕ, 0 < M ∧
      (M : ℝ) ≤ (4 * Real.pi * ((Nat.floor L + 1 : ℕ) : ℝ)) / ε + 1 ∧
      t ≤ ((Nat.floor L + 1 : ℕ) : ℝ) * (M : ℝ) ^ S.card ∧
      ∀ ρ ∈ S, ∃ p : ℤ, |t * ρ.im - p * (2 * Real.pi)| < ε := by
  classical
  let k : ℕ := Nat.floor L + 1
  have hk_pos : 0 < k := by
    exact Nat.succ_pos _
  have hL_lt_k : L < (k : ℝ) := by
    simpa [k] using Nat.lt_floor_add_one L
  let M : ℕ := Nat.floor ((4 * Real.pi * (k : ℝ)) / ε) + 1
  have hM_pos : 0 < M := by
    exact Nat.succ_pos _
  have hM_le :
      (M : ℝ) ≤ (4 * Real.pi * (k : ℝ)) / ε + 1 := by
    have hX_nonneg : 0 ≤ (4 * Real.pi * (k : ℝ)) / ε := by positivity
    calc
      (M : ℝ) = (Nat.floor ((4 * Real.pi * (k : ℝ)) / ε) : ℝ) + 1 := by
        simp [M]
      _ ≤ (4 * Real.pi * (k : ℝ)) / ε + 1 := by
        gcongr
        exact Nat.floor_le hX_nonneg
  have hM_gt : (4 * Real.pi * (k : ℝ)) / ε < (M : ℝ) := by
    simpa [M] using Nat.lt_floor_add_one ((4 * Real.pi * (k : ℝ)) / ε)
  let e : S ≃ Fin S.card := Fintype.equivOfCardEq (by simp)
  obtain ⟨q, hq_pos, hq_le, happrox⟩ :=
    DirichletApprox.dirichlet_approximation_simultaneous S.card
      (fun i : Fin S.card => ((e.symm i).1.im) / (2 * Real.pi)) M hM_pos
  let t : ℝ := (k : ℝ) * q
  refine ⟨t, ?_, M, hM_pos, ?_, ?_, ?_⟩
  · have hq_ge_one : (1 : ℝ) ≤ q := by
      exact_mod_cast hq_pos
    calc
      L < (k : ℝ) := hL_lt_k
      _ ≤ (k : ℝ) * q := by nlinarith
  · simpa [k] using hM_le
  · dsimp [t]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hq_le) (by positivity)
  · intro ρ hρ
    let i : Fin S.card := e ⟨ρ, hρ⟩
    let p0 : ℤ := round ((((e.symm i).1.im) / (2 * Real.pi)) * q)
    have hp0 :
        |(((e.symm i).1.im) / (2 * Real.pi)) * q - (p0 : ℝ)| < 1 / (M : ℝ) := by
      simpa [DirichletApprox.distToInt, p0] using happrox i
    have hi_im : (e.symm i).1.im = ρ.im := by
      simp [i]
    let p : ℤ := (k : ℤ) * p0
    refine ⟨p, ?_⟩
    have hq_phase :
        |q * ρ.im - (p0 : ℝ) * (2 * Real.pi)| < 2 * Real.pi / (M : ℝ) := by
      have hform :
          q * ρ.im - (p0 : ℝ) * (2 * Real.pi)
            = ((((e.symm i).1.im) / (2 * Real.pi)) * q - (p0 : ℝ)) * (2 * Real.pi) := by
        rw [hi_im]
        field_simp [Real.pi_ne_zero]
      calc
        |q * ρ.im - (p0 : ℝ) * (2 * Real.pi)|
            = |((((e.symm i).1.im) / (2 * Real.pi)) * q - (p0 : ℝ)) * (2 * Real.pi)| := by
                rw [hform]
        _ = |(((e.symm i).1.im) / (2 * Real.pi)) * q - (p0 : ℝ)| * (2 * Real.pi) := by
              rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        _ < (1 / (M : ℝ)) * (2 * Real.pi) := by
              exact mul_lt_mul_of_pos_right hp0 (by positivity)
        _ = 2 * Real.pi / (M : ℝ) := by ring
    have hkM_lt : (k : ℝ) * (2 * Real.pi / (M : ℝ)) < ε := by
      have hM_pos_real : 0 < (M : ℝ) := by
        exact_mod_cast hM_pos
      have haux : 4 * Real.pi * (k : ℝ) < (M : ℝ) * ε := by
        exact (div_lt_iff₀ hε).mp hM_gt
      have haux' : (k : ℝ) * (2 * Real.pi) < (M : ℝ) * ε := by
        nlinarith [haux, show 0 ≤ (k : ℝ) by positivity, Real.pi_pos]
      have hkM_lt' : ((k : ℝ) * (2 * Real.pi)) / (M : ℝ) < ε := by
        rw [div_lt_iff₀ hM_pos_real]
        nlinarith [haux']
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hkM_lt'
    calc
      |t * ρ.im - (p : ℝ) * (2 * Real.pi)|
          = |(k : ℝ) * (q * ρ.im - (p0 : ℝ) * (2 * Real.pi))| := by
              have : t * ρ.im - (p : ℝ) * (2 * Real.pi)
                  = (k : ℝ) * (q * ρ.im - (p0 : ℝ) * (2 * Real.pi)) := by
                    simp [t, p]
                    ring
              rw [this]
      _ = (k : ℝ) * |q * ρ.im - (p0 : ℝ) * (2 * Real.pi)| := by
            rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ))]
      _ < (k : ℝ) * (2 * Real.pi / (M : ℝ)) := by
            nlinarith [hq_phase, show 0 ≤ (k : ℝ) by positivity]
      _ < ε := hkM_lt

private lemma sin_shift_transport_lt
    {γ ξ t ε : ℝ} {p : ℤ}
    (hp : |t * γ - p * (2 * Real.pi)| < ε) :
    |Real.sin (γ * (t + ξ)) - Real.sin (γ * ξ)| < ε := by
  have hperiod :
      Real.sin (γ * (t + ξ)) = Real.sin ((t * γ - p * (2 * Real.pi)) + γ * ξ) := by
    have : γ * (t + ξ) = ((t * γ - p * (2 * Real.pi)) + γ * ξ) + p * (2 * Real.pi) := by
      ring
    rw [this, Real.sin_add_int_mul_two_pi]
  have hdist :=
    Real.abs_sin_sub_sin_le ((t * γ - p * (2 * Real.pi)) + γ * ξ) (γ * ξ)
  have hdist' :
      |Real.sin ((t * γ - p * (2 * Real.pi)) + γ * ξ) - Real.sin (γ * ξ)|
        ≤ |t * γ - p * (2 * Real.pi)| := by
    have hsub :
        ((t * γ - p * (2 * Real.pi)) + γ * ξ) - γ * ξ = t * γ - p * (2 * Real.pi) := by
      ring
    simpa [hsub] using hdist
  have hdist'' :
      |Real.sin (γ * (t + ξ)) - Real.sin (γ * ξ)| ≤ |t * γ - p * (2 * Real.pi)| := by
    rw [hperiod]
    exact hdist'
  exact lt_of_le_of_lt hdist'' hp

private lemma abelWeightedZeroKernel_transport_abs_le
    [ZeroOrdinateLowerBoundHyp]
    {ξ t ε : ℝ} {ρ : ℂ}
    (hξ_nonneg : 0 ≤ ξ)
    (hρ : ρ ∈ positiveImZerosBelow (1 / ξ))
    {p : ℤ} (hp : |t * ρ.im - p * (2 * Real.pi)| < ε) :
    |abelWeightedZeroKernel ξ (t + ξ) ρ - abelWeightedZeroKernel ξ ξ ρ| ≤ ε := by
  have hγ_one : (1 : ℝ) < ρ.im := positiveImZerosBelow_im_gt_one hρ
  have hγ_pos : 0 < ρ.im := lt_trans zero_lt_one hγ_one
  have hsin :
      |Real.sin (ρ.im * (t + ξ)) - Real.sin (ρ.im * ξ)| < ε :=
    sin_shift_transport_lt hp
  have hε_nonneg : 0 ≤ ε := le_of_lt (lt_of_le_of_lt (abs_nonneg _) hp)
  have hrewrite :
      abelWeightedZeroKernel ξ (t + ξ) ρ - abelWeightedZeroKernel ξ ξ ρ
        = ((Real.sin (ρ.im * (t + ξ)) - Real.sin (ρ.im * ξ)) / ρ.im) *
            Real.exp (-(ρ.im * ξ)) := by
    simp [abelWeightedZeroKernel, sub_eq_add_neg]
    ring
  calc
    |abelWeightedZeroKernel ξ (t + ξ) ρ - abelWeightedZeroKernel ξ ξ ρ|
        = |((Real.sin (ρ.im * (t + ξ)) - Real.sin (ρ.im * ξ)) / ρ.im) *
            Real.exp (-(ρ.im * ξ))| := by rw [hrewrite]
    _ = |Real.sin (ρ.im * (t + ξ)) - Real.sin (ρ.im * ξ)| / ρ.im *
          Real.exp (-(ρ.im * ξ)) := by
            rw [abs_mul, abs_div, abs_of_pos hγ_pos, abs_of_nonneg (Real.exp_pos _).le]
    _ ≤ ε / ρ.im * Real.exp (-(ρ.im * ξ)) := by
          gcongr
    _ ≤ ε / ρ.im := by
          have hnonneg : 0 ≤ ε / ρ.im := by exact div_nonneg hε_nonneg hγ_pos.le
          exact mul_le_of_le_one_right hnonneg
            (Real.exp_le_one_iff.mpr (by nlinarith [hγ_pos, hξ_nonneg]))
    _ ≤ ε := by
          have hρinv_le : 1 / ρ.im ≤ 1 := by
            rw [one_div_le hγ_pos (by positivity : (0 : ℝ) < 1)]
            simpa using le_of_lt hγ_one
          calc
            ε / ρ.im = ε * (1 / ρ.im) := by ring
            _ ≤ ε * 1 := by gcongr
            _ = ε := by ring

private lemma abelWeightedZeroSum_transport_abs_le
    [ZeroOrdinateLowerBoundHyp]
    {ξ t ε : ℝ} (hξ : 0 < ξ)
    (hphase :
      ∀ ρ ∈ positiveImZerosBelow (1 / ξ), ∃ p : ℤ, |t * ρ.im - p * (2 * Real.pi)| < ε) :
    |abelWeightedZeroSum ξ (t + ξ) - abelWeightedZeroSum ξ ξ|
      ≤ ε * (Nmult (1 / ξ) : ℝ) := by
  let S := positiveImZerosBelow (1 / ξ)
  have hsum :
      abelWeightedZeroSum ξ (t + ξ) - abelWeightedZeroSum ξ ξ
        = ∑ ρ ∈ S,
            (zeroMultiplicity ρ : ℝ) *
              (abelWeightedZeroKernel ξ (t + ξ) ρ - abelWeightedZeroKernel ξ ξ ρ) := by
    simp [abelWeightedZeroSum, abelWeightedZeroSumUpTo, S, Finset.sum_sub_distrib, mul_sub]
  rw [hsum]
  calc
    |∑ ρ ∈ S,
        (zeroMultiplicity ρ : ℝ) *
          (abelWeightedZeroKernel ξ (t + ξ) ρ - abelWeightedZeroKernel ξ ξ ρ)|
        ≤ ∑ ρ ∈ S,
            |(zeroMultiplicity ρ : ℝ) *
              (abelWeightedZeroKernel ξ (t + ξ) ρ - abelWeightedZeroKernel ξ ξ ρ)| := by
              exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ρ ∈ S,
          (zeroMultiplicity ρ : ℝ) *
            |abelWeightedZeroKernel ξ (t + ξ) ρ - abelWeightedZeroKernel ξ ξ ρ| := by
              refine Finset.sum_congr rfl ?_
              intro ρ hρ
              rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (zeroMultiplicity ρ : ℝ))]
    _ ≤ ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) * ε := by
          refine Finset.sum_le_sum ?_
          intro ρ hρ
          rcases hphase ρ hρ with ⟨p, hp⟩
          gcongr
          exact abelWeightedZeroKernel_transport_abs_le hξ.le hρ hp
    _ = ε * (Nmult (1 / ξ) : ℝ) := by
          calc
            ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) * ε
                = (∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ)) * ε := by rw [Finset.sum_mul]
            _ = (Nmult (1 / ξ) : ℝ) * ε := by
                  simp [S, sum_zeroMultiplicity_positiveImZerosBelow_real]
            _ = ε * (Nmult (1 / ξ) : ℝ) := by ring

private lemma abelWeightedZeroKernel_transport_base_abs_le
    [ZeroOrdinateLowerBoundHyp]
    {ξ η₀ t ε : ℝ} {ρ : ℂ}
    (hξ_nonneg : 0 ≤ ξ)
    (hρ : ρ ∈ positiveImZerosBelow (1 / ξ))
    {p : ℤ} (hp : |t * ρ.im - p * (2 * Real.pi)| < ε) :
    |abelWeightedZeroKernel ξ (t + η₀) ρ - abelWeightedZeroKernel ξ η₀ ρ| ≤ ε := by
  have hγ_one : (1 : ℝ) < ρ.im := positiveImZerosBelow_im_gt_one hρ
  have hγ_pos : 0 < ρ.im := lt_trans zero_lt_one hγ_one
  have hsin :
      |Real.sin (ρ.im * (t + η₀)) - Real.sin (ρ.im * η₀)| < ε := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (sin_shift_transport_lt (γ := ρ.im) (ξ := η₀) (t := t) (ε := ε) hp)
  have hε_nonneg : 0 ≤ ε := le_of_lt (lt_of_le_of_lt (abs_nonneg _) hp)
  have hrewrite :
      abelWeightedZeroKernel ξ (t + η₀) ρ - abelWeightedZeroKernel ξ η₀ ρ
        = ((Real.sin (ρ.im * (t + η₀)) - Real.sin (ρ.im * η₀)) / ρ.im) *
            Real.exp (-(ρ.im * ξ)) := by
    simp [abelWeightedZeroKernel, sub_eq_add_neg]
    ring
  calc
    |abelWeightedZeroKernel ξ (t + η₀) ρ - abelWeightedZeroKernel ξ η₀ ρ|
        = |((Real.sin (ρ.im * (t + η₀)) - Real.sin (ρ.im * η₀)) / ρ.im) *
            Real.exp (-(ρ.im * ξ))| := by rw [hrewrite]
    _ = |Real.sin (ρ.im * (t + η₀)) - Real.sin (ρ.im * η₀)| / ρ.im *
          Real.exp (-(ρ.im * ξ)) := by
            rw [abs_mul, abs_div, abs_of_pos hγ_pos, abs_of_nonneg (Real.exp_pos _).le]
    _ ≤ ε / ρ.im * Real.exp (-(ρ.im * ξ)) := by
          gcongr
    _ ≤ ε / ρ.im := by
          have hnonneg : 0 ≤ ε / ρ.im := by exact div_nonneg hε_nonneg hγ_pos.le
          exact mul_le_of_le_one_right hnonneg
            (Real.exp_le_one_iff.mpr (by nlinarith [hγ_pos, hξ_nonneg]))
    _ ≤ ε := by
          have hρinv_le : 1 / ρ.im ≤ 1 := by
            rw [one_div_le hγ_pos (by positivity : (0 : ℝ) < 1)]
            simpa using le_of_lt hγ_one
          calc
            ε / ρ.im = ε * (1 / ρ.im) := by ring
            _ ≤ ε * 1 := by gcongr
            _ = ε := by ring

private lemma abelWeightedZeroSum_transport_base_abs_le
    [ZeroOrdinateLowerBoundHyp]
    {ξ η₀ t ε : ℝ} (hξ : 0 < ξ)
    (hphase :
      ∀ ρ ∈ positiveImZerosBelow (1 / ξ), ∃ p : ℤ, |t * ρ.im - p * (2 * Real.pi)| < ε) :
    |abelWeightedZeroSum ξ (t + η₀) - abelWeightedZeroSum ξ η₀|
      ≤ ε * (Nmult (1 / ξ) : ℝ) := by
  let S := positiveImZerosBelow (1 / ξ)
  have hsum :
      abelWeightedZeroSum ξ (t + η₀) - abelWeightedZeroSum ξ η₀
        = ∑ ρ ∈ S,
            (zeroMultiplicity ρ : ℝ) *
              (abelWeightedZeroKernel ξ (t + η₀) ρ - abelWeightedZeroKernel ξ η₀ ρ) := by
    simp [abelWeightedZeroSum, abelWeightedZeroSumUpTo, S, Finset.sum_sub_distrib, mul_sub]
  rw [hsum]
  calc
    |∑ ρ ∈ S,
        (zeroMultiplicity ρ : ℝ) *
          (abelWeightedZeroKernel ξ (t + η₀) ρ - abelWeightedZeroKernel ξ η₀ ρ)|
        ≤ ∑ ρ ∈ S,
            |(zeroMultiplicity ρ : ℝ) *
              (abelWeightedZeroKernel ξ (t + η₀) ρ - abelWeightedZeroKernel ξ η₀ ρ)| := by
              exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ρ ∈ S,
          (zeroMultiplicity ρ : ℝ) *
            |abelWeightedZeroKernel ξ (t + η₀) ρ - abelWeightedZeroKernel ξ η₀ ρ| := by
              refine Finset.sum_congr rfl ?_
              intro ρ hρ
              rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (zeroMultiplicity ρ : ℝ))]
    _ ≤ ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) * ε := by
          refine Finset.sum_le_sum ?_
          intro ρ hρ
          rcases hphase ρ hρ with ⟨p, hp⟩
          gcongr
          exact abelWeightedZeroKernel_transport_base_abs_le hξ.le hρ hp
    _ = ε * (Nmult (1 / ξ) : ℝ) := by
          calc
            ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) * ε
                = (∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ)) * ε := by rw [Finset.sum_mul]
            _ = (Nmult (1 / ξ) : ℝ) * ε := by
                  simp [S, sum_zeroMultiplicity_positiveImZerosBelow_real]
            _ = ε * (Nmult (1 / ξ) : ℝ) := by ring

private lemma abelWeightedZeroSum_neg_diag (ξ : ℝ) :
    abelWeightedZeroSum ξ (-ξ) = -abelWeightedZeroSum ξ ξ := by
  unfold abelWeightedZeroSum abelWeightedZeroSumUpTo
  calc
    ∑ ρ ∈ positiveImZerosBelow (1 / ξ), (zeroMultiplicity ρ : ℝ) * abelWeightedZeroKernel ξ (-ξ) ρ
        = ∑ ρ ∈ positiveImZerosBelow (1 / ξ),
            -((zeroMultiplicity ρ : ℝ) * abelWeightedZeroKernel ξ ξ ρ) := by
              refine Finset.sum_congr rfl ?_
              intro ρ hρ
              simp [abelWeightedZeroKernel, Real.sin_neg]
              ring
    _ = -∑ ρ ∈ positiveImZerosBelow (1 / ξ),
          (zeroMultiplicity ρ : ℝ) * abelWeightedZeroKernel ξ ξ ρ := by
            rw [Finset.sum_neg_distrib]

/-! ## Hypothesis classes

Each class below is now phrased against the actual multiplicity-weighted Abel
sum. The diagonal lower bound is the main analytic leaf; the key-lemma and
PL-bridge classes package the two downstream classical steps. -/

/-- **Diagonal evaluation.** The Abel-weighted zero sum on the diagonal
`z = ξ + iξ` has a positive logarithmic lower bound as `ξ → 0+`.

Classically the main term is `(1/8) * log(1 / ξ)` from
`∫₀^∞ (sin t / t) * exp(-t) dt = π / 4`. -/
class LittlewoodDiagonalEvalHyp : Prop where
  diag_eval :
    ∃ A > 0, ∃ ξ₀ > 0, ∀ ξ, 0 < ξ → ξ < ξ₀ →
      A * Real.log (1 / ξ) ≤ abelWeightedZeroSum ξ ξ

theorem diagonalEvalLowerBound_of_multLowerBound
    [ZeroCountingMultLowerBoundHyp] :
    ∃ A > 0, ∃ ξ₀ > 0, ∀ ξ, 0 < ξ → ξ < ξ₀ →
      A * Real.log (1 / ξ) ≤ abelWeightedZeroSum ξ ξ := by
  rcases zeroCountingFunctionMult_lower_bound with ⟨T0, hT0⟩
  let S : ℝ := max T0 1
  refine ⟨Real.exp (-1) / (6 * Real.pi), by positivity, 1 / (S + 1), by positivity, ?_⟩
  intro ξ hξ hξ_lt
  have hS_ge_one : 1 ≤ S := le_max_right _ _
  have hS_pos : 0 < S := lt_of_lt_of_le zero_lt_one hS_ge_one
  have hS1_pos : 0 < S + 1 := by positivity
  have hmul_lt : ξ * (S + 1) < 1 := by
    have hmul := mul_lt_mul_of_pos_right hξ_lt hS1_pos
    have hright : (1 / (S + 1)) * (S + 1) = 1 := by
      exact one_div_mul_cancel hS1_pos.ne'
    exact hmul.trans_eq hright
  have hS_le_inv : S ≤ 1 / ξ := by
    rw [le_div_iff₀ hξ]
    nlinarith [hS_ge_one, hmul_lt]
  have hT0_le_inv : T0 ≤ 1 / ξ := le_trans (le_max_left _ _) hS_le_inv
  have hNmult :
      ((1 / ξ) / (3 * Real.pi)) * Real.log (1 / ξ) ≤ (Nmult (1 / ξ) : ℝ) :=
    hT0 (1 / ξ) hT0_le_inv
  have hsum_lower :
      ((Nmult (1 / ξ) : ℝ) * (ξ / 2 * Real.exp (-1))) ≤ abelWeightedZeroSum ξ ξ := by
    calc
      (Nmult (1 / ξ) : ℝ) * (ξ / 2 * Real.exp (-1))
          = ∑ ρ ∈ positiveImZerosBelow (1 / ξ),
              (zeroMultiplicity ρ : ℝ) * (ξ / 2 * Real.exp (-1)) := by
              rw [← sum_zeroMultiplicity_positiveImZerosBelow_real (1 / ξ), Finset.sum_mul]
      _ ≤ ∑ ρ ∈ positiveImZerosBelow (1 / ξ),
            (zeroMultiplicity ρ : ℝ) * abelWeightedZeroKernel ξ ξ ρ := by
              refine Finset.sum_le_sum ?_
              intro ρ hρ
              exact mul_le_mul_of_nonneg_left
                (abelWeightedZeroKernel_diag_lower hξ hρ)
                (by positivity)
      _ = abelWeightedZeroSum ξ ξ := rfl
  have hscaled :
      (ξ / 2 * Real.exp (-1))
        * (((1 / ξ) / (3 * Real.pi)) * Real.log (1 / ξ))
        ≤ (ξ / 2 * Real.exp (-1)) * (Nmult (1 / ξ) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hNmult (by positivity)
  have hmain :
      (Real.exp (-1) / (6 * Real.pi)) * Real.log (1 / ξ)
        ≤ (Nmult (1 / ξ) : ℝ) * (ξ / 2 * Real.exp (-1)) := by
    calc
      (Real.exp (-1) / (6 * Real.pi)) * Real.log (1 / ξ)
          = (ξ / 2 * Real.exp (-1))
              * (((1 / ξ) / (3 * Real.pi)) * Real.log (1 / ξ)) := by
                field_simp [hξ.ne', Real.pi_ne_zero]
                ring
      _ ≤ (ξ / 2 * Real.exp (-1)) * (Nmult (1 / ξ) : ℝ) := hscaled
      _ = (Nmult (1 / ξ) : ℝ) * (ξ / 2 * Real.exp (-1)) := by ring
  exact hmain.trans hsum_lower

instance [ZeroCountingMultLowerBoundHyp] : LittlewoodDiagonalEvalHyp where
  diag_eval := diagonalEvalLowerBound_of_multLowerBound

/-- **Littlewood's key lemma.** For arbitrarily large `η`, one can find
`ξ ∈ (0, 1]` with the Abel sum at `(ξ, η)` at least a constant multiple of
`log log η`. -/
class LittlewoodKeyLemmaHyp : Prop where
  key_lemma :
    ∃ K > 0, ∀ η₀ > 0,
      ∃ (ξ : ℝ), 0 < ξ ∧ ξ ≤ 1 ∧
      ∃ (η : ℝ), η₀ < η ∧
        K * Real.log (Real.log η) ≤ abelWeightedZeroSum ξ η

/-- **Phragmén-Lindelöf bridge.** A one-sided upper bound on `ψ(x) - x` forces
an upper bound of the same `log log η` scale for the Abel sum in the strip
`0 < ξ ≤ 1`. -/
class LittlewoodPLBridgeHyp : Prop where
  bridge :
    ∀ (_hRH : RiemannHypothesis'),
      ∀ (δ : ℝ), δ > 0 →
      (∀ᶠ x in atTop,
        -(chebyshevPsi x - x) < δ * Real.sqrt x * Real.log (Real.log (Real.log x))) →
      ∃ C₁ > 0,
      ∀ (ξ : ℝ), 0 < ξ → ξ ≤ 1 →
      ∀ (η : ℝ), η ≥ Real.exp (Real.exp 1) →
        abelWeightedZeroSum ξ η ≤ 2 * δ * Real.log (Real.log η) + C₁

/-- **Phragmén-Lindelöf Abel strip bound.** This hypothesis encodes the output
of the Phragmén-Lindelöf argument applied to `complexAbelFun` in the vertical
strip `0 < Re z ≤ 1`.

MATHEMATICAL CONTENT: Under RH the explicit formula
  `ψ(x) = x − ∑ x^ρ/ρ + O(…)`
connects the ψ upper bound to a boundary estimate on
  `complexAbelFun T z = ∑ m(ρ) exp(−γ z)/γ`.
Applying the Phragmén-Lindelöf principle (`PhragmenLindelof.vertical_strip`
from Mathlib) in the strip `{z | 0 < Re z < 2}` with the ψ-derived bound
on the left boundary and the exponential-decay bound on the right boundary
yields a uniform estimate on `−Im(complexAbelFun)` throughout the strip.

MATHEMATICAL STATUS: classical — follows from the truncated explicit formula
(see `ExplicitFormulaPsiHyp`) and `PhragmenLindelof.vertical_strip`.

REFERENCE: Ingham, "The Distribution of Prime Numbers", Chapter V. -/
class PhragmenLindelofAbelStripBoundHyp : Prop where
  /-- Upper bound: a one-sided ψ lower bound gives an upper bound on the Abel sum. -/
  strip_bound :
    ∀ (_hRH : RiemannHypothesis'),
      ∀ (δ : ℝ), δ > 0 →
      (∀ᶠ x in atTop,
        -(chebyshevPsi x - x) < δ * Real.sqrt x * Real.log (Real.log (Real.log x))) →
      ∃ C > 0,
      ∀ (T : ℝ), T ≥ 1 →
      ∀ (ξ : ℝ), 0 < ξ → ξ ≤ 1 →
      ∀ (η : ℝ), η ≥ Real.exp (Real.exp 1) →
        -(complexAbelFun T (↑ξ + ↑η * Complex.I)).im ≤
          2 * δ * Real.log (Real.log η) + C
  /-- Lower bound (symmetric): a one-sided ψ upper bound gives a lower bound
  on the Abel sum. This is the same PL argument with reversed sign. -/
  strip_bound_neg :
    ∀ (_hRH : RiemannHypothesis'),
      ∀ (δ : ℝ), δ > 0 →
      (∀ᶠ x in atTop,
        chebyshevPsi x - x < δ * Real.sqrt x * Real.log (Real.log (Real.log x))) →
      ∃ C > 0,
      ∀ (T : ℝ), T ≥ 1 →
      ∀ (ξ : ℝ), 0 < ξ → ξ ≤ 1 →
      ∀ (η : ℝ), η ≥ Real.exp (Real.exp 1) →
        (complexAbelFun T (↑ξ + ↑η * Complex.I)).im ≤
          2 * δ * Real.log (Real.log η) + C

/-- The PL Abel strip bound implies the PLBridge. -/
instance [PhragmenLindelofAbelStripBoundHyp] : LittlewoodPLBridgeHyp where
  bridge := by
    intro hRH δ hδ hψ
    obtain ⟨C, hC_pos, hbound⟩ := PhragmenLindelofAbelStripBoundHyp.strip_bound hRH δ hδ hψ
    exact ⟨C, hC_pos, fun ξ hξ hξ1 η hη => by
      have hT : (1 : ℝ) / ξ ≥ 1 := by rw [ge_iff_le, le_div_iff₀ hξ]; linarith [hξ1]
      rw [abelWeightedZeroSum_eq_neg_im_complexAbelFun ξ η hξ]
      exact hbound (1 / ξ) hT ξ hξ hξ1 η hη⟩

theorem littlewoodDiagonalEvalHyp_lower
    [LittlewoodDiagonalEvalHyp] :
    ∃ A > 0, ∃ ξ₀ > 0, ∀ ξ, 0 < ξ → ξ < ξ₀ →
      A * Real.log (1 / ξ) ≤ abelWeightedZeroSum ξ ξ := by
  simpa using LittlewoodDiagonalEvalHyp.diag_eval

theorem littlewoodKeyLemma_of_diagonal
    [LittlewoodDiagonalEvalHyp] [ZeroOrdinateLowerBoundHyp] [ZeroCountingCrudeBoundHyp] :
    ∃ K > 0, ∀ η₀ > 0,
      ∃ (ξ : ℝ), 0 < ξ ∧ ξ ≤ 1 ∧
      ∃ (η : ℝ), η₀ < η ∧
        K * Real.log (Real.log η) ≤ abelWeightedZeroSum ξ η := by
  obtain ⟨A, hA_pos, ξ₀, hξ₀_pos, hdiag⟩ := littlewoodDiagonalEvalHyp_lower
  rcases zeroCountingFunction_crude_bound with ⟨C, hC⟩
  let C0 : ℝ := max C 1
  let B0 : ℝ := 32 * Real.pi * Real.exp 1 + 2
  let D : ℝ := C0 * B0 + 2
  have hC0_pos : 0 < C0 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hB0_pos : 0 < B0 := by
    unfold B0
    positivity
  have hD_pos : 0 < D := by
    unfold D
    nlinarith
  refine ⟨A / 10, by positivity, ?_⟩
  intro η₀ hη₀
  let L : ℝ := max η₀ (Real.exp 1)
  let k : ℕ := Nat.floor L + 1
  let ξ : ℝ := min (ξ₀ / 2) (min (1 / (k : ℝ)) (min (1 / 4) (1 / D)))
  have hk_pos : 0 < k := by
    exact Nat.succ_pos _
  have hk_pos_real : 0 < (k : ℝ) := by
    exact_mod_cast hk_pos
  have hξ_pos : 0 < ξ := by
    unfold ξ
    refine lt_min ?_ ?_
    · nlinarith
    · refine lt_min ?_ ?_
      · exact one_div_pos.mpr hk_pos_real
      · refine lt_min ?_ ?_
        · norm_num
        · exact one_div_pos.mpr hD_pos
  have hξ_le_half : ξ ≤ ξ₀ / 2 := by
    unfold ξ
    exact min_le_left _ _
  have hξ_lt_ξ₀ : ξ < ξ₀ := by
    nlinarith [hξ_le_half, hξ₀_pos]
  have hξ_le_invk : ξ ≤ 1 / (k : ℝ) := by
    unfold ξ
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hξ_le_quarter : ξ ≤ 1 / 4 := by
    unfold ξ
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hξ_le_invD : ξ ≤ 1 / D := by
    unfold ξ
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hξ_le_one : ξ ≤ 1 := by
    nlinarith [hξ_le_quarter]
  have hL_nonneg : 0 ≤ L := by
    unfold L
    positivity
  let phaseTol : ℝ := ξ / (8 * Real.exp 1)
  have hphaseTol_pos : 0 < phaseTol := by
    unfold phaseTol
    positivity
  let S : Finset ℂ := positiveImZerosBelow (1 / ξ)
  obtain ⟨t, ht_gt_L, M, hM_pos, hM_upper, ht_bound, hphase⟩ :=
    bounded_simultaneous_near_period_finset S (ε := phaseTol) (L := L) hphaseTol_pos hL_nonneg
  let η : ℝ := t + ξ
  have hη_gt_η₀ : η₀ < η := by
    have hη₀_le_L : η₀ ≤ L := le_max_left _ _
    have hη₀_lt_t : η₀ < t := lt_of_le_of_lt hη₀_le_L ht_gt_L
    unfold η
    linarith
  have hdiag_here : A * Real.log (1 / ξ) ≤ abelWeightedZeroSum ξ ξ :=
    hdiag ξ hξ_pos hξ_lt_ξ₀
  have htransport :
      |abelWeightedZeroSum ξ η - abelWeightedZeroSum ξ ξ|
        ≤ phaseTol * (Nmult (1 / ξ) : ℝ) := by
    simpa [η, phaseTol, S] using
      (abelWeightedZeroSum_transport_abs_le (ξ := ξ) (t := t) (ε := phaseTol) hξ_pos hphase)
  have hNmult_diag :
      (Nmult (1 / ξ) : ℝ) ≤ (2 * Real.exp 1 / ξ) * abelWeightedZeroSum ξ ξ :=
    Nmult_le_diagonal_sum_scale hξ_pos
  have hphase_scale :
      phaseTol * (Nmult (1 / ξ) : ℝ) ≤ (1 / 4 : ℝ) * abelWeightedZeroSum ξ ξ := by
    calc
      phaseTol * (Nmult (1 / ξ) : ℝ)
          ≤ phaseTol * ((2 * Real.exp 1 / ξ) * abelWeightedZeroSum ξ ξ) := by
              exact mul_le_mul_of_nonneg_left hNmult_diag (by positivity)
      _ = (1 / 4 : ℝ) * abelWeightedZeroSum ξ ξ := by
            unfold phaseTol
            field_simp [hξ_pos.ne', Real.exp_ne_zero]
            ring
  have hsum_lower :
      (3 / 4 : ℝ) * abelWeightedZeroSum ξ ξ ≤ abelWeightedZeroSum ξ η := by
    have htransport' := abs_le.mp htransport
    have h1 : abelWeightedZeroSum ξ ξ - phaseTol * (Nmult (1 / ξ) : ℝ) ≤ abelWeightedZeroSum ξ η := by
      linarith [htransport'.1]
    have h2 : (3 / 4 : ℝ) * abelWeightedZeroSum ξ ξ
        ≤ abelWeightedZeroSum ξ ξ - phaseTol * (Nmult (1 / ξ) : ℝ) := by
      calc
        (3 / 4 : ℝ) * abelWeightedZeroSum ξ ξ
            = abelWeightedZeroSum ξ ξ - (1 / 4 : ℝ) * abelWeightedZeroSum ξ ξ := by ring
        _ ≤ abelWeightedZeroSum ξ ξ - phaseTol * (Nmult (1 / ξ) : ℝ) := by
            gcongr
    exact h2.trans h1
  have hsum_main :
      (A / 2) * Real.log (1 / ξ) ≤ abelWeightedZeroSum ξ η := by
    have hone : 1 ≤ 1 / ξ := by
      rw [one_le_div hξ_pos]
      exact hξ_le_one
    have hlog_nonneg : 0 ≤ Real.log (1 / ξ) := Real.log_nonneg hone
    have h34A : (3 / 4 : ℝ) * (A * Real.log (1 / ξ)) ≤ abelWeightedZeroSum ξ η := by
      exact le_trans (mul_le_mul_of_nonneg_left hdiag_here (by positivity)) hsum_lower
    have hhalf_le : (A / 2) * Real.log (1 / ξ) ≤ (3 / 4 : ℝ) * (A * Real.log (1 / ξ)) := by
      nlinarith [hA_pos, hlog_nonneg]
    exact hhalf_le.trans h34A
  have hk_le_invξ : (k : ℝ) ≤ 1 / ξ := by
    have hkξ_le : ξ * (k : ℝ) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right hξ_le_invk hk_pos_real.le
      simpa [hk_pos_real.ne'] using hmul
    rw [le_div_iff₀ hξ_pos]
    nlinarith [hkξ_le]
  have hM_le_B0 : (M : ℝ) ≤ B0 / ξ ^ 2 := by
    calc
      (M : ℝ) ≤ (4 * Real.pi * ((Nat.floor L + 1 : ℕ) : ℝ)) / phaseTol + 1 := hM_upper
      _ = 32 * Real.pi * Real.exp 1 * ((k : ℝ) / ξ) + 1 := by
            unfold phaseTol k
            field_simp [hξ_pos.ne', Real.exp_ne_zero]
            ring
      _ ≤ 32 * Real.pi * Real.exp 1 * ((1 / ξ) / ξ) + 1 := by
            gcongr
      _ = 32 * Real.pi * Real.exp 1 / ξ ^ 2 + 1 := by
            field_simp [hξ_pos.ne']
      _ ≤ B0 / ξ ^ 2 := by
            have hξsq_pos : 0 < ξ ^ 2 := by positivity
            have hone : (1 : ℝ) ≤ 2 / ξ ^ 2 := by
              rw [le_div_iff₀ hξsq_pos]
              nlinarith [hξ_le_one, hξ_pos]
            calc
              32 * Real.pi * Real.exp 1 / ξ ^ 2 + 1
                  ≤ 32 * Real.pi * Real.exp 1 / ξ ^ 2 + 2 / ξ ^ 2 := by
                    gcongr
              _ = B0 / ξ ^ 2 := by
                    unfold B0
                    field_simp [hξ_pos.ne']
  have hξ_inv_ge_four : 4 ≤ 1 / ξ := by
    rw [le_div_iff₀ hξ_pos]
    nlinarith [hξ_le_quarter]
  have hlog_inv_le_inv : Real.log (1 / ξ) ≤ 1 / ξ := by
    have hξinv_pos : 0 < 1 / ξ := one_div_pos.mpr hξ_pos
    have hlog := Real.log_le_sub_one_of_pos hξinv_pos
    have hone : 1 ≤ 1 / ξ := by
      rw [one_le_div hξ_pos]
      exact hξ_le_one
    linarith
  have hcard_le : (S.card : ℝ) ≤ C0 / ξ ^ 2 := by
    have hone : 1 ≤ 1 / ξ := by
      rw [one_le_div hξ_pos]
      exact hξ_le_one
    have hlog_nonneg : 0 ≤ Real.log (1 / ξ) := Real.log_nonneg hone
    have hNbase : (N (1 / ξ) : ℝ) ≤ C * (1 / ξ) * Real.log (1 / ξ) := hC hξ_inv_ge_four
    have hNle : (N (1 / ξ) : ℝ) ≤ C0 * (1 / ξ) * Real.log (1 / ξ) := by
      refine hNbase.trans ?_
      gcongr
      exact le_max_left _ _
    calc
      (S.card : ℝ) = N (1 / ξ) := by
        simp [S, card_positiveImZerosBelow]
      _ ≤ C0 * (1 / ξ) * Real.log (1 / ξ) := hNle
      _ ≤ C0 * (1 / ξ) * (1 / ξ) := by
            gcongr
      _ = C0 / ξ ^ 2 := by
            field_simp [hξ_pos.ne']
  let U : ℝ := Real.log 2 + Real.log (k : ℝ) + (S.card : ℝ) * Real.log (M : ℝ)
  have hη_gt_exp1 : Real.exp 1 < η := by
    have hexp1_le_L : Real.exp 1 ≤ L := le_max_right _ _
    have hexp1_lt_t : Real.exp 1 < t := lt_of_le_of_lt hexp1_le_L ht_gt_L
    unfold η
    linarith
  have hη_gt_one : 1 < η := by
    have : 1 < Real.exp 1 := by simpa using Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hlogη_pos : 0 < Real.log η := Real.log_pos hη_gt_one
  have hk_ge_one : 1 ≤ (k : ℝ) := by
    exact_mod_cast hk_pos
  have hM_ge_one : 1 ≤ (M : ℝ) := by
    exact_mod_cast hM_pos
  have hM_pos_real : 0 < (M : ℝ) := by
    exact_mod_cast hM_pos
  have hMpow_ge_one : 1 ≤ (M : ℝ) ^ S.card := by
    exact one_le_pow₀ hM_ge_one
  have hkM_ge_one : 1 ≤ (k : ℝ) * (M : ℝ) ^ S.card := by
    nlinarith
  have hη_upper : η ≤ 2 * (k : ℝ) * (M : ℝ) ^ S.card := by
    unfold η
    calc
      t + ξ ≤ t + 1 := by gcongr
      _ ≤ (k : ℝ) * (M : ℝ) ^ S.card + 1 := by gcongr
      _ ≤ (k : ℝ) * (M : ℝ) ^ S.card + (k : ℝ) * (M : ℝ) ^ S.card := by
            linarith
      _ = 2 * (k : ℝ) * (M : ℝ) ^ S.card := by ring
  have hlogη_le : Real.log η ≤ U := by
    have hrhs_pos : 0 < 2 * (k : ℝ) * (M : ℝ) ^ S.card := by positivity
    calc
      Real.log η ≤ Real.log (2 * (k : ℝ) * (M : ℝ) ^ S.card) := by
        exact Real.log_le_log (by positivity) hη_upper
      _ = U := by
        unfold U
        rw [show 2 * (k : ℝ) * (M : ℝ) ^ S.card = 2 * ((k : ℝ) * (M : ℝ) ^ S.card) by ring]
        rw [Real.log_mul (by positivity : (2 : ℝ) ≠ 0)
              (by positivity : ((k : ℝ) * (M : ℝ) ^ S.card) ≠ 0)]
        rw [Real.log_mul (by positivity : (k : ℝ) ≠ 0)
              (by positivity : ((M : ℝ) ^ S.card) ≠ 0)]
        rw [Real.log_pow]
        ring
  have hU_pos : 0 < U := lt_of_lt_of_le hlogη_pos hlogη_le
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogk_le : Real.log (k : ℝ) ≤ (k : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hk_pos_real
    linarith
  have hlogM_le : Real.log (M : ℝ) ≤ (M : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hM_pos_real
    linarith
  have hone_le_invξ4 : (1 : ℝ) ≤ 1 / ξ ^ 4 := by
    have hξ4_le_one : ξ ^ 4 ≤ 1 := pow_le_one₀ hξ_pos.le hξ_le_one
    rw [one_le_div (by positivity : (0 : ℝ) < ξ ^ 4)]
    exact hξ4_le_one
  have hk_le_invξ4 : (k : ℝ) ≤ 1 / ξ ^ 4 := by
    have hξ3_le_one : ξ ^ 3 ≤ 1 := pow_le_one₀ hξ_pos.le hξ_le_one
    have hpow_den : ξ ^ 4 ≤ ξ := by
      calc
        ξ ^ 4 = ξ * ξ ^ 3 := by ring
        _ ≤ ξ * 1 := by
            gcongr
        _ = ξ := by ring
    have hpow : 1 / ξ ≤ 1 / ξ ^ 4 :=
      one_div_le_one_div_of_le (by positivity : 0 < ξ ^ 4) hpow_den
    exact hk_le_invξ.trans hpow
  have hcard_logM :
      (S.card : ℝ) * Real.log (M : ℝ) ≤ C0 * B0 / ξ ^ 4 := by
    have hcard_nonneg : 0 ≤ (S.card : ℝ) := by positivity
    have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
    calc
      (S.card : ℝ) * Real.log (M : ℝ) ≤ (S.card : ℝ) * (M : ℝ) := by
            exact mul_le_mul_of_nonneg_left hlogM_le hcard_nonneg
      _ ≤ (C0 / ξ ^ 2) * (B0 / ξ ^ 2) := by
            exact mul_le_mul hcard_le hM_le_B0 hM_nonneg (by positivity)
      _ = C0 * B0 / ξ ^ 4 := by
            field_simp [hξ_pos.ne']
  have hU_le : U ≤ D / ξ ^ 4 := by
    have h1 : Real.log 2 ≤ 1 / ξ ^ 4 := hlog2_le_one.trans hone_le_invξ4
    have h2 : Real.log (k : ℝ) ≤ 1 / ξ ^ 4 := hlogk_le.trans hk_le_invξ4
    have h12 : Real.log 2 + Real.log (k : ℝ) ≤ 2 / ξ ^ 4 := by
      calc
        Real.log 2 + Real.log (k : ℝ) ≤ 1 / ξ ^ 4 + 1 / ξ ^ 4 := add_le_add h1 h2
        _ = 2 / ξ ^ 4 := by ring
    calc
      U = (Real.log 2 + Real.log (k : ℝ)) + (S.card : ℝ) * Real.log (M : ℝ) := by
            unfold U
            ring
      _ ≤ 2 / ξ ^ 4 + C0 * B0 / ξ ^ 4 := by
            exact add_le_add h12 hcard_logM
      _ = D / ξ ^ 4 := by
            unfold D
            field_simp [hξ_pos.ne']
            ring
  have hloglogη_le :
      Real.log (Real.log η) ≤ 5 * Real.log (1 / ξ) := by
    have hlogU_le : Real.log U ≤ Real.log D + 4 * Real.log (1 / ξ) := by
      calc
        Real.log U ≤ Real.log (D / ξ ^ 4) := by
          exact Real.log_le_log hU_pos hU_le
        _ = Real.log D + 4 * Real.log (1 / ξ) := by
          rw [div_eq_mul_inv]
          have hpow_inv : (ξ ^ 4)⁻¹ = (1 / ξ) ^ 4 := by
            have : (ξ ^ 4)⁻¹ = (ξ⁻¹) ^ 4 := by simp [inv_pow]
            simpa [one_div] using this
          rw [hpow_inv]
          rw [Real.log_mul (by positivity : D ≠ 0) (by positivity : (1 / ξ : ℝ) ^ 4 ≠ 0)]
          rw [Real.log_pow]
          norm_num
    have hlogD_le : Real.log D ≤ Real.log (1 / ξ) := by
      have hDξ_le : ξ * D ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_right hξ_le_invD hD_pos.le
        simpa [hD_pos.ne', mul_comm, mul_left_comm, mul_assoc] using hmul
      have hD_le : D ≤ 1 / ξ := by
        rw [le_div_iff₀ hξ_pos]
        simpa [mul_comm] using hDξ_le
      exact Real.log_le_log hD_pos hD_le
    have hbase : Real.log (Real.log η) ≤ Real.log U := Real.log_le_log hlogη_pos hlogη_le
    calc
      Real.log (Real.log η) ≤ Real.log U := hbase
      _ ≤ Real.log D + 4 * Real.log (1 / ξ) := hlogU_le
      _ ≤ Real.log (1 / ξ) + 4 * Real.log (1 / ξ) := by gcongr
      _ = 5 * Real.log (1 / ξ) := by ring
  have hK_le :
      (A / 10) * Real.log (Real.log η) ≤ (A / 2) * Real.log (1 / ξ) := by
    calc
      (A / 10) * Real.log (Real.log η)
          ≤ (A / 10) * (5 * Real.log (1 / ξ)) := by
              exact mul_le_mul_of_nonneg_left hloglogη_le (by positivity)
      _ = (A / 2) * Real.log (1 / ξ) := by ring
  have hsumA :
      (A / 2) * Real.log (1 / ξ) ≤ abelWeightedZeroSum ξ η := hsum_main
  refine ⟨ξ, hξ_pos, hξ_le_one, η, hη_gt_η₀, ?_⟩
  exact hK_le.trans hsumA

instance [LittlewoodDiagonalEvalHyp] [ZeroOrdinateLowerBoundHyp] [ZeroCountingCrudeBoundHyp] :
    LittlewoodKeyLemmaHyp where
  key_lemma := littlewoodKeyLemma_of_diagonal

theorem littlewoodKeyLemmaHyp_key
    [LittlewoodKeyLemmaHyp] :
    ∃ K > 0, ∀ η₀ > 0,
      ∃ (ξ : ℝ), 0 < ξ ∧ ξ ≤ 1 ∧
      ∃ (η : ℝ), η₀ < η ∧
        K * Real.log (Real.log η) ≤ abelWeightedZeroSum ξ η := by
  simpa using LittlewoodKeyLemmaHyp.key_lemma

theorem littlewoodPLBridgeHyp_bound
    [LittlewoodPLBridgeHyp] :
    ∀ (_hRH : RiemannHypothesis'),
      ∀ (δ : ℝ), δ > 0 →
      (∀ᶠ x in atTop,
        -(chebyshevPsi x - x) < δ * Real.sqrt x * Real.log (Real.log (Real.log x))) →
      ∃ C₁ > 0,
      ∀ (ξ : ℝ), 0 < ξ → ξ ≤ 1 →
      ∀ (η : ℝ), η ≥ Real.exp (Real.exp 1) →
        abelWeightedZeroSum ξ η ≤ 2 * δ * Real.log (Real.log η) + C₁ := by
  simpa using LittlewoodPLBridgeHyp.bridge

/-- **Negative PL Bridge.** Under a one-sided lower bound on ψ(x)-x, the Abel
sum is bounded from below. This is the symmetric version of PLBridge. -/
theorem littlewoodPLBridgeNeg_bound
    [PhragmenLindelofAbelStripBoundHyp] :
    ∀ (_hRH : RiemannHypothesis'),
      ∀ (δ : ℝ), δ > 0 →
      (∀ᶠ x in atTop,
        chebyshevPsi x - x < δ * Real.sqrt x * Real.log (Real.log (Real.log x))) →
      ∃ C₁ > 0,
      ∀ (ξ : ℝ), 0 < ξ → ξ ≤ 1 →
      ∀ (η : ℝ), η ≥ Real.exp (Real.exp 1) →
        -(2 * δ * Real.log (Real.log η) + C₁) ≤ abelWeightedZeroSum ξ η := by
  intro hRH δ hδ hψ
  obtain ⟨C, hC_pos, hbound⟩ :=
    PhragmenLindelofAbelStripBoundHyp.strip_bound_neg hRH δ hδ hψ
  exact ⟨C, hC_pos, fun ξ hξ hξ1 η hη => by
    have hT : (1 : ℝ) / ξ ≥ 1 := by rw [ge_iff_le, le_div_iff₀ hξ]; linarith [hξ1]
    rw [abelWeightedZeroSum_eq_neg_im_complexAbelFun ξ η hξ]
    have h := hbound (1 / ξ) hT ξ hξ hξ1 η hη
    linarith⟩

/-- **Negative Key Lemma.** The Abel sum can be made arbitrarily negative
(at least `-K · log log η` in magnitude) by choosing appropriate `(ξ, η)`.
This is the symmetric analogue of `LittlewoodKeyLemmaHyp`, obtained by
transporting the same near-period argument from the diagonal point `η = ξ`
to the reflected point `η = -ξ`.

MATHEMATICAL STATUS: follows from the same simultaneous Dirichlet
approximation argument as the positive Key Lemma, targeting
`γ₁ t ≡ 0 (mod 2π)` and then replacing `η = t + ξ` by `η = t - ξ`. -/
class LittlewoodKeyLemmaMinusHyp : Prop where
  key_lemma_minus :
    ∃ K > 0, ∀ η₀ > 0,
      ∃ (ξ : ℝ), 0 < ξ ∧ ξ ≤ 1 ∧
      ∃ (η : ℝ), η₀ < η ∧
        abelWeightedZeroSum ξ η ≤ -(K * Real.log (Real.log η))

set_option maxHeartbeats 800000 in
theorem littlewoodKeyLemmaMinus_of_diagonal
    [LittlewoodDiagonalEvalHyp] [ZeroOrdinateLowerBoundHyp] [ZeroCountingCrudeBoundHyp] :
    ∃ K > 0, ∀ η₀ > 0,
      ∃ (ξ : ℝ), 0 < ξ ∧ ξ ≤ 1 ∧
      ∃ (η : ℝ), η₀ < η ∧
        abelWeightedZeroSum ξ η ≤ -(K * Real.log (Real.log η)) := by
  obtain ⟨A, hA_pos, ξ₀, hξ₀_pos, hdiag⟩ := littlewoodDiagonalEvalHyp_lower
  rcases zeroCountingFunction_crude_bound with ⟨C, hC⟩
  let C0 : ℝ := max C 1
  let B0 : ℝ := 32 * Real.pi * Real.exp 1 + 2
  let D : ℝ := C0 * B0 + 2
  have hC0_pos : 0 < C0 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hB0_pos : 0 < B0 := by
    unfold B0
    positivity
  have hD_pos : 0 < D := by
    unfold D
    nlinarith
  refine ⟨A / 10, by positivity, ?_⟩
  intro η₀ hη₀
  let L : ℝ := max (η₀ + 1) (Real.exp 1 + 1)
  let k : ℕ := Nat.floor L + 1
  let ξ : ℝ := min (ξ₀ / 2) (min (1 / (k : ℝ)) (min (1 / 4) (1 / D)))
  have hk_pos : 0 < k := by
    exact Nat.succ_pos _
  have hk_pos_real : 0 < (k : ℝ) := by
    exact_mod_cast hk_pos
  have hξ_pos : 0 < ξ := by
    unfold ξ
    refine lt_min ?_ ?_
    · nlinarith
    · refine lt_min ?_ ?_
      · exact one_div_pos.mpr hk_pos_real
      · refine lt_min ?_ ?_
        · norm_num
        · exact one_div_pos.mpr hD_pos
  have hξ_le_half : ξ ≤ ξ₀ / 2 := by
    unfold ξ
    exact min_le_left _ _
  have hξ_lt_ξ₀ : ξ < ξ₀ := by
    nlinarith [hξ_le_half, hξ₀_pos]
  have hξ_le_invk : ξ ≤ 1 / (k : ℝ) := by
    unfold ξ
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hξ_le_quarter : ξ ≤ 1 / 4 := by
    unfold ξ
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hξ_le_invD : ξ ≤ 1 / D := by
    unfold ξ
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hξ_le_one : ξ ≤ 1 := by
    nlinarith [hξ_le_quarter]
  have hL_nonneg : 0 ≤ L := by
    unfold L
    positivity
  let phaseTol : ℝ := ξ / (8 * Real.exp 1)
  have hphaseTol_pos : 0 < phaseTol := by
    unfold phaseTol
    positivity
  let S : Finset ℂ := positiveImZerosBelow (1 / ξ)
  obtain ⟨t, ht_gt_L, M, hM_pos, hM_upper, ht_bound, hphase⟩ :=
    bounded_simultaneous_near_period_finset S (ε := phaseTol) (L := L) hphaseTol_pos hL_nonneg
  let η : ℝ := t - ξ
  have hη_gt_η₀ : η₀ < η := by
    have hη₀1_le_L : η₀ + 1 ≤ L := le_max_left _ _
    have hη₀1_lt_t : η₀ + 1 < t := lt_of_le_of_lt hη₀1_le_L ht_gt_L
    unfold η
    linarith
  have hdiag_here : A * Real.log (1 / ξ) ≤ abelWeightedZeroSum ξ ξ :=
    hdiag ξ hξ_pos hξ_lt_ξ₀
  have htransport :
      |abelWeightedZeroSum ξ η - abelWeightedZeroSum ξ (-ξ)|
        ≤ phaseTol * (Nmult (1 / ξ) : ℝ) := by
    simpa [η, phaseTol, S] using
      (abelWeightedZeroSum_transport_base_abs_le
        (ξ := ξ) (η₀ := -ξ) (t := t) (ε := phaseTol) hξ_pos hphase)
  have hNmult_diag :
      (Nmult (1 / ξ) : ℝ) ≤ (2 * Real.exp 1 / ξ) * abelWeightedZeroSum ξ ξ :=
    Nmult_le_diagonal_sum_scale hξ_pos
  have hphase_scale :
      phaseTol * (Nmult (1 / ξ) : ℝ) ≤ (1 / 4 : ℝ) * abelWeightedZeroSum ξ ξ := by
    calc
      phaseTol * (Nmult (1 / ξ) : ℝ)
          ≤ phaseTol * ((2 * Real.exp 1 / ξ) * abelWeightedZeroSum ξ ξ) := by
              exact mul_le_mul_of_nonneg_left hNmult_diag (by positivity)
      _ = (1 / 4 : ℝ) * abelWeightedZeroSum ξ ξ := by
            unfold phaseTol
            field_simp [hξ_pos.ne', Real.exp_ne_zero]
            ring
  have hsum_upper :
      abelWeightedZeroSum ξ η ≤ -(3 / 4 : ℝ) * abelWeightedZeroSum ξ ξ := by
    have htransport' := abs_le.mp htransport
    have h1 :
        abelWeightedZeroSum ξ η
          ≤ abelWeightedZeroSum ξ (-ξ) + phaseTol * (Nmult (1 / ξ) : ℝ) := by
      linarith [htransport'.2]
    have h2 :
        abelWeightedZeroSum ξ (-ξ) + phaseTol * (Nmult (1 / ξ) : ℝ)
          ≤ -(3 / 4 : ℝ) * abelWeightedZeroSum ξ ξ := by
      rw [abelWeightedZeroSum_neg_diag]
      nlinarith [hphase_scale]
    exact h1.trans h2
  have hsum_main :
      abelWeightedZeroSum ξ η ≤ -(A / 2) * Real.log (1 / ξ) := by
    have hone : 1 ≤ 1 / ξ := by
      rw [one_le_div hξ_pos]
      exact hξ_le_one
    have hlog_nonneg : 0 ≤ Real.log (1 / ξ) := Real.log_nonneg hone
    have h34A :
        abelWeightedZeroSum ξ η ≤ -(3 / 4 : ℝ) * (A * Real.log (1 / ξ)) := by
      have hdiag_scaled :
          -(3 / 4 : ℝ) * abelWeightedZeroSum ξ ξ
            ≤ -(3 / 4 : ℝ) * (A * Real.log (1 / ξ)) := by
        nlinarith [hdiag_here]
      exact hsum_upper.trans hdiag_scaled
    have hhalf_ge :
        -(3 / 4 : ℝ) * (A * Real.log (1 / ξ))
          ≤ -(A / 2) * Real.log (1 / ξ) := by
      nlinarith [hA_pos, hlog_nonneg]
    exact h34A.trans hhalf_ge
  have hk_le_invξ : (k : ℝ) ≤ 1 / ξ := by
    have hkξ_le : ξ * (k : ℝ) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right hξ_le_invk hk_pos_real.le
      simpa [hk_pos_real.ne'] using hmul
    rw [le_div_iff₀ hξ_pos]
    nlinarith [hkξ_le]
  have hM_le_B0 : (M : ℝ) ≤ B0 / ξ ^ 2 := by
    calc
      (M : ℝ) ≤ (4 * Real.pi * ((Nat.floor L + 1 : ℕ) : ℝ)) / phaseTol + 1 := hM_upper
      _ = 32 * Real.pi * Real.exp 1 * ((k : ℝ) / ξ) + 1 := by
            unfold phaseTol k
            field_simp [hξ_pos.ne', Real.exp_ne_zero]
            ring
      _ ≤ 32 * Real.pi * Real.exp 1 * ((1 / ξ) / ξ) + 1 := by
            gcongr
      _ = 32 * Real.pi * Real.exp 1 / ξ ^ 2 + 1 := by
            field_simp [hξ_pos.ne']
      _ ≤ B0 / ξ ^ 2 := by
            have hξsq_pos : 0 < ξ ^ 2 := by positivity
            have hone : (1 : ℝ) ≤ 2 / ξ ^ 2 := by
              rw [le_div_iff₀ hξsq_pos]
              nlinarith [hξ_le_one, hξ_pos]
            calc
              32 * Real.pi * Real.exp 1 / ξ ^ 2 + 1
                  ≤ 32 * Real.pi * Real.exp 1 / ξ ^ 2 + 2 / ξ ^ 2 := by
                    gcongr
              _ = B0 / ξ ^ 2 := by
                    unfold B0
                    field_simp [hξ_pos.ne']
  have hξ_inv_ge_four : 4 ≤ 1 / ξ := by
    rw [le_div_iff₀ hξ_pos]
    nlinarith [hξ_le_quarter]
  have hlog_inv_le_inv : Real.log (1 / ξ) ≤ 1 / ξ := by
    have hξinv_pos : 0 < 1 / ξ := one_div_pos.mpr hξ_pos
    have hlog := Real.log_le_sub_one_of_pos hξinv_pos
    have hone : 1 ≤ 1 / ξ := by
      rw [one_le_div hξ_pos]
      exact hξ_le_one
    linarith
  have hcard_le : (S.card : ℝ) ≤ C0 / ξ ^ 2 := by
    have hone : 1 ≤ 1 / ξ := by
      rw [one_le_div hξ_pos]
      exact hξ_le_one
    have hlog_nonneg : 0 ≤ Real.log (1 / ξ) := Real.log_nonneg hone
    have hNbase : (N (1 / ξ) : ℝ) ≤ C * (1 / ξ) * Real.log (1 / ξ) := hC hξ_inv_ge_four
    have hNle : (N (1 / ξ) : ℝ) ≤ C0 * (1 / ξ) * Real.log (1 / ξ) := by
      refine hNbase.trans ?_
      gcongr
      exact le_max_left _ _
    calc
      (S.card : ℝ) = N (1 / ξ) := by
        simp [S, card_positiveImZerosBelow]
      _ ≤ C0 * (1 / ξ) * Real.log (1 / ξ) := hNle
      _ ≤ C0 * (1 / ξ) * (1 / ξ) := by
            gcongr
      _ = C0 / ξ ^ 2 := by
            field_simp [hξ_pos.ne']
  let U : ℝ := Real.log 2 + Real.log (k : ℝ) + (S.card : ℝ) * Real.log (M : ℝ)
  have hη_gt_exp1 : Real.exp 1 < η := by
    have hexp1_1_le_L : Real.exp 1 + 1 ≤ L := le_max_right _ _
    have hexp1_1_lt_t : Real.exp 1 + 1 < t := lt_of_le_of_lt hexp1_1_le_L ht_gt_L
    unfold η
    linarith
  have hη_gt_one : 1 < η := by
    have : 1 < Real.exp 1 := by simpa using Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hlogη_pos : 0 < Real.log η := Real.log_pos hη_gt_one
  have hk_ge_one : 1 ≤ (k : ℝ) := by
    exact_mod_cast hk_pos
  have hM_ge_one : 1 ≤ (M : ℝ) := by
    exact_mod_cast hM_pos
  have hM_pos_real : 0 < (M : ℝ) := by
    exact_mod_cast hM_pos
  have hMpow_ge_one : 1 ≤ (M : ℝ) ^ S.card := by
    exact one_le_pow₀ hM_ge_one
  have hkM_ge_one : 1 ≤ (k : ℝ) * (M : ℝ) ^ S.card := by
    nlinarith
  have hη_upper : η ≤ 2 * (k : ℝ) * (M : ℝ) ^ S.card := by
    unfold η
    calc
      t - ξ ≤ t := by linarith
      _ ≤ (k : ℝ) * (M : ℝ) ^ S.card := ht_bound
      _ ≤ 2 * (k : ℝ) * (M : ℝ) ^ S.card := by
            linarith
  have hlogη_le : Real.log η ≤ U := by
    calc
      Real.log η ≤ Real.log (2 * (k : ℝ) * (M : ℝ) ^ S.card) := by
        exact Real.log_le_log (by positivity) hη_upper
      _ = U := by
        unfold U
        rw [show 2 * (k : ℝ) * (M : ℝ) ^ S.card = 2 * ((k : ℝ) * (M : ℝ) ^ S.card) by ring]
        rw [Real.log_mul (by positivity : (2 : ℝ) ≠ 0)
              (by positivity : ((k : ℝ) * (M : ℝ) ^ S.card) ≠ 0)]
        rw [Real.log_mul (by positivity : (k : ℝ) ≠ 0)
              (by positivity : ((M : ℝ) ^ S.card) ≠ 0)]
        rw [Real.log_pow]
        ring
  have hU_pos : 0 < U := lt_of_lt_of_le hlogη_pos hlogη_le
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogk_le : Real.log (k : ℝ) ≤ (k : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hk_pos_real
    linarith
  have hlogM_le : Real.log (M : ℝ) ≤ (M : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hM_pos_real
    linarith
  have hone_le_invξ4 : (1 : ℝ) ≤ 1 / ξ ^ 4 := by
    have hξ4_le_one : ξ ^ 4 ≤ 1 := pow_le_one₀ hξ_pos.le hξ_le_one
    rw [one_le_div (by positivity : (0 : ℝ) < ξ ^ 4)]
    exact hξ4_le_one
  have hk_le_invξ4 : (k : ℝ) ≤ 1 / ξ ^ 4 := by
    have hξ3_le_one : ξ ^ 3 ≤ 1 := pow_le_one₀ hξ_pos.le hξ_le_one
    have hpow_den : ξ ^ 4 ≤ ξ := by
      calc
        ξ ^ 4 = ξ * ξ ^ 3 := by ring
        _ ≤ ξ * 1 := by
            gcongr
        _ = ξ := by ring
    have hpow : 1 / ξ ≤ 1 / ξ ^ 4 :=
      one_div_le_one_div_of_le (by positivity : 0 < ξ ^ 4) hpow_den
    exact hk_le_invξ.trans hpow
  have hcard_logM :
      (S.card : ℝ) * Real.log (M : ℝ) ≤ C0 * B0 / ξ ^ 4 := by
    have hcard_nonneg : 0 ≤ (S.card : ℝ) := by positivity
    have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
    calc
      (S.card : ℝ) * Real.log (M : ℝ) ≤ (S.card : ℝ) * (M : ℝ) := by
            exact mul_le_mul_of_nonneg_left hlogM_le hcard_nonneg
      _ ≤ (C0 / ξ ^ 2) * (B0 / ξ ^ 2) := by
            exact mul_le_mul hcard_le hM_le_B0 hM_nonneg (by positivity)
      _ = C0 * B0 / ξ ^ 4 := by
            field_simp [hξ_pos.ne']
  have hU_le : U ≤ D / ξ ^ 4 := by
    have h1 : Real.log 2 ≤ 1 / ξ ^ 4 := hlog2_le_one.trans hone_le_invξ4
    have h2 : Real.log (k : ℝ) ≤ 1 / ξ ^ 4 := hlogk_le.trans hk_le_invξ4
    have h12 : Real.log 2 + Real.log (k : ℝ) ≤ 2 / ξ ^ 4 := by
      calc
        Real.log 2 + Real.log (k : ℝ) ≤ 1 / ξ ^ 4 + 1 / ξ ^ 4 := add_le_add h1 h2
        _ = 2 / ξ ^ 4 := by ring
    calc
      U = (Real.log 2 + Real.log (k : ℝ)) + (S.card : ℝ) * Real.log (M : ℝ) := by
            unfold U
            ring
      _ ≤ 2 / ξ ^ 4 + C0 * B0 / ξ ^ 4 := by
            exact add_le_add h12 hcard_logM
      _ = D / ξ ^ 4 := by
            unfold D
            field_simp [hξ_pos.ne']
            ring
  have hloglogη_le :
      Real.log (Real.log η) ≤ 5 * Real.log (1 / ξ) := by
    have hlogU_le : Real.log U ≤ Real.log D + 4 * Real.log (1 / ξ) := by
      calc
        Real.log U ≤ Real.log (D / ξ ^ 4) := by
          exact Real.log_le_log hU_pos hU_le
        _ = Real.log D + 4 * Real.log (1 / ξ) := by
          rw [div_eq_mul_inv]
          have hpow_inv : (ξ ^ 4)⁻¹ = (1 / ξ) ^ 4 := by
            have : (ξ ^ 4)⁻¹ = (ξ⁻¹) ^ 4 := by simp [inv_pow]
            simpa [one_div] using this
          rw [hpow_inv]
          rw [Real.log_mul (by positivity : D ≠ 0) (by positivity : (1 / ξ : ℝ) ^ 4 ≠ 0)]
          rw [Real.log_pow]
          norm_num
    have hlogD_le : Real.log D ≤ Real.log (1 / ξ) := by
      have hDξ_le : ξ * D ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_right hξ_le_invD hD_pos.le
        simpa [hD_pos.ne', mul_comm, mul_left_comm, mul_assoc] using hmul
      have hD_le : D ≤ 1 / ξ := by
        rw [le_div_iff₀ hξ_pos]
        simpa [mul_comm] using hDξ_le
      exact Real.log_le_log hD_pos hD_le
    have hbase : Real.log (Real.log η) ≤ Real.log U := Real.log_le_log hlogη_pos hlogη_le
    calc
      Real.log (Real.log η) ≤ Real.log U := hbase
      _ ≤ Real.log D + 4 * Real.log (1 / ξ) := hlogU_le
      _ ≤ Real.log (1 / ξ) + 4 * Real.log (1 / ξ) := by gcongr
      _ = 5 * Real.log (1 / ξ) := by ring
  have hK_le :
      (A / 10) * Real.log (Real.log η) ≤ (A / 2) * Real.log (1 / ξ) := by
    calc
      (A / 10) * Real.log (Real.log η)
          ≤ (A / 10) * (5 * Real.log (1 / ξ)) := by
              exact mul_le_mul_of_nonneg_left hloglogη_le (by positivity)
      _ = (A / 2) * Real.log (1 / ξ) := by ring
  have hsumA :
      abelWeightedZeroSum ξ η ≤ -((A / 10) * Real.log (Real.log η)) := by
    have hsum_main' :
        abelWeightedZeroSum ξ η ≤ -((A / 2) * Real.log (1 / ξ)) := by
      simpa using hsum_main
    have hK_neg :
        -((A / 2) * Real.log (1 / ξ)) ≤ -((A / 10) * Real.log (Real.log η)) := by
      exact neg_le_neg hK_le
    exact hsum_main'.trans hK_neg
  refine ⟨ξ, hξ_pos, hξ_le_one, η, hη_gt_η₀, ?_⟩
  simpa using hsumA

instance [LittlewoodDiagonalEvalHyp] [ZeroOrdinateLowerBoundHyp] [ZeroCountingCrudeBoundHyp] :
    LittlewoodKeyLemmaMinusHyp where
  key_lemma_minus := littlewoodKeyLemmaMinus_of_diagonal

/-! ## Classical contradiction: Key Lemma + PL Bridge → one-sided bounds impossible

Under RH, the PL bridge converts a one-sided eventual `ψ - x` bound into a
one-sided Abel bound. The corresponding Key Lemma has the opposite sign and
forces a contradiction for small enough `δ`. -/

/-- Under RH, the one-sided upper bound `ψ(x)-x < δ·√x·lll(x)` for all large
`x` and all `δ > 0` is impossible, given the negative Key Lemma and the
corrected PL bridge. -/
theorem littlewood_classical_contradiction
    [LittlewoodKeyLemmaMinusHyp] [PhragmenLindelofAbelStripBoundHyp]
    (hRH : RiemannHypothesis') :
    ¬ (∀ δ > 0, ∀ᶠ x in atTop,
      chebyshevPsi x - x < δ * Real.sqrt x * Real.log (Real.log (Real.log x))) := by
  intro h_bounded
  obtain ⟨K, hK_pos, hKeyLemmaMinus⟩ := LittlewoodKeyLemmaMinusHyp.key_lemma_minus
  have hK4_pos : K / 4 > 0 := by positivity
  have h_psi_bound := h_bounded (K / 4) hK4_pos
  obtain ⟨C₁, hC₁_pos, hPLNeg_applied⟩ :=
    littlewoodPLBridgeNeg_bound hRH (K / 4) hK4_pos h_psi_bound
  have hη₀_exists : ∃ η₀ > 0, ∀ η, η₀ < η → η ≥ Real.exp (Real.exp 1) ∧
      K * Real.log (Real.log η) > 2 * (K / 4) * Real.log (Real.log η) + C₁ := by
    set L := 2 * C₁ / K + 2
    have hL_ge : 1 ≤ L := by
      have : 0 ≤ 2 * C₁ / K := div_nonneg (by linarith) hK_pos.le
      linarith
    refine ⟨Real.exp (Real.exp L), by positivity, fun η hη => ?_⟩
    have hη_pos : 0 < η := lt_trans (by positivity) hη
    constructor
    · exact le_of_lt (lt_of_le_of_lt
        (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hL_ge)) hη)
    · have hlog_η : Real.exp L < Real.log η := by
        rw [← Real.log_exp (Real.exp L)]
        exact Real.log_lt_log (by positivity) hη
      have hloglog : L < Real.log (Real.log η) := by
        rw [← Real.log_exp L]
        exact Real.log_lt_log (by positivity) hlog_η
      have hKL : K / 2 * L = C₁ + K := by
        simp only [L]
        field_simp
      have : K / 2 * Real.log (Real.log η) > C₁ + K := by
        calc
          K / 2 * Real.log (Real.log η) > K / 2 * L := by nlinarith
          _ = C₁ + K := hKL
      linarith
  obtain ⟨η₀, hη₀_pos, hη₀_prop⟩ := hη₀_exists
  obtain ⟨ξ, hξ_pos, hξ_le, η, hη_large, hsum_upper⟩ := hKeyLemmaMinus η₀ hη₀_pos
  obtain ⟨hη_ge_ee, hK_gt⟩ := hη₀_prop η hη_large
  have hsum_neg_lower := hPLNeg_applied ξ hξ_pos hξ_le η hη_ge_ee
  linarith

/-- The same for the Ω₋ direction: `-(ψ(x)-x)` cannot be one-sided bounded.
Uses the positive Key Lemma and the corrected upper-bound PL bridge. -/
theorem littlewood_classical_contradiction_minus
    [LittlewoodKeyLemmaHyp] [LittlewoodPLBridgeHyp]
    (hRH : RiemannHypothesis') :
    ¬ (∀ δ > 0, ∀ᶠ x in atTop,
      -(chebyshevPsi x - x) < δ * Real.sqrt x * Real.log (Real.log (Real.log x))) := by
  intro h_bounded
  obtain ⟨K, hK_pos, hKeyLemma⟩ := LittlewoodKeyLemmaHyp.key_lemma
  have hK4_pos : K / 4 > 0 := by positivity
  have h_psi_bound := h_bounded (K / 4) hK4_pos
  obtain ⟨C₁, hC₁_pos, hPL_applied⟩ :=
    LittlewoodPLBridgeHyp.bridge hRH (K / 4) hK4_pos h_psi_bound
  have hη₀_exists : ∃ η₀ > 0, ∀ η, η₀ < η → η ≥ Real.exp (Real.exp 1) ∧
      K * Real.log (Real.log η) > 2 * (K / 4) * Real.log (Real.log η) + C₁ := by
    set L := 2 * C₁ / K + 2
    have hL_ge : 1 ≤ L := by
      have : 0 ≤ 2 * C₁ / K := div_nonneg (by linarith) hK_pos.le
      linarith
    refine ⟨Real.exp (Real.exp L), by positivity, fun η hη => ?_⟩
    have hη_pos : 0 < η := lt_trans (by positivity) hη
    constructor
    · exact le_of_lt (lt_of_le_of_lt
        (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hL_ge)) hη)
    · have hlog_η : Real.exp L < Real.log η := by
        rw [← Real.log_exp (Real.exp L)]
        exact Real.log_lt_log (by positivity) hη
      have hloglog : L < Real.log (Real.log η) := by
        rw [← Real.log_exp L]
        exact Real.log_lt_log (by positivity) hlog_η
      have hKL : K / 2 * L = C₁ + K := by
        simp only [L]
        field_simp
      have : K / 2 * Real.log (Real.log η) > C₁ + K := by
        calc K / 2 * Real.log (Real.log η) > K / 2 * L := by nlinarith
          _ = C₁ + K := hKL
      linarith
  obtain ⟨η₀, hη₀_pos, hη₀_prop⟩ := hη₀_exists
  obtain ⟨ξ, hξ_pos, hξ_le, η, hη_large, hsum_lower⟩ := hKeyLemma η₀ hη₀_pos
  obtain ⟨hη_ge_ee, hK_gt⟩ := hη₀_prop η hη_large
  have hsum_upper := hPL_applied ξ hξ_pos hξ_le η hη_ge_ee
  linarith

end Littlewood.Classical
