import Littlewood.ZetaZeros.ZeroCountingMultiplicity
import Littlewood.ZetaZeros.RectArgumentPrinciple
import Littlewood.ZetaZeros.RvMContourEvaluation
import Littlewood.ZetaZeros.RvMRightEdge
import Littlewood.Aristotle.ZetaLogDerivPole
import Littlewood.Aristotle.RiemannXiEntire

set_option autoImplicit false

noncomputable section

namespace ZetaZeros

open scoped BigOperators Real ComplexConjugate
open Complex Filter

/-- The total excess multiplicity of nontrivial zeta zeros up to height `T`:
each zero contributes `m - 1`, where `m` is its multiplicity. -/
noncomputable def zeroCountingMultiplicityExcess (T : ℝ) : ℕ :=
  ∑ ρ ∈ (finite_zeros_le T).toFinset, ((analyticOrderAt riemannZeta ρ).toNat - 1)

/-- The total repeated-zero mass up to height `T`, measured as the sum of the
analytic orders of `ζ'` along the zeta-zero set. A zero of `ζ` of order `m`
contributes `m - 1` here. -/
noncomputable def zeroCountingRepeatedZeroMass (T : ℝ) : ℕ :=
  ∑ ρ ∈ (finite_zeros_le T).toFinset, (analyticOrderAt (deriv riemannZeta) ρ).toNat

/-- The zeta zeros up to height `T` where the derivative also vanishes. This is
the repeated-zero support set for `ζ`. -/
noncomputable def repeatedZetaZerosUpTo (T : ℝ) : Finset ℂ :=
  ((finite_zeros_le T).toFinset).filter fun ρ => deriv riemannZeta ρ = 0

theorem zeroCountingMultiplicityExcess_eq_sum (T : ℝ) :
    zeroCountingMultiplicityExcess T =
      ∑ ρ ∈ (finite_zeros_le T).toFinset, ((analyticOrderAt riemannZeta ρ).toNat - 1) := by
  rfl

theorem zeroCountingRepeatedZeroMass_eq_sum (T : ℝ) :
    zeroCountingRepeatedZeroMass T =
      ∑ ρ ∈ (finite_zeros_le T).toFinset, (analyticOrderAt (deriv riemannZeta) ρ).toNat := by
  rfl

theorem mem_repeatedZetaZerosUpTo {T : ℝ} {ρ : ℂ} :
    ρ ∈ repeatedZetaZerosUpTo T ↔ ρ ∈ zerosUpTo T ∧ deriv riemannZeta ρ = 0 := by
  simp [repeatedZetaZerosUpTo, zerosUpTo]

private theorem analyticOrderAt_toNat_pos_of_mem_zerosUpTo {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zerosUpTo T) :
    0 < (analyticOrderAt riemannZeta ρ).toNat := by
  have hρ' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hρ
  rcases mem_zetaNontrivialZerosPos.mp hρ'.1 with ⟨hzeta, _⟩
  rcases mem_zetaNontrivialZeros.mp hzeta with ⟨hzero, _, hre_lt⟩
  have hρ_ne_one : ρ ≠ 1 := by
    intro h1
    rw [h1] at hre_lt
    norm_num at hre_lt
  rcases Aristotle.ZetaLogDerivInfra.zeta_analytic_order_finite_pos ρ hzero hρ_ne_one with
    ⟨n, hn, horder⟩
  simpa [horder] using hn

private theorem zeroCountingFunction_eq_finset_card_local (T : ℝ) :
    N T = (finite_zeros_le T).toFinset.card := by
  rw [zeroCountingFunction_eq_ncard]
  simpa [zerosUpTo] using (Set.ncard_eq_toFinset_card (zerosUpTo T) (finite_zeros_le T))

private theorem analyticOrderAt_deriv_toNat_eq_pred_of_mem_zerosUpTo {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zerosUpTo T) :
    (analyticOrderAt (deriv riemannZeta) ρ).toNat =
      (analyticOrderAt riemannZeta ρ).toNat - 1 := by
  have hρ' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hρ
  rcases mem_zetaNontrivialZerosPos.mp hρ'.1 with ⟨hzeta, _⟩
  rcases mem_zetaNontrivialZeros.mp hzeta with ⟨hzero, _, hre_lt⟩
  have hρ_ne_one : ρ ≠ 1 := by
    intro h1
    rw [h1] at hre_lt
    norm_num at hre_lt
  have h_anal := Aristotle.ZetaLogDerivPole.zeta_analyticAt ρ hρ_ne_one
  have h_ord : analyticOrderAt (deriv riemannZeta) ρ + 1 = analyticOrderAt riemannZeta ρ := by
    have h := h_anal.analyticOrderAt_deriv_add_one
    have h_sub_eq : (riemannZeta · - riemannZeta ρ) = riemannZeta := by
      ext z
      simp [hzero]
    rw [h_sub_eq] at h
    simpa using h
  have h_ne_top : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    Aristotle.ZetaLogDerivPole.zeta_analyticOrder_ne_top ρ hρ_ne_one
  have h_deriv_ne_top : analyticOrderAt (deriv riemannZeta) ρ ≠ ⊤ := by
    intro h_top
    rw [h_top] at h_ord
    exact h_ne_top h_ord.symm
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_ne_top
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h_deriv_ne_top
  rw [← hn, ← hm] at h_ord
  have h_ord_nat : m + 1 = n := by
    simpa using congrArg ENat.toNat h_ord
  have hm_eq : m = n - 1 := by
    omega
  rw [← hm, ← hn]
  exact hm_eq

private theorem analyticOrderAt_deriv_toNat_eq_pred_of_analytic_zero
    {f : ℂ → ℂ} {ρ : ℂ} (h_analytic : AnalyticAt ℂ f ρ) (hzero : f ρ = 0)
    (h_ne_top : analyticOrderAt f ρ ≠ ⊤) :
    (analyticOrderAt (deriv f) ρ).toNat = (analyticOrderAt f ρ).toNat - 1 := by
  have h_ord : analyticOrderAt (deriv f) ρ + 1 = analyticOrderAt f ρ := by
    have h := h_analytic.analyticOrderAt_deriv_add_one
    have h_sub_eq : (f · - f ρ) = f := by
      ext z
      simp [hzero]
    rw [h_sub_eq] at h
    simpa using h
  have h_deriv_ne_top : analyticOrderAt (deriv f) ρ ≠ ⊤ := by
    intro h_top
    rw [h_top] at h_ord
    exact h_ne_top h_ord.symm
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_ne_top
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h_deriv_ne_top
  rw [← hn, ← hm] at h_ord
  have h_ord_nat : m + 1 = n := by
    simpa using congrArg ENat.toNat h_ord
  have hm_eq : m = n - 1 := by
    omega
  rw [← hm, ← hn]
  exact hm_eq

private theorem analyticOrderAt_deriv_toNat_eq_zero_of_deriv_ne_zero_of_mem_zerosUpTo
    {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ zerosUpTo T) (hderiv : deriv riemannZeta ρ ≠ 0) :
    (analyticOrderAt (deriv riemannZeta) ρ).toNat = 0 := by
  have hρ' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hρ
  rcases mem_zetaNontrivialZerosPos.mp hρ'.1 with ⟨hzeta, _⟩
  rcases mem_zetaNontrivialZeros.mp hzeta with ⟨_, _, hre_lt⟩
  have hρ_ne_one : ρ ≠ 1 := by
    intro h1
    rw [h1] at hre_lt
    norm_num at hre_lt
  have h_anal : AnalyticAt ℂ (deriv riemannZeta) ρ :=
    (Aristotle.ZetaLogDerivPole.zeta_analyticAt ρ hρ_ne_one).deriv
  have hzero : analyticOrderAt (deriv riemannZeta) ρ = 0 :=
    h_anal.analyticOrderAt_eq_zero.mpr hderiv
  simpa [hzero]

private theorem RiemannXiAlt_zero_of_mem_zerosUpTo {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zerosUpTo T) :
    RiemannXiAlt ρ = 0 := by
  have hρ' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hρ
  rcases mem_zetaNontrivialZerosPos.mp hρ'.1 with ⟨hzeta, _⟩
  rcases mem_zetaNontrivialZeros.mp hzeta with ⟨hzero, hre_pos, hre_lt⟩
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hre_pos
    simp at hre_pos
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at hre_lt
    norm_num at hre_lt
  rw [RiemannXiAlt_eq_formula hρ0 hρ1,
    RvMRightEdge.completedZeta_eq_GammaR_mul_zeta ρ hρ0
      (Complex.Gammaℝ_ne_zero_of_re_pos hre_pos)]
  simp [hzero]

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
  let g : ℂ → ℂ := fun s => ((1 / 2 : ℂ) * s * (s - 1) * Complex.Gammaℝ s)
  have hGamma_analytic : AnalyticAt ℂ Complex.Gammaℝ ρ := by
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
  have hcongr : RiemannXiAlt =ᶠ[nhds ρ] fun s => g s * riemannZeta s := by
    filter_upwards [isOpen_ne.mem_nhds hρ0, isOpen_ne.mem_nhds hρ1,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρre_pos] with s hs0 hs1 hsre
    rw [RiemannXiAlt_eq_formula hs0 hs1,
      RvMRightEdge.completedZeta_eq_GammaR_mul_zeta s hs0 (Complex.Gammaℝ_ne_zero_of_re_pos hsre)]
    show (1 / 2 : ℂ) * s * (s - 1) * (Complex.Gammaℝ s * riemannZeta s) =
        (((1 / 2 : ℂ) * s * (s - 1) * Complex.Gammaℝ s) * riemannZeta s)
    ring_nf
  have hg_nonzero : g ρ ≠ 0 := by
    unfold g
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) hρ0)
        (sub_ne_zero.mpr hρ1))
      (Complex.Gammaℝ_ne_zero_of_re_pos hρre_pos)
  have hg_order : analyticOrderAt g ρ = 0 :=
    hg_analytic.analyticOrderAt_eq_zero.2 hg_nonzero
  calc
    analyticOrderAt RiemannXiAlt ρ
        = analyticOrderAt (fun s => g s * riemannZeta s) ρ := analyticOrderAt_congr hcongr
    _ = analyticOrderAt g ρ + analyticOrderAt riemannZeta ρ := by
      simpa using analyticOrderAt_mul hg_analytic hzeta_analytic
    _ = analyticOrderAt riemannZeta ρ := by rw [hg_order, zero_add]

private theorem analyticOrderAt_deriv_RiemannXiAlt_toNat_eq_riemannZeta_of_mem_zerosUpTo
    {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ zerosUpTo T) :
    (analyticOrderAt (deriv RiemannXiAlt) ρ).toNat =
      (analyticOrderAt (deriv riemannZeta) ρ).toNat := by
  have hρ' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hρ
  rcases mem_zetaNontrivialZerosPos.mp hρ'.1 with ⟨hzeta, _⟩
  rcases mem_zetaNontrivialZeros.mp hzeta with ⟨_, _, hre_lt⟩
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at hre_lt
    norm_num at hre_lt
  have hxi_ne_top : analyticOrderAt RiemannXiAlt ρ ≠ ⊤ := by
    rw [analyticOrderAt_RiemannXiAlt_eq_riemannZeta_of_mem_zerosUpTo hρ]
    exact Aristotle.ZetaLogDerivPole.zeta_analyticOrder_ne_top ρ hρ1
  rw [analyticOrderAt_deriv_toNat_eq_pred_of_analytic_zero
      (h_analytic := RiemannXiAlt_entire.analyticAt ρ)
      (hzero := RiemannXiAlt_zero_of_mem_zerosUpTo hρ)
      (h_ne_top := hxi_ne_top),
    analyticOrderAt_deriv_toNat_eq_pred_of_mem_zerosUpTo hρ,
    analyticOrderAt_RiemannXiAlt_eq_riemannZeta_of_mem_zerosUpTo hρ]

private theorem RiemannXiAlt_zero : RiemannXiAlt 0 = (1 / 2 : ℂ) := by
  unfold RiemannXiAlt
  norm_num

private theorem RiemannXiAlt_two : RiemannXiAlt 2 = (Real.pi / 6 : ℂ) := by
  rw [RiemannXiAlt_eq_formula (by norm_num) (by norm_num)]
  have hG : Complex.Gammaℝ (2 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  rw [RvMRightEdge.completedZeta_eq_GammaR_mul_zeta (2 : ℂ) (by norm_num) hG]
  simp [Complex.Gammaℝ_def, riemannZeta_two, Complex.Gamma_one]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_pos.ne'
  field_simp [hpi]
  norm_num
  simpa [Complex.cpow_neg_one, hpi] using inv_mul_cancel₀ hpi

private theorem exists_deriv_RiemannXiAlt_ne_zero : ∃ z : ℂ, deriv RiemannXiAlt z ≠ 0 := by
  by_contra h
  have hzero : ∀ z : ℂ, deriv RiemannXiAlt z = 0 := by
    simpa using h
  have hconst := is_const_of_deriv_eq_zero RiemannXiAlt_entire hzero (0 : ℂ) 2
  have hneq_real : (1 / 2 : ℝ) ≠ Real.pi / 6 := by
    nlinarith [Real.pi_gt_three]
  have hneq : RiemannXiAlt 0 ≠ RiemannXiAlt 2 := by
    rw [RiemannXiAlt_zero, RiemannXiAlt_two]
    intro h
    apply hneq_real
    simpa using congrArg Complex.re h
  exact hneq hconst

/-- The multiplicity-counted zero count equals the distinct zero count plus the
total excess multiplicity. -/
theorem zeroCountingFunctionMult_eq_zeroCountingFunction_add_excess (T : ℝ) :
    Nmult T = N T + zeroCountingMultiplicityExcess T := by
  classical
  rw [zeroCountingFunctionMult_eq_sum, zeroCountingFunction_eq_finset_card_local,
    zeroCountingMultiplicityExcess_eq_sum, Finset.card_eq_sum_ones]
  calc
    ∑ ρ ∈ (finite_zeros_le T).toFinset, (analyticOrderAt riemannZeta ρ).toNat
      = ∑ ρ ∈ (finite_zeros_le T).toFinset,
          (((analyticOrderAt riemannZeta ρ).toNat - 1) + 1) := by
            refine Finset.sum_congr rfl ?_
            intro ρ hρ
            have hpos : 0 < (analyticOrderAt riemannZeta ρ).toNat :=
              analyticOrderAt_toNat_pos_of_mem_zerosUpTo (by simpa using hρ)
            simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hpos).symm
    _ = (∑ ρ ∈ (finite_zeros_le T).toFinset,
          ((analyticOrderAt riemannZeta ρ).toNat - 1)) +
        ∑ _ρ ∈ (finite_zeros_le T).toFinset, 1 := by
            rw [Finset.sum_add_distrib]
    _ = ∑ _ρ ∈ (finite_zeros_le T).toFinset, 1 +
        ∑ ρ ∈ (finite_zeros_le T).toFinset,
          ((analyticOrderAt riemannZeta ρ).toNat - 1) := by
            rw [Nat.add_comm]

/-- The natural-number gap `Nmult(T) - N(T)` is exactly the excess
multiplicity up to height `T`. -/
theorem zeroCountingFunctionMult_sub_zeroCountingFunction_eq_excess (T : ℝ) :
    Nmult T - N T = zeroCountingMultiplicityExcess T := by
  rw [zeroCountingFunctionMult_eq_zeroCountingFunction_add_excess]
  exact Nat.add_sub_cancel_left _ _

/-- The real absolute difference between the distinct and multiplicity-counted
zero counts is exactly the excess multiplicity. -/
theorem zeroCountingFunction_abs_sub_zeroCountingFunctionMult_eq_excess (T : ℝ) :
    |(N T : ℝ) - (Nmult T : ℝ)| = (zeroCountingMultiplicityExcess T : ℝ) := by
  have hle : N T ≤ Nmult T := by
    rw [zeroCountingFunctionMult_eq_zeroCountingFunction_add_excess]
    exact Nat.le_add_right _ _
  have hsub : (N T : ℝ) - (Nmult T : ℝ) ≤ 0 := by
    exact sub_nonpos.mpr (by exact_mod_cast hle)
  rw [abs_of_nonpos hsub]
  calc
    -((N T : ℝ) - (Nmult T : ℝ)) = (Nmult T : ℝ) - (N T : ℝ) := by ring
    _ = (zeroCountingMultiplicityExcess T : ℝ) := by
        rw [← Nat.cast_sub hle, zeroCountingFunctionMult_sub_zeroCountingFunction_eq_excess]

/-- The excess multiplicity is exactly the total analytic order of `ζ'` along
the zeta-zero set up to height `T`. -/
theorem zeroCountingMultiplicityExcess_eq_repeatedZeroMass (T : ℝ) :
    zeroCountingMultiplicityExcess T = zeroCountingRepeatedZeroMass T := by
  classical
  rw [zeroCountingMultiplicityExcess_eq_sum, zeroCountingRepeatedZeroMass_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  symm
  exact analyticOrderAt_deriv_toNat_eq_pred_of_mem_zerosUpTo (by simpa using hρ)

/-- The repeated-zero mass is supported exactly on the common-zero set of `ζ`
and `ζ'` up to height `T`. -/
theorem zeroCountingRepeatedZeroMass_eq_sum_repeatedZetaZerosUpTo (T : ℝ) :
    zeroCountingRepeatedZeroMass T =
      Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
        (analyticOrderAt (deriv riemannZeta) ρ).toNat) := by
  classical
  rw [zeroCountingRepeatedZeroMass_eq_sum, repeatedZetaZerosUpTo, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  by_cases hderiv : deriv riemannZeta ρ = 0
  · simp [hderiv]
  · have hρ' : ρ ∈ zerosUpTo T := by
      simpa [zerosUpTo] using hρ
    simp [hderiv,
      analyticOrderAt_deriv_toNat_eq_zero_of_deriv_ne_zero_of_mem_zerosUpTo hρ' hderiv]

/-- The distinct-versus-multiplicity compatibility bound is equivalent to an
`O(log T)` bound on the excess multiplicity. This isolates the remaining gap in
`RiemannVonMangoldtReal` to a purely multiplicity-theoretic estimate. -/
theorem distinct_mult_compatibility_bound_iff_excess_bound (T0 : ℝ) :
    (∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      |(N T : ℝ) - (Nmult T : ℝ)| ≤ C * Real.log T) ↔
    (∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      (zeroCountingMultiplicityExcess T : ℝ) ≤ C * Real.log T) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro T hT
    simpa [zeroCountingFunction_abs_sub_zeroCountingFunctionMult_eq_excess T] using hC T hT
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro T hT
    simpa [zeroCountingFunction_abs_sub_zeroCountingFunctionMult_eq_excess T] using hC T hT

/-- Equivalent form of the compatibility problem: bound the total repeated-zero
mass, i.e. the total analytic order of `ζ'` along the zeta-zero set. -/
theorem distinct_mult_compatibility_bound_iff_repeatedZeroMass_bound (T0 : ℝ) :
    (∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      |(N T : ℝ) - (Nmult T : ℝ)| ≤ C * Real.log T) ↔
    (∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      (zeroCountingRepeatedZeroMass T : ℝ) ≤ C * Real.log T) := by
  constructor
  · rintro ⟨C, hC⟩
    have hbase :=
      (distinct_mult_compatibility_bound_iff_excess_bound T0).mp ⟨C, hC⟩
    rcases hbase with ⟨C', hC'⟩
    refine ⟨C', ?_⟩
    intro T hT
    simpa [zeroCountingMultiplicityExcess_eq_repeatedZeroMass T] using hC' T hT
  · rintro ⟨C, hC⟩
    have hbase : ∃ C' : ℝ, ∀ T : ℝ, T0 ≤ T →
        (zeroCountingMultiplicityExcess T : ℝ) ≤ C' * Real.log T := by
      refine ⟨C, ?_⟩
      intro T hT
      simpa [zeroCountingMultiplicityExcess_eq_repeatedZeroMass T] using hC T hT
    exact (distinct_mult_compatibility_bound_iff_excess_bound T0).mpr hbase

/-- Equivalent form of the compatibility problem: bound the multiplicity-counted
common-zero mass of `ζ` and `ζ'` on `zerosUpTo T`. -/
theorem distinct_mult_compatibility_bound_iff_commonZeroMass_bound (T0 : ℝ) :
    (∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      |(N T : ℝ) - (Nmult T : ℝ)| ≤ C * Real.log T) ↔
    (∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T) := by
  constructor
  · rintro ⟨C, hC⟩
    have hbase :=
      (distinct_mult_compatibility_bound_iff_repeatedZeroMass_bound T0).mp ⟨C, hC⟩
    rcases hbase with ⟨C', hC'⟩
    refine ⟨C', ?_⟩
    intro T hT
    simpa [zeroCountingRepeatedZeroMass_eq_sum_repeatedZetaZerosUpTo T] using hC' T hT
  · rintro ⟨C, hC⟩
    have hbase : ∃ C' : ℝ, ∀ T : ℝ, T0 ≤ T →
        (zeroCountingRepeatedZeroMass T : ℝ) ≤ C' * Real.log T := by
      refine ⟨C, ?_⟩
      intro T hT
      simpa [zeroCountingRepeatedZeroMass_eq_sum_repeatedZetaZerosUpTo T] using hC T hT
    exact (distinct_mult_compatibility_bound_iff_repeatedZeroMass_bound T0).mpr hbase

/-- The repeated-zero mass is bounded by the multiplicity-counted zero count of
`RiemannXiAlt'` on any rectangle `(-1,2) × (c,T+1)` whose bottom edge lies
strictly below ordinate `1`. Under `ZeroOrdinateLowerBoundHyp`, every zeta zero
up to height `T` then lies in the interior. -/
private theorem zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_bottom
    {c : ℝ} (T : ℝ) (hc_top : c < T + 1)
    (hbottom : ∀ ρ ∈ zetaNontrivialZerosPos, c < ρ.im) :
    zeroCountingRepeatedZeroMass T ≤
      RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) := by
  classical
  let Z :=
    {z ∈ RectArgumentPrinciple.openRect (-1) 2 c (T + 1) | deriv RiemannXiAlt z = 0}
  have hdiff : Differentiable ℂ (deriv RiemannXiAlt) := by
    intro z
    exact (RiemannXiAlt_entire.analyticAt z).deriv.differentiableAt
  have hfinZ : Z.Finite := by
    simpa [Z] using
      (RectArgumentPrinciple.finite_zeros_in_openRect (f := deriv RiemannXiAlt)
        (a := -1) (b := 2) (c := c) (d := T + 1) (by norm_num) hc_top hdiff
        exists_deriv_RiemannXiAlt_ne_zero)
  have hleft :
      Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
        (analyticOrderAt (deriv riemannZeta) ρ).toNat) =
      Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
        (analyticOrderAt (deriv RiemannXiAlt) ρ).toNat) := by
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    exact (analyticOrderAt_deriv_RiemannXiAlt_toNat_eq_riemannZeta_of_mem_zerosUpTo
      (mem_repeatedZetaZerosUpTo.mp hρ).1).symm
  rw [zeroCountingRepeatedZeroMass_eq_sum_repeatedZetaZerosUpTo,
    RectArgumentPrinciple.zeroCountRectMult_eq_sum (f := deriv RiemannXiAlt)
      (a := -1) (b := 2) (c := c) (d := T + 1) hfinZ]
  rw [hleft]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro ρ hρ
    have hρmem : ρ ∈ zerosUpTo T ∧ deriv riemannZeta ρ = 0 :=
      mem_repeatedZetaZerosUpTo.mp hρ
    have hρcond : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
      simpa [zerosUpTo] using hρmem.1
    have hrect : ρ ∈ RectArgumentPrinciple.openRect (-1) 2 c (T + 1) := by
      rcases mem_zetaNontrivialZerosPos.mp hρcond.1 with ⟨hzeta, _⟩
      rcases mem_zetaNontrivialZeros.mp hzeta with ⟨_, hre_pos, hre_lt⟩
      have him_gt_c : c < ρ.im := hbottom ρ hρcond.1
      have him_lt : ρ.im < T + 1 := lt_of_le_of_lt hρcond.2 (by linarith)
      refine ⟨by linarith, by linarith, him_gt_c, him_lt⟩
    have htoNat_eq :
        (analyticOrderAt (deriv RiemannXiAlt) ρ).toNat =
          (analyticOrderAt (deriv riemannZeta) ρ).toNat :=
      analyticOrderAt_deriv_RiemannXiAlt_toNat_eq_riemannZeta_of_mem_zerosUpTo hρmem.1
    have hXiDeriv_zero : deriv RiemannXiAlt ρ = 0 := by
      have hζ_analytic : AnalyticAt ℂ (deriv riemannZeta) ρ := by
        have hρ' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
          simpa [zerosUpTo] using hρmem.1
        rcases mem_zetaNontrivialZerosPos.mp hρ'.1 with ⟨hzeta, _⟩
        rcases mem_zetaNontrivialZeros.mp hzeta with ⟨_, _, hre_lt⟩
        have hρ1 : ρ ≠ 1 := by
          intro h
          rw [h] at hre_lt
          norm_num at hre_lt
        exact (Aristotle.ZetaLogDerivPole.zeta_analyticAt ρ hρ1).deriv
      have hζ_order_ne_zero : analyticOrderAt (deriv riemannZeta) ρ ≠ 0 :=
        (hζ_analytic.analyticOrderAt_ne_zero).2 hρmem.2
      have hζ_order_pos : 0 < (analyticOrderAt (deriv riemannZeta) ρ).toNat := by
        have hζ_ne_top : analyticOrderAt (deriv riemannZeta) ρ ≠ ⊤ := by
          have hρ' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
            simpa [zerosUpTo] using hρmem.1
          rcases mem_zetaNontrivialZerosPos.mp hρ'.1 with ⟨hzeta, _⟩
          rcases mem_zetaNontrivialZeros.mp hzeta with ⟨_, _, hre_lt⟩
          have hρ1 : ρ ≠ 1 := by
            intro h
            rw [h] at hre_lt
            norm_num at hre_lt
          have h_ord_ne_top : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
            Aristotle.ZetaLogDerivPole.zeta_analyticOrder_ne_top ρ hρ1
          intro htop
          have h_ord : analyticOrderAt (deriv riemannZeta) ρ + 1 = analyticOrderAt riemannZeta ρ := by
            have hz := hρmem.1
            have hρ'' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
              simpa [zerosUpTo] using hz
            rcases mem_zetaNontrivialZerosPos.mp hρ''.1 with ⟨hzeta', _⟩
            rcases mem_zetaNontrivialZeros.mp hzeta' with ⟨hzero, _, _⟩
            have h := (Aristotle.ZetaLogDerivPole.zeta_analyticAt ρ hρ1).analyticOrderAt_deriv_add_one
            have h_sub_eq : (riemannZeta · - riemannZeta ρ) = riemannZeta := by
              ext z
              simp [hzero]
            rw [h_sub_eq] at h
            simpa using h
          rw [htop] at h_ord
          exact h_ord_ne_top h_ord.symm
        have hnat_ne_zero : (analyticOrderAt (deriv riemannZeta) ρ).toNat ≠ 0 := by
          intro hzero
          have hcast :
              (((analyticOrderAt (deriv riemannZeta) ρ).toNat : ℕ) : ℕ∞) =
                analyticOrderAt (deriv riemannZeta) ρ := ENat.coe_toNat hζ_ne_top
          apply hζ_order_ne_zero
          rw [← hcast, hzero]
          simp
        exact Nat.pos_of_ne_zero hnat_ne_zero
      have hXi_order_pos : 0 < (analyticOrderAt (deriv RiemannXiAlt) ρ).toNat := by
        rwa [htoNat_eq]
      have hXi_order_ne_zero : analyticOrderAt (deriv RiemannXiAlt) ρ ≠ 0 := by
        intro hzero
        rw [hzero] at hXi_order_pos
        simpa using hXi_order_pos
      exact apply_eq_zero_of_analyticOrderAt_ne_zero hXi_order_ne_zero
    have hmemZ : ρ ∈ hfinZ.toFinset := by
      simpa [Z, Set.Finite.mem_toFinset] using (show ρ ∈ Z from ⟨hrect, hXiDeriv_zero⟩)
    exact hmemZ
  · intro ρ hρZ hρnot
    exact Nat.zero_le _

/-- The repeated-zero mass is bounded by the multiplicity-counted zero count of
`RiemannXiAlt'` on any rectangle `(-1,2) × (c,T+1)` whose bottom edge lies
strictly below ordinate `1`. Under `ZeroOrdinateLowerBoundHyp`, every zeta zero
up to height `T` then lies in the interior. -/
theorem zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt
    [ZeroOrdinateLowerBoundHyp] {c : ℝ} (hc_lt : c < 1) (T : ℝ) :
    0 ≤ T →
    zeroCountingRepeatedZeroMass T ≤
      RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) := by
  intro hT
  refine zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_bottom
    (c := c) T ?_ ?_
  · linarith [hc_lt, hT]
  · intro ρ hρ
    exact lt_trans hc_lt (zero_ord_lower_bound ρ hρ)

/-- Unconditional negative-bottom variant: because every `ρ ∈ zerosUpTo T` has
positive imaginary part, any rectangle `(-1,2) × (c,T+1)` with `c < 0` already
captures the entire repeated-zero support set up to height `T`. -/
theorem zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_nonpos_bottom
    {c : ℝ} (hc_le : c ≤ 0) (T : ℝ) :
    0 ≤ T →
    zeroCountingRepeatedZeroMass T ≤
      RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) := by
  intro hT
  refine zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_bottom
    (c := c) T ?_ ?_
  · linarith
  · intro ρ hρ
    exact lt_of_le_of_lt hc_le (mem_zetaNontrivialZerosPos.mp hρ).2

/-- Unconditional negative-bottom variant: because every `ρ ∈ zerosUpTo T` has
positive imaginary part, any rectangle `(-1,2) × (c,T+1)` with `c < 0` already
captures the entire repeated-zero support set up to height `T`. -/
theorem zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_neg_bottom
    {c : ℝ} (hc_lt : c < 0) (T : ℝ) :
    0 ≤ T →
    zeroCountingRepeatedZeroMass T ≤
      RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) := by
  exact zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_nonpos_bottom
    hc_lt.le T

/-- Bottom-zero specialization of the unconditional repeated-zero-mass bridge. -/
theorem zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_at_bottom_zero
    (T : ℝ) :
    0 ≤ T →
    zeroCountingRepeatedZeroMass T ≤
      RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 0 (T + 1) := by
  exact zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_nonpos_bottom
    (c := 0) (by norm_num) T

private theorem differentiable_deriv_RiemannXiAlt : Differentiable ℂ (deriv RiemannXiAlt) := by
  intro z
  exact (RiemannXiAlt_entire.analyticAt z).deriv.differentiableAt

private theorem commonZeroMass_real_eq_zeroCountingRepeatedZeroMass (T : ℝ) :
    ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
        (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ) =
      (zeroCountingRepeatedZeroMass T : ℝ) := by
  exact_mod_cast (zeroCountingRepeatedZeroMass_eq_sum_repeatedZetaZerosUpTo T).symm

/-- Pointwise argument-principle identity for `deriv RiemannXiAlt`: on a
zero-free rectangle boundary, the real part of the logarithmic rectangle
integral is exactly the multiplicity-counted rectangle zero count. -/
theorem xiDeriv_logIntegralRect_re_eq_zeroCountRectMult_of_boundary_nonvanishing
    {c T : ℝ} (hc_top : c < T + 1)
    (hbdy : ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 c (T + 1), deriv RiemannXiAlt z ≠ 0) :
    (RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 c (T + 1)).re =
      RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) := by
  have happ :
      RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 c (T + 1) =
        ↑(RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1)) := by
    exact RectArgumentPrinciple.argument_principle_rect_entire_mult (deriv RiemannXiAlt)
      (-1) 2 c (T + 1) (by norm_num) hc_top differentiable_deriv_RiemannXiAlt hbdy
  simpa using congrArg Complex.re happ

/-- Pointwise `ξ'` rectangle zero-count bound from boundary nonvanishing alone. -/
theorem xiDeriv_zeroCountRectMult_le_abs_logIntegralRect_re_of_boundary_nonvanishing
    {c T : ℝ} (hc_top : c < T + 1)
    (hbdy : ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 c (T + 1), deriv RiemannXiAlt z ≠ 0) :
    (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ) ≤
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 c (T + 1)).re| := by
  rw [xiDeriv_logIntegralRect_re_eq_zeroCountRectMult_of_boundary_nonvanishing hc_top hbdy]
  exact le_abs_self _

/-- Exact common-zero-mass domination by the multiplicity-counted zero count of
`RiemannXiAlt'` on a rectangle with nonpositive bottom edge. -/
theorem commonZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_nonpos_bottom
    {c : ℝ} (hc_le : c ≤ 0) (T : ℝ) :
    0 ≤ T →
    ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
        (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ) ≤
      RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) := by
  intro hT
  have hle_nat :=
    zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_nonpos_bottom
      hc_le T hT
  have hle : (zeroCountingRepeatedZeroMass T : ℝ) ≤
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ) := by
    exact_mod_cast hle_nat
  calc
    ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
        (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
      = (zeroCountingRepeatedZeroMass T : ℝ) :=
          commonZeroMass_real_eq_zeroCountingRepeatedZeroMass T
    _ ≤ (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ) := hle

/-- Bottom-zero specialization of the exact common-zero-mass domination theorem. -/
theorem commonZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_at_bottom_zero
    (T : ℝ) :
    0 ≤ T →
    ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
        (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ) ≤
      RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 0 (T + 1) := by
  exact commonZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_nonpos_bottom
    (c := 0) (by norm_num) T

/-- If `deriv RiemannXiAlt` has no zeros on the boundary of the rectangle
`(-1,2) × (c,T+1)` and its logarithmic rectangle integral has real part
`O(log T)`, then its multiplicity-counted zero count in that rectangle is also
`O(log T)`. Choosing `c < 1` avoids the forced symmetry zero at `1 / 2` on the
real axis. -/
theorem xiDeriv_zeroCountRectMult_bound_of_logIntegral_bound
    {c : ℝ} (hc_lt : c < 1) (T0 : ℝ) (hT0 : 0 ≤ T0)
    (hbdy : ∀ T : ℝ, T0 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 c (T + 1), deriv RiemannXiAlt z ≠ 0)
    (hlog : ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 c (T + 1)).re|
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ)
        ≤ C * Real.log T := by
  rcases hlog with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro T hT
  calc
    (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ)
      ≤ |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 c (T + 1)).re| :=
        xiDeriv_zeroCountRectMult_le_abs_logIntegralRect_re_of_boundary_nonvanishing
          (by linarith [hc_lt, hT0, hT]) (hbdy T hT)
    _ ≤ C * Real.log T := hC T hT

/-- Direct fixed-negative-bottom zero-count bridge in the exact `T ≥ 14` shape
used by the live RvM compatibility leaf: boundary nonvanishing plus an
`O(log T)` bound on the logarithmic rectangle integral of `RiemannXiAlt'`
imply the same `O(log T)` bound for its multiplicity-counted rectangle zero
count on `(-1,2) × (-1,T+1)`. -/
theorem xiDeriv_zeroCountRectMult_bound_at_neg_one_from14
    (hbdy : ∀ T : ℝ, 14 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt z ≠ 0)
    (hlog : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ)
          (T + 1)).re|
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1) : ℝ)
        ≤ C * Real.log T := by
  exact xiDeriv_zeroCountRectMult_bound_of_logIntegral_bound
    (c := (-1 : ℝ)) (by norm_num) 14 (by norm_num) hbdy hlog

/-- Fixed-bottom specialization of the `ξ'` argument-principle identity in the
exact `T ≥ 14` shape used downstream. -/
theorem xiDeriv_logIntegralRect_re_eq_zeroCountRectMult_at_neg_one_from14
    (hbdy : ∀ T : ℝ, 14 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt z ≠ 0) :
    ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1)).re =
        RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1) := by
  intro T hT
  exact xiDeriv_logIntegralRect_re_eq_zeroCountRectMult_of_boundary_nonvanishing
    (c := (-1 : ℝ)) (T := T) (by linarith) (hbdy T hT)

/-- Direct fixed-negative-bottom zero-count bridge in the exact `T ≥ 14` shape
used by the live RvM compatibility leaf, from a one-sided upper bound on the
real part of the logarithmic rectangle integral of `RiemannXiAlt'`. -/
theorem xiDeriv_zeroCountRectMult_bound_at_neg_one_from14_of_re_upper_bound
    (hbdy : ∀ T : ℝ, 14 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt z ≠ 0)
    (hupper : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ)
          (T + 1)).re
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1) : ℝ)
        ≤ C * Real.log T := by
  rcases hupper with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro T hT
  calc
    (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1) : ℝ)
      =
        (RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ)
          (T + 1)).re := by
            symm
            exact xiDeriv_logIntegralRect_re_eq_zeroCountRectMult_of_boundary_nonvanishing
              (c := (-1 : ℝ)) (T := T) (by linarith) (hbdy T hT)
    _ ≤ C * Real.log T := hC T hT

/-- Unconditional common-zero-mass bridge for a negative-bottom rectangle:
an `O(log T)` bound on the multiplicity-counted zero count of `RiemannXiAlt'`
in `(-1,2) × (c,T+1)` with `c < 0` yields the exact common-zero mass bound
needed by the distinct-versus-multiplicity compatibility wrapper. -/
theorem commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_of_nonpos_bottom
    {c : ℝ} (hc_le : c ≤ 0) (T0 : ℝ) (hT0 : 0 ≤ T0)
    (hbound : ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ)
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  rcases hbound with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro T hT
  calc
    ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
        (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
      ≤ (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ) :=
          commonZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt_of_nonpos_bottom
            hc_le T (le_trans hT0 hT)
    _ ≤ C * Real.log T := hC T hT

/-- Unconditional common-zero-mass bridge for a negative-bottom rectangle:
an `O(log T)` bound on the multiplicity-counted zero count of `RiemannXiAlt'`
in `(-1,2) × (c,T+1)` with `c < 0` yields the exact common-zero mass bound
needed by the distinct-versus-multiplicity compatibility wrapper. -/
theorem commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_of_neg_bottom
    {c : ℝ} (hc_lt : c < 0) (T0 : ℝ) (hT0 : 0 ≤ T0)
    (hbound : ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ)
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  exact commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_of_nonpos_bottom
    hc_lt.le T0 hT0 hbound

/-- Bottom-zero specialization of the unconditional common-zero-mass bridge from
an `RiemannXiAlt'` rectangle zero-count bound. -/
theorem commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_at_bottom_zero
    (T0 : ℝ) (hT0 : 0 ≤ T0)
    (hbound : ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 0 (T + 1) : ℝ)
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  exact commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_of_nonpos_bottom
    (c := 0) (by norm_num) T0 hT0 hbound

/-- Direct bottom-zero common-zero-mass bridge in the exact `T ≥ 14` shape used
by the live RvM compatibility leaf, from a multiplicity-counted
`RiemannXiAlt'` rectangle zero-count bound. -/
theorem commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_at_bottom_zero_from14
    (hbound : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 0 (T + 1) : ℝ)
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  exact commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_at_bottom_zero 14
    (by norm_num) hbound

/-- Direct fixed-negative-bottom common-zero-mass bridge in the exact `T ≥ 14`
shape used by the live RvM compatibility leaf, from a multiplicity-counted
`RiemannXiAlt'` rectangle zero-count bound on `(-1,2) × (-1,T+1)`. -/
theorem commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_at_neg_one_from14
    (hbound : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1) : ℝ)
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  exact commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_of_neg_bottom
    (c := (-1 : ℝ)) (by norm_num) 14 (by norm_num) hbound

/-- Minimal constructive derivative input behind the live RvM
common-zero-mass lane: some nonpositive-bottom rectangle for `RiemannXiAlt'`
has no boundary zeros and its logarithmic rectangle integral has real part
`O(log T)` in the exact `T ≥ 14` shape. -/
class XiDerivBoundaryLogIntegralBoundFrom14Hyp where
  c : ℝ
  hc_le : c ≤ 0
  hbdy :
    ∀ T : ℝ, 14 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 c (T + 1), deriv RiemannXiAlt z ≠ 0
  hlog :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 c (T + 1)).re|
        ≤ C * Real.log T

/-- The explicit boundary-nonvanishing plus logarithmic-integral input is
already enough to recover the exact `ξ'` rectangle zero-count bound consumed by
the live RvM compatibility lane. -/
theorem xiDerivZeroCountRectMult_bound_of_boundaryLogIntegralBoundFrom14Hyp
    [XiDerivBoundaryLogIntegralBoundFrom14Hyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2
          XiDerivBoundaryLogIntegralBoundFrom14Hyp.c (T + 1) : ℝ)
        ≤ C * Real.log T := by
  have hc_lt : XiDerivBoundaryLogIntegralBoundFrom14Hyp.c < 1 := by
    linarith [XiDerivBoundaryLogIntegralBoundFrom14Hyp.hc_le]
  exact xiDeriv_zeroCountRectMult_bound_of_logIntegral_bound
    (c := XiDerivBoundaryLogIntegralBoundFrom14Hyp.c)
    hc_lt
    14 (by norm_num)
    XiDerivBoundaryLogIntegralBoundFrom14Hyp.hbdy
    XiDerivBoundaryLogIntegralBoundFrom14Hyp.hlog

/-- Minimal explicit rectangle zero-count boundary for the remaining `ξ'` input
behind the live RvM common-zero-mass lane. This is now derivable from the more
primitive boundary/log-integral hypothesis above. -/
class XiDerivZeroCountRectMultBoundFrom14Hyp where
  c : ℝ
  hc_le : c ≤ 0
  bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ)
        ≤ C * Real.log T

instance [XiDerivBoundaryLogIntegralBoundFrom14Hyp] :
    XiDerivZeroCountRectMultBoundFrom14Hyp where
  c := XiDerivBoundaryLogIntegralBoundFrom14Hyp.c
  hc_le := XiDerivBoundaryLogIntegralBoundFrom14Hyp.hc_le
  bound := xiDerivZeroCountRectMult_bound_of_boundaryLogIntegralBoundFrom14Hyp

/-- The explicit `ξ'` rectangle zero-count hypothesis is exactly enough to
recover the common-zero-mass bound needed by the live RvM compatibility leaf. -/
theorem commonZeroMass_bound_of_xiDerivZeroCountRectMultBoundFrom14Hyp
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  simpa using
    commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_of_nonpos_bottom
      (c := XiDerivZeroCountRectMultBoundFrom14Hyp.c)
      XiDerivZeroCountRectMultBoundFrom14Hyp.hc_le
      14 (by norm_num)
      XiDerivZeroCountRectMultBoundFrom14Hyp.bound

/-- The same explicit `ξ'` rectangle zero-count hypothesis also closes the
distinct-versus-multiplicity compatibility wrapper in the exact `T ≥ 14`
shape used downstream. -/
theorem distinct_mult_compatibility_bound_of_xiDerivZeroCountRectMultBoundFrom14Hyp
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(N T : ℝ) - (Nmult T : ℝ)| ≤ C * Real.log T := by
  exact (distinct_mult_compatibility_bound_iff_commonZeroMass_bound 14).2
    commonZeroMass_bound_of_xiDerivZeroCountRectMultBoundFrom14Hyp

/-- Unconditional log-integral version of the exact common-zero-mass bridge:
for any rectangle `(-1,2) × (c,T+1)` with `c < 0`, boundary nonvanishing plus an
`O(log T)` bound on the real part of the logarithmic rectangle integral of
`RiemannXiAlt'` yields `O(log T)` control of the common-zero mass. -/
theorem commonZeroMass_bound_of_xiDeriv_logIntegral_bound_of_nonpos_bottom
    {c : ℝ} (hc_le : c ≤ 0) (T0 : ℝ) (hT0 : 0 ≤ T0)
    (hbdy : ∀ T : ℝ, T0 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 c (T + 1), deriv RiemannXiAlt z ≠ 0)
    (hlog : ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 c (T + 1)).re|
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  have hcount :=
    xiDeriv_zeroCountRectMult_bound_of_logIntegral_bound (c := c)
      (by linarith : c < 1) T0 hT0 hbdy hlog
  exact commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_of_nonpos_bottom
    hc_le T0 hT0 hcount

/-- Unconditional log-integral version of the exact common-zero-mass bridge:
for any rectangle `(-1,2) × (c,T+1)` with `c < 0`, boundary nonvanishing plus an
`O(log T)` bound on the real part of the logarithmic rectangle integral of
`RiemannXiAlt'` yields `O(log T)` control of the common-zero mass. -/
theorem commonZeroMass_bound_of_xiDeriv_logIntegral_bound_of_neg_bottom
    {c : ℝ} (hc_lt : c < 0) (T0 : ℝ) (hT0 : 0 ≤ T0)
    (hbdy : ∀ T : ℝ, T0 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 c (T + 1), deriv RiemannXiAlt z ≠ 0)
    (hlog : ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 c (T + 1)).re|
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  exact commonZeroMass_bound_of_xiDeriv_logIntegral_bound_of_nonpos_bottom
    hc_lt.le T0 hT0 hbdy hlog

/-- Bottom-zero specialization of the unconditional common-zero-mass bridge from
the `RiemannXiAlt'` logarithmic rectangle integral. -/
theorem commonZeroMass_bound_of_xiDeriv_logIntegral_bound_at_bottom_zero
    (T0 : ℝ) (hT0 : 0 ≤ T0)
    (hbdy : ∀ T : ℝ, T0 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 0 (T + 1), deriv RiemannXiAlt z ≠ 0)
    (hlog : ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 0 (T + 1)).re|
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  exact commonZeroMass_bound_of_xiDeriv_logIntegral_bound_of_nonpos_bottom
    (c := 0) (by norm_num) T0 hT0 hbdy hlog

/-- Direct bottom-zero common-zero-mass bridge in the exact `T ≥ 14` shape used
by the live RvM compatibility leaf, from a logarithmic rectangle-integral bound
for `RiemannXiAlt'`. -/
theorem commonZeroMass_bound_of_xiDeriv_logIntegral_bound_at_bottom_zero_from14
    (hbdy : ∀ T : ℝ, 14 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 0 (T + 1), deriv RiemannXiAlt z ≠ 0)
    (hlog : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 0 (T + 1)).re|
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  exact commonZeroMass_bound_of_xiDeriv_logIntegral_bound_at_bottom_zero 14
    (by norm_num) hbdy hlog

/-- Direct fixed-negative-bottom common-zero-mass bridge in the exact `T ≥ 14`
shape used by the live RvM compatibility leaf, from a logarithmic
rectangle-integral bound for `RiemannXiAlt'` on `(-1,2) × (-1,T+1)`. -/
theorem commonZeroMass_bound_of_xiDeriv_logIntegral_bound_at_neg_one_from14
    (hbdy : ∀ T : ℝ, 14 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt z ≠ 0)
    (hlog : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ)
          (T + 1)).re|
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  exact commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_at_neg_one_from14
    (xiDeriv_zeroCountRectMult_bound_at_neg_one_from14 hbdy hlog)

/-- Direct fixed-negative-bottom common-zero-mass bridge in the exact `T ≥ 14`
shape used by the live RvM compatibility leaf, from a one-sided upper bound on
the real part of the logarithmic rectangle integral of `RiemannXiAlt'` on
`(-1,2) × (-1,T+1)`. -/
theorem commonZeroMass_bound_of_xiDeriv_logIntegralRect_re_upper_bound_at_neg_one_from14
    (hbdy : ∀ T : ℝ, 14 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt z ≠ 0)
    (hupper : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ)
          (T + 1)).re
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      ((Finset.sum (repeatedZetaZerosUpTo T) (fun ρ =>
          (analyticOrderAt (deriv riemannZeta) ρ).toNat) : ℕ) : ℝ)
        ≤ C * Real.log T := by
  exact commonZeroMass_bound_of_xiDerivZeroCountRectMult_bound_at_neg_one_from14
    (xiDeriv_zeroCountRectMult_bound_at_neg_one_from14_of_re_upper_bound hbdy hupper)

/-- The normalized fixed bottom-edge contribution for the `ξ'` logarithmic
rectangle integral on `(-1,2) × (-1,T+1)`. -/
private def xiDerivNegOneBottomContribution : ℂ :=
  (1 / (2 * ↑Real.pi * I)) *
    (∫ x in (-1 : ℝ)..2,
      logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(-1 : ℝ) : ℂ) * I))

/-- The normalized contribution of the top, right, and left edges for the `ξ'`
logarithmic rectangle integral on `(-1,2) × (-1,T+1)`. -/
private def xiDerivNegOneUpperThreeContribution (T : ℝ) : ℂ :=
  (1 / (2 * ↑Real.pi * I)) *
    (-(∫ x in (-1 : ℝ)..2,
        logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)) +
      I * (∫ y in (-1 : ℝ)..(T + 1),
        logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) -
      I * (∫ y in (-1 : ℝ)..(T + 1),
        logDeriv (deriv RiemannXiAlt) (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I))))

/-- The normalized top-edge contribution for the fixed-bottom `ξ'`
logarithmic rectangle integral on `(-1,2) × (-1,T+1)`. -/
private def xiDerivNegOneTopContribution (T : ℝ) : ℂ :=
  (1 / (2 * ↑Real.pi * I)) *
    (-(∫ x in (-1 : ℝ)..2,
        logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)))

/-- The normalized right-plus-left vertical contribution for the fixed-bottom
`ξ'` logarithmic rectangle integral on `(-1,2) × (-1,T+1)`. -/
private def xiDerivNegOneSideContribution (T : ℝ) : ℂ :=
  (1 / (2 * ↑Real.pi * I)) *
    (I * (∫ y in (-1 : ℝ)..(T + 1),
        logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) -
      I * (∫ y in (-1 : ℝ)..(T + 1),
        logDeriv (deriv RiemannXiAlt) (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I))))

/-- The first derivative of `RiemannXiAlt` is continuous. -/
private theorem xiDeriv_continuous : Continuous (deriv RiemannXiAlt) := by
  simpa using
    ((RiemannXiAlt_entire.contDiff : ContDiff ℂ ⊤ RiemannXiAlt).continuous_deriv (by simp))

/-- The second derivative of `RiemannXiAlt` is continuous. -/
private theorem xiDerivDeriv_continuous : Continuous (deriv (deriv RiemannXiAlt)) := by
  have hcont : Continuous (iteratedDeriv 2 RiemannXiAlt) :=
    (RiemannXiAlt_entire.contDiff : ContDiff ℂ ⊤ RiemannXiAlt).continuous_iteratedDeriv 2
      (by simp)
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using hcont

/-- The functional equation differentiates to an odd symmetry for `RiemannXiAlt'`. -/
private theorem deriv_RiemannXiAlt_functional_eq (s : ℂ) :
    deriv RiemannXiAlt (1 - s) = -deriv RiemannXiAlt s := by
  have hiter_eq :
      iteratedDeriv 1 (fun z : ℂ => RiemannXiAlt (1 - z)) s = iteratedDeriv 1 RiemannXiAlt s :=
    Filter.EventuallyEq.iteratedDeriv_eq 1 <|
      Filter.Eventually.of_forall (fun z => RvMContour.riemannXiAlt_one_sub' z)
  have hcomp :
      iteratedDeriv 1 (fun z : ℂ => RiemannXiAlt (1 - z)) s =
        (-1 : ℂ) ^ 1 • iteratedDeriv 1 RiemannXiAlt (1 - s) := by
    simpa using congrArg (fun g : ℂ → ℂ => g s)
      (iteratedDeriv_comp_const_sub (n := 1) (f := RiemannXiAlt) (s := (1 : ℂ)))
  rw [iteratedDeriv_one] at hiter_eq hcomp
  have h : deriv RiemannXiAlt s = -deriv RiemannXiAlt (1 - s) := by
    calc
      deriv RiemannXiAlt s
          = deriv (fun z : ℂ => RiemannXiAlt (1 - z)) s := by
              simpa using hiter_eq.symm
      _ = -deriv RiemannXiAlt (1 - s) := by
            simpa using hcomp
  calc
    deriv RiemannXiAlt (1 - s) = -(-deriv RiemannXiAlt (1 - s)) := by ring
    _ = -deriv RiemannXiAlt s := by rw [← h]

/-- The second derivative of `RiemannXiAlt` is even under `s ↦ 1 - s`. -/
private theorem derivDeriv_RiemannXiAlt_functional_eq (s : ℂ) :
    deriv (deriv RiemannXiAlt) (1 - s) = deriv (deriv RiemannXiAlt) s := by
  have hiter_eq :
      deriv (deriv (fun z : ℂ => RiemannXiAlt (1 - z))) s = deriv (deriv RiemannXiAlt) s := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using
      (Filter.EventuallyEq.iteratedDeriv_eq 2 <|
        Filter.Eventually.of_forall (fun z => RvMContour.riemannXiAlt_one_sub' z))
  have hcomp :
      deriv (deriv (fun z : ℂ => RiemannXiAlt (1 - z))) s =
        deriv (deriv RiemannXiAlt) (1 - s) := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using
      (congrArg (fun g : ℂ → ℂ => g s)
        (iteratedDeriv_comp_const_sub (n := 2) (f := RiemannXiAlt) (s := (1 : ℂ))))
  exact hcomp.symm.trans hiter_eq

/-- The logarithmic derivative of `RiemannXiAlt'` has the same odd functional
equation as the completed-zeta lane. -/
private theorem xiDeriv_logDeriv_functional_eq (s : ℂ) :
    logDeriv (deriv RiemannXiAlt) (1 - s) = -logDeriv (deriv RiemannXiAlt) s := by
  rw [logDeriv_apply, logDeriv_apply, derivDeriv_RiemannXiAlt_functional_eq,
    deriv_RiemannXiAlt_functional_eq]
  simp [div_neg]

/-- Schwarz reflection for `RiemannXiAlt'`. -/
private theorem deriv_RiemannXiAlt_conj (s : ℂ) :
    deriv RiemannXiAlt (conj s) = conj (deriv RiemannXiAlt s) := by
  have h_eq :
      ∀ᶠ z in nhds (conj s), (conj ∘ RiemannXiAlt ∘ conj) z = RiemannXiAlt z :=
    Filter.Eventually.of_forall (fun z => by
      simpa [Function.comp_apply] using (RvMContour.riemannXiAlt_conj (conj z)).symm)
  have hd : DifferentiableAt ℂ RiemannXiAlt s := RiemannXiAlt_entire.differentiableAt
  have hcomp :
      deriv (conj ∘ RiemannXiAlt ∘ conj) (conj s) = conj (deriv RiemannXiAlt s) := by
    simpa [Function.comp_apply] using (hd.hasDerivAt.conj_conj).deriv
  have hderiv_eq :
      deriv (conj ∘ RiemannXiAlt ∘ conj) (conj s) = deriv RiemannXiAlt (conj s) :=
    Filter.EventuallyEq.deriv_eq h_eq
  exact hderiv_eq.symm.trans hcomp

/-- Schwarz reflection for the second derivative of `RiemannXiAlt`. -/
private theorem derivDeriv_RiemannXiAlt_conj (s : ℂ) :
    deriv (deriv RiemannXiAlt) (conj s) = conj (deriv (deriv RiemannXiAlt) s) := by
  have h_eq :
      ∀ᶠ z in nhds (conj s), (conj ∘ deriv RiemannXiAlt ∘ conj) z = deriv RiemannXiAlt z :=
    Filter.Eventually.of_forall (fun z => by
      simpa [Function.comp_apply] using (deriv_RiemannXiAlt_conj (conj z)).symm)
  have hd : DifferentiableAt ℂ (deriv RiemannXiAlt) s := by
    exact (RiemannXiAlt_entire.analyticAt s).deriv.differentiableAt
  have hcomp :
      deriv (conj ∘ deriv RiemannXiAlt ∘ conj) (conj s) =
        conj (deriv (deriv RiemannXiAlt) s) := by
    simpa [Function.comp_apply] using (hd.hasDerivAt.conj_conj).deriv
  have hderiv_eq :
      deriv (conj ∘ deriv RiemannXiAlt ∘ conj) (conj s) =
        deriv (deriv RiemannXiAlt) (conj s) :=
    Filter.EventuallyEq.deriv_eq h_eq
  exact hderiv_eq.symm.trans hcomp

/-- Schwarz reflection for the logarithmic derivative of `RiemannXiAlt'`. -/
private theorem xiDeriv_logDeriv_conj (s : ℂ) :
    logDeriv (deriv RiemannXiAlt) (conj s) = conj (logDeriv (deriv RiemannXiAlt) s) := by
  rw [logDeriv_apply, derivDeriv_RiemannXiAlt_conj, deriv_RiemannXiAlt_conj]
  symm
  exact map_div₀ (starRingEnd ℂ) (deriv (deriv RiemannXiAlt) s) (deriv RiemannXiAlt s)

/-- The left edge for `logDeriv (RiemannXiAlt')` is the reflected negative
conjugate of the right edge. -/
private theorem xiDeriv_logDeriv_left_right_edge (y : ℝ) :
    logDeriv (deriv RiemannXiAlt) (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)) =
      -conj (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) := by
  let z : ℂ := ((↑(2 : ℝ) : ℂ) - (↑y : ℂ) * I)
  have hone_sub_z : (1 : ℂ) - z = (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)) := by
    apply Complex.ext
    · simp [z]
      norm_num
    · simp [z]
  calc
    logDeriv (deriv RiemannXiAlt) (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I))
        = logDeriv (deriv RiemannXiAlt) (1 - z) := by
            rw [hone_sub_z]
    _ = -logDeriv (deriv RiemannXiAlt) z := xiDeriv_logDeriv_functional_eq z
    _ = -conj (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) := by
          have hzconj : z = conj ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) := by
            apply Complex.ext <;> simp [z]
          rw [hzconj]
          exact congrArg Neg.neg (xiDeriv_logDeriv_conj ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))

/-- The right edge is continuous as soon as `RiemannXiAlt'` has no zeros there. -/
private theorem xiDeriv_right_continuousOn (T : ℝ)
    (hright_nz : ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
      deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0) :
    ContinuousOn
      (fun y : ℝ => logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))
      (Set.Icc (-1 : ℝ) (T + 1)) := by
  have hnum : ContinuousOn
      (fun y : ℝ => deriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))
      (Set.Icc (-1 : ℝ) (T + 1)) :=
    (xiDerivDeriv_continuous.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
  have hden : ContinuousOn
      (fun y : ℝ => deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))
      (Set.Icc (-1 : ℝ) (T + 1)) :=
    (xiDeriv_continuous.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
  simpa [logDeriv_apply] using hnum.div hden hright_nz

/-- Hence the right-edge logarithmic derivative is interval-integrable on the
fixed-bottom contour. -/
private theorem xiDeriv_right_intervalIntegrable (T : ℝ) (hT : -1 ≤ T + 1)
    (hright_nz : ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
      deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0) :
    IntervalIntegrable
      (fun y : ℝ => logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))
      MeasureTheory.volume (-1) (T + 1) := by
  exact (xiDeriv_right_continuousOn T hright_nz).intervalIntegrable_of_Icc hT

/-- Under right-edge nonvanishing, the fixed-bottom side contribution is purely
real and determined by a single right-edge integral. -/
private theorem xiDerivNegOneSideContribution_eq_rightEdgeReal (T : ℝ) (hT : -1 ≤ T + 1)
    (hright_nz : ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
      deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0) :
    xiDerivNegOneSideContribution T =
      (((∫ y in (-1 : ℝ)..(T + 1),
          logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re : ℂ) /
        ↑Real.pi) := by
  set A : ℂ := ∫ y in (-1 : ℝ)..(T + 1),
      logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)
  have hright :
      IntervalIntegrable
        (fun y : ℝ => logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))
        MeasureTheory.volume (-1) (T + 1) :=
    xiDeriv_right_intervalIntegrable T hT hright_nz
  have hleft_eq :
      ∫ y in (-1 : ℝ)..(T + 1),
        logDeriv (deriv RiemannXiAlt) (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I)) =
      -conj A := by
    calc
      ∫ y in (-1 : ℝ)..(T + 1),
          logDeriv (deriv RiemannXiAlt) (((↑(-1 : ℝ) : ℂ) + (↑y : ℂ) * I))
          =
        ∫ y in (-1 : ℝ)..(T + 1),
          -conj (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with y
            intro _hy
            simpa using xiDeriv_logDeriv_left_right_edge y
      _ = -(∫ y in (-1 : ℝ)..(T + 1),
            conj (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))) := by
              rw [intervalIntegral.integral_neg]
      _ = -conj (∫ y in (-1 : ℝ)..(T + 1),
            logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) := by
              congr 1
              simpa using
                Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hright
      _ = -conj A := by
            rw [show A = ∫ y in (-1 : ℝ)..(T + 1),
              logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) from rfl]
  unfold xiDerivNegOneSideContribution
  rw [show (∫ y in (-1 : ℝ)..(T + 1),
        logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)) = A by simp [A],
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

/-- Real-part form of the fixed-bottom side contribution. -/
private theorem xiDerivNegOneSideContribution_re_eq_rightEdgeReal (T : ℝ) (hT : -1 ≤ T + 1)
    (hright_nz : ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
      deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0) :
    (xiDerivNegOneSideContribution T).re =
      (1 / Real.pi) *
        (∫ y in (-1 : ℝ)..(T + 1),
          logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re := by
  rw [xiDerivNegOneSideContribution_eq_rightEdgeReal T hT hright_nz]
  simp [div_eq_mul_inv, mul_comm]

/-- The fixed-bottom side leaf reduces to a one-sided bound for the real part
of the right-edge integral of `logDeriv (RiemannXiAlt')`. -/
private theorem xiDerivNegOneSideContribution_re_upper_bound_of_rightEdge_re_upper_bound
    (hright_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0)
    (hright_upper : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (1 / Real.pi) *
        (∫ y in (-1 : ℝ)..(T + 1),
          logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (xiDerivNegOneSideContribution T).re ≤ C * Real.log T := by
  rcases hright_upper with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro T hT
  rw [xiDerivNegOneSideContribution_re_eq_rightEdgeReal T (by linarith) (hright_nz T hT)]
  exact hC T hT

/-- The top edge for `logDeriv (RiemannXiAlt')` folds by the same
functional-equation-plus-conjugation symmetry as the completed-zeta lane. -/
private theorem xiDeriv_logDeriv_top_reflection (T x : ℝ) :
    logDeriv (deriv RiemannXiAlt) ((↑(1 - x) : ℂ) + (↑(T + 1) : ℂ) * I) =
      -conj (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)) := by
  let z : ℂ := ((↑x : ℂ) - (↑(T + 1) : ℂ) * I)
  have hone_sub_z : (1 : ℂ) - z = ((↑(1 - x) : ℂ) + (↑(T + 1) : ℂ) * I) := by
    apply Complex.ext <;> simp [z]
  calc
    logDeriv (deriv RiemannXiAlt) ((↑(1 - x) : ℂ) + (↑(T + 1) : ℂ) * I)
        = logDeriv (deriv RiemannXiAlt) (1 - z) := by
            rw [hone_sub_z]
    _ = -logDeriv (deriv RiemannXiAlt) z := xiDeriv_logDeriv_functional_eq z
    _ = -conj (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)) := by
          have hzconj : z = conj ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) := by
            apply Complex.ext <;> simp [z]
          rw [hzconj]
          exact congrArg Neg.neg
            (xiDeriv_logDeriv_conj ((↑x : ℂ) + (↑(T + 1) : ℂ) * I))

/-- The top edge is continuous as soon as `RiemannXiAlt'` has no zeros there. -/
private theorem xiDeriv_top_continuousOn (T : ℝ)
    (htop_nz : ∀ x ∈ Set.Icc (-1 : ℝ) 2,
      deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0) :
    ContinuousOn
      (fun x : ℝ => logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I))
      (Set.Icc (-1 : ℝ) 2) := by
  have hnum : ContinuousOn
      (fun x : ℝ => deriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I))
      (Set.Icc (-1 : ℝ) 2) :=
    (xiDerivDeriv_continuous.comp
      (continuous_ofReal.add (continuous_const.mul continuous_const))).continuousOn
  have hden : ContinuousOn
      (fun x : ℝ => deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I))
      (Set.Icc (-1 : ℝ) 2) :=
    (xiDeriv_continuous.comp
      (continuous_ofReal.add (continuous_const.mul continuous_const))).continuousOn
  simpa [logDeriv_apply] using hnum.div hden htop_nz

/-- Hence the top-edge logarithmic derivative is interval-integrable on the
fixed-bottom contour. -/
private theorem xiDeriv_top_intervalIntegrable (T : ℝ)
    (htop_nz : ∀ x ∈ Set.Icc (-1 : ℝ) 2,
      deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0) :
    IntervalIntegrable
      (fun x : ℝ => logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I))
      MeasureTheory.volume (-1) 2 := by
  exact (xiDeriv_top_continuousOn T htop_nz).intervalIntegrable_of_Icc (by norm_num)

/-- Functional equation plus conjugation fold the full fixed-bottom top edge
onto the half-top segment `[1/2, 2]`. -/
private theorem xiDerivNegOneTopContribution_re_eq_half_top_imIntegral (T : ℝ)
    (htop_nz : ∀ x ∈ Set.Icc (-1 : ℝ) 2,
      deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0) :
    (xiDerivNegOneTopContribution T).re =
      -(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im) := by
  let f : ℝ → ℂ := fun x =>
    logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)
  have hfull_cont : ContinuousOn f (Set.Icc (-1 : ℝ) 2) :=
    xiDeriv_top_continuousOn T htop_nz
  have hleft_cont : ContinuousOn f (Set.Icc (-1 : ℝ) (1 / 2 : ℝ)) := by
    refine hfull_cont.mono ?_
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hright_cont : ContinuousOn f (Set.Icc (1 / 2 : ℝ) 2) := by
    refine hfull_cont.mono ?_
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hleft_int : IntervalIntegrable f MeasureTheory.volume (-1) (1 / 2 : ℝ) :=
    hleft_cont.intervalIntegrable_of_Icc (by norm_num)
  have hright_int : IntervalIntegrable f MeasureTheory.volume (1 / 2) 2 :=
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
            simpa [f] using xiDeriv_logDeriv_top_reflection T x
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
      ∫ x in (-1 : ℝ)..2, f x =
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
    (xiDerivNegOneTopContribution T).re
        = (((1 / (2 * ↑Real.pi * I)) * (-(R - conj R))).re) := by
            unfold xiDerivNegOneTopContribution
            rw [hsplit]
    _ = -(1 / Real.pi) * R.im := hmain
    _ = -(1 / Real.pi) * (∫ x in (1 / 2 : ℝ)..2, (f x).im) := by
          rw [← hR_im]
    _ = -(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im) := by
          simp [f]

/-- The fixed-bottom top leaf reduces to a one-sided bound for the half-top
imaginary integral of `logDeriv (RiemannXiAlt')`. -/
private theorem xiDerivNegOneTopContribution_re_upper_bound_of_half_top_imIntegral_upper_bound
    (htop_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ x ∈ Set.Icc (-1 : ℝ) 2,
        deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0)
    (hhalf_upper : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      -(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im)
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (xiDerivNegOneTopContribution T).re ≤ C * Real.log T := by
  rcases hhalf_upper with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro T hT
  rw [xiDerivNegOneTopContribution_re_eq_half_top_imIntegral T (htop_nz T hT)]
  exact hC T hT

/-- Split the upper-three-edge contribution into the top edge and the two
vertical sides. -/
private theorem xiDerivNegOneUpperThreeContribution_eq_top_add_side (T : ℝ) :
    xiDerivNegOneUpperThreeContribution T =
      xiDerivNegOneTopContribution T + xiDerivNegOneSideContribution T := by
  unfold xiDerivNegOneUpperThreeContribution xiDerivNegOneTopContribution
    xiDerivNegOneSideContribution
  ring_nf

/-- Split the fixed-bottom `ξ'` logarithmic rectangle integral into its fixed
bottom contribution and the remaining upper-three-edge term. -/
private theorem xiDeriv_logIntegralRect_at_neg_one_eq_bottom_plus_upperThree (T : ℝ) :
    RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1) =
      xiDerivNegOneBottomContribution + xiDerivNegOneUpperThreeContribution T := by
  unfold RectArgumentPrinciple.logIntegralRect
    xiDerivNegOneBottomContribution xiDerivNegOneUpperThreeContribution
  ring_nf

/-- The fixed bottom edge is a `T`-independent compact contribution, hence it
is automatically `O(log T)` on `T ≥ 14`. -/
private theorem xiDerivNegOneBottomContribution_bound :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |xiDerivNegOneBottomContribution.re| ≤ C * Real.log T := by
  have hlog14_pos : 0 < Real.log 14 := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < 14)
  refine ⟨|xiDerivNegOneBottomContribution.re| / Real.log 14, ?_⟩
  intro T hT
  have hlog_mono : Real.log 14 ≤ Real.log T := by
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 14) hT
  have hcoeff_nonneg : 0 ≤ |xiDerivNegOneBottomContribution.re| / Real.log 14 := by
    positivity
  calc
    |xiDerivNegOneBottomContribution.re|
        = (|xiDerivNegOneBottomContribution.re| / Real.log 14) * Real.log 14 := by
            field_simp [show Real.log 14 ≠ 0 by linarith]
    _ ≤ (|xiDerivNegOneBottomContribution.re| / Real.log 14) * Real.log T := by
          exact mul_le_mul_of_nonneg_left hlog_mono hcoeff_nonneg
    _ = (|xiDerivNegOneBottomContribution.re| / Real.log 14) * Real.log T := by
          rfl

/-- The corrected fixed-bottom side lane is a main-term-corrected formula
bound on the whole upper-three-edge contribution, obtained by combining the top
edge with the exact right-edge rewrite. -/
private def xiDerivNegOneRightEdgePrefixContribution : ℝ :=
  (1 / Real.pi) *
    (∫ y in (-1 : ℝ)..15,
      (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)

/-- The right-edge logarithmic derivative is interval-integrable on the fixed
compact prefix `[-1, 15]` once `T ≥ 14`. -/
private theorem xiDeriv_right_prefix15_intervalIntegrable (T : ℝ) (hT : 14 ≤ T)
    (hright_nz : ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
      deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0) :
    IntervalIntegrable
      (fun y : ℝ => logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))
      MeasureTheory.volume (-1) 15 := by
  refine (xiDeriv_right_continuousOn T hright_nz).mono ?_ |>.intervalIntegrable_of_Icc ?_
  · intro y hy
    exact ⟨hy.1, by linarith [hy.2, hT]⟩
  · linarith

/-- The remaining right-edge tail `[15, T + 1]` is the only `T`-dependent part
of the fixed-bottom right-edge formula target. -/
private theorem xiDeriv_right_tail15_intervalIntegrable (T : ℝ) (hT : 14 ≤ T)
    (hright_nz : ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
      deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0) :
    IntervalIntegrable
      (fun y : ℝ => logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))
      MeasureTheory.volume 15 (T + 1) := by
  refine (xiDeriv_right_continuousOn T hright_nz).mono ?_ |>.intervalIntegrable_of_Icc ?_
  · intro y hy
    exact ⟨by linarith [hy.1], hy.2⟩
  · linarith

/-- The full right-edge real-part integral is an explicit constant prefix plus
the genuinely `T`-dependent tail from `15` upward. -/
private theorem xiDerivNegOneRightEdgeReal_eq_prefix15_add_tail (T : ℝ) (hT : 14 ≤ T)
    (hright_nz : ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
      deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0) :
    (1 / Real.pi) *
        (∫ y in (-1 : ℝ)..(T + 1),
          (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
      =
    xiDerivNegOneRightEdgePrefixContribution +
      (1 / Real.pi) *
        (∫ y in (15 : ℝ)..(T + 1),
          (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re) := by
  let f : ℝ → ℂ := fun y =>
    logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)
  have hprefix_int :
      IntervalIntegrable f MeasureTheory.volume (-1) 15 :=
    xiDeriv_right_prefix15_intervalIntegrable T hT hright_nz
  have htail_int :
      IntervalIntegrable f MeasureTheory.volume 15 (T + 1) :=
    xiDeriv_right_tail15_intervalIntegrable T hT hright_nz
  have hfull_int :
      IntervalIntegrable f MeasureTheory.volume (-1) (T + 1) :=
    xiDeriv_right_intervalIntegrable T (by linarith) hright_nz
  have hsplit :
      ∫ y in (-1 : ℝ)..(T + 1), f y =
        (∫ y in (-1 : ℝ)..15, f y) + (∫ y in (15 : ℝ)..(T + 1), f y) := by
    simpa [f] using
      (intervalIntegral.integral_add_adjacent_intervals hprefix_int htail_int).symm
  have hfull_re :
      (∫ y in (-1 : ℝ)..(T + 1), f y).re
        =
      ∫ y in (-1 : ℝ)..(T + 1), (f y).re := by
    symm
    simpa [f] using Complex.reCLM.intervalIntegral_comp_comm hfull_int
  have hprefix_re :
      (∫ y in (-1 : ℝ)..15, f y).re
        =
      ∫ y in (-1 : ℝ)..15, (f y).re := by
    symm
    simpa [f] using Complex.reCLM.intervalIntegral_comp_comm hprefix_int
  have htail_re :
      (∫ y in (15 : ℝ)..(T + 1), f y).re
        =
      ∫ y in (15 : ℝ)..(T + 1), (f y).re := by
    symm
    simpa [f] using Complex.reCLM.intervalIntegral_comp_comm htail_int
  calc
    (1 / Real.pi) *
        (∫ y in (-1 : ℝ)..(T + 1),
          (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
        = (1 / Real.pi) * (∫ y in (-1 : ℝ)..(T + 1), f y).re := by
            rw [hfull_re]
    _ = (1 / Real.pi) *
          ((∫ y in (-1 : ℝ)..15, f y) + (∫ y in (15 : ℝ)..(T + 1), f y)).re := by
            rw [hsplit]
    _ = (1 / Real.pi) *
          ((∫ y in (-1 : ℝ)..15, f y).re + (∫ y in (15 : ℝ)..(T + 1), f y).re) := by
            simp
    _ = (1 / Real.pi) *
          ((∫ y in (-1 : ℝ)..15, (f y).re) +
            (∫ y in (15 : ℝ)..(T + 1), (f y).re)) := by
            rw [hprefix_re, htail_re]
    _ = (1 / Real.pi) * (∫ y in (-1 : ℝ)..15, (f y).re) +
          (1 / Real.pi) *
            (∫ y in (15 : ℝ)..(T + 1), (f y).re) := by
            ring
    _ = xiDerivNegOneRightEdgePrefixContribution +
          (1 / Real.pi) *
            (∫ y in (15 : ℝ)..(T + 1), (f y).re) := by
            rw [show (1 / Real.pi) * (∫ y in (-1 : ℝ)..15, (f y).re) =
              xiDerivNegOneRightEdgePrefixContribution by
                rfl]
    _ = xiDerivNegOneRightEdgePrefixContribution +
          (1 / Real.pi) *
            (∫ y in (15 : ℝ)..(T + 1),
              (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re) := by
            simp [f]

/-- A tail formula bound from `15` upward already suffices for the full
right-edge formula target; the compact prefix is an explicit constant. -/
private theorem xiDeriv_rightEdge_formula_bound_of_tail15_formula_bound
    (tailTerm : ℝ → ℝ)
    (hright_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0)
    (htail : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) *
          (∫ y in (15 : ℝ)..(T + 1),
            (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
        - tailTerm T| ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) *
          (∫ y in (-1 : ℝ)..(T + 1),
            (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
        - (xiDerivNegOneRightEdgePrefixContribution + tailTerm T)| ≤ C * Real.log T := by
  rcases htail with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro T hT
  let A : ℝ :=
    (1 / Real.pi) *
      (∫ y in (15 : ℝ)..(T + 1),
        (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
  calc
    |(1 / Real.pi) *
        (∫ y in (-1 : ℝ)..(T + 1),
          (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
        - (xiDerivNegOneRightEdgePrefixContribution + tailTerm T)|
        = |(xiDerivNegOneRightEdgePrefixContribution + A) -
            (xiDerivNegOneRightEdgePrefixContribution + tailTerm T)| := by
          rw [xiDerivNegOneRightEdgeReal_eq_prefix15_add_tail T hT (hright_nz T hT)]
    _ = |A - tailTerm T| := by ring_nf
    _ ≤ C * Real.log T := by simpa [A] using hC T hT

/-- The corrected fixed-bottom side lane is a main-term-corrected formula
bound on the whole upper-three-edge contribution, obtained by combining the top
edge with the exact right-edge rewrite. -/
private theorem xiDerivNegOneUpperThree_re_eq_half_top_plus_rightEdge (T : ℝ)
    (hT : -1 ≤ T + 1)
    (htop_nz : ∀ x ∈ Set.Icc (-1 : ℝ) 2,
      deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0)
    (hright_nz : ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
      deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0) :
    (xiDerivNegOneUpperThreeContribution T).re =
      (-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im)) +
        (1 / Real.pi) *
        (∫ y in (-1 : ℝ)..(T + 1),
          (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re) := by
  have hsplit := congrArg Complex.re (xiDerivNegOneUpperThreeContribution_eq_top_add_side T)
  have hright :
      IntervalIntegrable
        (fun y : ℝ => logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))
        MeasureTheory.volume (-1) (T + 1) :=
    xiDeriv_right_intervalIntegrable T hT hright_nz
  have hre :
      (∫ y in (-1 : ℝ)..(T + 1),
          logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re
        =
      ∫ y in (-1 : ℝ)..(T + 1),
        (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re := by
    symm
    simpa using Complex.reCLM.intervalIntegral_comp_comm hright
  rw [hsplit, Complex.add_re]
  rw [xiDerivNegOneTopContribution_re_eq_half_top_imIntegral T htop_nz,
    xiDerivNegOneSideContribution_re_eq_rightEdgeReal T hT hright_nz, hre]

/-- The upper-three-edge formula target honestly splits into separate half-top
and right-edge formula leaves. -/
private theorem xiDerivNegOneUpperThree_formula_bound_of_half_top_formula_and_rightEdge_formula
    (halfTerm rightTerm : ℝ → ℝ)
    (htop_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ x ∈ Set.Icc (-1 : ℝ) 2,
        deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0)
    (hright_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0)
    (hhalf : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im)
        - halfTerm T| ≤ C * Real.log T)
    (hright : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) *
          (∫ y in (-1 : ℝ)..(T + 1),
            (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
        - rightTerm T| ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(xiDerivNegOneUpperThreeContribution T).re - (halfTerm T + rightTerm T)|
        ≤ C * Real.log T := by
  rcases hhalf with ⟨Ch, hCh⟩
  rcases hright with ⟨Cr, hCr⟩
  refine ⟨Ch + Cr, ?_⟩
  intro T hT
  let H : ℝ :=
    -(1 / Real.pi) *
      (∫ x in (1 / 2 : ℝ)..2,
        (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im)
  let R : ℝ :=
    (1 / Real.pi) *
      (∫ y in (-1 : ℝ)..(T + 1),
        (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
  have hsplit :
      (xiDerivNegOneUpperThreeContribution T).re - (halfTerm T + rightTerm T) =
        (H - halfTerm T) + (R - rightTerm T) := by
    rw [xiDerivNegOneUpperThree_re_eq_half_top_plus_rightEdge T
      (by linarith) (htop_nz T hT) (hright_nz T hT)]
    simp [H, R]
    ring
  calc
    |(xiDerivNegOneUpperThreeContribution T).re - (halfTerm T + rightTerm T)|
        = |(H - halfTerm T) + (R - rightTerm T)| := by rw [hsplit]
    _ ≤ |H - halfTerm T| + |R - rightTerm T| := abs_add_le _ _
    _ ≤ Ch * Real.log T + Cr * Real.log T := by
          gcongr
          · exact hCh T hT
          · exact hCr T hT
    _ = (Ch + Cr) * Real.log T := by ring

/-- Separate half-top and right-edge formula leaves already suffice for the
fixed-bottom logarithmic-rectangle formula target. -/
private theorem xiDeriv_logIntegralRect_formula_bound_at_neg_one_from14_of_half_top_formula_and_rightEdge_formula
    (halfTerm rightTerm : ℝ → ℝ)
    (htop_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ x ∈ Set.Icc (-1 : ℝ) 2,
        deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0)
    (hright_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0)
    (hhalf : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im)
        - halfTerm T| ≤ C * Real.log T)
    (hright : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) *
          (∫ y in (-1 : ℝ)..(T + 1),
            (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
        - rightTerm T| ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1)).re
        - (xiDerivNegOneBottomContribution.re + (halfTerm T + rightTerm T))|
        ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ :=
    xiDerivNegOneUpperThree_formula_bound_of_half_top_formula_and_rightEdge_formula
      halfTerm rightTerm htop_nz hright_nz hhalf hright
  refine ⟨C, ?_⟩
  intro T hT
  have hsplit :=
    congrArg Complex.re (xiDeriv_logIntegralRect_at_neg_one_eq_bottom_plus_upperThree T)
  have hinner :
      xiDerivNegOneBottomContribution.re + (xiDerivNegOneUpperThreeContribution T).re -
          (xiDerivNegOneBottomContribution.re + (halfTerm T + rightTerm T))
        =
      (xiDerivNegOneUpperThreeContribution T).re - (halfTerm T + rightTerm T) := by
    ring
  calc
    |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1)).re
        - (xiDerivNegOneBottomContribution.re + (halfTerm T + rightTerm T))|
        = |(xiDerivNegOneUpperThreeContribution T).re - (halfTerm T + rightTerm T)| := by
            rw [hsplit]
            rw [Complex.add_re, hinner]
    _ ≤ C * Real.log T := hC T hT

/-- After peeling off the explicit compact right-edge prefix, the remaining
external inputs are exactly a half-top formula bound and a right-edge tail
formula bound from `15` upward. -/
private theorem xiDerivNegOneUpperThree_formula_bound_of_half_top_formula_and_rightEdge_tail15_formula
    (halfTerm tailTerm : ℝ → ℝ)
    (htop_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ x ∈ Set.Icc (-1 : ℝ) 2,
        deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0)
    (hright_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0)
    (hhalf : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im)
        - halfTerm T| ≤ C * Real.log T)
    (htail : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) *
          (∫ y in (15 : ℝ)..(T + 1),
            (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
        - tailTerm T| ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(xiDerivNegOneUpperThreeContribution T).re -
          (halfTerm T + (xiDerivNegOneRightEdgePrefixContribution + tailTerm T))|
        ≤ C * Real.log T := by
  apply xiDerivNegOneUpperThree_formula_bound_of_half_top_formula_and_rightEdge_formula
    (halfTerm := halfTerm)
    (rightTerm := fun T => xiDerivNegOneRightEdgePrefixContribution + tailTerm T)
    htop_nz hright_nz hhalf
  exact xiDeriv_rightEdge_formula_bound_of_tail15_formula_bound tailTerm hright_nz htail

/-- The fixed-bottom logarithmic-rectangle formula target likewise reduces to
the same half-top formula input and right-edge tail formula input. -/
private theorem xiDeriv_logIntegralRect_formula_bound_at_neg_one_from14_of_half_top_formula_and_rightEdge_tail15_formula
    (halfTerm tailTerm : ℝ → ℝ)
    (htop_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ x ∈ Set.Icc (-1 : ℝ) 2,
        deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0)
    (hright_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0)
    (hhalf : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im)
        - halfTerm T| ≤ C * Real.log T)
    (htail : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) *
          (∫ y in (15 : ℝ)..(T + 1),
            (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
        - tailTerm T| ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1)).re
        - (xiDerivNegOneBottomContribution.re +
            (halfTerm T + (xiDerivNegOneRightEdgePrefixContribution + tailTerm T)))|
        ≤ C * Real.log T := by
  apply xiDeriv_logIntegralRect_formula_bound_at_neg_one_from14_of_half_top_formula_and_rightEdge_formula
    (halfTerm := halfTerm)
    (rightTerm := fun T => xiDerivNegOneRightEdgePrefixContribution + tailTerm T)
    htop_nz hright_nz hhalf
  exact xiDeriv_rightEdge_formula_bound_of_tail15_formula_bound tailTerm hright_nz htail

/-- The explicit `T`-independent part of the fixed-bottom `ξ'` log-rectangle
formula: the bottom edge plus the compact right-edge prefix. -/
private def xiDerivNegOneLogRectExplicitPrefixContribution : ℝ :=
  xiDerivNegOneBottomContribution.re + xiDerivNegOneRightEdgePrefixContribution

/-- Documentation surface for the fixed-bottom `ξ'` lane: after the exact local
splits proved above, the only remaining external inputs are
1. a half-top formula bound, and
2. a right-edge tail formula bound from `15` upward.

Everything else is explicit and `T`-independent. -/
private theorem xiDeriv_logIntegralRect_formula_bound_at_neg_one_from14_of_remaining_formula_inputs
    (halfTerm tailTerm : ℝ → ℝ)
    (htop_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ x ∈ Set.Icc (-1 : ℝ) 2,
        deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0)
    (hright_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0)
    (hhalf : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |-(1 / Real.pi) *
          (∫ x in (1 / 2 : ℝ)..2,
            (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im)
        - halfTerm T| ≤ C * Real.log T)
    (htail : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(1 / Real.pi) *
          (∫ y in (15 : ℝ)..(T + 1),
            (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
        - tailTerm T| ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1)).re
        - (xiDerivNegOneLogRectExplicitPrefixContribution + (halfTerm T + tailTerm T))|
        ≤ C * Real.log T := by
  obtain ⟨C, hC⟩ :=
    xiDeriv_logIntegralRect_formula_bound_at_neg_one_from14_of_half_top_formula_and_rightEdge_tail15_formula
      halfTerm tailTerm htop_nz hright_nz hhalf htail
  refine ⟨C, ?_⟩
  intro T hT
  have hmain :
      xiDerivNegOneBottomContribution.re + (halfTerm T + (xiDerivNegOneRightEdgePrefixContribution + tailTerm T))
        =
      xiDerivNegOneLogRectExplicitPrefixContribution + (halfTerm T + tailTerm T) := by
    simp [xiDerivNegOneLogRectExplicitPrefixContribution]
    ring
  simpa [hmain] using hC T hT

/-- The corrected fixed-bottom side lane is a main-term-corrected formula
bound on the whole upper-three-edge contribution, obtained by combining the top
edge with the exact right-edge rewrite. -/
private theorem xiDerivNegOneUpperThree_formula_bound_of_top_plus_rightEdge_formula_bound
    (mainTerm : ℝ → ℝ)
    (hright_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ y ∈ Set.Icc (-1 : ℝ) (T + 1),
        deriv RiemannXiAlt ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I) ≠ 0)
    (htopRight : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(xiDerivNegOneTopContribution T).re
        + (1 / Real.pi) *
            (∫ y in (-1 : ℝ)..(T + 1),
              (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
        - mainTerm T| ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(xiDerivNegOneUpperThreeContribution T).re - mainTerm T| ≤ C * Real.log T := by
  rcases htopRight with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro T hT
  have hsplit := congrArg Complex.re (xiDerivNegOneUpperThreeContribution_eq_top_add_side T)
  have hright :
      IntervalIntegrable
        (fun y : ℝ => logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I))
        MeasureTheory.volume (-1) (T + 1) :=
    xiDeriv_right_intervalIntegrable T (by linarith) (hright_nz T hT)
  have hre :
      (∫ y in (-1 : ℝ)..(T + 1),
          logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re
        =
      ∫ y in (-1 : ℝ)..(T + 1),
        (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re := by
    symm
    simpa using Complex.reCLM.intervalIntegral_comp_comm hright
  calc
    |(xiDerivNegOneUpperThreeContribution T).re - mainTerm T|
        = |(xiDerivNegOneTopContribution T).re
            + (1 / Real.pi) *
                (∫ y in (-1 : ℝ)..(T + 1),
                  logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re
            - mainTerm T| := by
              rw [hsplit, Complex.add_re,
                xiDerivNegOneSideContribution_re_eq_rightEdgeReal T (by linarith)
                  (hright_nz T hT)]
    _ = |(xiDerivNegOneTopContribution T).re
            + (1 / Real.pi) *
                (∫ y in (-1 : ℝ)..(T + 1),
                  (logDeriv (deriv RiemannXiAlt) ((↑(2 : ℝ) : ℂ) + (↑y : ℂ) * I)).re)
            - mainTerm T| := by
              rw [hre]
    _ ≤ C * Real.log T := hC T hT

/-- The full fixed-bottom one-sided `ξ'` rectangle-integral target reduces to
bounding the remaining top/right/left contribution. -/
private theorem xiDeriv_logIntegralRect_re_upper_bound_at_neg_one_from14_of_upperThree_re_upper_bound
    (hupperThree : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (xiDerivNegOneUpperThreeContribution T).re ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1)).re
        ≤ C * Real.log T := by
  obtain ⟨Cb, hCb⟩ := xiDerivNegOneBottomContribution_bound
  obtain ⟨Cu, hCu⟩ := hupperThree
  refine ⟨Cb + Cu, ?_⟩
  intro T hT
  have hsplit :=
    congrArg Complex.re (xiDeriv_logIntegralRect_at_neg_one_eq_bottom_plus_upperThree T)
  have hble : xiDerivNegOneBottomContribution.re ≤ |xiDerivNegOneBottomContribution.re| := by
    exact le_abs_self _
  calc
    (RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1)).re
        = xiDerivNegOneBottomContribution.re + (xiDerivNegOneUpperThreeContribution T).re := by
            simpa using hsplit
    _ ≤ |xiDerivNegOneBottomContribution.re| + Cu * Real.log T := by
          linarith [hble, hCu T hT]
    _ ≤ Cb * Real.log T + Cu * Real.log T := by
          linarith [hCb T hT]
    _ = (Cb + Cu) * Real.log T := by
          ring

/-- The remaining upper-three-edge fixed-bottom `ξ'` target reduces further to
separate one-sided bounds for the top edge and the two vertical sides. -/
private theorem xiDerivNegOneUpperThree_re_upper_bound_of_top_side_re_upper_bound
    (htop : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (xiDerivNegOneTopContribution T).re ≤ C * Real.log T)
    (hside : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (xiDerivNegOneSideContribution T).re ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (xiDerivNegOneUpperThreeContribution T).re ≤ C * Real.log T := by
  obtain ⟨Ct, hCt⟩ := htop
  obtain ⟨Cs, hCs⟩ := hside
  refine ⟨Ct + Cs, ?_⟩
  intro T hT
  have hsplit :=
    congrArg Complex.re (xiDerivNegOneUpperThreeContribution_eq_top_add_side T)
  calc
    (xiDerivNegOneUpperThreeContribution T).re
        = (xiDerivNegOneTopContribution T).re + (xiDerivNegOneSideContribution T).re := by
            simpa using hsplit
    _ ≤ Ct * Real.log T + Cs * Real.log T := by
          linarith [hCt T hT, hCs T hT]
    _ = (Ct + Cs) * Real.log T := by
          ring

/-- The fixed-bottom one-sided `ξ'` rectangle-integral target reduces to
separate one-sided bounds for its top edge and combined vertical sides. -/
private theorem xiDeriv_logIntegralRect_re_upper_bound_at_neg_one_from14_of_top_side_re_upper_bound
    (htop : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (xiDerivNegOneTopContribution T).re ≤ C * Real.log T)
    (hside : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (xiDerivNegOneSideContribution T).re ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 (-1 : ℝ) (T + 1)).re
        ≤ C * Real.log T := by
  apply xiDeriv_logIntegralRect_re_upper_bound_at_neg_one_from14_of_upperThree_re_upper_bound
  exact xiDerivNegOneUpperThree_re_upper_bound_of_top_side_re_upper_bound htop hside

/-- Direct contour-based consumer theorem for Nash: it is enough to control the
real part of the logarithmic rectangle integral of `deriv RiemannXiAlt`, under
the boundary nonvanishing needed for the argument principle. -/
theorem distinct_mult_compatibility_bound_of_xiDeriv_logIntegral_bound
    [ZeroOrdinateLowerBoundHyp] {c : ℝ} (hc_lt : c < 1) (T0 : ℝ) (hT0 : 0 ≤ T0)
    (hbdy : ∀ T : ℝ, T0 ≤ T →
      ∀ z ∈ RectArgumentPrinciple.rectBoundary (-1) 2 c (T + 1), deriv RiemannXiAlt z ≠ 0)
    (hlog : ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      |(RectArgumentPrinciple.logIntegralRect (deriv RiemannXiAlt) (-1) 2 c (T + 1)).re|
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      |(N T : ℝ) - (Nmult T : ℝ)| ≤ C * Real.log T := by
  have hcount :=
    xiDeriv_zeroCountRectMult_bound_of_logIntegral_bound hc_lt T0 hT0 hbdy hlog
  rcases hcount with ⟨C, hC⟩
  have hmass : ∃ C' : ℝ, ∀ T : ℝ, T0 ≤ T →
      (zeroCountingRepeatedZeroMass T : ℝ) ≤ C' * Real.log T := by
    refine ⟨C, ?_⟩
    intro T hT
    have hle_nat :=
      zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt
        hc_lt T (le_trans hT0 hT)
    have hle : (zeroCountingRepeatedZeroMass T : ℝ) ≤
        (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ) := by
      exact_mod_cast hle_nat
    exact le_trans hle (hC T hT)
  exact (distinct_mult_compatibility_bound_iff_repeatedZeroMass_bound T0).mpr hmass

/-- A direct consumer theorem for Nash: any `O(log T)` bound on the
multiplicity-counted zero count of `RiemannXiAlt'` on a rectangle
`(-1,2) × (c,T+1)` with `c < 1` yields the distinct-versus-multiplicity
compatibility bound. -/
theorem distinct_mult_compatibility_bound_of_xiDerivZeroCountRectMult_bound
    [ZeroOrdinateLowerBoundHyp] {c : ℝ} (hc_lt : c < 1) (T0 : ℝ)
    (hT0 : 0 ≤ T0)
    (hbound : ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ)
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, T0 ≤ T →
      |(N T : ℝ) - (Nmult T : ℝ)| ≤ C * Real.log T := by
  rcases hbound with ⟨C, hC⟩
  have hmass : ∃ C' : ℝ, ∀ T : ℝ, T0 ≤ T →
      (zeroCountingRepeatedZeroMass T : ℝ) ≤ C' * Real.log T := by
    refine ⟨C, ?_⟩
    intro T hT
    have hle_nat :=
      zeroCountingRepeatedZeroMass_le_zeroCountRectMult_deriv_RiemannXiAlt
        hc_lt T (le_trans hT0 hT)
    have hle : (zeroCountingRepeatedZeroMass T : ℝ) ≤
        (RectArgumentPrinciple.zeroCountRectMult (deriv RiemannXiAlt) (-1) 2 c (T + 1) : ℝ) := by
      exact_mod_cast hle_nat
    exact le_trans hle (hC T hT)
  exact (distinct_mult_compatibility_bound_iff_repeatedZeroMass_bound T0).mpr hmass

/-- A pointwise `O(log T)` bound on `|Im(logDeriv(ξ'))|` along the half-top
    edge yields the one-sided half-top imaginary integral bound consumed by
    the existing top-edge reduction machinery. -/
private theorem xiDeriv_half_top_imIntegral_bound_of_pointwise_im_bound
    (hpointwise : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      |(logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im|
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      -(1 / Real.pi) *
        (∫ x in (1 / 2 : ℝ)..2,
          (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im)
        ≤ C * Real.log T := by
  cases' hpointwise with C hC
  refine' ⟨(1 / Real.pi) * (3 / 2) * |C|, fun T hT => ?_⟩
  rw [intervalIntegral.integral_of_le]
  · have h_integral_bound :
        |∫ x in Set.Ioc (1 / 2 : ℝ) 2,
            (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im|
          ≤ (3 / 2) * |C| * Real.log T := by
      refine' le_trans
          (MeasureTheory.norm_integral_le_integral_norm
            (f := fun x : ℝ =>
              (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im))
          (le_trans
            (MeasureTheory.integral_mono_of_nonneg
              (μ := MeasureTheory.volume.restrict (Set.Ioc (1 / 2 : ℝ) 2))
              (f := fun x : ℝ =>
                |(logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im|)
              (g := fun _ : ℝ => |C| * Real.log T)
              ?_ ?_ ?_)
            ?_)
      · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
      · fun_prop
      · exact Filter.eventually_of_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioc) fun x hx =>
          le_trans (hC T hT x ⟨hx.1.le, hx.2⟩)
            (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.log_nonneg (by linarith)))
      · norm_num [mul_assoc, mul_comm, mul_left_comm]
    have hneg :
        -(∫ x in Set.Ioc (1 / 2 : ℝ) 2,
            (logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im)
          ≤ (3 / 2) * |C| * Real.log T := by
      exact le_trans (neg_le_abs _) h_integral_bound
    have hmul_nonneg : 0 ≤ (1 / Real.pi : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hneg hmul_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  · norm_num

/-- Composes the pointwise half-top bound with the existing top-edge reduction,
    shrinking the top split leaf to a pointwise `O(log T)` bound on
    `|Im(logDeriv(ξ'))|` along the half-top edge. -/
private theorem xiDerivNegOneTopContribution_re_bound_of_pointwise_top_im_bound
    (htop_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ x ∈ Set.Icc (-1 : ℝ) 2,
        deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0)
    (hpointwise : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      |(logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im|
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (xiDerivNegOneTopContribution T).re ≤ C * Real.log T := by
  exact xiDerivNegOneTopContribution_re_upper_bound_of_half_top_imIntegral_upper_bound
    htop_nz (xiDeriv_half_top_imIntegral_bound_of_pointwise_im_bound hpointwise)

/-- On the critical line `Re s = 1/2`, the logarithmic derivative of `ξ'` is
pure imaginary: its real part vanishes. This follows from combining the
functional equation `logDeriv(ξ')(1 − s) = −logDeriv(ξ')(s)` with the Schwarz
reflection `logDeriv(ξ')(conj s) = conj(logDeriv(ξ')(s))`, which together give
`conj(w) = −w` at `s = 1/2 + ti`. -/
private theorem xiDeriv_logDeriv_pure_imaginary_at_critical_line (t : ℝ) :
    (logDeriv (deriv RiemannXiAlt) ((1 / 2 : ℂ) + (↑t : ℂ) * I)).re = 0 := by
  set s : ℂ := (1 / 2 : ℂ) + (↑t : ℂ) * I
  have hone_sub : (1 : ℂ) - s = conj s := by
    apply Complex.ext <;> simp [s] <;> ring
  have hw : logDeriv (deriv RiemannXiAlt) (conj s) =
      -logDeriv (deriv RiemannXiAlt) s := by
    rw [← hone_sub]
    exact xiDeriv_logDeriv_functional_eq s
  have hconj : logDeriv (deriv RiemannXiAlt) (conj s) =
      conj (logDeriv (deriv RiemannXiAlt) s) :=
    xiDeriv_logDeriv_conj s
  have hkey : conj (logDeriv (deriv RiemannXiAlt) s) =
      -logDeriv (deriv RiemannXiAlt) s := by
    rw [← hconj, hw]
  have := congr_arg Complex.re hkey
  simp at this
  linarith

/-- At the critical line point on the top edge, `logDeriv(ξ')` is pure imaginary;
its real part vanishes identically. This is the `T`-parametrised form used by
the top-edge reduction. -/
private theorem xiDeriv_logDeriv_top_re_zero_at_half (T : ℝ) :
    (logDeriv (deriv RiemannXiAlt) ((↑(1 / 2 : ℝ) : ℂ) + (↑(T + 1) : ℂ) * I)).re = 0 := by
  have h : (↑(1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    push_cast
    ring
  rw [h]
  exact xiDeriv_logDeriv_pure_imaginary_at_critical_line (T + 1)

/-- The pointwise imaginary-part bound on the half-top edge follows from a
pointwise norm bound, because `|Im z| ≤ ‖z‖` for every complex number. -/
private theorem xiDeriv_pointwise_top_im_bound_of_pointwise_top_norm_bound
    (hpointwise_norm : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      ‖logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)‖
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      |(logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)).im|
        ≤ C * Real.log T := by
  rcases hpointwise_norm with ⟨C, hC⟩
  exact ⟨C, fun T hT x hx =>
    le_trans (Complex.abs_im_le_norm _)
      (hC T hT x hx)⟩

/-- A pointwise `O(log T)` norm bound on `logDeriv(ξ')` along the half-top
edge `[1/2, 2] + (T+1)i` suffices for the top-contribution real-part bound. -/
private theorem xiDerivNegOneTopContribution_re_bound_of_pointwise_top_norm_bound
    (htop_nz : ∀ T : ℝ, 14 ≤ T →
      ∀ x ∈ Set.Icc (-1 : ℝ) 2,
        deriv RiemannXiAlt ((↑x : ℂ) + (↑(T + 1) : ℂ) * I) ≠ 0)
    (hpointwise_norm : ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      ‖logDeriv (deriv RiemannXiAlt) ((↑x : ℂ) + (↑(T + 1) : ℂ) * I)‖
        ≤ C * Real.log T) :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      (xiDerivNegOneTopContribution T).re ≤ C * Real.log T := by
  exact xiDerivNegOneTopContribution_re_bound_of_pointwise_top_im_bound
    htop_nz (xiDeriv_pointwise_top_im_bound_of_pointwise_top_norm_bound hpointwise_norm)

end ZetaZeros
