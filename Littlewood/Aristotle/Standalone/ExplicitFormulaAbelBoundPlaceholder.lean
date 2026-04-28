import Littlewood.Aristotle.Standalone.MultWeightedExplicitFormulaProof
import Littlewood.Aristotle.Standalone.ExplicitFormulaAbelMultiplicityCorrectionPlaceholder
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aGeneralProvider
import Littlewood.Aristotle.CriticalZeros
import Littlewood.ZetaZeros.ZeroDensity

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

open Real Filter Topology Asymptotics Set Complex
open scoped Real BigOperators

namespace Littlewood.Classical

open Aristotle.DirichletPhaseAlignment (CriticalZeros ZerosBelow chebyshevPsi)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open ZetaZeros
open ZetaZeros.Density

/-!
# ExplicitFormulaAbelBoundHyp provider

This file turns the constructive B5a truncated explicit formula into the
multiplicity-weighted Abel-sum surface used by the classical Littlewood
Phragmen-Lindelöf argument.

The proof is now sorry-free. The only remaining leaf is isolated in
`AbelMultiplicityCorrectionBoundHyp`, which controls the oscillatory excess
multiplicity contribution

`∑ (m(ρ) - 1) * sin (γη) / γ`.
-/

private lemma dpa_chebyshevPsi_eq (x : ℝ) :
    Aristotle.DirichletPhaseAlignment.chebyshevPsi x = _root_.chebyshevPsi x := by
  unfold Aristotle.DirichletPhaseAlignment.chebyshevPsi _root_.chebyshevPsi
  rw [Chebyshev.psi_eq_sum_Icc]
  have hIcc : Finset.Icc 0 (Nat.floor x) = Finset.range (Nat.floor x + 1) := by
    ext n
    constructor
    · intro hn
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hn).2)
    · intro hn
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)⟩
  rw [hIcc]

private def positiveZerosBelowDistinct (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => 0 < ρ.im)

private def negativeZerosBelowDistinct (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => ρ.im < 0)

private def zeroZerosBelowDistinct (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => ρ.im = 0)

private lemma criticalZeros_finite_under_RH (hRH : RiemannHypothesis') (T : ℝ) :
    (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite := by
  refine (critical_zeros_finite T).subset ?_
  intro ρ hρ
  rcases hρ with ⟨hcrit, him⟩
  refine ⟨?_, hcrit.1⟩
  refine ⟨ρ.im, ?_, ?_⟩
  · simpa [abs_le] using him
  · apply Complex.ext
    · simpa using (rh_implies_critical_line (hRH := hRH) ρ (by
        simpa [CriticalZeros, zetaNontrivialZeros] using hcrit)).symm
    · simp

private lemma zerosBelow_mem_criticalZeros {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) :
    ρ ∈ CriticalZeros := by
  simp only [ZerosBelow] at hρ
  split_ifs at hρ with hfin
  · exact ((hfin.mem_toFinset).mp hρ).1
  · simp at hρ

private lemma zerosBelow_mem_zetaNontrivialZeros {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) :
    ρ ∈ zetaNontrivialZeros := by
  simpa [CriticalZeros, zetaNontrivialZeros] using zerosBelow_mem_criticalZeros hρ

private lemma zerosBelow_im_le {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ ZerosBelow T) :
    |ρ.im| ≤ T := by
  simp only [ZerosBelow] at hρ
  split_ifs at hρ with hfin
  · exact ((hfin.mem_toFinset).mp hρ).2
  · simp at hρ

private lemma zerosBelow_re_half (hRH : RiemannHypothesis') {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ ZerosBelow T) : ρ.re = 1 / 2 :=
  rh_implies_critical_line (hRH := hRH) ρ (zerosBelow_mem_zetaNontrivialZeros hρ)

private lemma conj_im_eq (ρ : ℂ) : (starRingEnd ℂ ρ).im = -ρ.im := by
  change (star ρ).im = _
  simp [Complex.conj_im]

private lemma conj_mem_zerosBelow (hRH : RiemannHypothesis') {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ ZerosBelow T) : starRingEnd ℂ ρ ∈ ZerosBelow T := by
  have hρz : ρ ∈ zetaNontrivialZeros := zerosBelow_mem_zetaNontrivialZeros hρ
  have hconj_crit : starRingEnd ℂ ρ ∈ CriticalZeros := by
    simpa [CriticalZeros, zetaNontrivialZeros] using (zero_conj_zero hρz)
  have hconj_im_le : |((starRingEnd ℂ) ρ).im| ≤ T := by
    rw [conj_im_eq, abs_neg]
    exact zerosBelow_im_le hρ
  have hfin : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite := criticalZeros_finite_under_RH hRH T
  rw [ZerosBelow, dif_pos hfin]
  exact hfin.mem_toFinset.mpr ⟨hconj_crit, hconj_im_le⟩

private lemma positiveZerosBelowDistinct_sub (T : ℝ) :
    positiveZerosBelowDistinct T ⊆ ZerosBelow T :=
  Finset.filter_subset _ _

private lemma conj_pos_mem_neg (hRH : RiemannHypothesis') (T : ℝ) :
    ∀ ρ ∈ positiveZerosBelowDistinct T, starRingEnd ℂ ρ ∈ negativeZerosBelowDistinct T := by
  intro ρ hρ
  simp only [negativeZerosBelowDistinct, Finset.mem_filter]
  have hρ_zb : ρ ∈ ZerosBelow T := positiveZerosBelowDistinct_sub T hρ
  have hρ_im : 0 < ρ.im := by
    simp only [positiveZerosBelowDistinct, Finset.mem_filter] at hρ
    exact hρ.2
  exact ⟨conj_mem_zerosBelow hRH hρ_zb, by rw [conj_im_eq]; linarith⟩

private lemma conj_neg_mem_pos (hRH : RiemannHypothesis') (T : ℝ) :
    ∀ ρ ∈ negativeZerosBelowDistinct T, starRingEnd ℂ ρ ∈ positiveZerosBelowDistinct T := by
  intro ρ hρ
  simp only [positiveZerosBelowDistinct, Finset.mem_filter]
  simp only [negativeZerosBelowDistinct, Finset.mem_filter] at hρ
  exact ⟨conj_mem_zerosBelow hRH hρ.1, by rw [conj_im_eq]; linarith⟩

private lemma re_cpow_div_conj_eq (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
    (((x : ℂ) ^ (starRingEnd ℂ ρ)) / (starRingEnd ℂ ρ)).re =
    (((x : ℂ) ^ ρ) / ρ).re := by
  have harg : (↑x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact ne_of_lt Real.pi_pos
  have h_cpow : (↑x : ℂ) ^ (starRingEnd ℂ ρ) = starRingEnd ℂ ((↑x : ℂ) ^ ρ) := by
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  have h_div :
      starRingEnd ℂ ((↑x : ℂ) ^ ρ) / starRingEnd ℂ ρ =
        starRingEnd ℂ (((↑x : ℂ) ^ ρ) / ρ) := (map_div₀ (starRingEnd ℂ) _ _).symm
  rw [h_cpow, h_div, Complex.conj_re]

private lemma nonPosIm_decomp (T : ℝ) :
    (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)) =
    negativeZerosBelowDistinct T ∪ zeroZerosBelowDistinct T := by
  ext ρ
  simp only [Finset.mem_filter, negativeZerosBelowDistinct, zeroZerosBelowDistinct,
    Finset.mem_union, Finset.mem_filter, not_lt]
  constructor
  · intro ⟨hmem, hle⟩
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inl ⟨hmem, h⟩
    · exact Or.inr ⟨hmem, h⟩
  · rintro (⟨hmem, hlt⟩ | ⟨hmem, heq⟩)
    · exact ⟨hmem, le_of_lt hlt⟩
    · exact ⟨hmem, le_of_eq heq⟩

private lemma negIm_zeroIm_disjoint (T : ℝ) :
    Disjoint (negativeZerosBelowDistinct T) (zeroZerosBelowDistinct T) := by
  simp only [negativeZerosBelowDistinct, zeroZerosBelowDistinct]
  rw [Finset.disjoint_filter]
  intro ρ _ hlt heq
  linarith

private lemma zeroIm_card_le_one (hRH : RiemannHypothesis') (T : ℝ) :
    (zeroZerosBelowDistinct T).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro ρ₁ hρ₁ ρ₂ hρ₂
  simp only [zeroZerosBelowDistinct, Finset.mem_filter] at hρ₁ hρ₂
  have hre₁ := zerosBelow_re_half hRH hρ₁.1
  have hre₂ := zerosBelow_re_half hRH hρ₂.1
  exact Complex.ext (by rw [hre₁, hre₂]) (by rw [hρ₁.2, hρ₂.2])

private lemma zeroIm_term_bound (hRH : RiemannHypothesis') (T x : ℝ) (hx : 2 ≤ x)
    (ρ : ℂ) (hρ : ρ ∈ zeroZerosBelowDistinct T) :
    |(((x : ℂ) ^ ρ / ρ)).re| ≤ 2 * Real.sqrt x := by
  simp only [zeroZerosBelowDistinct, Finset.mem_filter] at hρ
  have hre : ρ.re = 1 / 2 := zerosBelow_re_half hRH hρ.1
  have him : ρ.im = 0 := hρ.2
  have hx_pos : (0 : ℝ) < x := by linarith
  calc
    |(((x : ℂ) ^ ρ / ρ)).re|
        ≤ ‖((x : ℂ) ^ ρ / ρ)‖ := Complex.abs_re_le_norm _
    _ = ‖(x : ℂ) ^ ρ‖ / ‖ρ‖ := norm_div _ _
    _ = x ^ ρ.re / ‖ρ‖ := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    _ = x ^ (1 / 2 : ℝ) / ‖ρ‖ := by rw [hre]
    _ = Real.sqrt x / ‖ρ‖ := by rw [Real.sqrt_eq_rpow]
    _ = 2 * Real.sqrt x := by
          have hρ_eq : ρ = (↑(1 / 2 : ℝ) : ℂ) := Complex.ext (by simp [hre]) (by simp [him])
          rw [hρ_eq, Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          ring

private theorem zero_sum_conjugate_bound (hRH : RiemannHypothesis') (T x : ℝ) (hx : 2 ≤ x) :
    ∃ R : ℝ, |R| ≤ 2 * Real.sqrt x ∧
      (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re =
      2 * (∑ ρ ∈ positiveZerosBelowDistinct T, ((x : ℂ) ^ ρ / ρ)).re + R := by
  set f : ℂ → ℝ := fun ρ => (((x : ℂ) ^ ρ) / ρ).re
  have hx_pos : (0 : ℝ) < x := by linarith
  have h_decomp :
      ∑ ρ ∈ ZerosBelow T, f ρ =
      ∑ ρ ∈ positiveZerosBelowDistinct T, f ρ +
      ∑ ρ ∈ (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)), f ρ :=
    (Finset.sum_filter_add_sum_filter_not (ZerosBelow T) (fun ρ => 0 < ρ.im) f).symm
  have h_nonpos :
      ∑ ρ ∈ (ZerosBelow T).filter (fun ρ => ¬(0 < ρ.im)), f ρ =
      ∑ ρ ∈ negativeZerosBelowDistinct T, f ρ + ∑ ρ ∈ zeroZerosBelowDistinct T, f ρ := by
    conv_lhs => rw [nonPosIm_decomp T]
    exact Finset.sum_union (negIm_zeroIm_disjoint T)
  have h_neg_eq_pos :
      ∑ ρ ∈ negativeZerosBelowDistinct T, f ρ =
      ∑ ρ ∈ positiveZerosBelowDistinct T, f ρ := by
    apply Finset.sum_nbij' (starRingEnd ℂ) (starRingEnd ℂ)
      (conj_neg_mem_pos hRH T) (conj_pos_mem_neg hRH T)
      (fun ρ _ => Complex.conj_conj ρ) (fun ρ _ => Complex.conj_conj ρ)
    intro ρ _hρ
    exact (re_cpow_div_conj_eq x hx_pos ρ).symm
  set R := ∑ ρ ∈ zeroZerosBelowDistinct T, f ρ
  have hR_bound : |R| ≤ 2 * Real.sqrt x := by
    calc
      |R| ≤ ∑ ρ ∈ zeroZerosBelowDistinct T, |f ρ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ρ ∈ zeroZerosBelowDistinct T, (2 * Real.sqrt x) :=
            Finset.sum_le_sum (fun ρ hρ => zeroIm_term_bound hRH T x hx ρ hρ)
      _ = (zeroZerosBelowDistinct T).card * (2 * Real.sqrt x) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (2 * Real.sqrt x) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast zeroIm_card_le_one hRH T
      _ = 2 * Real.sqrt x := one_mul _
  refine ⟨R, hR_bound, ?_⟩
  have h_re_sum :
      (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re =
      ∑ ρ ∈ ZerosBelow T, f ρ := by
    change Complex.reAddGroupHom (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)) = _
    rw [map_sum]
    rfl
  have h_re_pos :
      (∑ ρ ∈ positiveZerosBelowDistinct T, ((x : ℂ) ^ ρ / ρ)).re =
      ∑ ρ ∈ positiveZerosBelowDistinct T, f ρ := by
    change Complex.reAddGroupHom (∑ ρ ∈ positiveZerosBelowDistinct T, ((x : ℂ) ^ ρ / ρ)) = _
    rw [map_sum]
    rfl
  rw [h_re_sum, h_re_pos, h_decomp, h_nonpos, h_neg_eq_pos]
  ring

private lemma positiveZerosBelowDistinct_eq_positiveImZerosBelow (hRH : RiemannHypothesis') (T : ℝ) :
    positiveZerosBelowDistinct T = positiveImZerosBelow T := by
  have hfin : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite := criticalZeros_finite_under_RH hRH T
  ext ρ
  constructor
  · intro hρ
    simp only [positiveZerosBelowDistinct, Finset.mem_filter] at hρ
    have hmem := hfin.mem_toFinset.mp (by
      simpa [ZerosBelow, dif_pos hfin] using hρ.1)
    refine mem_positiveImZerosBelow.mpr ?_
    refine ⟨?_, ?_⟩
    · exact (mem_zetaNontrivialZerosPos).2 ⟨by
          simpa [CriticalZeros, zetaNontrivialZeros] using hmem.1, hρ.2⟩
    · have him_le : ρ.im ≤ T := by
        exact (abs_le.mp hmem.2).2
      exact him_le
  · intro hρ
    rcases mem_positiveImZerosBelow.mp hρ with ⟨hρpos, hρle⟩
    rcases mem_zetaNontrivialZerosPos.mp hρpos with ⟨hρz, hρim_pos⟩
    have hmem_fin : ρ ∈ (criticalZeros_finite_under_RH hRH T).toFinset := by
      apply (criticalZeros_finite_under_RH hRH T).mem_toFinset.mpr
      refine ⟨?_, ?_⟩
      · simpa [CriticalZeros, zetaNontrivialZeros] using hρz
      · show |ρ.im| ≤ T
        rw [abs_of_pos hρim_pos]
        exact hρle
    simp [positiveZerosBelowDistinct, ZerosBelow, dif_pos hfin, hmem_fin, hρim_pos]

private lemma positiveImZerosBelow_re_half (hRH : RiemannHypothesis') {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow T) : ρ.re = 1 / 2 := by
  exact rh_implies_critical_line (hRH := hRH) ρ (mem_positiveImZerosBelow.mp hρ).1.1

private noncomputable def posInjToZeroOrdinate (hRH : RiemannHypothesis') {T : ℝ}
    (ρ : {ρ : ℂ // ρ ∈ positiveImZerosBelow T}) : ZeroOrdinate := by
  refine ⟨ρ.val.im, ?_⟩
  exact ⟨ρ.val, (mem_positiveImZerosBelow.mp ρ.property).1, rfl⟩

private lemma posInjToZeroOrdinate_injective (hRH : RiemannHypothesis') {T : ℝ} :
    Function.Injective (posInjToZeroOrdinate hRH (T := T)) := by
  intro a b hab
  apply Subtype.ext
  have him : a.val.im = b.val.im := by
    simpa [posInjToZeroOrdinate] using congrArg (fun γ : ZeroOrdinate => (γ : ℝ)) hab
  have hre_a : a.val.re = 1 / 2 := positiveImZerosBelow_re_half hRH a.property
  have hre_b : b.val.re = 1 / 2 := positiveImZerosBelow_re_half hRH b.property
  exact Complex.ext (by simpa [hre_a, hre_b]) (by simpa using him)

private lemma sum_inv_sq_positiveImZerosBelow_le_tsum
    (hRH : RiemannHypothesis') [ZeroCountingSummabilityHyp] (T : ℝ) :
    ∑ ρ ∈ positiveImZerosBelow T, 1 / ρ.im ^ (2 : ℕ) ≤
      ∑' γ : ZeroOrdinate, 1 / ((γ : ℝ) ^ (2 : ℕ)) := by
  classical
  let S : Finset ZeroOrdinate :=
    ((positiveImZerosBelow T).attach.image (fun ρ => posInjToZeroOrdinate hRH ρ))
  have hsum_eq :
      ∑ ρ ∈ positiveImZerosBelow T, 1 / ρ.im ^ (2 : ℕ) =
        Finset.sum S (fun γ => 1 / ((γ : ℝ) ^ (2 : ℕ))) := by
    calc
      ∑ ρ ∈ positiveImZerosBelow T, 1 / ρ.im ^ (2 : ℕ)
        = ∑ ρ ∈ (positiveImZerosBelow T).attach, 1 / ρ.1.im ^ (2 : ℕ) := by
            symm
            simpa using
              (Finset.sum_attach (positiveImZerosBelow T) (fun ρ : ℂ => 1 / ρ.im ^ (2 : ℕ)))
      _ = Finset.sum S (fun γ => 1 / ((γ : ℝ) ^ (2 : ℕ))) := by
            rw [Finset.sum_image]
            · refine Finset.sum_congr rfl ?_
              intro ρ hρ
              simp [S, posInjToZeroOrdinate]
            · intro a _ b _ hab
              exact posInjToZeroOrdinate_injective hRH hab
  have hsumm : Summable (fun γ : ZeroOrdinate => 1 / ((γ : ℝ) ^ (2 : ℕ))) := by
    simpa [Real.rpow_natCast] using
      (summable_inv_gamma_sq : Summable (fun γ : ZeroOrdinate => 1 / (γ : ℝ) ^ (2 : ℝ)))
  have hnonneg : ∀ γ : ZeroOrdinate, 0 ≤ 1 / ((γ : ℝ) ^ (2 : ℕ)) := by
    intro γ
    exact one_div_nonneg.mpr (pow_nonneg (le_of_lt (ZeroOrdinate.pos γ)) _)
  rw [hsum_eq]
  exact hsumm.sum_le_tsum S (fun γ _ => hnonneg γ)

private lemma distinct_kernel_error_bound
    (hRH : RiemannHypothesis')
    [ZeroCountingSummabilityHyp] [ZeroOrdinateLowerBoundHyp]
    (η T : ℝ) :
    |(∑ ρ ∈ positiveImZerosBelow T, (((Real.exp η : ℂ) ^ ρ / ρ).re)) -
        Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)|
      ≤ (Real.exp (η / 2) / 2) * (∑' γ : ZeroOrdinate, 1 / ((γ : ℝ) ^ (2 : ℕ))) := by
  have hsum_sub :
      (∑ ρ ∈ positiveImZerosBelow T, (((Real.exp η : ℂ) ^ ρ / ρ).re)) -
          Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) =
        ∑ ρ ∈ positiveImZerosBelow T,
          ((((Real.exp η : ℂ) ^ ρ / ρ).re) - Real.exp (η / 2) * Real.sin (ρ.im * η) / ρ.im) := by
    rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    ring
  rw [hsum_sub]
  calc
    |∑ ρ ∈ positiveImZerosBelow T,
        (((Real.exp η : ℂ) ^ ρ / ρ).re - Real.exp (η / 2) * Real.sin (ρ.im * η) / ρ.im)|
      ≤ ∑ ρ ∈ positiveImZerosBelow T,
          |(((Real.exp η : ℂ) ^ ρ / ρ).re - Real.exp (η / 2) * Real.sin (ρ.im * η) / ρ.im)| := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ρ ∈ positiveImZerosBelow T, Real.exp (η / 2) / (2 * ρ.im ^ (2 : ℕ)) := by
          refine Finset.sum_le_sum ?_
          intro ρ hρ
          have hρ_half : ρ.re = 1 / 2 := positiveImZerosBelow_re_half hRH hρ
          have hρ_eq : ρ = (1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I := by
            apply Complex.ext <;> simp [hρ_half]
          have hγ : 1 < ρ.im := zero_ord_lower_bound ρ (mem_positiveImZerosBelow.mp hρ).1
          rw [hρ_eq]
          simpa using re_cpow_div_rho_approx ρ.im η hγ
    _ = (Real.exp (η / 2) / 2) * ∑ ρ ∈ positiveImZerosBelow T, 1 / ρ.im ^ (2 : ℕ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro ρ hρ
          have hρim_ne : ρ.im ≠ 0 := (positiveImZerosBelow_im_pos hρ).ne'
          field_simp [hρim_ne]
    _ ≤ (Real.exp (η / 2) / 2) * (∑' γ : ZeroOrdinate, 1 / ((γ : ℝ) ^ (2 : ℕ))) := by
          gcongr
          exact sum_inv_sq_positiveImZerosBelow_le_tsum hRH T

private lemma weighted_correction_eq
    (η T : ℝ) :
    (∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)) -
        abelWeightedZeroSumUpTo T 0 η =
      -∑ ρ ∈ positiveImZerosBelow T,
        (((zeroMultiplicity ρ : ℝ) - 1) * Real.sin (ρ.im * η) / ρ.im) := by
  unfold abelWeightedZeroSumUpTo abelWeightedZeroKernel
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  simp
  ring

private theorem explicitFormulaAbelBound_of_general
    (hRH : RiemannHypothesis') [ExplicitFormulaPsiGeneralHyp]
    [AbelMultiplicityCorrectionBoundHyp] [ZeroCountingSummabilityHyp]
    [ZeroOrdinateLowerBoundHyp] :
    ExplicitFormulaAbelBoundHyp := by
  obtain ⟨C0, hEF0⟩ := ExplicitFormulaPsiGeneralHyp.proof
  obtain ⟨Kcorr, hKcorr_pos, hcorr⟩ := AbelMultiplicityCorrectionBoundHyp.bound
  let Ksq : ℝ := ∑' γ : ZeroOrdinate, 1 / ((γ : ℝ) ^ (2 : ℕ))
  have hKsq_nonneg : 0 ≤ Ksq := by
    dsimp [Ksq]
    exact tsum_nonneg (fun γ => by
      exact one_div_nonneg.mpr (pow_nonneg (le_of_lt (ZeroOrdinate.pos γ)) _))
  let C : ℝ := |C0| + (Ksq + 2 + 2 * Kcorr)
  have hC_pos : 0 < C := by
    dsimp [C]
    nlinarith [abs_nonneg C0, hKsq_nonneg, hKcorr_pos]
  refine ⟨C, hC_pos, ?_⟩
  intro η T hη hT
  let x : ℝ := Real.exp η
  have hx : x ≥ 2 := by
    dsimp [x]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp 1]
    have hη1 : 1 ≤ η := by linarith
    exact le_trans h2 (Real.exp_le_exp.mpr hη1)
  have hx_pos : 0 < x := by
    dsimp [x]
    exact Real.exp_pos η
  have hexp_half : Real.exp (η * (1 / 2)) = Real.exp (η / 2) := by
    congr 1
    ring
  have hbase_nonneg :
      0 ≤ Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) + η ^ 2 := by
    positivity
  have hEF :
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re|
        ≤ |C0| * (Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) + η ^ 2) := by
    have hraw :
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x - (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)|
          ≤ C0 * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) :=
      hEF0 x T hx hT
    have hsqrt_exp : Real.sqrt x = Real.exp (η / 2) := by
      dsimp [x]
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos η), Real.log_exp]
      ring
    have hlog_exp : Real.log x = η := by
      dsimp [x]
      rw [Real.log_exp]
    calc
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re|
        = |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x - (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| := by ring_nf
      _ ≤ C0 * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := hraw
      _ = C0 * (Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T) + η ^ 2) := by
            rw [hsqrt_exp, hlog_exp]
            ring
      _ ≤ |C0| * (Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) + η ^ 2) := by
            have hshape_le :
                Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T) + η ^ 2
                  ≤ Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) + η ^ 2 := by
              have hexp_pos : 0 ≤ Real.exp (η / 2) := (Real.exp_pos _).le
              nlinarith
            have hshape_nonneg' :
                0 ≤ Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T) + η ^ 2 := by
              positivity
            exact le_trans
              (mul_le_mul_of_nonneg_right (le_abs_self C0) hshape_nonneg')
              (mul_le_mul_of_nonneg_left hshape_le (abs_nonneg C0))
  have hpair :
      ∃ R : ℝ, |R| ≤ 2 * Real.exp (η / 2) ∧
        (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re =
          2 * (∑ ρ ∈ positiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re + R := by
    obtain ⟨R, hR, hsum⟩ := zero_sum_conjugate_bound hRH T x hx
    refine ⟨R, ?_, ?_⟩
    ·
      have hsqrt_exp : Real.sqrt x = Real.exp (η / 2) := by
        dsimp [x]
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos η), Real.log_exp]
        ring
      simpa [hsqrt_exp] using hR
    ·
      simpa [positiveZerosBelowDistinct_eq_positiveImZerosBelow hRH T] using hsum
  have hkernel :
      |(∑ ρ ∈ positiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ).re) -
          Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)|
        ≤ (Real.exp (η / 2) / 2) * Ksq := by
    simpa [Ksq, x] using distinct_kernel_error_bound hRH η T
  have hcorr' :
      |(∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)) -
          abelWeightedZeroSumUpTo T 0 η| ≤ Kcorr := by
    rw [weighted_correction_eq, abs_neg]
    exact hcorr η T hη hT
  have hsum_bridge :
      |(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
          2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)|
        ≤ Real.exp (η / 2) * (Ksq + 2) := by
    obtain ⟨R, hR, hpair_eq⟩ := hpair
    have hmid :
        |(∑ ρ ∈ positiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ).re) -
            Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)|
          ≤ Real.exp (η / 2) * (Ksq / 2) := by
      simpa [Ksq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hkernel
    calc
      |(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
          2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)|
          = |2 * ((∑ ρ ∈ positiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ).re) -
                Real.exp (η / 2) *
                  ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)) + R| := by
                have hlin :
                    (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
                        2 * Real.exp (η / 2) *
                          ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) =
                      2 * ((∑ ρ ∈ positiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ).re) -
                        Real.exp (η / 2) *
                          ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)) + R := by
                  rw [hpair_eq]
                  rw [← hexp_half]
                  set A : ℝ := ∑ ρ ∈ positiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ).re
                  set B : ℝ := Real.exp (η * (1 / 2)) *
                    ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)
                  have hlin₁ : 2 * A + R - 2 * B = 2 * A - 2 * B + R := by ring
                  have hlin₂ : 2 * A - 2 * B + R = 2 * (A - B) + R := by ring
                  simpa [A, B, mul_assoc, mul_left_comm, mul_comm] using hlin₁.trans hlin₂
                rw [hlin]
      _ ≤ 2 *
            |(∑ ρ ∈ positiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ).re) -
                Real.exp (η / 2) *
                  ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)| + |R| := by
            calc
              |2 * ((∑ ρ ∈ positiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ).re) -
                  Real.exp (η / 2) *
                    ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)) + R|
                  ≤ |2 * ((∑ ρ ∈ positiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ).re) -
                      Real.exp (η / 2) *
                        ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im))| + |R| :=
                          abs_add_le _ _
              _ = 2 *
                    |(∑ ρ ∈ positiveImZerosBelow T, ((x : ℂ) ^ ρ / ρ).re) -
                        Real.exp (η / 2) *
                          ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)| + |R| := by
                    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (Real.exp (η / 2) * (Ksq / 2)) + 2 * Real.exp (η / 2) := by
            gcongr
      _ = Real.exp (η / 2) * (Ksq + 2) := by ring
  have hcorr_bound :
      |2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
          2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η|
        ≤ 2 * Kcorr * Real.exp (η / 2) := by
    calc
      |2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
          2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η|
          = |(2 * Real.exp (η / 2)) *
              ((∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)) -
                abelWeightedZeroSumUpTo T 0 η)| := by
                ring_nf
      _ = (2 * Real.exp (η / 2)) *
            |(∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)) -
              abelWeightedZeroSumUpTo T 0 η| := by
                rw [abs_mul, abs_of_pos]
                positivity
      _ ≤ (2 * Real.exp (η / 2)) * Kcorr := by
            gcongr
      _ = 2 * Kcorr * Real.exp (η / 2) := by ring
  let base : ℝ := Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) + η ^ 2
  have hbase_ge_exp : Real.exp (η / 2) ≤ base := by
    dsimp [base]
    have hsqrt_pos : 0 < Real.sqrt T := by
      refine Real.sqrt_pos.2 ?_
      linarith
    have hfac_ge_one : 1 ≤ (Real.log T) ^ 2 / Real.sqrt T + 1 := by
      have hterm_nonneg : 0 ≤ (Real.log T) ^ 2 / Real.sqrt T := by
        have : 0 ≤ (Real.log T) ^ 2 := sq_nonneg (Real.log T)
        exact div_nonneg this (Real.sqrt_nonneg _)
      linarith
    have hexp_nonneg : 0 ≤ Real.exp (η / 2) := (Real.exp_pos _).le
    calc
      Real.exp (η / 2) ≤ Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) := by
            nlinarith
      _ ≤ Real.exp (η / 2) * ((Real.log T) ^ 2 / Real.sqrt T + 1) + η ^ 2 := by
            nlinarith [sq_nonneg η]
  have hB :
      |(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
          2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)|
        ≤ (Ksq + 2) * base := by
    have hK_nonneg : 0 ≤ Ksq + 2 := by nlinarith
    calc
      |(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
          2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)|
        ≤ Real.exp (η / 2) * (Ksq + 2) := hsum_bridge
      _ = (Ksq + 2) * Real.exp (η / 2) := by ring
      _ ≤ (Ksq + 2) * base := by gcongr
  have hCcorr :
      |2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
          2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η|
        ≤ (2 * Kcorr) * base := by
    have hK_nonneg : 0 ≤ 2 * Kcorr := by positivity
    calc
      |2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
          2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η|
        ≤ 2 * Kcorr * Real.exp (η / 2) := hcorr_bound
      _ ≤ (2 * Kcorr) * base := by
            gcongr
  have hsplit :
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + 2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η =
        (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re) -
        ((∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
          2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)) -
        (2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
          2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η) := by
    rw [← hexp_half]
    ring
  let U : ℝ :=
    Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x +
      (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re
  let V : ℝ :=
    (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
      2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)
  let W : ℝ :=
    2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
      2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η
  have htri1 : |U - V - W| ≤ |U - V| + |W| := by
    simpa [sub_eq_add_neg, add_assoc] using
      (show |(U - V) + (-W)| ≤ |U - V| + |-W| from abs_add_le (U - V) (-W))
  have htri2 : |U - V| ≤ |U| + |V| := by
    simpa [sub_eq_add_neg] using
      (show |U + (-V)| ≤ |U| + |-V| from abs_add_le U (-V))
  calc
    |_root_.chebyshevPsi (Real.exp η) - Real.exp η + 2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η|
      = |Aristotle.DirichletPhaseAlignment.chebyshevPsi (Real.exp η) - Real.exp η +
          2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η| := by
            rw [← dpa_chebyshevPsi_eq (Real.exp η)]
    _ 
      = |(Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re) -
          ((∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
            2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)) -
          (2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
            2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η)| := by
            rw [hsplit]
    _ ≤ |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re| +
          |(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
            2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)| +
          |2 * Real.exp (η / 2) * ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
            2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η| := by
            calc
              |(Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re) -
                  ((∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
                    2 * Real.exp (η / 2) *
                      ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)) -
                  (2 * Real.exp (η / 2) *
                    ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
                    2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η)|
                  ≤
                    |(Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re) -
                      ((∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
                        2 * Real.exp (η / 2) *
                          ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im))| +
                    |2 * Real.exp (η / 2) *
                      ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
                      2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η| := by
                        simpa [U, V, W] using htri1
              _ ≤ |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re| +
                    |(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ / ρ)).re -
                      2 * Real.exp (η / 2) *
                        ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im)| +
                    |2 * Real.exp (η / 2) *
                      ∑ ρ ∈ positiveImZerosBelow T, (Real.sin (ρ.im * η) / ρ.im) -
                      2 * Real.exp (η / 2) * abelWeightedZeroSumUpTo T 0 η| := by
                        simpa [U, V, W, add_assoc, add_left_comm, add_comm] using
                          add_le_add_right htri2 |W|
    _ ≤ |C0| * base + (Ksq + 2) * base + (2 * Kcorr) * base := by
          exact add_le_add (add_le_add hEF hB) hCcorr
    _ = C * base := by
          dsimp [C, base]
          ring

/-- Honest B5a-to-Abel bridge: the remaining analytic content is now isolated in
the uniform oscillatory leaf `AbelMultiplicityCorrectionBoundHyp`, while the
conversion from the distinct B5a sum to the multiplicity-weighted Abel surface
is proved here. In particular, this bridge does not route through the weaker
zero-counting gap leaf `NmultNGapBoundHyp`. -/
theorem explicitFormulaAbelBoundHyp_of_general (hRH : RiemannHypothesis')
    [ExplicitFormulaPsiGeneralHyp] [AbelMultiplicityCorrectionBoundHyp]
    [ZeroCountingSummabilityHyp] [ZeroOrdinateLowerBoundHyp] :
    ExplicitFormulaAbelBoundHyp :=
  explicitFormulaAbelBound_of_general hRH

end Littlewood.Classical
