import Littlewood.Aristotle.Standalone.RHPiPerronTruncatedWitness
import Littlewood.Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
import Littlewood.Bridge.PiLiDirectOscillation

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge

open Filter Complex ZetaZeros
open GrowthDomination
open scoped ComplexConjugate
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiPerronTruncatedWitness
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
open PiLiDirectOscillationBridge

/-- Honest replacement surface for the Perron-threshold phase/seed chain.

It is exactly the fixed-height eventual `sqrt/log` error bound consumed by
`perronThreshold`; unlike `TruncatedExplicitFormulaPiHyp`, it does not expose
the false arbitrary-finite-set `pi_approx` field. -/
class PerronSqrtErrorEventuallyAtHeightHyp : Prop where
  witness :
    ∀ (hRH : ZetaZeros.RiemannHypothesis) (T : ℝ),
      ∀ᶠ x in atTop,
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
          ≤ Real.sqrt x / Real.log x

private lemma mem_zero_finset_nontrivial
    {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (finite_zeros_le T).toFinset) :
    ρ ∈ zetaNontrivialZeros := by
  have hz : ρ ∈ zerosUpTo T := by
    simpa using hρ
  have hz' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hz
  exact (mem_zetaNontrivialZerosPos.1 hz'.1).1

private lemma mem_zero_finset_im_pos
    {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (finite_zeros_le T).toFinset) :
    0 < ρ.im := by
  have hz : ρ ∈ zerosUpTo T := by
    simpa using hρ
  have hz' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hz
  exact (mem_zetaNontrivialZerosPos.1 hz'.1).2

private lemma term_re_conj_eq
    {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    (((x : ℂ) ^ (conj ρ)) / (conj ρ)).re = (((x : ℂ) ^ ρ) / ρ).re := by
  have harg : ((x : ℂ).arg) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt hx)]
    simpa [ne_comm] using Real.pi_ne_zero
  have hcpow : (x : ℂ) ^ (conj ρ) = conj ((x : ℂ) ^ ρ) := by
    simpa [Complex.conj_ofReal] using Complex.cpow_conj (x := (x : ℂ)) (n := ρ) harg
  have hdiv :
      (conj ((x : ℂ) ^ ρ)) / (conj ρ) = conj (((x : ℂ) ^ ρ) / ρ) := by
    simpa using (RCLike.conj_div (K := ℂ) (x := ((x : ℂ) ^ ρ)) (y := ρ))
  calc
    (((x : ℂ) ^ (conj ρ)) / (conj ρ)).re
        = (conj (((x : ℂ) ^ ρ) / ρ)).re := by
            rw [hcpow, hdiv]
    _ = (((x : ℂ) ^ ρ) / ρ).re := by
          simpa using (Complex.conj_re (((x : ℂ) ^ ρ) / ρ))

/--
For fixed finite-zero height `T`, derive a Perron-style `sqrt/log` explicit-formula
error witness in the canonical project shape `piMainFromZeros ((finite_zeros_le T).toFinset)`.
-/
theorem perron_sqrt_error_at_fixed_height_of_truncatedPiBridge
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    {T : ℝ} (X : ℝ) :
    ∃ x : ℝ, X < x ∧
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ Real.sqrt x / Real.log x := by
  let Spos : Finset ℂ := (finite_zeros_le T).toFinset
  let Sneg : Finset ℂ := Spos.image conj
  have hdisj : Disjoint Spos Sneg := by
    refine Finset.disjoint_left.2 ?_
    intro ρ hρpos hρneg
    rcases Finset.mem_image.1 hρneg with ⟨ρ0, hρ0, hρeq⟩
    have hρ_im_pos : 0 < ρ.im := mem_zero_finset_im_pos (T := T) hρpos
    have hρ0_im_pos : 0 < ρ0.im := mem_zero_finset_im_pos (T := T) hρ0
    have hρ_im_neg : ρ.im < 0 := by
      rw [← hρeq, Complex.conj_im]
      linarith
    exact (not_lt_of_ge (le_of_lt hρ_im_pos)) hρ_im_neg
  let Sfull : Finset ℂ := Spos.disjUnion Sneg hdisj

  have hSfull : ∀ ρ ∈ Sfull, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    have hmem : ρ ∈ Spos ∨ ρ ∈ Sneg := by
      simpa [Sfull] using (Finset.mem_disjUnion.1 hρ)
    rcases hmem with hρS | hρS
    · refine ⟨mem_zero_finset_nontrivial (T := T) hρS, ?_⟩
      exact hRH ρ (mem_zero_finset_nontrivial (T := T) hρS)
    · rcases Finset.mem_image.1 hρS with ⟨ρ0, hρ0S, rfl⟩
      have hρ0 : ρ0 ∈ zetaNontrivialZeros :=
        mem_zero_finset_nontrivial (T := T) hρ0S
      refine ⟨zero_conj_zero hρ0, ?_⟩
      simpa using hRH ρ0 hρ0

  have h_approx_full :
      ∀ᶠ x in atTop,
        |piLiErr x + ((∑ ρ ∈ Sfull, (x : ℂ) ^ ρ / ρ).re) / Real.log x|
          ≤ (1 : ℝ) * (Real.sqrt x / Real.log x) :=
    TruncatedExplicitFormulaPiHyp.pi_approx Sfull hSfull 1 zero_lt_one

  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 h_approx_full
  let x : ℝ := max (max X B) (Real.exp 1) + 1
  have hXx : X < x := by
    dsimp [x]
    linarith [le_max_left X B, le_max_left (max X B) (Real.exp 1)]
  have hBx : B ≤ x := by
    dsimp [x]
    linarith [le_max_right X B, le_max_left (max X B) (Real.exp 1)]
  have hx1 : 1 < x := by
    dsimp [x]
    have h_exp1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith [le_max_right (max X B) (Real.exp 1), h_exp1]

  have hx_pos : 0 < x := lt_trans zero_lt_one hx1
  have h_sum_image :
      (∑ ρ ∈ Sneg, (((x : ℂ) ^ ρ) / ρ).re)
        = (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) := by
    classical
    have h_image :
        (∑ ρ ∈ Sneg, (((x : ℂ) ^ ρ) / ρ).re)
          = (∑ ρ ∈ Spos, (((x : ℂ) ^ (conj ρ)) / (conj ρ)).re) := by
      unfold Sneg
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact star_injective hab
    calc
      (∑ ρ ∈ Sneg, (((x : ℂ) ^ ρ) / ρ).re)
          = (∑ ρ ∈ Spos, (((x : ℂ) ^ (conj ρ)) / (conj ρ)).re) := h_image
      _ = (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) := by
            refine Finset.sum_congr rfl ?_
            intro ρ hρ
            exact term_re_conj_eq hx_pos ρ

  have h_sum_full :
      ((∑ ρ ∈ Sfull, (x : ℂ) ^ ρ / ρ).re)
        = (2 * (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re)) := by
    have h_split :
        (∑ ρ ∈ Sfull, (x : ℂ) ^ ρ / ρ)
          = (∑ ρ ∈ Spos, (x : ℂ) ^ ρ / ρ) +
            (∑ ρ ∈ Sneg, (x : ℂ) ^ ρ / ρ) := by
      unfold Sfull
      simpa using (Finset.sum_disjUnion (s₁ := Spos) (s₂ := Sneg)
        (f := fun ρ : ℂ => (x : ℂ) ^ ρ / ρ) hdisj)
    have h_split_re :
        ((∑ ρ ∈ Sfull, (x : ℂ) ^ ρ / ρ).re)
          = (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) +
            (∑ ρ ∈ Sneg, (((x : ℂ) ^ ρ) / ρ).re) := by
      rw [h_split, Complex.add_re]
      simp
    calc
      ((∑ ρ ∈ Sfull, (x : ℂ) ^ ρ / ρ).re)
          = (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) +
              (∑ ρ ∈ Sneg, (((x : ℂ) ^ ρ) / ρ).re) := h_split_re
      _ = (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) +
            (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) := by rw [h_sum_image]
      _ = 2 * (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) := by ring

  have h_err_full := hB x hBx
  have h_err_pos :
      |piLiErr x + (2 * (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re)) / Real.log x|
        ≤ Real.sqrt x / Real.log x := by
    simpa [h_sum_full] using h_err_full

  refine ⟨x, hXx, hx1, ?_⟩
  simpa [piMainFromZeros, Spos, mul_assoc, mul_comm, mul_left_comm] using h_err_pos

/--
Height-parameterized form of `perron_sqrt_error_at_fixed_height_of_truncatedPiBridge`.
Kept explicit in `T` for downstream constructions that must synchronize the
zero cutoff with other RH-side witnesses.
-/
theorem perron_sqrt_error_at_height_of_truncatedPiBridge
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (T : ℝ) (X : ℝ) :
    ∃ x : ℝ, X < x ∧
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ Real.sqrt x / Real.log x := by
  simpa using
    (perron_sqrt_error_at_fixed_height_of_truncatedPiBridge
      (hRH := hRH) (T := T) X)

/--
Frequent fixed-height Perron witness at `sqrt/log` scale.

This is the filter-form companion to the existential `∀ X` statement and is often
the right form for intersecting with eventual side conditions.
-/
theorem perron_sqrt_error_frequently_at_height_of_truncatedPiBridge
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (T : ℝ) :
    ∃ᶠ x in atTop,
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ Real.sqrt x / Real.log x := by
  rw [Filter.frequently_atTop]
  intro X
  rcases perron_sqrt_error_at_height_of_truncatedPiBridge hRH T X with
    ⟨x, hXx, hx1, herr⟩
  exact ⟨x, le_of_lt hXx, hx1, herr⟩

/--
Eventual fixed-height Perron witness at `sqrt/log` scale.

This strengthens the `∃ x > X` form to an eventual-in-`x` statement at each
fixed cutoff `T`, in the project's canonical `piMainFromZeros` shape.
-/
theorem perron_sqrt_error_eventually_at_height_of_truncatedPiBridge
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (T : ℝ) :
    ∀ᶠ x in atTop,
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ Real.sqrt x / Real.log x := by
  let Spos : Finset ℂ := (finite_zeros_le T).toFinset
  let Sneg : Finset ℂ := Spos.image conj
  have hdisj : Disjoint Spos Sneg := by
    refine Finset.disjoint_left.2 ?_
    intro ρ hρpos hρneg
    rcases Finset.mem_image.1 hρneg with ⟨ρ0, hρ0, hρeq⟩
    have hρ_im_pos : 0 < ρ.im := mem_zero_finset_im_pos (T := T) hρpos
    have hρ_im_neg : ρ.im < 0 := by
      rw [← hρeq, Complex.conj_im]
      have hρ0_im_pos : 0 < ρ0.im := mem_zero_finset_im_pos (T := T) hρ0
      linarith
    exact (not_lt_of_ge (le_of_lt hρ_im_pos)) hρ_im_neg
  let Sfull : Finset ℂ := Spos.disjUnion Sneg hdisj

  have hSfull : ∀ ρ ∈ Sfull, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    have hmem : ρ ∈ Spos ∨ ρ ∈ Sneg := by
      simpa [Sfull] using (Finset.mem_disjUnion.1 hρ)
    rcases hmem with hρS | hρS
    · refine ⟨mem_zero_finset_nontrivial (T := T) hρS, ?_⟩
      exact hRH ρ (mem_zero_finset_nontrivial (T := T) hρS)
    · rcases Finset.mem_image.1 hρS with ⟨ρ0, hρ0S, rfl⟩
      have hρ0 : ρ0 ∈ zetaNontrivialZeros :=
        mem_zero_finset_nontrivial (T := T) hρ0S
      refine ⟨zero_conj_zero hρ0, ?_⟩
      simpa using hRH ρ0 hρ0

  have h_approx_full :
      ∀ᶠ x in atTop,
        |piLiErr x + ((∑ ρ ∈ Sfull, (x : ℂ) ^ ρ / ρ).re) / Real.log x|
          ≤ (1 : ℝ) * (Real.sqrt x / Real.log x) :=
    TruncatedExplicitFormulaPiHyp.pi_approx Sfull hSfull 1 zero_lt_one

  filter_upwards [h_approx_full, eventually_ge_atTop (Real.exp 1)] with x h_err_full hxexp
  have h_exp1_gt_one : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hx1 : 1 < x := lt_of_lt_of_le h_exp1_gt_one hxexp
  have hx_pos : 0 < x := lt_trans zero_lt_one hx1

  have h_sum_image :
      (∑ ρ ∈ Sneg, (((x : ℂ) ^ ρ) / ρ).re)
        = (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) := by
    classical
    have h_image :
        (∑ ρ ∈ Sneg, (((x : ℂ) ^ ρ) / ρ).re)
          = (∑ ρ ∈ Spos, (((x : ℂ) ^ (conj ρ)) / (conj ρ)).re) := by
      unfold Sneg
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact star_injective hab
    calc
      (∑ ρ ∈ Sneg, (((x : ℂ) ^ ρ) / ρ).re)
          = (∑ ρ ∈ Spos, (((x : ℂ) ^ (conj ρ)) / (conj ρ)).re) := h_image
      _ = (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) := by
            refine Finset.sum_congr rfl ?_
            intro ρ hρ
            exact term_re_conj_eq hx_pos ρ

  have h_sum_full :
      ((∑ ρ ∈ Sfull, (x : ℂ) ^ ρ / ρ).re)
        = (2 * (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re)) := by
    have h_split :
        (∑ ρ ∈ Sfull, (x : ℂ) ^ ρ / ρ)
          = (∑ ρ ∈ Spos, (x : ℂ) ^ ρ / ρ) +
            (∑ ρ ∈ Sneg, (x : ℂ) ^ ρ / ρ) := by
      unfold Sfull
      simpa using (Finset.sum_disjUnion (s₁ := Spos) (s₂ := Sneg)
        (f := fun ρ : ℂ => (x : ℂ) ^ ρ / ρ) hdisj)
    have h_split_re :
        ((∑ ρ ∈ Sfull, (x : ℂ) ^ ρ / ρ).re)
          = (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) +
            (∑ ρ ∈ Sneg, (((x : ℂ) ^ ρ) / ρ).re) := by
      rw [h_split, Complex.add_re]
      simp
    calc
      ((∑ ρ ∈ Sfull, (x : ℂ) ^ ρ / ρ).re)
          = (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) +
              (∑ ρ ∈ Sneg, (((x : ℂ) ^ ρ) / ρ).re) := h_split_re
      _ = (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) +
            (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) := by rw [h_sum_image]
      _ = 2 * (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re) := by ring

  have h_err_pos :
      |piLiErr x + (2 * (∑ ρ ∈ Spos, (((x : ℂ) ^ ρ) / ρ).re)) / Real.log x|
        ≤ Real.sqrt x / Real.log x := by
    simpa [h_sum_full] using h_err_full

  refine ⟨hx1, ?_⟩
  simpa [piMainFromZeros, Spos, mul_assoc, mul_comm, mul_left_comm] using h_err_pos

/-- Compatibility instance for legacy consumers: the old truncated-π bridge
implies the honest fixed-height Perron error interface. This is the only local
bridge from the false `pi_approx` field to the repaired threshold surface. -/
instance perronSqrtErrorEventuallyAtHeightHyp_of_truncatedPiBridge
    [TruncatedExplicitFormulaPiHyp] : PerronSqrtErrorEventuallyAtHeightHyp where
  witness := perron_sqrt_error_eventually_at_height_of_truncatedPiBridge

/--
Eventual fixed-height Perron witness at Littlewood's `piScale`.

This is the `sqrt/log` eventual bound upgraded via eventual `lll x ≥ 1`.
-/
theorem perron_piScale_error_eventually_at_height_of_truncatedPiBridge
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (T : ℝ) :
    ∀ᶠ x in atTop,
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ piScale x := by
  filter_upwards
    [perron_sqrt_error_eventually_at_height_of_truncatedPiBridge hRH T, lll_eventually_ge_one]
    with x hx hlll
  rcases hx with ⟨hx1, herr⟩
  exact ⟨hx1, sqrt_error_le_piScale_of_lll_ge_one hx1 hlll herr⟩

/--
Existential fixed-height Perron witness at Littlewood's `piScale`.

For every threshold `X`, one can choose `x > X` at the same fixed height `T`
with explicit-formula error bounded by `piScale`.
-/
theorem perron_piScale_error_at_height_of_truncatedPiBridge
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (T : ℝ) (X : ℝ) :
    ∃ x : ℝ, X < x ∧
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ piScale x := by
  rcases (Filter.eventually_atTop.1
      (perron_piScale_error_eventually_at_height_of_truncatedPiBridge hRH T)) with
    ⟨B, hB⟩
  let x : ℝ := max X B + 1
  have hB_le : B ≤ x := by
    dsimp [x]
    linarith [le_max_right X B]
  have hx_data : 1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x :=
    hB x hB_le
  refine ⟨x, ?_, hx_data.1, hx_data.2⟩
  dsimp [x]
  linarith [le_max_left X B]

/--
Frequent fixed-height Perron witness at Littlewood's `piScale`.
-/
theorem perron_piScale_error_frequently_at_height_of_truncatedPiBridge
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (T : ℝ) :
    ∃ᶠ x in atTop,
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ piScale x := by
  rw [Filter.frequently_atTop]
  intro X
  rcases perron_piScale_error_at_height_of_truncatedPiBridge hRH T X with
    ⟨x, hXx, hx1, herr⟩
  exact ⟨x, le_of_lt hXx, hx1, herr⟩

/--
From a truncated-explicit-formula bridge hypothesis for `π-li`, derive the RH
Perron-style `sqrt/log` witness family used by the standalone Blocker-7 chain.

This theorem is fully proved (no `sorry`, no axioms): it upgrades the bridge
formula on a conjugation-closed finite zero set to the project's canonical
`finite_zeros_le T`/`piMainFromZeros` shape.
-/
theorem perron_sqrt_error_family_of_truncatedPiBridge
    [TruncatedExplicitFormulaPiHyp] :
    PerronSqrtErrorThresholdFamily := by
  intro hRH X
  rcases perron_sqrt_error_at_fixed_height_of_truncatedPiBridge
      (hRH := hRH) (T := 4) X with ⟨x, hXx, hx1, herr⟩
  refine ⟨x, hXx, (4 : ℝ), by norm_num, hx1, ?_⟩
  simpa using herr

/-- Instance form: the bridge-level truncated π explicit-formula hypothesis
supplies the Perron `sqrt/log` threshold family used by the standalone RH-π
chain. -/
instance perronSqrtErrorThresholdFamilyHyp_of_truncatedPiBridge
    [TruncatedExplicitFormulaPiHyp] : PerronSqrtErrorThresholdFamilyHyp where
  witness := perron_sqrt_error_family_of_truncatedPiBridge

end Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
