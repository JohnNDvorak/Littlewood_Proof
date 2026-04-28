import Littlewood.Aristotle.AbelSummation
import Littlewood.ZetaZeros.DistinctMultiplicityCompatibility
import Littlewood.ZetaZeros.ZeroCountingAssumptions

/-!
# Abel multiplicity correction

This recovers the former constructive proof of the uniform oscillatory
multiplicity-correction bound, adapted to the current theorem-first
distinct-versus-multiplicity infrastructure.

The old source depended on a removed placeholder module and a removed
`ZeroCountingMultiplicityExcessLogBoundHyp` class. This file keeps the useful
proof, reintroduces only the focused local class surface, and connects it to the
current `XiDerivZeroCountRectMultBoundFrom14Hyp` route when that hypothesis is
available.
-/

set_option maxHeartbeats 1600000
set_option autoImplicit false

noncomputable section

namespace ZetaZeros

open scoped BigOperators Real

/-- Focused theorem-class surface for logarithmic control of excess
multiplicity. This is a compatibility surface for recovered Abel-correction
infrastructure; the current repo exposes the main content theorem-first through
`distinct_mult_compatibility_bound_iff_excess_bound`. -/
class ZeroCountingMultiplicityExcessLogBoundHyp : Prop where
  bound :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀,
      (zeroCountingMultiplicityExcess T : ℝ) ≤ C * Real.log T

theorem zeroCountingMultiplicityExcess_log_bound
    [ZeroCountingMultiplicityExcessLogBoundHyp] :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀,
      (zeroCountingMultiplicityExcess T : ℝ) ≤ C * Real.log T :=
  ZeroCountingMultiplicityExcessLogBoundHyp.bound

/-- The current `ξ'` rectangle-count route supplies the recovered logarithmic
excess-multiplicity class. -/
instance (priority := 90)
    [XiDerivZeroCountRectMultBoundFrom14Hyp] :
    ZeroCountingMultiplicityExcessLogBoundHyp where
  bound := by
    have hcompat :=
      distinct_mult_compatibility_bound_of_xiDerivZeroCountRectMultBoundFrom14Hyp
    rcases (distinct_mult_compatibility_bound_iff_excess_bound 14).mp hcompat with ⟨C, hC⟩
    exact ⟨C, 14, hC⟩

end ZetaZeros

namespace Littlewood.Classical

open scoped BigOperators Real
open ZetaZeros

/-- Distinct positive-imaginary zeta zeros up to height `T`. Multiplicity is
attached separately via `zeroMultiplicity`. -/
noncomputable def positiveImZerosBelow (T : ℝ) : Finset ℂ :=
  (finite_zeros_le T).toFinset

/-- Multiplicity of a zeta zero, encoded by analytic order. -/
noncomputable def zeroMultiplicity (ρ : ℂ) : ℕ :=
  (analyticOrderAt riemannZeta ρ).toNat

lemma mem_positiveImZerosBelow {T : ℝ} {ρ : ℂ} :
    ρ ∈ positiveImZerosBelow T ↔ ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
  simp [positiveImZerosBelow, zerosUpTo, Set.Finite.mem_toFinset]

lemma positiveImZerosBelow_im_pos {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow T) : 0 < ρ.im := by
  rcases mem_positiveImZerosBelow.mp hρ with ⟨hρ_pos, _⟩
  exact (mem_zetaNontrivialZerosPos.mp hρ_pos).2

lemma positiveImZerosBelow_im_le {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow T) : ρ.im ≤ T :=
  (mem_positiveImZerosBelow.mp hρ).2

/-- Focused uniform oscillatory multiplicity-correction leaf for the B5a-to-Abel
bridge. This is a ψ-lane leaf; it is stronger than logarithmic control of
`Nmult - N` alone. -/
class AbelMultiplicityCorrectionBoundHyp : Prop where
  bound :
    ∃ K > 0, ∀ η T : ℝ, η ≥ 2 → T ≥ 2 →
      |∑ ρ ∈ positiveImZerosBelow T,
          (((zeroMultiplicity ρ : ℝ) - 1) * Real.sin (ρ.im * η) / ρ.im)| ≤ K

/-! ### Local multiplicity helpers -/

private lemma positiveImZerosBelow_subset_of_le' {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    positiveImZerosBelow T₁ ⊆ positiveImZerosBelow T₂ := by
  intro ρ hρ
  rcases mem_positiveImZerosBelow.mp hρ with ⟨hρzero, hρle⟩
  exact mem_positiveImZerosBelow.mpr ⟨hρzero, hρle.trans hT⟩

private lemma one_le_zeroMultiplicity' {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow T) :
    1 ≤ zeroMultiplicity ρ := by
  rcases mem_positiveImZerosBelow.mp hρ with ⟨hρ_pos, _⟩
  rcases ZetaZeros.mem_zetaNontrivialZerosPos.mp hρ_pos with ⟨hzeta, _⟩
  rcases ZetaZeros.mem_zetaNontrivialZeros.mp hzeta with ⟨hzero, _, hre_lt⟩
  have hρ_ne_one : ρ ≠ 1 := by
    intro h1
    rw [h1] at hre_lt
    norm_num at hre_lt
  rcases Aristotle.ZetaLogDerivInfra.zeta_analytic_order_finite_pos ρ hzero hρ_ne_one with
    ⟨n, hn, horder⟩
  simpa [zeroMultiplicity, horder] using Nat.succ_le_of_lt hn

private lemma mult_sub_one_nonneg {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow T) :
    0 ≤ (zeroMultiplicity ρ : ℝ) - 1 :=
  sub_nonneg.mpr (by exact_mod_cast one_le_zeroMultiplicity' hρ)

private lemma sum_mult_sub_one_eq_excess (T : ℝ) :
    ∑ ρ ∈ positiveImZerosBelow T, ((zeroMultiplicity ρ : ℝ) - 1) =
      (ZetaZeros.zeroCountingMultiplicityExcess T : ℝ) := by
  calc ∑ ρ ∈ positiveImZerosBelow T, ((zeroMultiplicity ρ : ℝ) - 1)
      = ∑ ρ ∈ positiveImZerosBelow T, (((zeroMultiplicity ρ - 1 : ℕ) : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro ρ hρ
          rw [Nat.cast_sub (one_le_zeroMultiplicity' hρ), Nat.cast_one]
    _ = (ZetaZeros.zeroCountingMultiplicityExcess T : ℝ) := by
          simp only [positiveImZerosBelow, zeroMultiplicity]
          exact_mod_cast (ZetaZeros.zeroCountingMultiplicityExcess_eq_sum T).symm

private lemma excess_nonneg (T : ℝ) :
    0 ≤ (ZetaZeros.zeroCountingMultiplicityExcess T : ℝ) :=
  Nat.cast_nonneg _

/-! ### Oscillatory correction bound -/

private lemma abs_sum_mul_sin_div_le (T η : ℝ) :
    |∑ ρ ∈ positiveImZerosBelow T,
        (((zeroMultiplicity ρ : ℝ) - 1) * Real.sin (ρ.im * η) / ρ.im)|
    ≤ ∑ ρ ∈ positiveImZerosBelow T, ((zeroMultiplicity ρ : ℝ) - 1) / ρ.im := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  have hm := mult_sub_one_nonneg hρ
  have hγ := positiveImZerosBelow_im_pos hρ
  rw [abs_div, abs_mul, abs_of_nonneg hm, abs_of_nonneg hγ.le]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right hm (Real.abs_sin_le_one _)) hγ.le

private lemma im_gt_one'
    {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ positiveImZerosBelow T) : (1 : ℝ) < ρ.im :=
  zero_ord_lower_bound ρ (mem_positiveImZerosBelow.mp hρ).1

private lemma excess_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    (ZetaZeros.zeroCountingMultiplicityExcess T₁ : ℝ) ≤
      (ZetaZeros.zeroCountingMultiplicityExcess T₂ : ℝ) := by
  rw [← sum_mult_sub_one_eq_excess, ← sum_mult_sub_one_eq_excess]
  exact Finset.sum_le_sum_of_subset_of_nonneg (positiveImZerosBelow_subset_of_le' h)
    (fun ρ hρ _ => mult_sub_one_nonneg hρ)

private lemma excess_le_gap
    [ZetaZeros.ZeroCountingMultiplicityExcessLogBoundHyp] :
    ∃ Cg T₀ : ℝ, ∀ T ≥ T₀,
      (ZetaZeros.zeroCountingMultiplicityExcess T : ℝ) ≤ Cg * Real.log T := by
  exact ZetaZeros.zeroCountingMultiplicityExcess_log_bound

private lemma excess_bound_all
    [ZetaZeros.ZeroCountingMultiplicityExcessLogBoundHyp] :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (ZetaZeros.zeroCountingMultiplicityExcess (n : ℝ) : ℝ) ≤
        C * (1 + Real.log ((n : ℝ) + 1)) := by
  rcases excess_le_gap with ⟨Cg, T₀, hgap⟩
  set M := Nat.ceil (max T₀ 2) + 1
  set EM := (ZetaZeros.zeroCountingMultiplicityExcess (M : ℝ) : ℝ)
  set C₀ := max (max (|Cg| + 1) (EM + 1)) 1
  have hC₀ : 0 < C₀ := by positivity
  refine ⟨C₀, hC₀, fun n => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_pos n
  have hlog_nn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hn1
  by_cases hn : T₀ ≤ (n : ℝ)
  · have h_gap := hgap _ hn
    have habs : 0 ≤ |Cg| := abs_nonneg Cg
    have h_le_abs_log : Cg * Real.log (n : ℝ) ≤ |Cg| * Real.log ((n : ℝ) + 1) := by
      rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn_pos
      · simp
      · exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (Real.log_nonneg (by exact_mod_cast hn_pos)))
          (mul_le_mul_of_nonneg_left
            (Real.log_le_log (by exact_mod_cast hn_pos) (by linarith)) habs)
    calc (ZetaZeros.zeroCountingMultiplicityExcess (n : ℝ) : ℝ)
        ≤ Cg * Real.log (n : ℝ) := h_gap
      _ ≤ |Cg| * Real.log ((n : ℝ) + 1) := h_le_abs_log
      _ ≤ (|Cg| + 1) * (1 + Real.log ((n : ℝ) + 1)) := by
          calc |Cg| * Real.log (↑n + 1)
              ≤ |Cg| * Real.log (↑n + 1) + (|Cg| + 1 + Real.log (↑n + 1)) := by
                  linarith
            _ = (|Cg| + 1) * (1 + Real.log (↑n + 1)) := by ring
      _ ≤ C₀ * (1 + Real.log ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right
            (le_trans (le_max_left _ _) (le_max_left _ _)) (by linarith)
  · push_neg at hn
    have hn_le_M : n ≤ M := by
      have hlt : (n : ℝ) < max T₀ 2 := lt_of_lt_of_le hn (le_max_left _ _)
      have hle : (n : ℝ) ≤ ↑(Nat.ceil (max T₀ 2)) := le_trans (le_of_lt hlt) (Nat.le_ceil _)
      have : n ≤ Nat.ceil (max T₀ 2) := by exact_mod_cast hle
      omega
    calc (ZetaZeros.zeroCountingMultiplicityExcess (n : ℝ) : ℝ)
        ≤ EM := excess_mono (by exact_mod_cast hn_le_M)
      _ ≤ EM + 1 := by linarith
      _ ≤ C₀ := le_trans (le_max_right _ _) (le_max_left _ _)
      _ ≤ C₀ * (1 + Real.log ((n : ℝ) + 1)) :=
          le_mul_of_one_le_right hC₀.le (by linarith)

private lemma ceil_shell_excess_le' (T : ℝ) {m : ℕ} (hm2 : 2 ≤ m) :
    ∑ ρ ∈ positiveImZerosBelow T with Nat.ceil ρ.im = m, ((zeroMultiplicity ρ : ℝ) - 1)
      ≤ (ZetaZeros.zeroCountingMultiplicityExcess (m : ℝ) : ℝ) -
        (ZetaZeros.zeroCountingMultiplicityExcess (((m - 1 : ℕ) : ℝ)) : ℝ) := by
  let sbig := positiveImZerosBelow (m : ℝ)
  let ssmall := positiveImZerosBelow (((m - 1 : ℕ) : ℝ))
  have hsubset : (positiveImZerosBelow T).filter (fun ρ => Nat.ceil ρ.im = m) ⊆ sbig \ ssmall := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    rcases hρ with ⟨hρT, hceil⟩
    rcases mem_positiveImZerosBelow.mp hρT with ⟨hρzero, _⟩
    refine Finset.mem_sdiff.mpr ⟨mem_positiveImZerosBelow.mpr ⟨hρzero, ?_⟩, ?_⟩
    · simpa [hceil] using Nat.le_ceil ρ.im
    · intro hρs
      linarith [positiveImZerosBelow_im_le hρs, show (((m - 1 : ℕ) : ℝ)) < ρ.im from by
        simpa using Nat.lt_ceil.mp (by simpa [hceil] using show m - 1 < m by omega)]
  have hsubset_big : ssmall ⊆ sbig :=
    positiveImZerosBelow_subset_of_le' (by exact_mod_cast Nat.sub_le m 1)
  calc ∑ ρ ∈ positiveImZerosBelow T with Nat.ceil ρ.im = m, ((zeroMultiplicity ρ : ℝ) - 1)
      ≤ (sbig \ ssmall).sum (fun ρ => ((zeroMultiplicity ρ : ℝ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun ρ hρ _ => mult_sub_one_nonneg ((Finset.mem_sdiff.mp hρ).1))
    _ = _ := by
        dsimp [sbig, ssmall]
        linarith [Finset.sum_sdiff hsubset_big
            (f := fun ρ : ℂ => ((zeroMultiplicity ρ : ℝ) - 1)),
          sum_mult_sub_one_eq_excess (m : ℝ),
          sum_mult_sub_one_eq_excess (((m - 1 : ℕ) : ℝ))]

private lemma abel_Icc_le (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n) (Nval : ℕ) (hNv : 2 ≤ Nval) :
    ∑ n ∈ Finset.Icc 2 Nval, (E n - E (n - 1)) / ((n : ℝ) - 1) ≤
      E Nval / ((Nval : ℝ) - 1) +
        ∑ n ∈ Finset.Icc 2 (Nval - 1), E n / ((n : ℝ) * ((n : ℝ) - 1)) := by
  induction Nval with
  | zero => omega
  | succ Ni ih =>
    by_cases hN2 : Ni + 1 = 2
    · have hNi1 : Ni = 1 := by omega
      subst hNi1
      simp [Finset.Icc_self, show (2 : ℕ) - 1 = 1 from rfl]
      linarith [hE 1]
    · have hNge2 : 2 ≤ Ni := by omega
      have hNpos : (0 : ℝ) < (Ni : ℝ) := by positivity
      have hNm1 : (0 : ℝ) < (Ni : ℝ) - 1 := by
        have : (1 : ℝ) < (Ni : ℝ) := by exact_mod_cast show 1 < Ni by omega
        linarith
      have hLHS : ∑ n ∈ Finset.Icc 2 (Ni + 1), (E n - E (n - 1)) / ((n : ℝ) - 1) =
          (E (Ni + 1) - E Ni) / (Ni : ℝ) +
          ∑ n ∈ Finset.Icc 2 Ni, (E n - E (n - 1)) / ((n : ℝ) - 1) := by
        have hins : Finset.Icc 2 (Ni + 1) = insert (Ni + 1) (Finset.Icc 2 Ni) := by
          ext x
          simp [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hins, Finset.sum_insert (by simp [Finset.mem_Icc])]
        congr 1
        show (E (Ni + 1) - E (Ni + 1 - 1)) / (↑(Ni + 1) - 1) = _
        simp only [show Ni + 1 - 1 = Ni from rfl]
        congr 1
        push_cast
        ring
      have hRHS_sum : ∑ n ∈ Finset.Icc 2 Ni, E n / ((n : ℝ) * ((n : ℝ) - 1)) =
          E Ni / ((Ni : ℝ) * ((Ni : ℝ) - 1)) +
          ∑ n ∈ Finset.Icc 2 (Ni - 1), E n / ((n : ℝ) * ((n : ℝ) - 1)) := by
        have hins : Finset.Icc 2 Ni = insert Ni (Finset.Icc 2 (Ni - 1)) := by
          ext x
          simp [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hins, Finset.sum_insert (by simp [Finset.mem_Icc]; omega)]
      have hkey : E Ni / ((Ni : ℝ) - 1) + (E (Ni + 1) - E Ni) / (Ni : ℝ) =
          E (Ni + 1) / (Ni : ℝ) + E Ni / ((Ni : ℝ) * ((Ni : ℝ) - 1)) := by
        field_simp
        ring
      rw [hLHS, show Ni + 1 - 1 = Ni from rfl, hRHS_sum,
        show ((Ni + 1 : ℕ) : ℝ) - 1 = (Ni : ℝ) from by push_cast; ring]
      linarith [ih hNge2]

private lemma log_plus_one_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) :
    1 + Real.log x ≤ 2 * Real.sqrt x := by
  have hx_pos : 0 < x := by linarith
  have hsqrt_ge1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  suffices Real.log x ≤ Real.sqrt x from by linarith
  rw [← Real.exp_le_exp]
  calc Real.exp (Real.log x) = x := Real.exp_log hx_pos
    _ = Real.sqrt x ^ 2 := (Real.sq_sqrt hx_pos.le).symm
    _ ≤ Real.exp (Real.sqrt x) := by
        have h4 := Real.sum_le_exp_of_nonneg (Real.sqrt_nonneg x) 4
        simp [Finset.sum_range_succ, Nat.factorial] at h4
        nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt x),
          Real.sq_sqrt hx_pos.le, Real.sqrt_nonneg x]

/-- The partial sums `∑_{γ≤T} (m(ρ)-1)/γ` are uniformly bounded from logarithmic
excess-multiplicity control. -/
private lemma excess_div_im_bounded
    [ZetaZeros.ZeroCountingMultiplicityExcessLogBoundHyp] :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 2 ≤ T →
      ∑ ρ ∈ positiveImZerosBelow T,
        ((zeroMultiplicity ρ : ℝ) - 1) / ρ.im ≤ K := by
  rcases excess_bound_all with ⟨C, hC, hCb⟩
  have h_base : Summable (fun n : ℕ => 1 / (n : ℝ) ^ ((3 : ℝ) / 2)) :=
    Real.summable_one_div_nat_rpow.2 (by norm_num : (1 : ℝ) < 3 / 2)
  have h_shift : Summable (fun k : ℕ => 1 / ((k : ℝ) + 2) ^ ((3 : ℝ) / 2)) :=
    ((summable_nat_add_iff 2).2 h_base).congr (fun k => by push_cast; ring_nf)
  have h_summ : Summable (fun k : ℕ => 8 / ((k : ℝ) + 2) ^ ((3 : ℝ) / 2)) := by
    have := h_shift.mul_left 8
    exact this.congr (fun k => by ring)
  set S := ∑' k : ℕ, 8 / ((k : ℝ) + 2) ^ ((3 : ℝ) / 2)
  set K := C * 3 + C * S + 1
  refine ⟨K, by positivity, fun T hT => ?_⟩
  set E : ℕ → ℝ := fun n => (ZetaZeros.zeroCountingMultiplicityExcess (n : ℝ) : ℝ)
  have hE_nn : ∀ n, 0 ≤ E n := fun n => excess_nonneg _
  set Nval := Nat.ceil T
  have hNge : 2 ≤ Nval := by
    have : 1 < Nat.ceil T := Nat.lt_ceil.mpr (by push_cast; linarith)
    omega
  have hNm1_pos : (0 : ℝ) < (Nval : ℝ) - 1 := by
    have : (1 : ℝ) < (Nval : ℝ) := by exact_mod_cast show 1 < Nval by omega
    linarith
  have h_step1 : ∀ ρ ∈ positiveImZerosBelow T,
      ((zeroMultiplicity ρ : ℝ) - 1) / ρ.im ≤
      ((zeroMultiplicity ρ : ℝ) - 1) / ((Nat.ceil ρ.im : ℝ) - 1) := by
    intro ρ hρ
    have hgt1 := im_gt_one' hρ
    have hceil_sub_pos : (0 : ℝ) < (Nat.ceil ρ.im : ℝ) - 1 := by
      have hceil_ge2 : 2 ≤ Nat.ceil ρ.im := by
        have : 1 < Nat.ceil ρ.im := Nat.lt_ceil.mpr (by push_cast; linarith)
        omega
      have : (1 : ℝ) < (Nat.ceil ρ.im : ℝ) := by exact_mod_cast show 1 < Nat.ceil ρ.im by omega
      linarith
    have hceil_sub_le_im : (Nat.ceil ρ.im : ℝ) - 1 ≤ ρ.im := by
      linarith [Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ ρ.im)]
    exact div_le_div_of_nonneg_left (mult_sub_one_nonneg hρ) hceil_sub_pos hceil_sub_le_im
  have h_maps : ∀ ρ ∈ positiveImZerosBelow T, Nat.ceil ρ.im ∈ Finset.Icc 2 Nval := by
    intro ρ hρ
    rw [Finset.mem_Icc]
    constructor
    · have : 1 < Nat.ceil ρ.im := Nat.lt_ceil.mpr (by push_cast; linarith [im_gt_one' hρ])
      omega
    · exact Nat.ceil_le_ceil (positiveImZerosBelow_im_le hρ)
  have h_fiber_le : ∀ n ∈ Finset.Icc 2 Nval,
      ∑ ρ ∈ (positiveImZerosBelow T).filter (fun ρ => Nat.ceil ρ.im = n),
        ((zeroMultiplicity ρ : ℝ) - 1) / ((Nat.ceil ρ.im : ℝ) - 1) ≤
        (E n - E (n - 1)) / ((n : ℝ) - 1) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast show 1 < n by omega
      linarith
    rw [show ∑ ρ ∈ (positiveImZerosBelow T).filter (fun ρ => Nat.ceil ρ.im = n),
        ((zeroMultiplicity ρ : ℝ) - 1) / ((Nat.ceil ρ.im : ℝ) - 1) =
        (∑ ρ ∈ positiveImZerosBelow T with Nat.ceil ρ.im = n,
          ((zeroMultiplicity ρ : ℝ) - 1)) / ((n : ℝ) - 1) from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun ρ hρ => by
        congr 1
        congr 1
        exact_mod_cast (Finset.mem_filter.mp hρ).2]
    exact div_le_div_of_nonneg_right (ceil_shell_excess_le' T hn2) hn1_pos.le
  have h_fiber_eq := Finset.sum_fiberwise_of_maps_to h_maps
    (fun ρ => ((zeroMultiplicity ρ : ℝ) - 1) / ((Nat.ceil ρ.im : ℝ) - 1))
  have h_shell :
      ∑ ρ ∈ positiveImZerosBelow T, ((zeroMultiplicity ρ : ℝ) - 1) / ρ.im ≤
      ∑ n ∈ Finset.Icc 2 Nval, (E n - E (n - 1)) / ((n : ℝ) - 1) :=
    (Finset.sum_le_sum h_step1).trans (h_fiber_eq ▸ Finset.sum_le_sum h_fiber_le)
  have h_abel := abel_Icc_le E hE_nn Nval hNge
  have h_boundary : E Nval / ((Nval : ℝ) - 1) ≤ C * 3 := by
    rw [div_le_iff₀ hNm1_pos]
    have hlog_le : 1 + Real.log (↑Nval + 1) ≤ (Nval : ℝ) + 1 := by
      have := Real.add_one_le_exp (Real.log (↑Nval + 1))
      rw [Real.exp_log (by linarith : (0 : ℝ) < ↑Nval + 1)] at this
      linarith
    calc E Nval ≤ C * (1 + Real.log (↑Nval + 1)) := hCb Nval
      _ ≤ C * ((Nval : ℝ) + 1) := mul_le_mul_of_nonneg_left hlog_le hC.le
      _ ≤ C * (3 * ((Nval : ℝ) - 1)) := by
          have hNge2_real : (2 : ℝ) ≤ (Nval : ℝ) := by exact_mod_cast hNge
          exact mul_le_mul_of_nonneg_left (by linarith) hC.le
      _ = C * 3 * ((Nval : ℝ) - 1) := by ring
  have h_series : ∑ n ∈ Finset.Icc 2 (Nval - 1),
      E n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ C * S := by
    have h_term : ∀ n ∈ Finset.Icc 2 (Nval - 1),
        E n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ C * (8 / ((n : ℝ)) ^ ((3 : ℝ) / 2)) := by
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_pos : (0 : ℝ) < ↑n := by exact_mod_cast show 0 < n by omega
      have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
        have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast show 1 < n by omega
        linarith
      have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos_of_pos hn_pos
      rw [div_le_iff₀ (mul_pos hn_pos hn1_pos)]
      have hlog_bound : 1 + Real.log (↑n + 1) ≤ 8 * ((n : ℝ) - 1) / Real.sqrt n := by
        rw [le_div_iff₀ hsqrt_pos]
        calc (1 + Real.log (↑n + 1)) * Real.sqrt ↑n
            ≤ 2 * Real.sqrt (↑n + 1) * Real.sqrt ↑n :=
              mul_le_mul_of_nonneg_right
                (log_plus_one_le_two_sqrt (by linarith)) (Real.sqrt_nonneg _)
          _ ≤ 2 * Real.sqrt (2 * ↑n) * Real.sqrt ↑n := by gcongr; linarith
          _ = 2 * (Real.sqrt 2 * Real.sqrt ↑n) * Real.sqrt ↑n := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          _ = 2 * Real.sqrt 2 * ↑n := by
              rw [show 2 * (Real.sqrt 2 * Real.sqrt ↑n) * Real.sqrt ↑n =
                  2 * Real.sqrt 2 * (Real.sqrt ↑n * Real.sqrt ↑n) from by ring,
                Real.mul_self_sqrt hn_pos.le]
          _ ≤ 3 * ↑n := by
              have hsqrt2_le : Real.sqrt 2 ≤ 3 / 2 :=
                (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3 / 2)).mpr (by norm_num)
              nlinarith
          _ ≤ 8 * ((n : ℝ) - 1) := by
              have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
              linarith
      calc E n ≤ C * (1 + Real.log (↑n + 1)) := hCb n
        _ ≤ C * (8 * ((n : ℝ) - 1) / Real.sqrt n) :=
            mul_le_mul_of_nonneg_left hlog_bound hC.le
        _ = C * (8 / ((n : ℝ)) ^ ((3 : ℝ) / 2)) * ((n : ℝ) * ((n : ℝ) - 1)) := by
            rw [show (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * Real.sqrt n from by
              rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 from by norm_num,
                Real.rpow_add hn_pos, Real.rpow_one]]
            field_simp
    calc ∑ n ∈ Finset.Icc 2 (Nval - 1), E n / ((n : ℝ) * ((n : ℝ) - 1))
        ≤ ∑ n ∈ Finset.Icc 2 (Nval - 1), C * (8 / ((n : ℝ)) ^ ((3 : ℝ) / 2)) :=
          Finset.sum_le_sum h_term
      _ ≤ C * S := by
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ hC.le
          set g : ℕ → ℝ := fun k => 8 / ((k : ℝ) + 2) ^ ((3 : ℝ) / 2)
          show ∑ n ∈ Finset.Icc 2 (Nval - 1), 8 / (↑n : ℝ) ^ ((3 : ℝ) / 2) ≤ tsum g
          have heq : ∀ i ∈ Finset.Icc 2 (Nval - 1),
              8 / (↑i : ℝ) ^ ((3 : ℝ) / 2) = g (i - 2) := by
            intro i hi
            simp only [g]
            congr 1
            congr 1
            have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
            push_cast [Nat.cast_sub hi2]
            ring
          rw [Finset.sum_congr rfl heq,
            ← Finset.sum_image (f := g) (g := fun n => n - 2)
              (s := Finset.Icc 2 (Nval - 1))
              (fun a ha b hb (h : a - 2 = b - 2) => by
                simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
                omega)]
          exact h_summ.sum_le_tsum _ (fun _ _ => by dsimp [g]; positivity)
  calc ∑ ρ ∈ positiveImZerosBelow T, ((zeroMultiplicity ρ : ℝ) - 1) / ρ.im
      ≤ ∑ n ∈ Finset.Icc 2 Nval, (E n - E (n - 1)) / ((n : ℝ) - 1) := h_shell
    _ ≤ E Nval / ((Nval : ℝ) - 1) +
          ∑ n ∈ Finset.Icc 2 (Nval - 1), E n / ((n : ℝ) * ((n : ℝ) - 1)) := h_abel
    _ ≤ C * 3 + C * S := add_le_add h_boundary h_series
    _ ≤ K := by linarith

instance (priority := 200)
    [ZetaZeros.ZeroCountingMultiplicityExcessLogBoundHyp] :
    AbelMultiplicityCorrectionBoundHyp where
  bound := by
    obtain ⟨K, hK, hKb⟩ := excess_div_im_bounded
    exact ⟨K, hK, fun η T _hη hT => (abs_sum_mul_sin_div_le T η).trans (hKb T hT)⟩

end Littlewood.Classical
