/-
Helper lemmas for the far-sum bound in RvMPartialSummation.
-/
import Littlewood.Development.ZetaLogDerivBound

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Complex Real Set MeasureTheory Topology Filter HadamardXi

namespace FarSumHelpers

/-! ### Pure algebraic/arithmetic helpers -/

/-
Triangle reciprocal bound: if a + b ≥ c with a, b, c > 0,
    then c / (a * b) ≤ 1/a + 1/b.
-/
theorem triangle_reciprocal (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (htri : c ≤ a + b) : c / (a * b) ≤ 1 / a + 1 / b := by
  rw [ div_add_div, div_le_div_iff₀ ] <;> nlinarith [ mul_pos ha hb ]

/-- For 0 < a and 0 < b with a + b ≥ t > 0, we have t/(a*b) ≤ 1/a + 1/b. -/
theorem triangle_reciprocal' (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (htri : t ≤ a + b) : t / (a * b) ≤ 1 / a + 1 / b := by
  exact triangle_reciprocal a b t ha hb htri

/-! ### Per-term norm bounds -/

variable [h : HadamardXiCore]

/-
For a far zero with |Im(ρ)| > 1 and |Im(ρ) - t| > 1:
    ‖1/(s-ρ) + 1/ρ‖ ≤ √5 * (1/|Im(ρ)-t| + 1/|Im(ρ)|)

    Proof: ‖term‖ = ‖s‖/(‖ρ‖·‖s-ρ‖) ≤ √5|t|/(|γ|·|γ-t|).
    By triangle: |t| ≤ |γ| + |γ-t|, so |t|/(|γ|·|γ-t|) ≤ 1/|γ-t| + 1/|γ|.
-/
theorem far_term_bound_big_im (n : ℕ) (σ t : ℝ)
    (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 2) (ht : 2 ≤ |t|)
    (hzne : h.zeros n ≠ 0) (hne : (↑σ + ↑t * I : ℂ) ≠ h.zeros n)
    (hfar : ¬|(h.zeros n).im - t| ≤ 1) (hbig : 1 < |(h.zeros n).im|) :
    ‖1 / ((↑σ + ↑t * I : ℂ) - h.zeros n) + 1 / h.zeros n‖ ≤
      Real.sqrt 5 * (1 / |(h.zeros n).im - t| + 1 / |(h.zeros n).im|) := by
  -- By hadamard_term_norm (from RvMPartialSummation), ‖1/(s-ρ)+1/ρ‖ = ‖s‖/(‖ρ‖·‖s-ρ‖).
  have h_norm : ‖(1 / (σ + t * Complex.I - h.zeros n) + 1 / h.zeros n)‖ = ‖σ + t * Complex.I‖ / (‖h.zeros n‖ * ‖σ + t * Complex.I - h.zeros n‖) := by
    rw [ div_add_div, norm_div ];
    · rw [ norm_mul, mul_comm ] ; ring;
    · exact sub_ne_zero_of_ne hne;
    · assumption;
  -- By norm_s_le from RvMPartialSummation, ‖σ + t * I‖ ≤ √5 * |t|.
  have h_norm_s : ‖σ + t * Complex.I‖ ≤ Real.sqrt 5 * |t| := by
    exact Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_num [ Complex.normSq ] ; nlinarith [ abs_mul_abs_self t, Real.mul_self_sqrt ( show 0 ≤ 5 by norm_num ) ] ⟩;
  -- By combining the results from the norm bounds and the triangle inequality, we get the desired inequality.
  have h_combined : ‖(1 / (σ + t * Complex.I - h.zeros n) + 1 / h.zeros n)‖ ≤ Real.sqrt 5 * |t| / (|(h.zeros n).im| * |(h.zeros n).im - t|) := by
    rw [h_norm];
    gcongr;
    · exact mul_pos ( by positivity ) ( by linarith );
    · exact Complex.abs_im_le_norm _;
    · norm_num [ Complex.normSq, Complex.norm_def ];
      exact Real.abs_le_sqrt ( by nlinarith );
  refine le_trans h_combined ?_;
  field_simp;
  rw [ div_add_one, div_le_div_iff_of_pos_right ] <;> cases abs_cases ( ( h.zeros n |> Complex.im ) - t ) <;> cases abs_cases ( ( h.zeros n |> Complex.im ) ) <;> cases abs_cases t <;> linarith

/-
For a far zero with |Im(ρ)| ≤ 1 and |t| ≥ 2:
    ‖1/(s-ρ) + 1/ρ‖ ≤ 2√5 / ‖ρ‖

    Proof: |Im(ρ)-t| ≥ |t|-1 ≥ |t|/2. So ‖s-ρ‖ ≥ |t|/2.
    ‖term‖ ≤ √5|t|/(‖ρ‖·|t|/2) = 2√5/‖ρ‖.
-/
theorem far_term_bound_small_im (n : ℕ) (σ t : ℝ)
    (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 2) (ht : 2 ≤ |t|)
    (hzne : h.zeros n ≠ 0) (hne : (↑σ + ↑t * I : ℂ) ≠ h.zeros n)
    (hfar : ¬|(h.zeros n).im - t| ≤ 1) (hsmall : |(h.zeros n).im| ≤ 1) :
    ‖1 / ((↑σ + ↑t * I : ℂ) - h.zeros n) + 1 / h.zeros n‖ ≤
      2 * Real.sqrt 5 / ‖h.zeros n‖ := by
  -- By combining the results from the previous steps, we conclude the proof.
  have h_final : ‖(σ + t * I : ℂ)‖ / (‖h.zeros n‖ * ‖(σ + t * I : ℂ) - h.zeros n‖) ≤ 2 * Real.sqrt 5 / ‖h.zeros n‖ := by
    have h_norm_s : ‖(σ + t * I : ℂ)‖ ≤ Real.sqrt 5 * |t| := by
      norm_num [ Complex.normSq, Complex.norm_def ] at *;
      rw [ Real.sqrt_le_left ] <;> nlinarith [ abs_mul_abs_self t, Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]
    have h_norm_s_minus_rho : ‖(σ + t * I : ℂ) - h.zeros n‖ ≥ |t| / 2 := by
      have h_norm_s_minus_rho : ‖(σ + t * I : ℂ) - h.zeros n‖ ≥ |t - (h.zeros n).im| := by
        simpa using Complex.abs_im_le_norm ( σ + t * Complex.I - h.zeros n );
      cases abs_cases t <;> cases abs_cases ( t - ( h.zeros n |> Complex.im ) ) <;> cases abs_cases ( ( h.zeros n |> Complex.im ) ) <;> linarith;
    field_simp;
    rw [ div_le_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ), abs_nonneg t ];
  rw [ div_add_div ] <;> norm_num [ hzne, hne ];
  · simpa only [ mul_comm ] using h_final;
  · exact sub_ne_zero_of_ne hne

/-- For a far zero with |Im(ρ)| > 2|t|:
    ‖1/(s-ρ) + 1/ρ‖ ≤ 2√5 * |t| / |Im(ρ)|²

    Proof: ‖ρ‖ ≥ |Im(ρ)|, ‖s-ρ‖ ≥ |Im(ρ)-t| ≥ |Im(ρ)|/2.
    So ‖ρ‖·‖s-ρ‖ ≥ |Im(ρ)|²/2.
    ‖term‖ ≤ √5|t|/(|Im(ρ)|²/2) = 2√5|t|/|Im(ρ)|². -/
theorem far_term_bound_huge_im (n : ℕ) (σ t : ℝ)
    (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 2) (ht : 2 ≤ |t|)
    (hzne : h.zeros n ≠ 0) (hne : (↑σ + ↑t * I : ℂ) ≠ h.zeros n)
    (hfar : ¬|(h.zeros n).im - t| ≤ 1) (hhuge : 2 * |t| < |(h.zeros n).im|) :
    ‖1 / ((↑σ + ↑t * I : ℂ) - h.zeros n) + 1 / h.zeros n‖ ≤
      2 * Real.sqrt 5 * |t| / |(h.zeros n).im| ^ 2 := by
  set γ := (h.zeros n).im
  have him_pos : 0 < |γ| := by linarith
  have him_half : |γ| / 2 ≤ |γ - t| := by
    have h1 : |t| < |γ| / 2 := by linarith
    have h2 : |γ| - |t| ≤ |γ - t| := abs_sub_abs_le_abs_sub γ t
    linarith
  -- Norm identity
  have h_norm : ‖(1 / (↑σ + ↑t * I - h.zeros n) + 1 / h.zeros n)‖ =
      ‖↑σ + ↑t * I‖ / (‖h.zeros n‖ * ‖↑σ + ↑t * I - h.zeros n‖) := by
    rw [div_add_div, norm_div]
    · rw [norm_mul, mul_comm]; ring
    · exact sub_ne_zero_of_ne hne
    · exact hzne
  have h_norm_s : ‖(↑σ + ↑t * I : ℂ)‖ ≤ Real.sqrt 5 * |t| := by
    exact Real.sqrt_le_iff.mpr ⟨by positivity,
      by norm_num [Complex.normSq]; nlinarith [abs_mul_abs_self t,
        Real.mul_self_sqrt (show (0:ℝ) ≤ 5 by norm_num)]⟩
  have h_im_le_norm : |γ| ≤ ‖h.zeros n‖ := Complex.abs_im_le_norm _
  have h_im_sub_le_norm : |γ - t| ≤ ‖(↑σ + ↑t * I : ℂ) - h.zeros n‖ := by
    have key : ((↑σ + ↑t * I : ℂ) - h.zeros n).im = t - γ := by
      simp [γ, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_im, Complex.I_re, Complex.ofReal_re]
    calc |γ - t| = |t - γ| := by rw [abs_sub_comm]
      _ = |((↑σ + ↑t * I : ℂ) - h.zeros n).im| := by rw [key]
      _ ≤ _ := Complex.abs_im_le_norm _
  -- Lower bound on denominator
  have h_denom_lb : |γ| ^ 2 / 2 ≤ ‖h.zeros n‖ * ‖↑σ + ↑t * I - h.zeros n‖ := by
    calc |γ| ^ 2 / 2 = |γ| * (|γ| / 2) := by ring
      _ ≤ ‖h.zeros n‖ * ‖(↑σ + ↑t * I : ℂ) - h.zeros n‖ := by
          apply mul_le_mul h_im_le_norm
          · linarith [him_half, h_im_sub_le_norm]
          · positivity
          · exact norm_nonneg _
  rw [h_norm]
  have denom_pos : 0 < ‖h.zeros n‖ * ‖↑σ + ↑t * I - h.zeros n‖ :=
    mul_pos (norm_pos_iff.mpr hzne) (norm_pos_iff.mpr (sub_ne_zero_of_ne hne))
  have him2_pos : (0:ℝ) < |γ| ^ 2 := by positivity
  have him2_half_pos : (0:ℝ) < |γ| ^ 2 / 2 := by linarith
  calc ‖↑σ + ↑t * I‖ / (‖h.zeros n‖ * ‖↑σ + ↑t * I - h.zeros n‖)
      ≤ (Real.sqrt 5 * |t|) / (|γ| ^ 2 / 2) := by
        gcongr
    _ = 2 * Real.sqrt 5 * |t| / |γ| ^ 2 := by ring

/-! ### Finiteness and counting -/

/-
The set of zeros with |Im| ≤ 1 is finite.
-/
theorem finite_small_im_zeros
    (hfin_strip : ∀ t : ℝ, Set.Finite {n : ℕ | |(h.zeros n).im - t| ≤ 1}) :
    Set.Finite {n : ℕ | |(h.zeros n).im| ≤ 1} := by
  simpa using hfin_strip 0

/-
The set of zeros with |Im| ≤ R is finite (for any R).
-/
theorem finite_bounded_im_zeros (R : ℝ)
    (hfin_strip : ∀ t : ℝ, Set.Finite {n : ℕ | |(h.zeros n).im - t| ≤ 1}) :
    Set.Finite {n : ℕ | |(h.zeros n).im| ≤ R} := by
  refine Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_Icc ( -⌈R⌉ ) ⌈R⌉ ) fun t ht => hfin_strip t ) ?_;
  simp +decide [ Set.subset_def, abs_le ];
  exact fun n hn₁ hn₂ => ⟨ ⌊ ( h.zeros n |> Complex.im ) ⌋, by linarith [ Int.floor_le ( ( h.zeros n |> Complex.im ) ) ], ⟨ by exact Int.le_floor.2 <| by norm_num; linarith [ Int.le_ceil R ], by exact Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; linarith [ Int.le_ceil R ] ⟩, by linarith [ Int.lt_floor_add_one ( ( h.zeros n |> Complex.im ) ) ] ⟩

/-! ### Density-based sum bounds -/

/-- Key density bound: sum of 1/|γ-t| over far zeros with 1 < |γ| ≤ 2|t|+2.
    Uses density ≤ C(1+log|t|) per unit strip and harmonic sum.

    The Mathlib-only abstract version `density_sum_reciprocal_shifted_abstract`
    in `NearHeightShellSumCorrected` is proved sorry-free (Aristotle job
    58a331f3). The bridge from this FarSumHelpers form to the abstract form
    requires uniform extension of the density hypothesis to `|s| < 2`, which
    introduces bookkeeping not yet completed here. -/
theorem density_sum_reciprocal_shifted
    (hfin_strip : ∀ t : ℝ, Set.Finite {n : ℕ | |(h.zeros n).im - t| ≤ 1})
    (hdensity : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ((hfin_strip t).toFinset.card : ℝ) ≤ C * (1 + Real.log |t|)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ t : ℝ, 2 ≤ |t| →
      let S := ((finite_bounded_im_zeros (2*|t|+2) hfin_strip).toFinset \
                (hfin_strip t).toFinset).filter (fun n => 1 < |(h.zeros n).im|)
      (S.sum (fun n => 1 / |(h.zeros n).im - t|) : ℝ) ≤ C' * (Real.log |t|) ^ 2 := by
  sorry

/-- Key density bound: sum of 1/|γ| over zeros with 1 < |γ| ≤ 2|t|+2. -/
theorem density_sum_reciprocal_gamma
    (hfin_strip : ∀ t : ℝ, Set.Finite {n : ℕ | |(h.zeros n).im - t| ≤ 1})
    (hdensity : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ((hfin_strip t).toFinset.card : ℝ) ≤ C * (1 + Real.log |t|)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ t : ℝ, 2 ≤ |t| →
      let S := (finite_bounded_im_zeros (2*|t|+2) hfin_strip).toFinset.filter
                (fun n => 1 < |(h.zeros n).im|)
      (S.sum (fun n => 1 / |(h.zeros n).im|) : ℝ) ≤ C' * (Real.log |t|) ^ 2 := by
  sorry

/-- Tail bound: ∑_{|γ|>2|t|} |t|/|γ|² ≤ C·(1+log|t|).
    Uses density to bound the tail of ∑ 1/|γ|². -/
theorem density_tail_inv_sq
    (hfin_strip : ∀ t : ℝ, Set.Finite {n : ℕ | |(h.zeros n).im - t| ≤ 1})
    (hdensity : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ((hfin_strip t).toFinset.card : ℝ) ≤ C * (1 + Real.log |t|)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ t : ℝ, 2 ≤ |t| →
      (∑' (n : {n : ℕ // 2 * |t| < |(h.zeros n).im|}),
        |t| / |(h.zeros ↑n).im| ^ 2 : ℝ) ≤ C' * (1 + Real.log |t|) := by
  sorry

end FarSumHelpers