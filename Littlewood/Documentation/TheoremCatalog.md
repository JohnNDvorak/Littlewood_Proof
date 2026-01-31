# Aristotle Theorem Catalog

Generated automatically. Lists all theorems/lemmas available for wiring.


## BinetStirling (11)
```
lemma log_one_add_sub_self_asymptotic :
lemma log_one_add_inv_im_asymptotic :
lemma log_split_lemma :
lemma log_quarter_plus_it_half_asymptotic :
lemma stirling_approx_im_asymptotic :
lemma binet_integrand_limit_zero :
lemma binet_integrand_limit_infinity :
lemma binet_integrand_continuous :
lemma binet_integrand_differentiable :
lemma bounded_of_continuous_limits {f : ℝ → ℝ}
lemma binet_integrand_bounded :
```

## CosBound (1)
```
lemma complex_cos_bound_vertical_strip (a b : ℝ) :
```

## CriticalZeros (3)
```
lemma simultaneous_dirichlet_approx (γs : List ℝ) (ε : ℝ) (hε : ε > 0) :
lemma exists_seq_zeros (h_hardy : ∀ (T : ℝ), ∃ (γ : ℝ), γ > T ∧ riemannZeta (1/2 + Complex.I * γ) = 0) :
lemma critical_zeros_finite (T : ℝ) : (critical_zeros_set T).Finite := by
```

## DirichletApprox (3)
```
lemma exists_approx_pair (n N : ℕ) (hN : 0 < N) (f : Fin (N ^ n + 1) → Fin n → ℝ)
theorem dirichlet_simultaneous_approximation (n : ℕ) (α : Fin n → ℝ) (N : ℕ) (hN : 0 < N) :
theorem oscillation_alignment (n : ℕ) (γ : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
```

## DirichletSeries (1)
```
lemma log_pow_mul_neg_power_bounded (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
```

## ExplicitFormulaV3 (1)
```
theorem explicit_formula_psi_v3 (x : ℝ) (hx : 1 < x) (T : ℝ) (hT : 1 < T) :
```

## FunctionalEquationHyp (1)
```
theorem riemannZeta_eq_chiFE_mul (s : ℂ) (hs : ∀ n : ℕ, s ≠ 1 + n) (hs' : s ≠ 0) :
```

## FunctionalEquationV2 (2)
```
lemma LambdaV2_eq_completedZeta (s : ℂ) (hs : 0 < s.re) :
theorem LambdaV2_one_sub (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
```

## GammaGrowth (9)
```
lemma norm_cos_pi_div_two_sub_I_mul_t_div_two_asymp :
lemma norm_gamma_one_sub_I_mul_t_asymp :
lemma norm_two_mul_two_pi_pow_sub_one_plus_I_mul_t_asymp :
lemma zeta_conj_eq : ∀ t : ℝ, ‖riemannZeta (1 - Complex.I * t)‖ = ‖riemannZeta (1 + Complex.I * t)‖ := by
lemma harmonic_le_one_plus_log (n : ℕ) (hn : n ≥ 1) :
lemma partial_sum_bound (t : ℝ) (N : ℕ) (hN : N ≥ 1) :
lemma integral_fract_term (s : ℂ) (n : ℕ) (hn : n ≥ 1) (hs : s ≠ 1) (hs_pos : 0 < s.re) :
lemma sum_integral_fract_term (s : ℂ) (N M : ℕ) (hN : N ≥ 1) (hNM : N ≤ M) (hs : s ≠ 1) (hs_pos : 0 < s.re) :
lemma integral_fract_bound (n : ℕ) (s : ℂ) (hn : n ≥ 1) (hs : 0 < s.re) :
```

## HardyZComplete (4)
```
lemma gamma_conj' (s : ℂ) : Complex.Gamma (conj s) = conj (Complex.Gamma s) :=
lemma hardyCompletedZeta_conj (s : ℂ) :
lemma hardyZV3_eq_hardyZ' (t : ℝ) : hardyZV3 t = hardyZ' t := by
theorem hardyZV3_real (t : ℝ) : (hardyZV3 t).im = 0 := by
```

## HardyZReal (13)
```
lemma conj_log_nat {n : ℕ} (hn : n ≠ 0) :
lemma star_cpow_nat {n : ℕ} (hn : n ≠ 0) (s : ℂ) : star ((n : ℂ) ^ s) = (n : ℂ) ^ (star s) := by
lemma star_one_div_nat_cpow {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
lemma riemannZeta_conj (s : ℂ) : riemannZeta (star s) = star (riemannZeta s) := by
lemma gamma_conj (s : ℂ) : Complex.Gamma (star s) = star (Complex.Gamma s) :=
lemma critical_line_star_eq (t : ℝ) : star ((1:ℂ)/2 + I * t) = 1 - ((1:ℂ)/2 + I * t) := by
lemma completedRiemannZeta_conj (s : ℂ) :
lemma completedRiemannZeta_real_on_critical_line (t : ℝ) :
lemma half_plus_tI_ne_zero (t : ℝ) : (1/2 : ℂ) + t * I ≠ 0 := by
lemma gamma_quarter_ne_zero (t : ℝ) : Complex.Gamma (1/4 + t/2 * I) ≠ 0 := by
lemma gammaR_ne_zero_at_half (t : ℝ) : Gammaℝ ((1 : ℂ)/2 + t * I) ≠ 0 := by
lemma hardyZ_eq_completedZeta_div_norm (t : ℝ) :
theorem hardyZ'_real (t : ℝ) : (hardyZ' t).im = 0 := by
```

## HardyZRealV2 (9)
```
theorem analyticOn_riemannZeta_v2 : AnalyticOn ℂ riemannZeta {1}ᶜ := by
theorem identity_theorem_extension_v2 {f g : ℂ → ℂ} {U : Set ℂ}
lemma gamma_duplication_hardy_v2 (t : ℝ) :
lemma gamma_reflection_hardy_v2 (t : ℝ) :
theorem hardyZV2_real (t : ℝ) : (hardyZV2 t).im = 0 := by
theorem hardyZV2_zero_iff_zeta_zero (t : ℝ) :
theorem hardyZV2_abs_eq_zeta_abs (t : ℝ) :
theorem continuous_hardyZV2 : Continuous hardyZV2 := by
theorem hardyZV2_constant_sign_between_zeros (t₁ t₂ : ℝ) (h_lt : t₁ < t₂)
```

## HardyZRealV4 (3)
```
theorem gamma_duplication_hardyV4 (t : ℝ) :
theorem gamma_reflection_hardyV4 (t : ℝ) :
theorem hardyZV4_real (t : ℝ) : (hardyZV4 t).im = 0 := by
```

## HarmonicSumIntegral (6)
```
lemma harmonicSum_eq_harmonic (n : ℕ) : harmonicSum n = harmonic n := by
lemma harmonicSum_N_truncation_sub_half_log_isBigO :
lemma integral_harmonicSum_sub_half_log_isBigO :
lemma integral_half_log_isTheta :
lemma T_isLittleO_T_log_T :
lemma integral_harmonicSum_asymp :
```

## HorizontalSegmentBounds (3)
```
lemma norm_integrand_le (x : ℝ) (hx : 1 < x) (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 < T) (σ : ℝ) (hσ : σ ∈ Set.Icc 0 c) :
lemma horizontal_segment_xpow_bound (x : ℝ) (hx : 1 < x) (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 1 < T) :
lemma horizontal_segment_bound (x : ℝ) (hx : 1 < x) (c : ℝ) (hc : 1 < c) (T : ℝ) (hT : 1 < T)
```

## IntegralArctanFormula (1)
```
lemma integral_real_part_arctan (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) :
```

## IntegralLogSqrtAsymp (1)
```
lemma integral_log_sqrt_quarter_asymp :
```

## LandauLemma (12)
```
theorem partial_sums_mono {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
theorem tendsto_atTop_of_nonneg_not_summable
theorem dirichlet_series_eq_tsum_real
theorem analyticAt_bounded_on_compact
lemma continuousAt_finset_sum' {α : Type*} [TopologicalSpace α] {β : Type*} [AddCommMonoid β]
lemma zero_rpow_neg_continuousAt (σ₀ : ℝ) (hσ₀ : σ₀ ≠ 0) :
lemma unbounded_partial_sums (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (σ_c : ℝ)
lemma partial_sum_continuousAt (a : ℕ → ℝ) (N : ℕ) (σ : ℝ) (hσ : σ ≠ 0) :
theorem dirichlet_series_tendsto_atTop
theorem landau_dirichlet_singularity
theorem landau_singularity_of_continuation
theorem riemann_zeta_singularity_at_one : ¬AnalyticAt ℂ riemannZeta 1 := by
```

## LaurentExpansion (16)
```
lemma deriv_sub_one_mul_zeta (s : ℂ) (hs : s ≠ 1) :
lemma neg_zeta_logderiv_eq' (s : ℂ) (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
lemma zetaMulSubOne_continuousAt_one' : ContinuousAt zetaMulSubOne 1 := by
lemma zetaMulSubOne_differentiableAt (s : ℂ) (hs : s ≠ 1) : DifferentiableAt ℂ zetaMulSubOne s := by
theorem zetaMulSubOne_analyticAt_one : AnalyticAt ℂ zetaMulSubOne 1 := by
lemma sqZeta_eq_mul_zetaMulSubOne (s : ℂ) : sqZeta s = (s - 1) * zetaMulSubOne s := by
theorem sqZeta_analyticAt_one : AnalyticAt ℂ sqZeta 1 := by
theorem deriv_sqZeta_continuousAt_one : ContinuousAt (deriv sqZeta) 1 := by
lemma sqZeta_has_deriv_at_one : HasDerivAt sqZeta 1 1 := by
lemma deriv_sqZeta_at_one : deriv sqZeta 1 = 1 := sqZeta_has_deriv_at_one.deriv
lemma deriv_sqZeta_eq (s : ℂ) (hs : s ≠ 1) :
lemma sub_sq_mul_zeta_deriv_tendsto :
lemma riemannZeta_ne_zero_near_one :
theorem neg_zeta_logDeriv_residue_one :
theorem neg_zeta_logDeriv_principal_part :
theorem zetaMulSubOne_continuousAt_one : ContinuousAt zetaMulSubOne 1 :=
```

## MeanSquare (10)
```
lemma norm_chi_critical_line (t : ℝ) : ‖chi (1/2 + I * t)‖ = 1 := by
lemma N_t_eq_N_truncation (t : ℝ) : N_t t = N_truncation t := rfl
lemma sum_Icc_eq_harmonicSum (n : ℕ) :
lemma harmonic_sum_bound :
lemma integral_log_sqrt_asymp :
lemma integral_harmonic_sum_asymp :
lemma integral_cpow_neg_mul_bound (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) (hnm : n ≠ m) (A B : ℝ) :
lemma norm_integral_offDiagSsq_le (T : ℝ) (hT : T ≥ 1) :
lemma normSq_partialZeta_eq (t : ℝ) :
theorem mean_square_partial_zeta_asymp :
```

## NAsymptotic (1)
```
theorem N_asymptotic
```

## NZerosStirling (2)
```
theorem S_bound (T : ℝ) (hT : 2 ≤ T) : ∃ C, |S T| ≤ C * Real.log T := by
theorem N_from_S_and_Stirling (T : ℝ) (hT : 2 ≤ T)
```

## OffDiagonalBound (1)
```
lemma norm_integral_offDiagSsqReal_le (N : ℕ) (T : ℝ) (hT : 1 ≤ T) :
```

## PartialSummation (4)
```
lemma sumLambdaDivLog_eq_psi_div_log_add_integral (x : ℝ) (hx : x ≥ 2) :
lemma sumLambdaDivLog_sub_primeCounting_eq_sum_prime_powers (x : ℝ) :
lemma pi_sub_li_decomposition (x : ℝ) (hx : x ≥ 2) :
theorem psi_oscillation_implies_pi_li_oscillation
```

## PartialSummationPiLi (8)
```
theorem li_integration_by_parts (x : ℝ) (hx : 2 ≤ x) :
theorem sum_vonMangoldt_div_log (x : ℝ) (hx : 2 ≤ x) :
lemma vonMangoldt_div_log_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≥ 1) :
theorem sum_vonMangoldt_eq_sum_prime_powers (x : ℝ) :
theorem prime_pow_inj {p q k l : ℕ} (hp : p.Prime) (hq : q.Prime) (hk : k ≥ 1) (hl : l ≥ 1) :
lemma prime_pow_le_iff_le_root (p k : ℕ) (x : ℝ) (hp : p ≥ 2) (hk : k ≥ 1) (hx : x ≥ 2) :
theorem sum_prime_powers_fixed_k (x : ℝ) (k : ℕ) (hk : k ≥ 1) (c : ℝ) :
theorem primePowerCorrectionSum_term_two_bound (x : ℝ) (hx : 0 ≤ x) :
```

## PartialZetaNormSq (1)
```
lemma normSq_partialZetaSum_general (N : ℕ) (s : ℂ) :
```

## PerronContourIntegrals (12)
```
lemma verticalIntegral_cpow_div (x c : ℝ) (hx : 1 < x) (hc : 0 < c) (T : ℝ) (hT : 0 < T) :
theorem perron_truncated (x : ℝ) (hx : 1 < x) (T : ℝ) (hT : 1 < T) :
lemma horizontalIntegral_bound (x : ℝ) (hx : 1 < x) (T : ℝ) (hT : 0 < T) (a c : ℝ) (hac : a ≤ c) :
lemma horizontalIntegral_bound_infinite (x c T : ℝ) (hx : 1 < x) (hT : 0 < T) :
lemma leftVerticalIntegral_bound (x : ℝ) (hx : 1 < x) (R : ℝ) (hR : 0 < R) (T : ℝ) (hT : 0 < T) :
lemma exp_sub_one_div_z_continuous : Continuous exp_sub_one_div_z := by
lemma hasDerivAt_exp_sub_one_div_z_zero : HasDerivAt exp_sub_one_div_z (1/2) 0 := by
lemma exp_sub_one_div_z_entire : Differentiable ℂ exp_sub_one_div_z := by
lemma perron_integrand_eq (x : ℝ) (hx : 0 < x) (s : ℂ) :
lemma integral_one_div_s_left_vert (R T : ℝ) (hR : 0 < R) (hT : 0 < T) :
lemma integral_one_div_s_right_vert (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
lemma integral_one_div_s_bottom_horiz (c R T : ℝ) (hc : 0 < c) (hR : 0 < R) (hT : 0 < T) :
```

## PerronContourIntegralsV2 (17)
```
lemma perron_horizontal_bound_pointwise (y : ℝ) (hy : 0 < y) (x : ℝ) (T : ℝ) (hT : 0 < T) :
lemma integral_rpow_on_interval (y : ℝ) (hy : 0 < y) (hy1 : y ≠ 1) (a b : ℝ) :
lemma integral_y_pow_div_T (y : ℝ) (hy : 0 < y) (hy1 : y ≠ 1) (T : ℝ) (hT : T ≠ 0) (a b : ℝ) :
lemma integral_norm_bound_large_y (y : ℝ) (hy : 1 < y) (c : ℝ) (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : -R ≤ c) :
lemma integral_norm_bound_small_y (y : ℝ) (hy : 0 < y) (hy1 : y < 1) (c : ℝ) (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : c ≤ R) :
lemma vertical_integral_bound_far_left (y : ℝ) (hy : 0 < y) (R : ℝ) (hR : 0 < R) (T : ℝ) (hT : 0 < T) :
lemma vertical_integral_bound_far_right (y : ℝ) (hy : 0 < y) (R : ℝ) (hR : 0 < R) (T : ℝ) (hT : 0 < T) :
lemma integral_norm_bound_large_y_improper (y : ℝ) (hy : 1 < y) (c : ℝ) (T : ℝ) (hT : 0 < T) :
lemma integral_y_pow_sub_one_div_z_rect_eq_zero (y : ℝ) (hy : 0 < y) (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R) :
lemma integral_one_div_z_left_side_value (R T : ℝ) (hR : 0 < R) (hT : 0 < T) :
lemma integral_one_div_z_right_side_value (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
lemma integral_one_div_z_top_value (c T R : ℝ) (hT : 0 < T) :
lemma integral_one_div_z_bottom_value (c T R : ℝ) (hT : 0 < T) :
lemma integral_one_div_z_rect_eq_two_pi_I (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R) :
lemma integral_boundary_rect_perron_pos (y : ℝ) (hy : 1 < y) (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R) :
lemma integral_boundary_rect_perron_neg (y : ℝ) (hy : 0 < y) (hy1 : y < 1) (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : c < R) :
lemma integral_norm_bound_small_y_improper (y : ℝ) (hy : 0 < y) (hy1 : y < 1) (c : ℝ) (T : ℝ) (hT : 0 < T) :
```

## PerronFormulaV2 (2)
```
lemma zetaZerosInStrip_finite (T : ℝ) : (zetaZerosInStrip T).Finite := by
theorem perron_for_psi (x : ℝ) (hx : x ≥ 2) (T : ℝ) (hT : T ≥ 2) :
```

## PerronNew (1)
```
theorem perron_formula_truncated (x T : ℝ) (hx : 2 ≤ x) (hT : 2 ≤ T) :
```

## PhaseAlignment (2)
```
lemma align_phases (γs : Finset ℝ) (ε : ℝ) (hε : ε > 0) :
lemma cos_alignment (γs : Finset ℝ) (ε : ℝ) (hε : ε > 0) (M : ℝ) :
```

## PhragmenLindelof (12)
```
lemma convexity_exponent_ge_one (σ : ℝ) (hσ : 1 ≤ σ) : convexity_exponent σ = 0 := by
lemma convexity_exponent_half : convexity_exponent (1/2) = 1/4 := by
lemma convexity_exponent_nonneg (σ : ℝ) : 0 ≤ convexity_exponent σ := by
lemma convexity_exponent_zero : convexity_exponent 0 = 1/2 := by
lemma zeta_bound_gt_one (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
lemma zeta_bound_at_two (t : ℝ) : ‖riemannZeta (2 + t * I)‖ ≤ Real.pi^2 / 6 := by
theorem zeta_critical_line_bound :
theorem zeta_convexity_bound (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
lemma gamma_growth (σ : ℝ) (hσ : 0 < σ) :
theorem hardyZ_growth :
theorem zeta_near_one_bound (σ : ℝ) (hσ : 1 < σ) (hσ2 : σ < 2) :
theorem zeta_large_sigma_bound (σ : ℝ) (hσ : 2 ≤ σ) (t : ℝ) :
```

## PhragmenLindelofStrip (4)
```
theorem zeta_bound_ge_two : ∃ C, ∀ s : ℂ, 2 ≤ s.re → ‖riemannZeta s‖ ≤ C := by
theorem abs_exp_eps_sq_le {a b ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : a ≤ z.re ∧ z.re ≤ b) :
theorem is_bounded_exp_eps_sq_mul {f : ℂ → ℂ} {a b ε : ℝ} (hab : a < b) (hε : 0 < ε)
theorem is_bounded_exp_eps_sq_mul_closed {f : ℂ → ℂ} {a b M : ℝ} (hab : a < b)
```

## PhragmenLindelofV2 (5)
```
theorem phragmen_lindelof_convexity_v2 {f : ℂ → ℂ} {a b : ℝ} (hab : a < b)
lemma zeta_entire_analytic_v2 : Differentiable ℂ zeta_entire_v2 := by
lemma g_growth_condition_v2 (g : ℂ → ℂ) (a b : ℝ) (hab : a < b)
theorem polynomial_growth_implies_bounded_of_boundary_bounded_v2
lemma zeta_entire_growth_v2
```

## PiLiOscillation (7)
```
lemma combined_error_bound
lemma exists_pos_oscillation
lemma exists_pos_oscillation_aux
lemma exists_pos_oscillation_aux_v2
lemma exists_neg_oscillation_aux
lemma exists_pos_oscillation_final
lemma exists_pos_oscillation_valid
```

## PsiDominance (5)
```
theorem pi_sub_li_decomposition (x : ℝ) (hx : 2 ≤ x) :
lemma psi_pos_dominates_errors
lemma psi_neg_dominates_errors
lemma sqrt_div_log_tendsto_atTop : Filter.Tendsto (fun x => Real.sqrt x / Real.log x) Filter.atTop Filter.atTop := by
lemma psi_neg_dominates_errors_with_bounds
```

## RiemannVonMangoldt (7)
```
theorem riemann_von_mangoldt (T : ℝ) (hT : 2 ≤ T) :
theorem Theta_asymp (T : ℝ) (hT : 2 ≤ T) :
theorem S_T_bound (T : ℝ) (hT : 2 ≤ T) :
theorem NZeros_eq_Theta_S (T : ℝ) (hT : 2 ≤ T) :
theorem S_T_bound_uniform :
theorem riemann_von_mangoldt_reduction
theorem riemann_von_mangoldt_conditional
```

## RiemannVonMangoldtV2 (3)
```
theorem riemann_von_mangoldt_argument (T : ℝ) (hT : 2 ≤ T) :
theorem N_eq_main_plus_S (T : ℝ) (hT : 2 ≤ T) :
lemma N_main_term_eq (T : ℝ) (hT : 2 ≤ T) :
```

## RiemannXi (4)
```
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
theorem RiemannXi_one_sub (s : ℂ) : RiemannXi (1 - s) = RiemannXi s := by
theorem differentiable_RiemannXi : Differentiable ℂ RiemannXi := by
theorem RiemannXi_eq_completedRiemannZeta (s : ℂ) (hs : s ≠ 0) (hs' : s ≠ 1) :
```

## RiemannXiEntire (2)
```
theorem RiemannXiAlt_entire : Differentiable ℂ RiemannXiAlt := by
theorem RiemannXiAlt_eq_formula {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
```

## SchmidtNew (10)
```
theorem trigPoly_zero_iff_coeffs_zero (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0)
theorem trigPoly_mean_zero (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0)
theorem trigPoly_integral_bounded (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0)
theorem trigPoly_mean_square (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0)
theorem trigPoly_tendsto_zero_implies_zero (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0)
theorem tendsto_zero_of_nonneg_integrable_uniformContinuous {f : ℝ → ℝ}
theorem trigPoly_nonneg_implies_zero (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0)
theorem tendsto_zero_of_nonneg_on_Ici_integrable_uniformContinuous {f : ℝ → ℝ}
theorem trigPoly_eventually_nonneg_implies_zero (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0)
theorem schmidt_oscillation (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0)
```

## SchmidtOscillation (11)
```
lemma trigPoly_mean_zero (S : Finset ℝ) (c ph : ℝ → ℝ) (h_nonzero : ∀ γ ∈ S, γ ≠ 0) :
lemma trigPoly_zero_iff_coeffs_zero (S : Finset ℝ) (c ph : ℝ → ℝ)
lemma dirichlet_simultaneous_approx (S : Finset ℝ) (N : ℕ) (hN : N > 0) :
lemma exists_near_integer_multiples (S : Finset ℝ) (ε : ℝ) (hε : 0 < ε) (M : ℝ) :
lemma trigPoly_almost_periodic (S : Finset ℝ) (c ph : ℝ → ℝ)
lemma trigPoly_nonneg_of_eventually_nonneg (S : Finset ℝ) (c ph : ℝ → ℝ)
lemma trigPoly_mean_square (S : Finset ℝ) (c ph : ℝ → ℝ)
lemma trigPoly_eq_zero_of_nonneg_everywhere (S : Finset ℝ) (c ph : ℝ → ℝ)
lemma trigPoly_not_nonneg_everywhere (S : Finset ℝ) (c ph : ℝ → ℝ)
theorem schmidt_oscillation_lemma_finite
theorem schmidt_oscillation_lemma_finite_set
```

## SchmidtOscillationInfinite (9)
```
lemma finite_sum_cos_mean_zero (s : Finset ℝ) (c : ℝ → ℝ) (ph : ℝ → ℝ) (hs : ∀ γ ∈ s, γ ≠ 0) :
lemma finite_sum_cos_sq_mean (s : Finset ℝ) (c : ℝ → ℝ) (ph : ℝ → ℝ) (hs_pos : ∀ γ ∈ s, γ > 0) :
lemma finite_sum_cos_pos (s : Finset ℝ) (c : ℝ → ℝ) (ph : ℝ → ℝ)
lemma mean_square_zero_of_nonpos_mean_zero {f : ℝ → ℝ}
lemma finite_sum_cos_pos_of_mean_zero (s : Finset ℝ) (c : ℝ → ℝ) (ph : ℝ → ℝ)
lemma integral_cos_sq_tendsto_half (A B : ℝ) (ph : ℝ → ℝ) :
lemma oscillation_contradiction {γs : Set ℝ} (h_unbounded : ¬ BddAbove γs) (c : ℝ → ℝ) (ph : ℝ → ℝ) (c₀ : ℝ)
theorem schmidt_oscillation_lemma_v2
theorem psi_minus_x_oscillates_v5
```

## StirlingGammaBounds (16)
```
lemma complex_sin_vertical_bound (σ : ℝ) :
lemma gamma_reflection_bound (σ : ℝ) (hσ : 0 < σ) (hσ' : σ < 2) :
lemma gamma_step_down (σ : ℝ) :
lemma gamma_one_bound :
lemma gamma_two_bound :
lemma stirling_proxy_bound_one :
lemma stirling_proxy_bound_two :
lemma stirling_proxy_differentiable :
lemma gamma_growth_crude :
lemma stirling_proxy_growth_bound_aux :
lemma log_growth_vs_exp (B : ℝ) :
lemma norm_le_im_add_two (z : ℂ) (h : 1 ≤ z.re ∧ z.re ≤ 2) : ‖z‖ ≤ |z.im| + 2 := by
lemma log_growth_inequality (B : ℝ) :
lemma growth_bound_implies_condition {f : ℂ → ℂ} (A B : ℝ)
lemma stirling_proxy_growth_proven :
lemma stirling_proxy_bounded_strip :
```

## ThreeFourOne (10)
```
lemma three_four_one_inequality (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
lemma three_four_one_from_square (θ : ℝ) :
lemma three_four_one_tight : 3 + 4 * Real.cos Real.pi + Real.cos (2 * Real.pi) = 0 := by
lemma neg_log_one_sub_re_eq_tsum (z : ℂ) (hz : ‖z‖ < 1) :
lemma real_part_log_series (r θ : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
lemma summable_r_pow_div_mul_cos (r θ k : ℝ) (hr : |r| < 1) :
lemma log_combination_eq_sum (r θ : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
theorem real_part_log_euler_product_term_ge_zero (r θ : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
lemma log_norm_zeta_eq_sum_re_log (s : ℂ) (hs : 1 < s.re) :
theorem zeta_product_ge_one (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
```

## ThreeFourOneV2 (6)
```
lemma trig_ineq_v2 (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) ≥ 0 := by
lemma log_norm_zeta_eq_tsum_v2 (s : ℂ) (hs : 1 < s.re) :
lemma term_nonneg_v2 (r : ℝ) (hr : 0 ≤ r) (θ : ℝ) :
lemma log_zeta_combination_nonneg_v2 (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
theorem three_four_one_v2 (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
theorem zeta_ne_zero_re_one_v2 (t : ℝ) (ht : t ≠ 0) : riemannZeta (1 + I * t) ≠ 0 :=
```

## TrigPolyIndependence (3)
```
lemma integral_cos_bounded (omega : ℝ) (homega : omega ≠ 0) (ph : ℝ) (T : ℝ) (_hT : 0 ≤ T) :
lemma cos_mul_cos_eq (a b : ℝ) :
lemma trigPoly_zero_iff_coeffs_zero (gammas : Finset ℝ) (hgammas : ∀ g ∈ gammas, g > 0)
```

## TruncatedExplicitFormula (1)
```
theorem psi_as_trig_sum (x : ℝ) (hx : 2 < x) (T : ℝ) (hT : 2 ≤ T) :
```

## XiDifferentiability (7)
```
theorem xi_LiteralCorrected_entire : Differentiable ℂ xi_LiteralCorrected := by
theorem xi_Literal_eq_xi_LiteralCorrected (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) : xi_Literal s = xi_LiteralCorrected s := by
theorem xi_Literal_value_one : xi_Literal 1 = 0 := by
theorem xi_LiteralCorrected_one : xi_LiteralCorrected 1 = 1 := by
theorem xi_Literal_tendsto_one : Filter.Tendsto xi_Literal (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
theorem xi_Literal_not_continuousAt_one : ¬ ContinuousAt xi_Literal 1 := by
theorem xi_Literal_not_differentiable : ¬ Differentiable ℂ xi_Literal := by
```

## ZeroCounting (10)
```
theorem xi_Mathlib_functional_equation (s : ℂ) : xi_Mathlib s = xi_Mathlib (1 - s) := by
theorem xi_Mathlib_zeros_eq_zeta_zeros (s : ℂ) (hs_re : 0 < s.re) (hs_re' : s.re < 1) :
theorem xi_Mathlib_corrected_entire : Differentiable ℂ xi_Mathlib_corrected := by
theorem xi_Mathlib_eq_corrected (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
theorem xi_Mathlib_differentiable : Differentiable ℂ xi_Mathlib := by
theorem zetaZeroCount_via_argument (T : ℝ) (hT : 0 < T) :
theorem riemann_von_mangoldt (T : ℝ) (hT : 1 < T) :
theorem zetaZeroCount_asymp :
lemma completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta (s : ℂ) (hs : 0 < s.re) (_hs1 : s ≠ 1) :
lemma xi_Mathlib_eq_RiemannXi (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hs_re : 0 < s.re) :
```

## ZeroCountingNew (3)
```
theorem S_term_bound : S_term =O[Filter.atTop] (fun T => Real.log T) := by
theorem zero_counting_main_term_of_RiemannVonMangoldt (h : RiemannVonMangoldtProperty) :
theorem zero_counting_main_term (h : RiemannVonMangoldtProperty) :
```

## ZeroCountingV2 (3)
```
theorem zero_counting_asymptotic (T : ℝ) (hT : T ≥ 2) :
theorem zero_counting_precise (T : ℝ) (hT : T ≥ 2) :
theorem S_bound : ∃ C > 0, ∀ T ≥ 2, |SArg T| ≤ C * Real.log T := by
```

## ZeroCountingXi (3)
```
theorem xi_entire : Differentiable ℂ xi := by
theorem xi_Mathlib_differentiable : Differentiable ℂ xi := xi_entire
theorem zetaZeroCount_via_argument (T : ℝ) (hT : 0 < T)
```

## ZetaMeanSquare (7)
```
theorem chi_zeta_eq_factor {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
lemma integral_cpow_frac_it (T : ℝ) (n m : ℕ) (n_pos : 0 < n) (m_pos : 0 < m) (h_ne : n ≠ m) :
theorem fourth_moment_zeta_half_asymp [ZetaFourthMomentBound] :
theorem mean_square_zeta_half_asymp [ZetaMeanSquareHalfBound] :
theorem mean_square_zeta_sigma_asymp [ZetaMeanSquareSigmaBound] {σ : ℝ} (hσ : 1/2 < σ) (hσ' : σ ≠ 1) :
lemma norm_chi_zeta_half (t : ℝ) : ‖chi_zeta (1/2 + I * t)‖ = 1 := by
lemma diagonal_term_sigma_gt_half (σ : ℝ) (hσ : 1/2 < σ) (T : ℝ) :
```

## ZetaMoments (3)
```
theorem zeta_second_moment (T : ℝ) (hT : T ≥ 2) :
theorem zeta_fourth_moment_bound (T : ℝ) (hT : T ≥ 2) :
theorem zeta_mean_square_vertical_lines (σ : ℝ) (hσ : σ > 1/2) (T : ℝ) (hT : T ≥ 2) :
```

## ZetaZeroInfrastructure (14)
```
lemma C_pos : 0 < C := by
lemma c_zero_free_pos : 0 < c_zero_free := by
lemma term_norm_eq (x : ℝ) (hx : 0 < x) (ρ : ℂ) :
lemma sum_abs_bound (x : ℝ) (hx : 1 < x) (T : ℝ) :
lemma zero_free_region_bound (x : ℝ) (hx : 1 < x) (ρ : ℂ) (h_zero_free : ρ.re ≤ 1 - c_zero_free / Real.log (abs ρ.im)) :
lemma zeta_zeros_isolated (s : ℂ) (hs : riemannZeta s = 0) (h_ne_one : s ≠ 1) :
lemma criticalBox_compact (T : ℝ) : IsCompact (criticalBox T) := by
lemma no_zeros_on_boundary (s : ℂ) (h_re : s.re = 0 ∨ s.re = 1) : riemannZeta s ≠ 0 := by
lemma finite_subset_of_compact_discrete {X : Type*} [TopologicalSpace X] {S : Set X} (h_compact : IsCompact S) (h_discrete : DiscreteTopology S) : Set.Finite S := by
lemma zetaZerosUpTo_eq_closed_inter (T : ℝ) :
lemma isClosed_zeta_zeros : IsClosed {s : ℂ | riemannZeta s = 0} := by
lemma zetaZerosUpTo_compact (T : ℝ) : IsCompact (zetaZerosUpTo T) := by
lemma finite_zeros (T : ℝ) : Set.Finite (zetaZerosUpTo T) := by
lemma sum_split (T : ℝ) (f : ℂ → ℂ) :
```
