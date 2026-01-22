# Littlewood Project - Complete Lemma Index

**Generated:** 2026-01-21
**Task:** 76

## Statistics
- Total theorems/lemmas:      304
- Files with sorry:      119 lines

---

## By File

### Littlewood/Basic/ChebyshevFunctions.lean
```
43:theorem chebyshevPsi_sub_chebyshevTheta_isBigO :
66:theorem chebyshevTheta_le (x : ℝ) (hx : 1 ≤ x) : θ x ≤ 2 * x := by
78:theorem chebyshevPsi_le (x : ℝ) (hx : 1 ≤ x) : ψ x ≤ 6 * x := by
91:theorem chebyshevTheta_asymptotic : Tendsto (fun x => θ x / x) atTop (nhds 1) := by
99:theorem chebyshevPsi_asymptotic : Tendsto (fun x => ψ x / x) atTop (nhds 1) := by
107:theorem chebyshevTheta_eventually_ge : ∀ᶠ x in atTop, x / 2 ≤ θ x := by
124:theorem chebyshevTheta_two : θ 2 = Real.log 2 := by
129:theorem chebyshevPsi_two : ψ 2 = Real.log 2 := by
```

### Littlewood/Basic/LogarithmicIntegral.lean
```
73:theorem logarithmicIntegral_of_le_two {x : ℝ} (hx : x ≤ 2) : li x = 0 := by
78:theorem logarithmicIntegral_two : li 2 = 0 := logarithmicIntegral_of_le_two le_rfl
80:theorem logarithmicIntegral_nonneg {x : ℝ} (_hx : 2 ≤ x) : 0 ≤ li x := by
105:theorem logarithmicIntegral_pos {x : ℝ} (hx : 2 < x) : 0 < li x := by
122:theorem logarithmicIntegral_strictMono : StrictMonoOn li (Set.Ici 2) := by
162:theorem logarithmicIntegral_mono {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : li x ≤ li y := by
174:theorem logarithmicIntegral_sub {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
200:theorem logarithmicIntegral_integration_by_parts {x : ℝ} (hx : 2 < x) :
287:theorem logarithmicIntegral_asymptotic :
343:theorem logarithmicIntegral_bigO_one :
426:theorem logarithmicIntegral_bigO_two :
455:theorem logarithmicIntegral_expansion (n : ℕ) :
548:theorem logarithmicIntegral_gt_divLog {x : ℝ} (hx : 2 < x) :
586:theorem logarithmicIntegral_lt_bound {x : ℝ} (hx : 2 ≤ x) :
634:theorem logarithmicIntegral_sub_divLog_tendsto :
773:theorem logarithmicIntegral_hasDerivAt {x : ℝ} (hx : 2 < x) :
810:theorem logarithmicIntegral_continuousOn : ContinuousOn li (Set.Ioi 2) := by
815:theorem logarithmicIntegral_deriv {x : ℝ} (hx : 2 < x) :
826:theorem logarithmicIntegral_lower_bound {x : ℝ} (hx : 2 ≤ x) :
833:theorem logarithmicIntegral_upper_bound {x : ℝ} (hx : 2 ≤ x) :
```

### Littlewood/Basic/OmegaNotation.lean
```
81:theorem IsOmegaPlusMinus.isOmega (h : f =Ω±[g]) : f =Ω[g] := by
90:theorem IsOmegaPlus.isOmega (h : f =Ω₊[g]) (_hg : ∀ᶠ x in atTop, 0 < g x) : f =Ω[g] := by
98:theorem IsOmegaMinus.neg_isOmegaPlus (h : f =Ω₋[g]) : (fun x => -f x) =Ω₊[g] := by
107:theorem IsOmegaPlus.neg_isOmegaMinus (h : f =Ω₊[g]) : (fun x => -f x) =Ω₋[g] := by
116:theorem IsOmegaPlusMinus.neg (h : f =Ω±[g]) : (fun x => -f x) =Ω±[g] :=
124:theorem IsOmegaPlus.frequently_ge (h : f =Ω₊[g]) :
129:theorem IsOmegaMinus.frequently_le (h : f =Ω₋[g]) :
134:theorem IsOmegaPlusMinus.sign_changes (h : f =Ω±[g]) (hg : ∀ᶠ x in atTop, 0 < g x) :
165:theorem isOmegaPlusMinus_of_limsup_liminf
210:theorem IsOmegaPlusMinus.const_mul (h : f =Ω±[g]) (c : ℝ) (hc : 0 < c) :
230:theorem IsOmegaPlusMinus.div_const (h : f =Ω±[g]) (c : ℝ) (hc : 0 < c) :
```

### Littlewood/Bridge/FromGauss.lean
```
35:theorem chebyshevPsi_asymptotic_from_gauss :
44:theorem chebyshevTheta_asymptotic_from_gauss :
53:theorem chebyshevTheta_eventually_ge_from_gauss :
```

### Littlewood/CoreLemmas/DirichletApproximation.lean
```
47:theorem distToInt_nonneg (x : ℝ) : 0 ≤ ‖x‖ᵢₙₜ := abs_nonneg _
49:theorem distToInt_le_half (x : ℝ) : ‖x‖ᵢₙₜ ≤ 1/2 := by
54:theorem distToInt_zero : ‖(0 : ℝ)‖ᵢₙₜ = 0 := by simp [distToInt]
56:theorem distToInt_int (n : ℤ) : ‖(n : ℝ)‖ᵢₙₜ = 0 := by
60:theorem distToInt_add_int (x : ℝ) (n : ℤ) : ‖x + n‖ᵢₙₜ = ‖x‖ᵢₙₜ := by
64:theorem distToInt_neg (x : ℝ) : ‖-x‖ᵢₙₜ = ‖x‖ᵢₙₜ := by
80:theorem sin_pi_le_pi_distToInt (x : ℝ) : |sin (π * x)| ≤ π * ‖x‖ᵢₙₜ := by
107:theorem sin_pi_le_half_pi (x : ℝ) : |sin (π * x)| ≤ π / 2 := by
114:theorem sin_sub_sin_le (α β : ℝ) :
143:theorem pigeonhole_cube (K N : ℕ) (_hN : 0 < N) (points : Fin (N^K + 1) → Fin K → ℕ)
167:theorem dirichlet_approximation_simultaneous
244:theorem dirichlet_approximation_simultaneous_infinitely_many
428:theorem dirichlet_for_zeta_zeros (K : ℕ)
439:theorem littlewood_x_choice (N : ℕ) (hN : 2 ≤ N) (n : ℕ) (hn : 1 ≤ n) :
458:theorem sin_approx_when_close (θ n N : ℝ) (_hN : 0 < N)
501:theorem sinc_product_bound (K : ℕ) (θ : Fin K → ℝ) (δ : ℝ) (_hδ : 0 < δ) :
```

### Littlewood/CoreLemmas/LandauLemma.lean
```
140:theorem landau_lemma
161:theorem dirichletIntegral_converges
168:theorem dirichletIntegral_analytic
175:theorem dirichletIntegral_deriv
183:theorem dirichletIntegral_powerSeries
192:theorem radius_exceeds_abscissa
208:theorem landau_extension
221:theorem landau_lemma_series
234:theorem zetaLogDeriv_pole_at_zero (ρ : ℂ) (hρ : riemannZeta ρ = 0)
240:theorem zetaLogDeriv_vonMangoldt (s : ℂ) (hs : 1 < s.re) :
289:theorem lseries_analytic_in_half_plane (f : ℕ → ℂ) :
303:theorem vonMangoldt_lseries_analytic (s : ℂ) (hs : 1 < s.re) :
319:theorem vonMangoldt_lseries_summable (s : ℂ) (hs : 1 < s.re) :
354:theorem vonMangoldt_eq_neg_zeta_logderiv (s : ℂ) (hs : 1 < s.re) :
379:theorem zeta_zero_implies_vonMangoldt_singularity (ρ : ℂ) (hρ : riemannZeta ρ = 0)
```

### Littlewood/CoreLemmas/WeightedAverageFormula.lean
```
138:theorem weighted_average_formula_RH
156:theorem integral_psi_minus_x (x : ℝ) (hx : 1 < x) [IntegralPsiMinusXHyp] :
164:theorem average_of_power (x δ : ℝ) (ρ : ℂ) (hx : 0 < x) (_hδ : 0 < δ) :
239:theorem rh_power_factor (hRH : RiemannHypothesis') (ρ : zetaNontrivialZeros)
274:theorem sinh_imaginary_sin (δ γ : ℝ) :
294:theorem rho_to_gamma_error (hRH : RiemannHypothesis') [RhoToGammaErrorHyp] :
299:theorem sum_over_positive_ordinates (f : ℂ → ℂ)
312:theorem zero_sum_tail (x T : ℝ) (hT : 1 ≤ T) [ZeroSumTailHyp] :
319:theorem main_sum_bound (x M : ℝ) (hM : 2 ≤ M) [MainSumBoundHyp] :
330:theorem aligned_sum_large (M : ℕ) (hM : 2 ≤ M) (n : ℕ) (hn : 1 ≤ n)
```

### Littlewood/Development/Bridge.lean
```
157:lemma hardy_implies_infinite_critical_zeros
168:theorem development_compatible_with_hypotheses : True := trivial
```

### Littlewood/Development/HardyTheorem.lean
```
87:theorem riemannSiegelTheta_asymptotic_stub (t : ℝ) (ht : t > 0) :
111:theorem hardyZ_real (t : ℝ) : (hardyZ t).im = 0 := by
123:theorem hardyZ_zero_iff (t : ℝ) :
138:theorem sign_change_implies_zero (t₁ t₂ : ℝ) (ht : t₁ < t₂)
166:theorem hardyZ_is_real (t : ℝ) : (hardyZ t).im = 0 := by
172:lemma hardyZ_eq_re (t : ℝ) : hardyZ t = (hardyZ t).re := by
177:theorem hardyZ_continuous : Continuous hardyZ := by
184:theorem hardyZ_real_val_continuous : Continuous hardyZ_real_val := by
189:theorem hardyZ_not_zero : ∃ t : ℝ, hardyZ t ≠ 0 := by
198:theorem hardyZ_growth_bound :
210:theorem hardyZ_sign_change_in_interval :
217:theorem sign_change_gives_zero (t₁ t₂ : ℝ) (ht : t₁ < t₂)
232:theorem hardy_from_sign_changes :
254:theorem hardy_infinitely_many_zeros_stub :
260:theorem hardy_zeros_density_stub :
```

### Littlewood/Development/LandauLemma.lean
```
138:lemma partial_sums_monotone
158:lemma term_comparison
178:lemma cpow_ofReal_ofReal_im (x : ℝ) (hx : 0 < x) (y : ℝ) : ((x : ℂ) ^ (y : ℂ)).im = 0 := by
198:lemma lseries_term_im_eq_zero (a : ℕ → ℝ) (σ : ℝ) (n : ℕ) :
227:lemma tsum_im_eq_zero_of_forall_im_eq_zero {f : ℕ → ℂ}
248:lemma lseries_real_on_real_axis (a : ℕ → ℝ) (_ha : ∀ n, 0 ≤ a n) (σ : ℝ)
258:lemma abscissa_characterization (f : ℕ → ℂ) (s : ℂ)
264:lemma lseries_analytic_on_half_plane (f : ℕ → ℂ) :
269:lemma lseries_smooth (f : ℕ → ℂ) (s : ℂ) (hs : LSeries.abscissaOfAbsConv f < s.re) (m : ℕ) :
358:theorem landau_lemma_stub
```

### Littlewood/Development/MainTheoremsVerification.lean
```
80:theorem main_theorems_compile : True := by
116:theorems are fully proved, they can replace the sorried instances.
```

### Littlewood/Development/TypeBridge.lean
```
128:lemma summatory_zero (a : ℕ → ℂ) : summatory a 0 = 0 := by
134:lemma summatory_nat (a : ℕ → ℂ) (n : ℕ) :
140:lemma summatory_const_on_Ico (a : ℕ → ℂ) (n : ℕ) (x : ℝ) (hx : x ∈ Ico (n : ℝ) (n + 1)) :
152:lemma summatory_step (a : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n) :
166:lemma summatory_eq_mathlib_form (a : ℕ → ℂ) (x : ℝ) :
174:theorem lseries_integral_uses_summatory (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
307:theorem lseries_analytic_from_mathlib (f : ℕ → ℂ) (s : ℂ)
345:theorem partial_sums_monotone (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
367:theorem nonneg_divergent_partial_sums_tendsto_top
390:theorem lseries_real_tendsto_top_of_nonneg_divergent
399:theorem landau_lseries_not_analytic_at_boundary
476:theorem neg_zeta_logderiv_eq_vonMangoldt (s : ℂ) (hs : 1 < s.re) :
```

### Littlewood/Development/ZeroFreeRegion.lean
```
89:theorem trig_inequality (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) ≥ 0 := by
98:theorem trig_identity (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
143:theorem trig_coefficients_explanation (θ : ℝ) :
149:theorem trig_inequality_via_norm (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) ≥ 0 := by
163:theorem zeta_ne_zero_on_one_line (s : ℂ) (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
170:theorem zeta_ne_zero_on_critical_line (t : ℝ) : riemannZeta (1 + t * I) ≠ 0 := by
178:theorem zeta_residue_at_one : Filter.Tendsto (fun s => (s - 1) * riemannZeta s)
183:theorem zeta_euler_product (s : ℂ) (hs : 1 < s.re) :
188:theorem zeta_euler_product_log (s : ℂ) (hs : 1 < s.re) :
193:theorem neg_zeta_logderiv_eq_vonMangoldt (s : ℂ) (hs : 1 < s.re) :
250:theorem mertens_inequality_stub (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
267:theorem zero_free_region_stub :
311:theorem zeta_product_lower_bound (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
329:lemma zero_forces_zeta_large (σ : ℝ) (t : ℝ) (hσ : 1 < σ) (ht : t ≠ 0)
341:lemma zeta_pole_behavior :
360:lemma neg_zeta_logderiv_expansion :
376:lemma neg_zeta_logderiv_re_bound :
397:theorem de_la_vallee_poussin_zero_free :
```

### Littlewood/ExplicitFormulas/ConversionFormulas.lean
```
35:theorem theta_from_psi (x : ℝ) (hx : 1 < x) :
81:theorem theta_psi_first_correction [ThetaPsiFirstCorrectionHyp] (x : ℝ) (hx : 2 ≤ x) :
87:theorem theta_psi_simple (x : ℝ) (hx : 2 ≤ x) :
107:theorem theta_psi_RH (hRH : ZetaZeros.RiemannHypothesis') [ThetaPsiRHHyp hRH] (x : ℝ) (hx : 2 ≤ x) :
127:theorem pi_from_theta_summation [PiFromThetaSummationHyp] (x : ℝ) (hx : 2 < x) :
146:theorem li_expansion [LiExpansionHyp] (x : ℝ) (hx : 2 < x) :
163:theorem pi_li_from_theta [PiLiFromThetaHyp] (x : ℝ) (hx : 2 < x) :
181:theorem pi_li_from_psi_RH (hRH : ZetaZeros.RiemannHypothesis') [PiLiFromPsiRHHyp hRH]
201:theorem omega_psi_to_theta [OmegaPsiToThetaHyp] (f : ℝ → ℝ)
219:theorem omega_theta_to_pi_li [OmegaThetaToPiLiHyp] (f : ℝ → ℝ)
227:theorem omega_psi_to_pi_li [OmegaPsiToThetaHyp] [OmegaThetaToPiLiHyp] (f : ℝ → ℝ)
```

### Littlewood/ExplicitFormulas/ExplicitFormulaPsi.lean
```
42:theorem chebyshevPsi0_eq_of_not_int {x : ℝ} (hx : x ≠ ⌊x⌋) : ψ₀ x = chebyshevPsi x := by
60:theorem explicit_formula_psi (x : ℝ) (hx : 1 < x) [ExplicitFormulaPsiHyp] :
67:theorem explicit_formula_psi_conditional (x : ℝ) (hx : 1 < x) [ExplicitFormulaPsiHyp] :
98:theorem explicit_formula_psiSmoothed (k : ℕ) (x : ℝ) (hx : 1 < x)
139:theorem explicit_formula_integral (x : ℝ) (hx : 1 < x) [ExplicitFormulaIntegralHyp] :
147:theorem explicit_formula_double_integral (x : ℝ) (hx : 1 < x)
189:theorem psi_mellin (x : ℝ) (hx : 0 < x) (c : ℝ) (hc : 1 < c) [PsiMellinHyp] :
200:theorem mellin_contour_shift (x : ℝ) (hx : 1 < x) (c : ℝ) (hc : 1 < c)
248:theorem zero_sum_bound_RH (hRH : RiemannHypothesis') (x : ℝ) (hx : 2 ≤ x)
255:theorem psi_error_bound (x : ℝ) (hx : 2 ≤ x) [PsiErrorBoundHyp] :
260:theorem psi_error_bound_RH (hRH : RiemannHypothesis') (x : ℝ) (hx : 2 ≤ x)
```

### Littlewood/Main/LittlewoodPi.lean
```
42:theorem littlewood_pi_li :
57:theorem pi_gt_li_infinitely_often :
75:theorem pi_lt_li_infinitely_often :
93:theorem pi_minus_li_sign_changes :
101:theorem first_crossover_bound :
107:theorem logarithmic_density_positive :
```

### Littlewood/Main/LittlewoodPsi.lean
```
37:theorem littlewood_psi_omega_plus_RH (hRH : ZetaZeros.RiemannHypothesis) :
43:theorem littlewood_psi_omega_minus_RH (hRH : ZetaZeros.RiemannHypothesis) :
49:theorem littlewood_psi_assuming_RH (hRH : ZetaZeros.RiemannHypothesis) :
59:theorem dirichlet_step (M : ℕ) (hM : 10 ≤ M) :
66:theorem x_choice (M n : ℕ) (hM : 2 ≤ M) (hn : 1 ≤ n) (sign : Bool) :
76:theorem zero_sum_large (M n : ℕ) (hM : 10 ≤ M) (hn : 1 ≤ n)
88:theorem average_implies_large (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ)
108:theorem littlewood_psi_RH_false (hRH : ¬ZetaZeros.RiemannHypothesis) :
118:theorem littlewood_psi :
127:theorem littlewood_limsup_lower :
149:theorem littlewood_liminf_upper :
```

### Littlewood/Mertens/MertensFirst.lean
```
44:lemma sum_log_eq_log_factorial (n : ℕ) :
63:lemma log_factorial_eq_sum_vonMangoldt_floor (n : ℕ) :
114:lemma sum_vonMangoldt_fract_le_psi (n : ℕ) :
136:lemma sum_vonMangoldt_div_main_estimate (n : ℕ) (hn : n ≠ 0) :
170:lemma log_factorial_le (n : ℕ) : Real.log n ! ≤ n * Real.log n + n := by
186:lemma log_factorial_ge (n : ℕ) (hn : 1 ≤ n) :
199:theorem sum_vonMangoldt_div_eq_log_plus_O1 :
258:lemma sum_vonMangoldt_div_eq_sum_primes_plus_powers (n : ℕ) :
290:lemma sum_prime_powers_bounded :
337:theorem mertens_first :
373:theorem mertens_first_continuous :
```

### Littlewood/Oscillation/SchmidtPi.lean
```
34:theorem pi_li_oscillation_minus [Schmidt.PsiOscillationSqrtHyp] :
45:theorem pi_li_oscillation_RH_false (ε : ℝ) (hε : 0 < ε) (hRH_false : 1/2 < Θ)
65:theorem schmidt_limitation [Schmidt.PsiOscillationSqrtHyp] :
75:theorem littlewood_needed_for_omega_plus :
```

### Littlewood/Oscillation/SchmidtTheorem.lean
```
126:theorem schmidt_psi_oscillation (ε : ℝ) (hε : 0 < ε) [SchmidtPsiOscillationHyp] :
131:theorem psi_oscillation_sqrt [PsiOscillationSqrtHyp] :
140:theorem mellin_psi_identity (s : ℂ) (hs : 1 < s.re) [MellinPsiIdentityHyp] :
147:theorem omega_minus_necessity (ε : ℝ) (hε : 0 < ε)
153:theorem omega_plus_necessity (ε : ℝ) (hε : 0 < ε)
165:theorem hardy_critical_line_zeros [HardyCriticalLineZerosHyp] :
170:theorem psi_oscillation_from_critical_zeros [PsiOscillationFromCriticalZerosHyp] :
179:theorem theta_oscillation_minus [ThetaOscillationMinusHyp] :
184:theorem theta_oscillation_RH (hRH : ZetaZeros.RiemannHypothesis) [ThetaOscillationRHHyp] :
```

### Littlewood/ZetaZeros/SupremumRealPart.lean
```
96:theorem zetaZeroRealPart_lt_one {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
100:theorem zetaZeroRealPart_pos {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
104:theorem zetaZeroRealParts_bddAbove : BddAbove zetaZeroRealParts := by
111:theorem zetaZeroRealParts_bddBelow : BddBelow zetaZeroRealParts := by
118:theorem zetaZeroRealParts_nonempty [FirstZeroOrdinateHyp] : zetaZeroRealParts.Nonempty := by
126:theorem zetaZeroSupRealPart_le_one [FirstZeroOrdinateHyp] : Θ ≤ 1 := by
133:theorem zetaZeroSupRealPart_pos [FirstZeroOrdinateHyp] : 0 < Θ := by
140:theorem zetaZeroSupRealPart_ge_half [FirstZeroOrdinateHyp] : 1/2 ≤ Θ := by
157:theorem zetaZeroSupRealPart_achieved [FirstZeroOrdinateHyp] :
185:theorem RiemannHypothesis_iff [FirstZeroOrdinateHyp] : RiemannHypothesis ↔ Θ = 1/2 := by
217:theorem zetaZeroSupRealPart_eq_half_of_RH [FirstZeroOrdinateHyp]
222:theorem zetaZeroSupRealPart_gt_half_of_not_RH [FirstZeroOrdinateHyp]
236:theorem zeroFreeRegion_delaValleePoussin [ZeroFreeRegionHyp] :
242:theorem zetaZeroSupRealPart_eq_one_or_half [FirstZeroOrdinateHyp]
248:theorem zetaZeroInfRealPart [FirstZeroOrdinateHyp] : sInf zetaZeroRealParts = 1 - Θ := by
279:theorem chebyshev_error_bound_Theta [FirstZeroOrdinateHyp] [ChebyshevErrorBoundThetaHyp]
309:theorem chebyshev_error_bound_RH [FirstZeroOrdinateHyp]
321:theorem chebyshev_error_bound_zeroFree [FirstZeroOrdinateHyp]
```

### Littlewood/ZetaZeros/ZeroCountingFunction.lean
```
55:theorem logDeriv_sub_const (x a : ℂ) :
78:theorem mem_zetaNontrivialZeros {s : ℂ} :
82:theorem mem_zetaNontrivialZerosPos {s : ℂ} :
91:theorem riemannXi_zero_iff_completed {s : ℂ} (hpos : 0 < s.re) (hlt : s.re < 1) :
114:theorem logDeriv_riemannXi (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
152:theorem completedRiemannZeta_eq_zero_iff_riemannZeta {s : ℂ} (hs : 0 < s.re) :
172:theorem mem_zetaNontrivialZeros_iff_completed {s : ℂ} :
185:theorem mem_zetaNontrivialZeros_iff_xi {s : ℂ} :
215:theorem zeroCountingFunction_eq_ncard (T : ℝ) : N T = (zerosUpTo T).ncard := rfl
226:theorem zerosUpTo_eq_completed (T : ℝ) : zerosUpTo T = completedZerosUpTo T := by
247:theorem zerosUpTo_eq_xi (T : ℝ) : zerosUpTo T = xiZerosUpTo T := by
264:theorem zerosUpTo_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : zerosUpTo T₁ ⊆ zerosUpTo T₂ := by
297:theorem finite_zeros_le (T : ℝ) : (zerosUpTo T).Finite := by
431:theorem zeroCountingFunction_finite (T : ℝ) : (zeroCountingFunction T : ℕ∞) < ⊤ := by
435:theorem zerosUpTo_finite (T : ℝ) : (zerosUpTo T).Finite := finite_zeros_le T
438:theorem completedZerosUpTo_finite (T : ℝ) : (completedZerosUpTo T).Finite := by
442:theorem xiZerosUpTo_finite (T : ℝ) : (xiZerosUpTo T).Finite := by
454:theorem zeroCountingFunction_nonneg (T : ℝ) : 0 ≤ N T := Nat.zero_le _
456:theorem zeroCountingFunction_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : N T₁ ≤ N T₂ := by
459:theorem zeroCountingFunction_neg (T : ℝ) (hT : T ≤ 0) : N T = 0 := by
```

### Littlewood/ZetaZeros/ZeroDensity.lean
```
45:theorem ZeroOrdinate.pos (γ : ZeroOrdinate) : 0 < (γ : ℝ) := by
50:theorem zetaZeroOrdinates_countable : zetaZeroOrdinates.Countable := by
73:lemma exists_zeroOfOrdinate (γ : ZeroOrdinate) :
82:lemma zeroOfOrdinate_im (γ : ZeroOrdinate) :
86:lemma zeroOfOrdinate_injective : Function.Injective zeroOfOrdinate := by
212:theorem summable_inv_gamma_pow [ZeroCountingSummabilityHyp] (α : ℝ) (hα : 1 < α) :
217:theorem summable_inv_gamma_sq [ZeroCountingSummabilityHyp] :
222:theorem tsum_inv_gamma_sq_pos [ZeroCountingSummabilityHyp] [FirstZeroOrdinateHyp] :
238:theorem summable_inv_gamma_gamma_add_one [ZeroCountingSummabilityHyp] :
272:theorem ordinatesUpTo_finite (T : ℝ) : (ordinatesUpTo T).Finite := by
295:theorem ordinatesUpTo_ncard_le (T : ℝ) :
340:theorem sum_inv_gamma_le_log_sq (T : ℝ) (hT : 4 ≤ T) :
371:theorem sum_inv_gamma_asymptotic [ZeroCountingSumInvGammaAsymptoticHyp] :
388:theorem sum_one_eq_N [ZeroCountingSumOneEqHyp] (T : ℝ) :
403:theorem sum_inv_gamma_sq_tail (T : ℝ) (hT : 4 ≤ T) :
434:theorem sum_inv_gamma_sq_tail_asymptotic [ZeroCountingTailSqAsymptoticHyp] :
443:theorem sum_inv_gamma_pow_tail (α : ℝ) (hα : 1 < α) (T : ℝ) (hT : 4 ≤ T) :
473:theorem summable_inv_rho_sq [ZeroCountingSummabilityHyp] :
478:theorem summable_inv_rho_rho_add_one [ZeroCountingSummabilityHyp] :
512:theorem rh_rho_norm_sq (hRH : RiemannHypothesis') (ρ : zetaNontrivialZeros) :
```
