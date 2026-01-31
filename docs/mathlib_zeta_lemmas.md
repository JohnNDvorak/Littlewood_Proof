# Mathlib Zeta Function Lemmas Reference

**Generated:** 2026-01-21
**Task:** 78

## RiemannZeta.lean

```
lemma HurwitzZeta.completedHurwitzZetaEven_zero (s : ℂ) :
lemma HurwitzZeta.completedHurwitzZetaEven₀_zero (s : ℂ) :
lemma HurwitzZeta.completedCosZeta_zero (s : ℂ) :
lemma HurwitzZeta.completedCosZeta₀_zero (s : ℂ) :
lemma completedRiemannZeta_eq (s : ℂ) :
theorem differentiable_completedZeta₀ : Differentiable ℂ completedRiemannZeta₀ :=
theorem differentiableAt_completedZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
theorem completedRiemannZeta₀_one_sub (s : ℂ) :
theorem completedRiemannZeta_one_sub (s : ℂ) :
lemma completedRiemannZeta_residue_one :
lemma HurwitzZeta.hurwitzZetaEven_zero : hurwitzZetaEven 0 = riemannZeta := rfl
lemma HurwitzZeta.cosZeta_zero : cosZeta 0 = riemannZeta := by
lemma HurwitzZeta.hurwitzZeta_zero : hurwitzZeta 0 = riemannZeta := by
lemma HurwitzZeta.expZeta_zero : expZeta 0 = riemannZeta := by
theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
lemma riemannZeta_def_of_ne_zero {s : ℂ} (hs : s ≠ 0) :
theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
theorem completedZeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
theorem zeta_eq_tsum_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < re s) :
theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) :
lemma two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even {k : ℕ} (hk : 2 ≤ k) (hk2 : Even k) :
lemma riemannZeta_residue_one : Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by
theorem tendsto_sub_mul_tsum_nat_cpow :
theorem tendsto_sub_mul_tsum_nat_rpow :
```

## LSeries Files

### AbstractFuncEq.lean
```
lemma WeakFEPair.h_feq' (P : WeakFEPair E) (x : ℝ) (hx : 0 < x) :
lemma hf_zero (P : WeakFEPair E) (r : ℝ) :
lemma hf_zero' (P : WeakFEPair E) :
lemma hf_top' (r : ℝ) : P.f =O[atTop] (· ^ r) := by
lemma hf_zero' (r : ℝ) : P.f =O[𝓝[>] 0] (· ^ r) := by
theorem hasMellin (s : ℂ) : HasMellin P.f s (P.Λ s) :=
lemma Λ_eq : P.Λ = mellin P.f := rfl
lemma symm_Λ_eq : P.symm.Λ = mellin P.g := rfl
theorem differentiable_Λ : Differentiable ℂ P.Λ := fun s ↦
theorem functional_equation (s : ℂ) :
lemma hf_modif_int :
lemma hf_modif_FE (x : ℝ) (hx : 0 < x) :
lemma f_modif_aux1 : EqOn (fun x ↦ P.f_modif x - P.f x + P.f₀)
lemma f_modif_aux2 [CompleteSpace E] {s : ℂ} (hs : P.k < re s) :
lemma Λ₀_eq (s : ℂ) : P.Λ₀ s = P.Λ s + (1 / s) • P.f₀ + (P.ε / (P.k - s)) • P.g₀ := by
lemma symm_Λ₀_eq (s : ℂ) :
theorem differentiable_Λ₀ : Differentiable ℂ P.Λ₀ := P.toStrongFEPair.differentiable_Λ
theorem differentiableAt_Λ {s : ℂ} (hs : s ≠ 0 ∨ P.f₀ = 0) (hs' : s ≠ P.k ∨ P.g₀ = 0) :
theorem hasMellin [CompleteSpace E]
theorem functional_equation₀ (s : ℂ) : P.Λ₀ (P.k - s) = P.ε • P.symm.Λ₀ s :=
```

### Basic.lean
```
lemma term_def (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
lemma term_def₀ {f : ℕ → ℂ} (hf : f 0 = 0) (s : ℂ) (n : ℕ) :
lemma term_zero (f : ℕ → ℂ) (s : ℂ) : term f s 0 = 0 := rfl
lemma term_of_ne_zero {n : ℕ} (hn : n ≠ 0) (f : ℕ → ℂ) (s : ℂ) :
lemma term_of_ne_zero' {s : ℂ} (hs : s ≠ 0) (f : ℕ → ℂ) (n : ℕ) :
lemma term_congr {f g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) (s : ℂ) (n : ℕ) :
lemma pow_mul_term_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
lemma norm_term_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
lemma norm_term_le {f g : ℕ → ℂ} (s : ℂ) {n : ℕ} (h : ‖f n‖ ≤ ‖g n‖) :
lemma norm_term_le_of_re_le_re (f : ℕ → ℂ) {s s' : ℂ} (h : s.re ≤ s'.re) (n : ℕ) :
lemma term_nonneg {a : ℕ → ℂ} {n : ℕ} (h : 0 ≤ a n) (x : ℝ) : 0 ≤ term a x n := by
lemma term_pos {a : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) (h : 0 < a n) (x : ℝ) : 0 < term a x n := by
lemma LSeries_congr {f g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) (s : ℂ) :
lemma LSeriesSummable_congr {f g : ℕ → ℂ} (s : ℂ) (h : ∀ {n}, n ≠ 0 → f n = g n) :
lemma LSeriesSummable.congr' {f g : ℕ → ℂ} (s : ℂ) (h : f =ᶠ[atTop] g) (hf : LSeriesSummable f s) :
lemma LSeriesSummable_congr' {f g : ℕ → ℂ} (s : ℂ) (h : f =ᶠ[atTop] g) :
theorem LSeries.eq_zero_of_not_LSeriesSummable (f : ℕ → ℂ) (s : ℂ) :
theorem LSeriesSummable_zero {s : ℂ} : LSeriesSummable 0 s := by
lemma LSeriesHasSum.LSeriesSummable {f : ℕ → ℂ} {s a : ℂ}
lemma LSeriesHasSum.LSeries_eq {f : ℕ → ℂ} {s a : ℂ}
```

### Convergence.lean
```
lemma LSeries.abscissaOfAbsConv_congr {f g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) :
lemma LSeries.abscissaOfAbsConv_congr' {f g : ℕ → ℂ} (h : f =ᶠ[atTop] g) :
lemma LSeriesSummable_of_abscissaOfAbsConv_lt_re {f : ℕ → ℂ} {s : ℂ}
lemma LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re {f : ℕ → ℂ} {s : ℂ}
lemma LSeriesSummable.abscissaOfAbsConv_le {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable {f : ℕ → ℂ} {x : ℝ}
lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' {f : ℕ → ℂ} {x : EReal}
lemma LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow {f : ℕ → ℂ} {x : ℝ}
lemma LSeries.abscissaOfAbsConv_le_of_isBigO_rpow {f : ℕ → ℂ} {x : ℝ}
lemma LSeries.abscissaOfAbsConv_le_of_le_const {f : ℕ → ℂ} (h : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C) :
lemma LSeries.abscissaOfAbsConv_le_one_of_isBigO_one {f : ℕ → ℂ} (h : f =O[atTop] fun _ ↦ (1 : ℝ)) :
lemma LSeries.summable_real_of_abscissaOfAbsConv_lt {f : ℕ → ℝ} {x : ℝ}
lemma LSeries.abscissaOfAbsConv_binop_le {F : (ℕ → ℂ) → (ℕ → ℂ) → (ℕ → ℂ)}
```

### Convolution.lean
```
lemma toArithmeticFunction_congr {R : Type*} [Zero R] {f f' : ℕ → R}
lemma ArithmeticFunction.toArithmeticFunction_eq_self {R : Type*} [Zero R]
lemma LSeries.convolution_congr {R : Type*} [Semiring R] {f f' g g' : ℕ → R}
lemma ArithmeticFunction.coe_mul {R : Type*} [Semiring R] (f g : ArithmeticFunction R) :
lemma convolution_def {R : Type*} [Semiring R] (f g : ℕ → R) :
lemma convolution_map_zero {R : Type*} [Semiring R] (f g : ℕ → R) : (f ⍟ g) 0 = 0 := by
lemma term_convolution (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
lemma term_convolution' (f g : ℕ → ℂ) (s : ℂ) :
lemma LSeriesHasSum.convolution {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
lemma LSeries_convolution' {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
lemma LSeries_convolution {f g : ℕ → ℂ} {s : ℂ}
lemma LSeriesSummable.convolution {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
lemma LSeries.abscissaOfAbsConv_convolution_le (f g : ℕ → ℂ) :
lemma LSeriesHasSum_mul {f g : ArithmeticFunction ℂ} {s a b : ℂ} (hf : LSeriesHasSum ↗f s a)
lemma LSeries_mul' {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
lemma LSeries_mul {f g : ArithmeticFunction ℂ} {s : ℂ}
lemma LSeriesSummable_mul {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
```

### Deriv.lean
```
lemma LSeries.hasDerivAt_term (f : ℕ → ℂ) (n : ℕ) (s : ℂ) :
lemma LSeries_hasDerivAt {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
lemma LSeries_deriv {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
lemma LSeries_deriv_eqOn {f : ℕ → ℂ} :
lemma LSeriesSummable_logMul_of_lt_re {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
lemma LSeries.abscissaOfAbsConv_logMul {f : ℕ → ℂ} :
lemma LSeries.absicssaOfAbsConv_logPowMul {f : ℕ → ℂ} {m : ℕ} :
lemma LSeries_iteratedDeriv {f : ℕ → ℂ} (m : ℕ) {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
lemma LSeries_differentiableOn (f : ℕ → ℂ) :
lemma LSeries_analyticOnNhd (f : ℕ → ℂ) :
lemma LSeries_analyticOn (f : ℕ → ℂ) :
```

### Dirichlet.lean
```
lemma ArithmeticFunction.one_eq_delta : ↗(1 : ArithmeticFunction ℂ) = δ := by
lemma not_LSeriesSummable_moebius_at_one : ¬ LSeriesSummable ↗μ 1 := by
lemma LSeriesSummable_moebius_iff {s : ℂ} : LSeriesSummable ↗μ s ↔ 1 < s.re := by
lemma abscissaOfAbsConv_moebius : abscissaOfAbsConv ↗μ = 1 := by
lemma ArithmeticFunction.const_one_eq_zeta {R : Type*} [AddMonoidWithOne R] {n : ℕ} (hn : n ≠ 0) :
lemma LSeries.one_convolution_eq_zeta_convolution {R : Type*} [Semiring R] (f : ℕ → R) :
lemma LSeries.convolution_one_eq_convolution_zeta {R : Type*} [Semiring R] (f : ℕ → R) :
lemma isMultiplicative_toArithmeticFunction {N : ℕ} {R : Type*} [CommMonoidWithZero R]
lemma apply_eq_toArithmeticFunction_apply {N : ℕ} {R : Type*} [CommMonoidWithZero R]
lemma mul_convolution_distrib {R : Type*} [CommSemiring R] {n : ℕ} (χ : DirichletCharacter R n)
lemma mul_delta {n : ℕ} (χ : DirichletCharacter ℂ n) : ↗χ * δ = δ :=
lemma delta_mul {n : ℕ} (χ : DirichletCharacter ℂ n) : δ * ↗χ = δ :=
lemma convolution_mul_moebius {n : ℕ} (χ : DirichletCharacter ℂ n) : ↗χ ⍟ (↗χ * ↗μ) = δ := by
lemma modZero_eq_delta {χ : DirichletCharacter ℂ 0} : ↗χ = δ := by
lemma modOne_eq_one {R : Type*} [CommMonoidWithZero R] {χ : DirichletCharacter R 1} :
lemma LSeries_modOne_eq : L ↗χ₁ = L 1 :=
lemma not_LSeriesSummable_at_one {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) :
lemma LSeriesSummable_of_one_lt_re {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
lemma LSeriesSummable_iff {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) {s : ℂ} :
lemma absicssaOfAbsConv_eq_one {N : ℕ} (hn : N ≠ 0) (χ : DirichletCharacter ℂ N) :
```

### DirichletContinuation.lean
```
lemma LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
lemma deriv_LFunction_eq_deriv_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
lemma differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
lemma differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
lemma Even.LFunction_neg_two_mul_nat_add_one {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) :
lemma Even.LFunction_neg_two_mul_nat {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) [NeZero n] :
lemma LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
lemma LFunctionTrivChar_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
lemma LFunctionTrivChar_residue_one :
lemma Even.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Even) (s : ℂ) :
lemma Odd.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) (s : ℂ) :
lemma completedLFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
lemma differentiableAt_completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ)
lemma differentiable_completedLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
lemma LFunction_eq_completed_div_gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ)
lemma rootNumber_modOne (χ : DirichletCharacter ℂ 1) : rootNumber χ = 1 := by
theorem completedLFunction_one_sub {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
lemma LFunctionTrivChar₁_apply_one_ne_zero : LFunctionTrivChar₁ n 1 ≠ 0 := by
lemma differentiable_LFunctionTrivChar₁ : Differentiable ℂ (LFunctionTrivChar₁ n) := by
lemma deriv_LFunctionTrivChar₁_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
```

### HurwitzZeta.lean
```
lemma hurwitzZetaEven_eq (a : UnitAddCircle) (s : ℂ) :
lemma hurwitzZetaOdd_eq (a : UnitAddCircle) (s : ℂ) :
lemma differentiableAt_hurwitzZeta (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 1) :
lemma hasSum_hurwitzZeta_of_one_lt_re {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
lemma hurwitzZeta_residue_one (a : UnitAddCircle) :
lemma differentiableAt_hurwitzZeta_sub_one_div (a : UnitAddCircle) :
lemma tendsto_hurwitzZeta_sub_one_div_nhds_one (a : UnitAddCircle) :
lemma differentiable_hurwitzZeta_sub_hurwitzZeta (a b : UnitAddCircle) :
lemma cosZeta_eq (a : UnitAddCircle) (s : ℂ) :
lemma sinZeta_eq (a : UnitAddCircle) (s : ℂ) :
lemma hasSum_expZeta_of_one_lt_re (a : ℝ) {s : ℂ} (hs : 1 < re s) :
lemma differentiableAt_expZeta (a : UnitAddCircle) (s : ℂ) (hs : s ≠ 1 ∨ a ≠ 0) :
lemma differentiable_expZeta_of_ne_zero {a : UnitAddCircle} (ha : a ≠ 0) :
lemma LSeriesHasSum_exp (a : ℝ) {s : ℂ} (hs : 1 < re s) :
lemma hurwitzZeta_one_sub (a : UnitAddCircle) {s : ℂ}
lemma expZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ 1 - n) :
```

### HurwitzZetaEven.lean
```
lemma evenKernel_def (a x : ℝ) :
lemma evenKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : evenKernel a x = 0 := by
lemma cosKernel_def (a x : ℝ) : ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x) := by
lemma cosKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : cosKernel a x = 0 := by
lemma evenKernel_eq_cosKernel_of_zero : evenKernel 0 = cosKernel 0 := by
lemma evenKernel_neg (a : UnitAddCircle) (x : ℝ) : evenKernel (-a) x = evenKernel a x := by
lemma cosKernel_neg (a : UnitAddCircle) (x : ℝ) : cosKernel (-a) x = cosKernel a x := by
lemma continuousOn_evenKernel (a : UnitAddCircle) : ContinuousOn (evenKernel a) (Ioi 0) := by
lemma continuousOn_cosKernel (a : UnitAddCircle) : ContinuousOn (cosKernel a) (Ioi 0) := by
lemma evenKernel_functional_equation (a : UnitAddCircle) (x : ℝ) :
lemma hasSum_int_evenKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
lemma hasSum_int_cosKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
lemma hasSum_int_evenKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
lemma hasSum_int_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
lemma hasSum_nat_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
lemma isBigO_atTop_evenKernel_sub (a : UnitAddCircle) : ∃ p : ℝ, 0 < p ∧
lemma isBigO_atTop_cosKernel_sub (a : UnitAddCircle) :
lemma hurwitzEvenFEPair_zero_symm :
lemma hurwitzEvenFEPair_neg (a : UnitAddCircle) : hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a := by
lemma completedHurwitzZetaEven_eq (a : UnitAddCircle) (s : ℂ) :
```

### HurwitzZetaOdd.lean
```
lemma jacobiTheta₂''_conj (z τ : ℂ) :
lemma jacobiTheta₂''_add_left (z τ : ℂ) : jacobiTheta₂'' (z + 1) τ = jacobiTheta₂'' z τ := by
lemma jacobiTheta₂''_neg_left (z τ : ℂ) : jacobiTheta₂'' (-z) τ = -jacobiTheta₂'' z τ := by
lemma jacobiTheta₂'_functional_equation' (z τ : ℂ) :
lemma oddKernel_def (a x : ℝ) : ↑(oddKernel a x) = jacobiTheta₂'' a (I * x) := by
lemma oddKernel_def' (a x : ℝ) : ↑(oddKernel ↑a x) = cexp (-π * a ^ 2 * x) *
lemma oddKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : oddKernel a x = 0 := by
lemma sinKernel_def (a x : ℝ) : ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) / (-2 * π) := by
lemma sinKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : sinKernel a x = 0 := by
lemma oddKernel_neg (a : UnitAddCircle) (x : ℝ) : oddKernel (-a) x = -oddKernel a x := by
lemma sinKernel_neg (a : UnitAddCircle) (x : ℝ) :
lemma continuousOn_oddKernel (a : UnitAddCircle) : ContinuousOn (oddKernel a) (Ioi 0) := by
lemma continuousOn_sinKernel (a : UnitAddCircle) : ContinuousOn (sinKernel a) (Ioi 0) := by
lemma oddKernel_functional_equation (a : UnitAddCircle) (x : ℝ) :
lemma hasSum_int_oddKernel (a : ℝ) {x : ℝ} (hx : 0 < x) :
lemma hasSum_int_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) : HasSum
lemma hasSum_nat_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
lemma isBigO_atTop_oddKernel (a : UnitAddCircle) :
lemma isBigO_atTop_sinKernel (a : UnitAddCircle) :
lemma differentiable_completedHurwitzZetaOdd (a : UnitAddCircle) :
```

### HurwitzZetaValues.lean
```
theorem cosZeta_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc 0 1) :
theorem sinZeta_two_mul_nat_add_one (hk : k ≠ 0) (hx : x ∈ Icc 0 1) :
theorem cosZeta_two_mul_nat' (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
theorem sinZeta_two_mul_nat_add_one' (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
theorem hurwitzZetaEven_one_sub_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
theorem hurwitzZetaOdd_neg_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
theorem hurwitzZeta_neg_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
theorem riemannZeta_two_mul_nat {k : ℕ} (hk : k ≠ 0) :
theorem riemannZeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := by
theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90 := by
theorem riemannZeta_neg_nat_eq_bernoulli' (k : ℕ) :
theorem riemannZeta_neg_nat_eq_bernoulli (k : ℕ) :
```

### Injectivity.lean
```
lemma LSeries.abscissaOfAbsConv_add_le (f g : ℕ → ℂ) :
lemma LSeries.abscissaOfAbsConv_sub_le (f g : ℕ → ℂ) :
lemma cpow_mul_div_cpow_eq_div_div_cpow (m n : ℕ) (z : ℂ) (x : ℝ) :
lemma LSeries.tendsto_cpow_mul_atTop {f : ℕ → ℂ} {n : ℕ} (h : ∀ m ≤ n, f m = 0)
lemma LSeries.tendsto_atTop {f : ℕ → ℂ} (ha : abscissaOfAbsConv f < ⊤) :
lemma LSeries_eq_zero_of_abscissaOfAbsConv_eq_top {f : ℕ → ℂ} (h : abscissaOfAbsConv f = ⊤) :
lemma LSeries_eventually_eq_zero_iff' {f : ℕ → ℂ} :
lemma LSeries_eq_zero_iff {f : ℕ → ℂ} (hf : f 0 = 0) :
lemma LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq {f g : ℕ → ℂ}
lemma LSeries.eq_of_LSeries_eventually_eq {f g : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤)
lemma LSeries_eq_iff_of_abscissaOfAbsConv_lt_top {f g : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤)
lemma LSeries_injOn : Set.InjOn LSeries {f | f 0 = 0 ∧ abscissaOfAbsConv f < ⊤} := by
```

### Linearity.lean
```
lemma LSeries.term_add (f g : ℕ → ℂ) (s : ℂ) : term (f + g) s = term f s + term g s := by
lemma LSeries.term_add_apply (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
lemma LSeriesHasSum.add {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
lemma LSeriesSummable.add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
lemma LSeries_add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
lemma LSeries.term_neg (f : ℕ → ℂ) (s : ℂ) : term (-f) s = -term f s := by
lemma LSeries.term_neg_apply (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : term (-f) s n = -term f s n := by
lemma LSeriesHasSum.neg {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
lemma LSeriesSummable.neg {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
lemma LSeriesSummable.neg_iff {f : ℕ → ℂ} {s : ℂ} :
lemma LSeries_neg (f : ℕ → ℂ) (s : ℂ) : LSeries (-f) s = -LSeries f s := by
lemma LSeries.term_sub (f g : ℕ → ℂ) (s : ℂ) : term (f - g) s = term f s - term g s := by
lemma LSeries.term_sub_apply (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
lemma LSeriesHasSum.sub {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
lemma LSeriesSummable.sub {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
lemma LSeries_sub {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
lemma LSeries.term_smul (f : ℕ → ℂ) (c s : ℂ) : term (c • f) s = c • term f s := by
lemma LSeries.term_smul_apply (f : ℕ → ℂ) (c s : ℂ) (n : ℕ) :
lemma LSeriesHasSum.smul {f : ℕ → ℂ} (c : ℂ) {s a : ℂ} (hf : LSeriesHasSum f s a) :
lemma LSeriesSummable.smul {f : ℕ → ℂ} (c : ℂ) {s : ℂ} (hf : LSeriesSummable f s) :
```

### MellinEqDirichlet.lean
```
lemma hasSum_mellin {a : ι → ℂ} {p : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
lemma hasSum_mellin_pi_mul {a : ι → ℂ} {q : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
lemma hasSum_mellin_pi_mul₀ {a : ι → ℂ} {p : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
lemma hasSum_mellin_pi_mul_sq {a : ι → ℂ} {r : ι → ℝ} {F : ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
lemma hasSum_mellin_pi_mul_sq' {a : ι → ℂ} {r : ι → ℝ} {F : ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
```

### Nonvanishing.lean
```
lemma isMultiplicative_zetaMul (χ : DirichletCharacter ℂ N) : χ.zetaMul.IsMultiplicative :=
lemma LSeriesSummable_zetaMul (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
lemma zetaMul_prime_pow_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) {p : ℕ}
lemma zetaMul_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (n : ℕ) :
lemma summable_neg_log_one_sub_mul_prime_cpow {s : ℂ} (hs : 1 < s.re) :
lemma norm_LSeries_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
lemma norm_LFunction_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
lemma LFunctionTrivChar_isBigO_near_one_horizontal :
lemma LFunction_isBigO_horizontal {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
theorem LFunction_ne_zero_of_re_eq_one {s : ℂ} (hs : s.re = 1) (hχs : χ ≠ 1 ∨ s ≠ 1) :
theorem LFunction_ne_zero_of_one_le_re ⦃s : ℂ⦄ (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
theorem LFunction_apply_one_ne_zero (hχ : χ ≠ 1) : LFunction χ 1 ≠ 0 :=
lemma _root_.riemannZeta_ne_zero_of_one_le_re ⦃s : ℂ⦄ (hs : 1 ≤ s.re) :
```

### Positivity.lean
```
lemma iteratedDeriv_alternating {a : ℕ → ℂ} (hn : 0 ≤ a) {x : ℝ}
lemma positive {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1) {x : ℝ} (hx : abscissaOfAbsConv a < x) :
lemma positive_of_differentiable_of_eqOn {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1) {f : ℂ → ℂ}
lemma iteratedDeriv_LSeries_alternating (a : ArithmeticFunction ℂ) (hn : ∀ n, 0 ≤ a n) {x : ℝ}
lemma LSeries_positive {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1) {x : ℝ}
lemma LSeries_positive_of_differentiable_of_eqOn {a : ArithmeticFunction ℂ} (ha₀ : 0 ≤ (a ·))
```

### PrimesInAP.lean
```
lemma tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers {f : ℕ → α}
lemma tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers {f : ℕ → α}
lemma residueClass_nonneg (n : ℕ) : 0 ≤ residueClass a n :=
lemma residueClass_le (n : ℕ) : residueClass a n ≤ vonMangoldt n :=
lemma residueClass_apply_zero : residueClass a 0 = 0 := by
lemma abscissaOfAbsConv_residueClass_le_one :
lemma support_residueClass_prime_div :
lemma summable_residueClass_non_primes_div :
lemma residueClass_apply (ha : IsUnit a) (n : ℕ) :
lemma residueClass_eq (ha : IsUnit a) :
lemma LSeries_residueClass_eq (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
lemma continuousOn_LFunctionResidueClassAux' :
lemma continuousOn_LFunctionResidueClassAux :
lemma eqOn_LFunctionResidueClassAux (ha : IsUnit a) :
lemma LFunctionResidueClassAux_real (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
lemma LSeries_residueClass_lower_bound (ha : IsUnit a) :
lemma not_summable_residueClass_prime_div (ha : IsUnit a) :
theorem infinite_setOf_prime_and_eq_mod (ha : IsUnit a) :
theorem forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : ℕ) :
theorem forall_exists_prime_gt_and_zmodEq (n : ℕ) {q : ℕ} {a : ℤ} (hq : q ≠ 0) (h : IsCoprime a q) :
```

### RiemannZeta.lean
```
lemma HurwitzZeta.completedHurwitzZetaEven_zero (s : ℂ) :
lemma HurwitzZeta.completedHurwitzZetaEven₀_zero (s : ℂ) :
lemma HurwitzZeta.completedCosZeta_zero (s : ℂ) :
lemma HurwitzZeta.completedCosZeta₀_zero (s : ℂ) :
lemma completedRiemannZeta_eq (s : ℂ) :
theorem differentiable_completedZeta₀ : Differentiable ℂ completedRiemannZeta₀ :=
theorem differentiableAt_completedZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
theorem completedRiemannZeta₀_one_sub (s : ℂ) :
theorem completedRiemannZeta_one_sub (s : ℂ) :
lemma completedRiemannZeta_residue_one :
lemma HurwitzZeta.hurwitzZetaEven_zero : hurwitzZetaEven 0 = riemannZeta := rfl
lemma HurwitzZeta.cosZeta_zero : cosZeta 0 = riemannZeta := by
lemma HurwitzZeta.hurwitzZeta_zero : hurwitzZeta 0 = riemannZeta := by
lemma HurwitzZeta.expZeta_zero : expZeta 0 = riemannZeta := by
theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
lemma riemannZeta_def_of_ne_zero {s : ℂ} (hs : s ≠ 0) :
theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
theorem completedZeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
```

### SumCoeff.lean
```
theorem LSeriesSummable_of_sum_norm_bigO
theorem LSeriesSummable_of_sum_norm_bigO_and_nonneg
theorem LSeries_eq_mul_integral (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
theorem LSeries_eq_mul_integral' (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
theorem LSeries_eq_mul_integral_of_nonneg (f : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div
theorem LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg (f : ℕ → ℝ) {l : ℝ}
```

### ZMod.lean
```
lemma LSeriesSummable_of_one_lt_re (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
lemma LFunction_modOne_eq (Φ : ZMod 1 → ℂ) (s : ℂ) :
lemma LFunction_eq_LSeries (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
lemma differentiableAt_LFunction (Φ : ZMod N → ℂ) (s : ℂ) (hs : s ≠ 1 ∨ ∑ j, Φ j = 0) :
lemma differentiable_LFunction_of_sum_zero {Φ : ZMod N → ℂ} (hΦ : ∑ j, Φ j = 0) :
lemma LFunction_residue_one (Φ : ZMod N → ℂ) :
lemma LFunction_stdAddChar_eq_expZeta (j : ZMod N) (s : ℂ) (hjs : j ≠ 0 ∨ s ≠ 1) :
lemma LFunction_dft (Φ : ZMod N → ℂ) {s : ℂ} (hs : Φ 0 = 0 ∨ s ≠ 1) :
theorem LFunction_one_sub (Φ : ZMod N → ℂ) {s : ℂ}
lemma LFunction_def_even (hΦ : Φ.Even) (s : ℂ) :
lemma LFunction_def_odd (hΦ : Φ.Odd) (s : ℂ) :
lemma completedLFunction_const_mul (a : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
lemma completedLFunction_def_even (hΦ : Φ.Even) (s : ℂ) :
lemma completedLFunction_def_odd (hΦ : Φ.Odd) (s : ℂ) :
lemma completedLFunction_modOne_eq (Φ : ZMod 1 → ℂ) (s : ℂ) :
lemma differentiable_completedLFunction₀ (Φ : ZMod N → ℂ) :
lemma completedLFunction_eq (Φ : ZMod N → ℂ) (s : ℂ) :
lemma differentiableAt_completedLFunction (Φ : ZMod N → ℂ) (s : ℂ) (hs₀ : s ≠ 0 ∨ Φ 0 = 0)
lemma differentiable_completedLFunction (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0) :
lemma LFunction_eq_completed_div_gammaFactor_even (hΦ : Φ.Even) (s : ℂ) (hs : s ≠ 0 ∨ Φ 0 = 0) :
```
