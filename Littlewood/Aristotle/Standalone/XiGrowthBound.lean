/-
Xi growth bound: |ξ(s)| ≤ C · exp(C · |s| · log|s|) for |s| ≥ 2.

ξ(s) = RiemannXiAlt s = (1/2)(s(s-1) · Λ₀(s) + 1)

where Λ₀ = completedRiemannZeta₀ is entire.

Strategy:
1. Λ₀ is bounded on any vertical strip [a,b] (Mellin representation)
2. Using functional equation Λ₀(1-s) = Λ₀(s), reduce to Re(s) ≥ 1/2
3. The Mellin bound on [1/2, R] grows at most like exp(C·R·log R)
4. Combined with |s(s-1)| ≤ ‖s‖² + ‖s‖, get exp(C·‖s‖·log‖s‖)

Sorry count: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option maxHeartbeats 6400000
set_option maxRecDepth 4000
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Real Set Filter Topology HurwitzZeta MeasureTheory
open scoped BigOperators Real Nat Classical

noncomputable section

namespace Aristotle.Standalone.XiGrowthBound

/-! ## Definition of RiemannXiAlt -/

noncomputable def RiemannXiAlt (s : ℂ) : ℂ :=
  (1/2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

theorem differentiable_RiemannXiAlt : Differentiable ℂ RiemannXiAlt := by
  unfold RiemannXiAlt
  apply Differentiable.const_mul
  apply Differentiable.add
  · exact (differentiable_id.mul (differentiable_id.sub_const 1)).mul
      differentiable_completedZeta₀
  · exact differentiable_const _

/-! ## Step 1: completedRiemannZeta₀ bounded on vertical strips -/

theorem completedRiemannZeta₀_bounded_on_strip (a b : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖completedRiemannZeta₀ s‖ ≤ M := by
  by_cases hab : a ≤ b; swap
  · exact ⟨1, one_pos, fun s ha hb => absurd (ha.trans hb) (not_le.mpr (by linarith))⟩
  set Q := (hurwitzEvenFEPair (0 : UnitAddCircle)).toStrongFEPair with hQ_def
  have hconv_a := (Q.hasMellin ((a / 2 : ℝ) : ℂ)).1
  have hconv_b := (Q.hasMellin ((b / 2 : ℝ) : ℂ)).1
  have hint_a := hconv_a.norm
  have hint_b := hconv_b.norm
  set Ia := ∫ t in Ioi (0 : ℝ), ‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1) • Q.f t‖
  set Ib := ∫ t in Ioi (0 : ℝ), ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1) • Q.f t‖
  have hIa_nn : 0 ≤ Ia := setIntegral_nonneg measurableSet_Ioi fun t _ => norm_nonneg _
  have hIb_nn : 0 ≤ Ib := setIntegral_nonneg measurableSet_Ioi fun t _ => norm_nonneg _
  refine ⟨(Ia + Ib) / 2 + 1, by linarith, fun s ha hb => ?_⟩
  suffices h_main : ‖mellin Q.f (s / 2)‖ ≤ Ia + Ib by
    have h_eq : completedRiemannZeta₀ s = mellin Q.f (s / 2) / 2 := rfl
    rw [h_eq, norm_div, Complex.norm_ofNat]; linarith
  have hconv_s := (Q.hasMellin (s / 2)).1
  calc ‖mellin Q.f (s / 2)‖
      ≤ ∫ t in Ioi (0 : ℝ), ‖(↑t : ℂ) ^ (s / 2 - 1) • Q.f t‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), (‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1) • Q.f t‖ +
          ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1) • Q.f t‖) := by
        apply setIntegral_mono_on hconv_s.norm (hint_a.add hint_b) measurableSet_Ioi
        intro t ht; rw [mem_Ioi] at ht
        have hcpow : ‖(↑t : ℂ) ^ (s / 2 - 1)‖ ≤
            ‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1)‖ + ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1)‖ := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos ht,
              Complex.norm_cpow_eq_rpow_re_of_pos ht]
          have hre_s : (s / 2 - 1).re = s.re / 2 - 1 := by
            simp [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re]
          have hre_a : ((↑(a / 2) : ℂ) - 1).re = a / 2 - 1 := by
            simp [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
          have hre_b : ((↑(b / 2) : ℂ) - 1).re = b / 2 - 1 := by
            simp [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
          rw [hre_s, hre_a, hre_b]
          by_cases h1 : 1 ≤ t
          · calc t ^ (s.re / 2 - 1) ≤ t ^ (b / 2 - 1) :=
                  rpow_le_rpow_of_exponent_le h1 (by linarith)
              _ ≤ t ^ (a / 2 - 1) + t ^ (b / 2 - 1) :=
                  le_add_of_nonneg_left (rpow_nonneg (by linarith : (0:ℝ) ≤ t) _)
          · calc t ^ (s.re / 2 - 1) ≤ t ^ (a / 2 - 1) :=
                  rpow_le_rpow_of_exponent_ge (by linarith : 0 < t) (by linarith [not_le.mp h1])
                    (by linarith)
              _ ≤ t ^ (a / 2 - 1) + t ^ (b / 2 - 1) :=
                  le_add_of_nonneg_right (rpow_nonneg (by linarith : (0:ℝ) ≤ t) _)
        calc ‖(↑t : ℂ) ^ (s / 2 - 1) • Q.f t‖
            = ‖(↑t : ℂ) ^ (s / 2 - 1)‖ * ‖Q.f t‖ := norm_smul _ _
          _ ≤ (‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1)‖ + ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1)‖) *
              ‖Q.f t‖ := mul_le_mul_of_nonneg_right hcpow (norm_nonneg _)
          _ = ‖(↑t : ℂ) ^ ((↑(a / 2) : ℂ) - 1) • Q.f t‖ +
              ‖(↑t : ℂ) ^ ((↑(b / 2) : ℂ) - 1) • Q.f t‖ := by
              rw [add_mul, norm_smul, norm_smul]
    _ = Ia + Ib := integral_add hint_a hint_b

/-! ## Step 2: Polynomial prefactor bound -/

theorem norm_s_mul_s_sub_one_le (s : ℂ) : ‖s * (s - 1)‖ ≤ ‖s‖ ^ 2 + ‖s‖ := by
  rw [norm_mul]
  calc ‖s‖ * ‖s - 1‖ ≤ ‖s‖ * (‖s‖ + 1) := by
        gcongr; exact (norm_sub_le s 1).trans (by simp)
    _ = ‖s‖ ^ 2 + ‖s‖ := by ring

/-! ## Auxiliary lemmas for the Mellin growth bound -/

/-
The formula: Λ₀(s) = Γ_ℝ(s)·ζ(s) + 1/s + 1/(1-s) for s with Γ_ℝ(s) ≠ 0 and s ≠ 0.
-/
private theorem completedRiemannZeta₀_formula (s : ℂ) (hs₀ : s ≠ 0) (hg : s.Gammaℝ ≠ 0) :
    completedRiemannZeta₀ s = s.Gammaℝ * riemannZeta s + 1 / s + 1 / (1 - s) := by
  rw [ riemannZeta_def_of_ne_zero hs₀ ];
  rw [ mul_div_cancel₀ _ hg, completedRiemannZeta_eq ] ; ring

/-
Bound on |ζ(s)| for Re(s) ≥ 2: the Dirichlet series converges absolutely
    and is bounded by ζ(2) < 2.
-/
private theorem norm_riemannZeta_le_two (s : ℂ) (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ 2 := by
  -- For $s$ with $\Re(s) \geq 2$, we have $|\zeta(s)| \leq \sum_{n=1}^\infty \frac{1}{n^{\Re(s)}} \leq \sum_{n=1}^\infty \frac{1}{n^2} = \frac{\pi^2}{6} < 2$ using the p-series test.
  have h_bound_n2 : ‖riemannZeta s‖ ≤ ∑' n : ℕ, (1 : ℝ) / (n + 1) ^ (2 : ℝ) := by
    have h_bound_n2 : ‖riemannZeta s‖ ≤ ∑' n : ℕ, (1 : ℝ) / (n + 1) ^ s.re := by
      rw [ zeta_eq_tsum_one_div_nat_add_one_cpow ];
      · convert norm_tsum_le_tsum_norm _ <;> norm_num;
        · rw [ ← Complex.norm_cpow_eq_rpow_re_of_pos ] <;> norm_cast ; norm_num;
        · have h_summable : Summable (fun n : ℕ => (1 : ℝ) / (n + 1) ^ s.re) := by
            exact_mod_cast summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_rpow.2 <| by linarith;
          convert h_summable using 1;
          ext; rw [ ← Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_add_one_pos _ ) ] ; norm_num;
      · linarith;
    refine' le_trans h_bound_n2 ( Summable.tsum_le_tsum _ _ _ );
    · exact fun n => one_div_le_one_div_of_le ( by positivity ) ( by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) hs ) );
    · exact_mod_cast summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_rpow.2 <| by linarith;
    · simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
  have h_pi_sq_div_6_lt_2 : Real.pi ^ 2 / 6 < 2 := by
    -- We know that $\pi \approx 3.14$, so we can estimate $\pi^2 \approx 9.86$.
    have h_pi_approx : Real.pi < 3.4 := by
      pi_upper_bound [ 7 / 5 ];
    norm_num at h_pi_approx ; nlinarith only [ Real.pi_gt_three, h_pi_approx ];
  exact h_bound_n2.trans ( by have := HasSum.tsum_eq ( hasSum_nat_add_iff' 1 |>.2 <| hasSum_zeta_two ) ; norm_num at * ; linarith )

/-
Bound on |Γ_ℝ(s)| ≤ Γ(Re(s)/2) for Re(s) > 0. Uses that |π^(-s/2)| ≤ 1
    for Re(s) ≥ 0 and |Γ(s/2)| ≤ Γ(Re(s)/2).
-/
private theorem norm_GammaR_le (s : ℂ) (hs : 0 < s.re) :
    ‖s.Gammaℝ‖ ≤ Real.Gamma (s.re / 2) := by
  rw [ Complex.Gammaℝ, Complex.Gamma ];
  rcases n : ⌊1 - ( s/2 : ℂ ).re⌋₊ with ( _ | _ | n );
  · norm_num [ Complex.cpow_def_of_ne_zero, Real.pi_ne_zero ] at *;
    norm_num [ Complex.norm_exp, Complex.log_re, Complex.log_im, GammaAux ];
    refine' le_trans ( mul_le_of_le_one_left ( norm_nonneg _ ) _ ) _;
    · norm_num [ Complex.arg ];
      split_ifs <;> nlinarith [ Real.pi_gt_three, Real.log_pos ( show Real.pi > 1 by linarith [ Real.pi_gt_three ] ) ];
    · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) _;
      convert ( integral_rpow_mul_exp_neg_rpow zero_lt_one ( show -1 < s.re / 2 - 1 by linarith ) ) |> le_of_eq using 1;
      · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => _;
        norm_num [ Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp ] ; ring;
      · norm_num;
  · rw [ Nat.floor_eq_zero.mpr ] at n <;> norm_num at *;
    linarith;
  · rw [ Nat.floor_eq_zero.mpr ] at n <;> norm_num at * ; linarith

/-
Γ_ℝ(s) ≠ 0 when Re(s) > 0.
-/
private theorem GammaR_ne_zero_of_re_pos (s : ℂ) (hs : 0 < s.re) : s.Gammaℝ ≠ 0 := by
  exact mul_ne_zero ( by norm_num [ Complex.cpow_def ] ) ( Complex.Gamma_ne_zero ( by exact fun m => by intro H; rw [ Complex.ext_iff ] at H; norm_num at H; linarith ) )

/-
Crude Stirling bound: Γ(σ) ≤ exp(4·σ·log σ) for σ ≥ 2.
    Proof: by log-convexity of Γ, on [n, n+1] we have Γ(σ) ≤ max(Γ(n), Γ(n+1)) = n!.
    Then n! ≤ n^n ≤ σ^σ = exp(σ·log σ) ≤ exp(4·σ·log σ).
-/
private theorem Gamma_le_exp_mul_log (σ : ℝ) (hσ : 2 ≤ σ) :
    Real.Gamma σ ≤ Real.exp (4 * σ * Real.log σ) := by
  -- By log-convexity of Gamma, on [n, n+1] we have Gamma(σ) ≤ max(Gamma(n), Gamma(n+1)) = n!.
  have h_max : Real.Gamma σ ≤ Real.Gamma (⌊σ⌋₊ + 1) := by
    have h_max : ∀ x y z : ℝ, 0 < x → x ≤ y → y ≤ z → Real.log (Real.Gamma y) ≤ (1 - (y - x) / (z - x)) * Real.log (Real.Gamma x) + ((y - x) / (z - x)) * Real.log (Real.Gamma z) := by
      intros x y z hx hy hz
      have h_convex : ConvexOn ℝ (Set.Ioi 0) (Real.log ∘ Real.Gamma) := by
        exact Real.convexOn_log_Gamma;
      convert h_convex.2 hx ( show 0 < z by linarith ) _ _ _ using 1 <;> norm_num;
      · grind;
      · exact div_le_one_of_le₀ ( by linarith ) ( by linarith );
      · exact div_nonneg ( by linarith ) ( by linarith );
    have := h_max ⌊σ⌋₊ σ ( ⌊σ⌋₊ + 1 ) ?_ ?_ ?_ <;> norm_num at * <;> try linarith [ Nat.floor_le ( show 0 ≤ σ by linarith ), Nat.lt_floor_add_one σ ] ;
    · rw [ ← Real.log_le_log_iff ( Real.Gamma_pos_of_pos ( by positivity ) ) ( Real.Gamma_pos_of_pos ( by positivity ) ), Real.Gamma_add_one ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.floor_pos.mpr <| by linarith ) ];
      rw [ Real.Gamma_add_one ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.floor_pos.mpr <| by linarith ) ] at this;
      rw [ Real.log_mul ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.floor_pos.mpr <| by linarith ) ( ne_of_gt <| Real.Gamma_pos_of_pos <| Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) ] at * ; nlinarith [ Nat.floor_le <| show 0 ≤ σ by linarith, Nat.lt_floor_add_one σ, Real.log_nonneg <| show ( ⌊σ⌋₊ : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr <| Nat.floor_pos.mpr <| by linarith, Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) <| show ( ⌊σ⌋₊ : ℝ ) ≤ σ by exact Nat.floor_le <| show 0 ≤ σ by linarith ];
    · exact Nat.floor_pos.mpr ( by linarith );
  -- Then n! ≤ n^n ≤ σ^σ = exp(σ·log σ) ≤ exp(4·σ·log σ).
  have h_bound : Real.Gamma (⌊σ⌋₊ + 1) ≤ Real.exp (⌊σ⌋₊ * Real.log ⌊σ⌋₊) := by
    rw [ Real.Gamma_nat_eq_factorial, Real.exp_nat_mul, Real.exp_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) ];
    exact mod_cast Nat.recOn ⌊σ⌋₊ ( by norm_num ) fun n ih => by rw [ pow_succ' ] ; exact le_trans ( Nat.mul_le_mul_left _ ih ) ( by gcongr ; linarith ) ;
  refine le_trans h_max <| h_bound.trans <| Real.exp_le_exp.mpr ?_;
  gcongr <;> nlinarith [ Nat.floor_le ( show 0 ≤ σ by positivity ), Nat.lt_floor_add_one σ, Real.log_nonneg ( show 1 ≤ σ by linarith ) ]

/-
Bound for completedRiemannZeta₀ when Re(s) > 4: uses the formula approach.
    |Λ₀(s)| ≤ |Γ_ℝ(s)| · |ζ(s)| + |1/s| + |1/(1-s)|
    ≤ Γ(Re(s)/2) · 2 + 1 + 1 ≤ exp(2·Re(s)·log(Re(s))).
-/
private theorem mellin_bound_large_re (s : ℂ) (hs : 4 < s.re) :
    ‖completedRiemannZeta₀ s‖ ≤ Real.exp (2 * s.re * Real.log s.re) := by
  have h_bound : ‖completedRiemannZeta₀ s‖ ≤ 2 * Real.exp (2 * s.re * Real.log (s.re / 2)) + 2 := by
    have h_riemann_zeta : ‖riemannZeta s‖ ≤ 2 := by
      exact norm_riemannZeta_le_two s ( by linarith )
    have h_gamma_r : ‖s.Gammaℝ‖ ≤ Real.exp (2 * s.re * Real.log (s.re / 2)) := by
      refine' le_trans ( norm_GammaR_le s ( by linarith ) ) _;
      convert Gamma_le_exp_mul_log ( s.re / 2 ) ( by linarith ) using 1 ; ring
    have h_one_s : ‖1/s‖ ≤ 1 := by
      norm_num [ Complex.norm_def, Complex.normSq ];
      exact inv_le_one_of_one_le₀ <| Real.le_sqrt_of_sq_le <| by nlinarith
    have h_one_s_minus_one : ‖1/(1-s)‖ ≤ 1 := by
      norm_num [ Complex.norm_def, Complex.normSq ] at *;
      exact inv_le_one_of_one_le₀ <| Real.le_sqrt_of_sq_le <| by nlinarith;
    have h_combined : ‖completedRiemannZeta₀ s‖ ≤ ‖s.Gammaℝ‖ * ‖riemannZeta s‖ + ‖1/s‖ + ‖1/(1-s)‖ := by
      rw [ completedRiemannZeta₀_formula s ( by rintro rfl; norm_num at hs ) ( GammaR_ne_zero_of_re_pos s ( by linarith ) ) ] ; exact le_trans ( norm_add₃_le .. ) ( by norm_num ) ;
    have h_final : ‖completedRiemannZeta₀ s‖ ≤ 2 * Real.exp (2 * s.re * Real.log (s.re / 2)) + 2 := by
      nlinarith [ norm_nonneg ( s.Gammaℝ ), norm_nonneg ( riemannZeta s ) ]
    exact h_final;
  rw [ show s.re = ( s.re / 2 ) * 2 by ring, Real.log_mul ( by linarith ) ( by linarith ) ];
  ring_nf at *;
  rw [ Real.exp_add ];
  have h_exp : Real.exp (s.re * Real.log 2 * 2) ≥ 4 := by
    rw [ show ( 4 : ℝ ) = ( Real.exp ( Real.log 2 * 2 ) ) by rw [ Real.exp_mul, Real.exp_log ] <;> norm_num ] ; gcongr ; nlinarith [ Real.log_pos one_lt_two ];
  nlinarith [ Real.add_one_le_exp ( s.re * Real.log ( s.re * ( 1 / 2 ) ) * 2 ), show 1 ≤ Real.exp ( s.re * Real.log ( s.re * ( 1 / 2 ) ) * 2 ) by exact Real.one_le_exp ( by nlinarith [ Real.log_nonneg ( show s.re * ( 1 / 2 ) ≥ 1 by linarith ) ] ) ]

/-
Auxiliary: M₀ ≤ exp(C * R * log R) when C ≥ log(M₀+1)/(2·log 2) + 1 and R ≥ 2.
-/
private theorem M₀_le_exp_CRlogR (M₀ : ℝ) (hM₀_pos : 0 < M₀) (C R : ℝ)
    (hC_ge : C ≥ Real.log (M₀ + 1) / (2 * Real.log 2) + 1) (hR : 2 ≤ R) :
    M₀ ≤ Real.exp (C * R * Real.log R) := by
  -- Since $C \geq \frac{\log(M₀+1)}{2\log 2} + 1$ and $R \geq 2$, we have $C * R * \log R \geq \log(M₀+1) + \log 2$.
  have h_exp_ge : C * R * Real.log R ≥ Real.log (M₀ + 1) + Real.log 2 := by
    -- Since $C \geq \frac{\log(M₀+1)}{2\log 2} + 1$ and $R \geq 2$, we have $C * R * \log R \geq \left(\frac{\log(M₀+1)}{2\log 2} + 1\right) * 2 * \log 2$.
    have h_exp_ge : C * R * Real.log R ≥ (Real.log (M₀ + 1) / (2 * Real.log 2) + 1) * 2 * Real.log 2 := by
      gcongr;
      · exact mul_nonneg ( le_trans ( by exact add_nonneg ( div_nonneg ( Real.log_nonneg ( by linarith ) ) ( by positivity ) ) zero_le_one ) hC_ge ) ( by positivity );
      · exact le_trans ( add_nonneg ( div_nonneg ( Real.log_nonneg ( by linarith ) ) ( by positivity ) ) zero_le_one ) hC_ge;
    nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( Real.log ( M₀ + 1 ) ) ( by positivity : ( 2 * Real.log 2 ) ≠ 0 ) ];
  exact le_trans ( by rw [ ← Real.log_le_iff_le_exp ( by positivity ) ] ; linarith [ Real.log_le_log ( by positivity ) ( by linarith : M₀ + 1 ≥ M₀ ), Real.log_nonneg one_le_two ] ) ( Real.exp_le_exp.mpr h_exp_ge )

/-! ## Step 3: Mellin growth bound -/

/-- The Mellin bound on [1/2, R] grows at most like exp(C·R·log R) for R ≥ 2.
    Note: the original statement had R ≥ 1, but exp(C·1·log 1) = 1, which is
    too small to bound |Λ₀| on [1/2, 1]. We use R ≥ 2 since the downstream
    application calls this with R = 1 + ‖s‖ ≥ 3. -/
theorem mellin_bound_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      ∃ M : ℝ, 0 < M ∧
        (∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ R →
          ‖completedRiemannZeta₀ s‖ ≤ M) ∧
        M ≤ Real.exp (C * R * Real.log R) := by
  obtain ⟨M₀, hM₀_pos, hM₀_bound⟩ := completedRiemannZeta₀_bounded_on_strip (1/2) 4
  -- Choose C large enough: need C ≥ 4 for the formula approach AND
  -- exp(C*2*log 2) ≥ M₀ for the small R case.
  set C := max 4 (Real.log (M₀ + 1) / (2 * Real.log 2) + 1)
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (le_max_left _ _)
  have hC_ge4 : (4 : ℝ) ≤ C := le_max_left _ _
  have hC_ge_log : C ≥ Real.log (M₀ + 1) / (2 * Real.log 2) + 1 := le_max_right _ _
  refine ⟨C, hC_pos, fun R hR => ?_⟩
  -- Use M = exp(C * R * log R) directly
  refine ⟨Real.exp (C * R * Real.log R), Real.exp_pos _, ?_, le_refl _⟩
  intro s hs₁ hs₂
  by_cases hs4 : s.re ≤ 4
  · -- Re(s) ∈ [1/2, 4]: use M₀ from the fixed strip [1/2, 4]
    calc ‖completedRiemannZeta₀ s‖ ≤ M₀ := hM₀_bound s hs₁ hs4
      _ ≤ Real.exp (C * R * Real.log R) := M₀_le_exp_CRlogR M₀ hM₀_pos C R hC_ge_log hR
  · -- Re(s) > 4: use the formula Λ₀(s) = Γ_ℝ(s)·ζ(s) + 1/s + 1/(1-s)
    push_neg at hs4
    calc ‖completedRiemannZeta₀ s‖
        ≤ Real.exp (2 * s.re * Real.log s.re) := mellin_bound_large_re s hs4
      _ ≤ Real.exp (C * R * Real.log R) := by
          apply Real.exp_le_exp_of_le
          have hs_re_pos : 0 < s.re := by linarith
          have hlog_R_pos : 0 < Real.log R := Real.log_pos (by linarith)
          -- 2 * s.re * log(s.re) ≤ C * R * log R
          -- since s.re ≤ R, log(s.re) ≤ log R, and C ≥ 4 ≥ 2
          calc 2 * s.re * Real.log s.re
              ≤ 2 * R * Real.log R := by
                apply mul_le_mul (mul_le_mul_of_nonneg_left hs₂ (by norm_num))
                  (Real.log_le_log hs_re_pos hs₂) (Real.log_nonneg (by linarith))
                  (by positivity)
            _ ≤ C * R * Real.log R := by
                have hC4 : 2 ≤ C := le_trans (by norm_num : (2:ℝ) ≤ 4) (le_max_left 4 _)
                nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC4 (by linarith)) hlog_R_pos.le]

/-! ## Step 4: Main theorem -/

/-- **Main theorem**: |ξ(s)| ≤ exp(C · |s| · log|s|) for |s| ≥ 2. -/
theorem xi_growth_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ ‖s‖ →
      ‖RiemannXiAlt s‖ ≤ Real.exp (C * ‖s‖ * Real.log ‖s‖) := by
  obtain ⟨C₀, hC₀, hMellin⟩ := mellin_bound_growth
  -- Use 4*C₀ + 3 to absorb the polynomial factor
  use 4 * C₀ + 3
  refine ⟨by linarith, fun s hs => ?_⟩
  have hs_pos : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hs
  have hlog_pos : 0 < Real.log ‖s‖ := Real.log_pos (lt_of_lt_of_le one_lt_two hs)
  have hrL : 0 < ‖s‖ * Real.log ‖s‖ := mul_pos hs_pos hlog_pos
  set r := ‖s‖
  -- Bound Λ₀(s) via functional equation + strip bound
  have h_Λ₀ : ‖completedRiemannZeta₀ s‖ ≤
      Real.exp (C₀ * (1 + r) * Real.log (1 + r)) := by
    by_cases hre : (1 : ℝ) / 2 ≤ s.re
    · obtain ⟨M, hM_pos, hM_bound, hM_growth⟩ := hMellin (1 + r) (by linarith)
      calc ‖completedRiemannZeta₀ s‖
          ≤ M := hM_bound s hre (by linarith [Complex.re_le_norm s])
        _ ≤ _ := hM_growth
    · push_neg at hre
      rw [← completedRiemannZeta₀_one_sub]
      have hre' : 1/2 ≤ (1 - s).re := by simp [Complex.sub_re]; linarith
      have hre'_le : (1 - s).re ≤ 1 + r := by
        simp [Complex.sub_re]; linarith [neg_abs_le s.re, Complex.abs_re_le_norm s]
      obtain ⟨M, hM_pos, hM_bound, hM_growth⟩ := hMellin (1 + r) (by linarith)
      calc ‖completedRiemannZeta₀ (1 - s)‖ ≤ M := hM_bound _ hre' hre'_le
        _ ≤ _ := hM_growth
  -- Bookkeeping: ‖ξ(s)‖ ≤ (1/2)((r²+r)·exp(C₀(1+r)log(1+r)) + 1) ≤ exp((4C₀+3)rL)
  -- Step 1: C₀*(1+r)*log(1+r) ≤ 4*C₀*r*log r
  have h_log_bound : C₀ * (1 + r) * Real.log (1 + r) ≤ 4 * C₀ * r * Real.log r := by
    have h1r : 1 + r ≤ 2 * r := by show 1 + ‖s‖ ≤ 2 * ‖s‖; linarith
    have h_log : Real.log (1 + r) ≤ 2 * Real.log r := by
      calc Real.log (1 + r)
          ≤ Real.log (r ^ 2) := Real.log_le_log (by linarith) (by nlinarith [sq_nonneg (r-1)])
        _ = 2 * Real.log r := by rw [Real.log_pow]; push_cast; ring
    nlinarith [mul_le_mul_of_nonneg_left h1r hC₀.le,
               mul_le_mul_of_nonneg_left h_log (mul_nonneg hC₀.le (by linarith : 0 ≤ 1 + r))]
  -- Step 2: bound product P * A
  have h_PA : ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ ≤
      (r ^ 2 + r) * Real.exp (4 * C₀ * r * Real.log r) := by
    calc ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖
        ≤ (r ^ 2 + r) * ‖completedRiemannZeta₀ s‖ :=
          mul_le_mul_of_nonneg_right (norm_s_mul_s_sub_one_le s) (norm_nonneg _)
      _ ≤ (r ^ 2 + r) * Real.exp (C₀ * (1 + r) * Real.log (1 + r)) :=
          mul_le_mul_of_nonneg_left h_Λ₀ (by nlinarith)
      _ ≤ (r ^ 2 + r) * Real.exp (4 * C₀ * r * Real.log r) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le h_log_bound) (by nlinarith)
  -- Step 3: r² ≤ exp(r*log r), r ≤ exp(r*log r)
  have h_sq : r ^ 2 ≤ Real.exp (r * Real.log r) := by
    rw [← Real.exp_log (pow_pos hs_pos 2)]
    exact Real.exp_le_exp_of_le (by rw [Real.log_pow]; push_cast; nlinarith [hlog_pos])
  have h_r_le : r ≤ Real.exp (r * Real.log r) := by
    calc r = Real.exp (Real.log r) := (Real.exp_log hs_pos).symm
      _ ≤ Real.exp (r * Real.log r) := Real.exp_le_exp_of_le (by nlinarith)
  -- Step 4: (r²+r) ≤ exp(2*r*log r)
  have h_poly : r ^ 2 + r ≤ Real.exp (2 * r * Real.log r) := by
    calc r ^ 2 + r ≤ Real.exp (r * Real.log r) + Real.exp (r * Real.log r) :=
          add_le_add h_sq h_r_le
      _ = 2 * Real.exp (r * Real.log r) := by ring
      _ ≤ Real.exp (r * Real.log r) * Real.exp (r * Real.log r) := by
          nlinarith [Real.exp_pos (r * Real.log r),
                     show (2:ℝ) ≤ Real.exp (r * Real.log r) from le_trans (by nlinarith) h_sq]
      _ = Real.exp (2 * r * Real.log r) := by rw [← Real.exp_add]; ring_nf
  -- Step 5: combine
  have h_combined : ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ ≤
      Real.exp ((2 + 4 * C₀) * r * Real.log r) := by
    calc ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖
        ≤ (r ^ 2 + r) * Real.exp (4 * C₀ * r * Real.log r) := h_PA
      _ ≤ Real.exp (2 * r * Real.log r) * Real.exp (4 * C₀ * r * Real.log r) :=
          mul_le_mul_of_nonneg_right h_poly (Real.exp_nonneg _)
      _ = Real.exp ((2 + 4 * C₀) * r * Real.log r) := by rw [← Real.exp_add]; ring_nf
  -- Step 6: final bound on ‖ξ(s)‖
  -- ‖ξ(s)‖ = ‖(1/2)(s(s-1)Λ₀(s) + 1)‖ ≤ (1/2)(‖s(s-1)‖·‖Λ₀(s)‖ + 1)
  have h_xi : ‖RiemannXiAlt s‖ ≤ (1/2) * (‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ + 1) := by
    unfold RiemannXiAlt
    calc ‖(1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta₀ s + 1)‖
        = ‖(1/2 : ℂ)‖ * ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ := norm_mul _ _
      _ ≤ ‖(1/2 : ℂ)‖ * (‖s * (s - 1) * completedRiemannZeta₀ s‖ + ‖(1 : ℂ)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = (1/2) * (‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ + 1) := by
          rw [norm_mul]; simp
  -- 2 + 4C₀ < 4C₀ + 3 always
  have h_const : (2 + 4 * C₀) * r * Real.log r < (4 * C₀ + 3) * r * Real.log r := by nlinarith
  have h_one_le : (1 : ℝ) ≤ Real.exp ((4 * C₀ + 3) * r * Real.log r) :=
    le_trans (by norm_num : (1:ℝ) ≤ 1 + 0)
      (by linarith [Real.add_one_le_exp ((4 * C₀ + 3) * r * Real.log r),
                     show 0 ≤ (4 * C₀ + 3) * r * Real.log r from by positivity])
  calc ‖RiemannXiAlt s‖
      ≤ (1/2) * (‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ + 1) := h_xi
    _ ≤ (1/2) * (Real.exp ((2 + 4 * C₀) * r * Real.log r) + 1) := by
        linarith [h_combined]
    _ ≤ (1/2) * (Real.exp ((4 * C₀ + 3) * r * Real.log r) +
          Real.exp ((4 * C₀ + 3) * r * Real.log r)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
        linarith [Real.exp_le_exp_of_le h_const.le]
    _ = Real.exp ((4 * C₀ + 3) * r * Real.log r) := by ring

/-! ## Step 5: Corollary — finite order bound -/

theorem xi_finite_order (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ ‖s‖ →
      ‖RiemannXiAlt s‖ ≤ Real.exp (C * ‖s‖ ^ (1 + ε)) := by
  obtain ⟨C₀, hC₀, hbound⟩ := xi_growth_bound
  use C₀ / ε
  refine ⟨div_pos hC₀ hε, fun s hs => ?_⟩
  have hs_pos : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hs
  have hs1 : 1 ≤ ‖s‖ := le_trans (by norm_num : (1:ℝ) ≤ 2) hs
  have hkey : C₀ * ‖s‖ * Real.log ‖s‖ ≤ C₀ / ε * ‖s‖ ^ (1 + ε) := by
    have hlog_le : Real.log ‖s‖ ≤ ‖s‖ ^ ε / ε := by
      rw [le_div_iff₀ hε]
      calc Real.log ‖s‖ * ε
          ≤ Real.exp (Real.log ‖s‖ * ε) := by
            linarith [Real.add_one_le_exp (Real.log ‖s‖ * ε)]
        _ = ‖s‖ ^ ε := by rw [rpow_def_of_pos hs_pos]
    calc C₀ * ‖s‖ * Real.log ‖s‖
        ≤ C₀ * ‖s‖ * (‖s‖ ^ ε / ε) := by
          exact mul_le_mul_of_nonneg_left hlog_le (mul_nonneg hC₀.le hs_pos.le)
      _ = C₀ / ε * (‖s‖ * ‖s‖ ^ ε) := by ring
      _ = C₀ / ε * ‖s‖ ^ (1 + ε) := by congr 1; rw [rpow_add hs_pos, rpow_one]
  calc ‖RiemannXiAlt s‖
      ≤ Real.exp (C₀ * ‖s‖ * Real.log ‖s‖) := hbound s hs
    _ ≤ Real.exp (C₀ / ε * ‖s‖ ^ (1 + ε)) := Real.exp_le_exp_of_le hkey

end Aristotle.Standalone.XiGrowthBound