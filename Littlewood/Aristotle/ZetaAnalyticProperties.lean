import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 3200000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.ZetaAnalyticProperties

/-
Define the factor χ(s) = 2^s π^{s-1} sin(πs/2) Γ(1-s) from the functional equation.
-/
noncomputable def chi (s : ℂ) : ℂ :=
  (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.sin (Real.pi * s / 2) * Complex.Gamma (1 - s)

/-
The functional equation ζ(s) = χ(s)ζ(1-s) holds for s with 0 < Re(s) < 1.
-/

theorem zeta_eq_chi_mul_zeta_one_sub {s : ℂ} (h_re : 0 < s.re) (h_re' : s.re < 1) :
    riemannZeta s = chi s * riemannZeta (1 - s) := by
      have := @riemannZeta_one_sub ( 1 - s );
      simp_all +decide [ Complex.cos, Complex.exp_neg, mul_sub ];
      convert this ( fun n => ?_ ) ( by aesop ) using 1;
      · unfold chi; ring;
        rw [ Complex.cpow_def_of_ne_zero ( by norm_num [ Real.pi_ne_zero ] ), Complex.cpow_def_of_ne_zero ( by norm_num [ Real.pi_ne_zero ] ) ] ; ring;
        rw [ Complex.cpow_def_of_ne_zero ( by norm_num [ Real.pi_ne_zero ] ) ] ; ring;
        field_simp;
        rw [ Complex.log_mul ( by norm_num [ Real.pi_ne_zero ] ) ( by norm_num ) ] ; ring;
        · norm_num [ Complex.sin, Complex.exp_add, Complex.exp_neg ] ; ring;
          norm_num [ Complex.exp_ne_zero, Complex.exp_neg, Complex.exp_log ] ; ring;
          norm_num [ ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add ] ; ring;
          norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, mul_div ] ; ring;
          norm_num;
        · norm_num [ Complex.arg ];
          split_ifs <;> constructor <;> linarith [ Real.pi_pos ];
      · exact ne_of_apply_ne Complex.re ( by norm_num; linarith )

/-
Define N(T) as the number of zeros in the critical strip with imaginary part between 0 and T.
-/
noncomputable def zetaZeroCount (T : ℝ) : ℕ :=
  Set.ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im < T}

/-
The zeros of the Riemann zeta function are isolated.
-/
theorem riemannZeta_zeros_isolated {s : ℂ} (h_zero : riemannZeta s = 0) :
    ∃ ε > 0, ∀ z ∈ Metric.ball s ε, riemannZeta z = 0 → z = s := by
      by_cases hs : s = 1;
      · exact absurd h_zero ( by rw [ hs ] ; exact riemannZeta_one_ne_zero )
      · -- Since `riemannZeta` is analytic at `s` (because `s ≠ 1`), by the identity theorem for analytic functions, if `riemannZeta` is zero at `s`, then there's a neighborhood around `s` where `riemannZeta` is zero only at `s`.
        have h_analytic : AnalyticAt ℂ riemannZeta s := by
          apply_rules [ DifferentiableOn.analyticAt, differentiableAt_riemannZeta ];
          exact fun z hz => DifferentiableAt.differentiableWithinAt ( differentiableAt_riemannZeta hz );
          exact isOpen_ne.mem_nhds hs;
        have := h_analytic.eventually_eq_zero_or_eventually_ne_zero;
        rcases this with h|h <;> simp_all +decide [ eventually_nhdsWithin_iff ];
        · have h_id : AnalyticOn ℂ riemannZeta (Set.univ \ {1}) := by
            apply_rules [ DifferentiableOn.analyticOn ];
            · exact fun x hx => DifferentiableAt.differentiableWithinAt ( differentiableAt_riemannZeta ( by aesop ) );
            · exact isOpen_univ.sdiff isClosed_singleton;
          have h_id : ∀ z : ℂ, z ≠ 1 → riemannZeta z = 0 := by
            intro z hz;
            have h_id : AnalyticOnNhd ℂ riemannZeta (Set.univ \ {1}) := by
              apply_rules [ DifferentiableOn.analyticOnNhd ];
              · exact h_id.differentiableOn;
              · exact isOpen_univ.sdiff isClosed_singleton;
            apply h_id.eqOn_zero_of_preconnected_of_eventuallyEq_zero;
            any_goals tauto;
            have h_preconnected : IsPreconnected (Set.univ \ {0} : Set ℂ) := by
              have h_preconnected : IsConnected (Set.univ \ {0} : Set ℂ) := by
                have h_preconnected : IsConnected (Set.range (fun z : ℂ => Complex.exp z)) := by
                  exact isConnected_range ( Complex.continuous_exp );
                convert h_preconnected using 1;
                ext; simp [Complex.exp_ne_zero];
              exact h_preconnected.isPreconnected;
            convert h_preconnected.image ( fun x => x + 1 ) ( Continuous.continuousOn ( by continuity ) ) using 1 ; ext ; simp +decide [ Set.diff_eq ];
          exact absurd ( h_id 2 ( by norm_num ) ) ( by norm_num [ riemannZeta_two ] );
        · rcases Metric.mem_nhds_iff.mp h with ⟨ ε, ε_pos, hε ⟩ ; exact ⟨ ε, ε_pos, fun z hz hz' => Classical.not_not.1 fun hz'' => hε hz hz'' hz' ⟩ ;

/-
The Riemann zeta function is non-zero in a punctured neighborhood of s=1.
-/
theorem riemannZeta_ne_zero_near_one :
    ∀ᶠ s in nhds 1, s ≠ 1 → riemannZeta s ≠ 0 := by
      have h_zeta_not_zero : ∀ᶠ s in nhdsWithin 1 {1}ᶜ, riemannZeta s ≠ 0 := by
        have h_limit : Filter.Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
          exact HurwitzZeta.hurwitzZetaEven_residue_one 0;
        filter_upwards [ h_limit.eventually_ne one_ne_zero ] with s hs using by aesop;
      rw [ eventually_nhdsWithin_iff ] at h_zeta_not_zero ; aesop

/-
The set of zeros of the Riemann zeta function in the closed rectangle [0, 1] x [0, T] is closed.
-/
theorem isClosed_zeta_zeros_in_rect (T : ℝ) :
    IsClosed {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} := by
      refine' isClosed_iff_clusterPt.mpr _;
      intro s hs;
      -- Since $s$ is a cluster point, there exists a sequence $\{s_n\}$ in the set such that $s_n \to s$.
      obtain ⟨s_n, hs_n⟩ : ∃ s_n : ℕ → ℂ, (∀ n, riemannZeta (s_n n) = 0 ∧ 0 ≤ (s_n n).re ∧ (s_n n).re ≤ 1 ∧ 0 ≤ (s_n n).im ∧ (s_n n).im ≤ T) ∧ Filter.Tendsto s_n Filter.atTop (nhds s) := by
        rw [ clusterPt_principal_iff ] at hs;
        choose! s_n hs_n using hs;
        exact ⟨ fun n => s_n ( Metric.ball s ( 1 / ( n + 1 ) ) ), fun n => hs_n _ ( Metric.ball_mem_nhds _ <| by positivity ) |>.2, tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => by simpa using hs_n _ ( Metric.ball_mem_nhds _ <| by positivity ) |>.1.out.le ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
      by_cases h : s = 1 <;> simp_all +decide [ clusterPt_principal_iff ];
      · contrapose! hs;
        have := riemannZeta_ne_zero_near_one;
        exact ⟨ { s : ℂ | s ≠ 1 → riemannZeta s ≠ 0 }, this, by ext; aesop ⟩;
      · -- Since $s$ is a cluster point, we have $\zeta(s) = 0$.
        have h_zero : riemannZeta s = 0 := by
          have h_zero : Filter.Tendsto (fun n => riemannZeta (s_n n)) Filter.atTop (nhds (riemannZeta s)) := by
            exact DifferentiableAt.continuousAt ( differentiableAt_riemannZeta h ) |> ContinuousAt.tendsto |> Filter.Tendsto.comp <| hs_n.2;
          exact tendsto_nhds_unique h_zero ( by simpa only [ hs_n.1 ] using tendsto_const_nhds );
        exact ⟨ h_zero, by exact le_of_tendsto_of_tendsto' tendsto_const_nhds ( Complex.continuous_re.continuousAt.tendsto.comp hs_n.2 ) fun n => hs_n.1 n |>.2.1, by exact le_of_tendsto_of_tendsto' ( Complex.continuous_re.continuousAt.tendsto.comp hs_n.2 ) tendsto_const_nhds fun n => hs_n.1 n |>.2.2.1, by exact le_of_tendsto_of_tendsto' tendsto_const_nhds ( Complex.continuous_im.continuousAt.tendsto.comp hs_n.2 ) fun n => hs_n.1 n |>.2.2.2.1, by exact le_of_tendsto_of_tendsto' ( Complex.continuous_im.continuousAt.tendsto.comp hs_n.2 ) tendsto_const_nhds fun n => hs_n.1 n |>.2.2.2.2 ⟩

/-
The set of zeros of the Riemann zeta function in the closed rectangle [0, 1] x [0, T] is finite.
-/
theorem zeta_zeros_finite_in_closure (T : ℝ) :
    {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}.Finite := by
      -- The set of zeros of the Riemann zeta function in the closed rectangle [0, 1] x [0, T] is discrete.
      have h_discrete : DiscreteTopology {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} := by
        refine' discreteTopology_iff_isOpen_singleton.mpr _;
        intro a
        obtain ⟨s, hs⟩ := a
        have h_isolated : ∃ ε > 0, ∀ z ∈ Metric.ball s ε, riemannZeta z = 0 → z = s := by
          have := riemannZeta_zeros_isolated hs.1; aesop;
        generalize_proofs at *;
        rw [ Metric.isOpen_iff ] ; aesop;
      -- The set of zeros of the Riemann zeta function in the closed rectangle [0, 1] x [0, T] is compact.
      have h_compact : IsCompact {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} := by
        refine' ( Metric.isCompact_iff_isClosed_bounded.mpr _ );
        refine' ⟨ _, _ ⟩;
        · exact isClosed_zeta_zeros_in_rect T;
        · exact isBounded_iff_forall_norm_le.mpr ⟨ 1 + T, by rintro s ⟨ hs₁, hs₂, hs₃, hs₄, hs₅ ⟩ ; exact Complex.norm_le_abs_re_add_abs_im _ |> le_trans <| by cases abs_cases s.re <;> cases abs_cases s.im <;> linarith ⟩;
      exact h_compact.finite ⟨h_discrete⟩

/-
Define the logarithmic derivative of the Riemann zeta function and the line integral of the logarithmic derivative along a segment.
-/
noncomputable def zetaLogDeriv (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

noncomputable def lineIntegralLogDeriv (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  ∫ t : ℝ in (0)..1, (deriv f (z + t * (w - z)) / f (z + t * (w - z))) * (w - z)

/-
The Riemann zeta function is analytic at any point s ≠ 1.
-/
theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  refine' DifferentiableOn.analyticAt _ _;
  exact { z : ℂ | z ≠ 1 };
  · intro z hz; refine' DifferentiableAt.differentiableWithinAt _; exact differentiableAt_riemannZeta hz;
  · exact isOpen_ne.mem_nhds hs


/-
Define N(T) as the number of zeros in the critical strip with imaginary part between 0 and T, counted with multiplicity.
-/
noncomputable def zetaZeroCountMult (T : ℝ) : ℕ :=
  let S := {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im < T}
  if h : S.Finite then
    ∑ s ∈ h.toFinset, ENat.toNat (analyticOrderAt riemannZeta s)
  else 0

/-
For s with Re(s) >= 2, |zeta(s) - 1| <= |zeta(2) - 1|.
-/
theorem norm_zeta_sub_one_le_zeta_two_sub_one {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ ‖riemannZeta 2 - 1‖ := by
      -- We have $\zeta(s) - 1 = \sum_{n=2}^\infty n^{-s}$.
      have h_sum : riemannZeta s - 1 = ∑' n : ℕ, (1 / ((n + 2 : ℂ) ^ s)) := by
        rw [ zeta_eq_tsum_one_div_nat_add_one_cpow ];
        · rw [ Summable.tsum_eq_zero_add ];
          · norm_num [ add_assoc ];
          · have h_summable : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) := by
              refine' .of_norm _;
              have := Real.summable_one_div_nat_rpow.2 ( show 1 < s.re by linarith );
              convert this using 1;
              ext; rw [ ← Complex.norm_cpow_eq_rpow_re_of_nonneg ] <;> norm_num;
              linarith;
            exact_mod_cast h_summable.comp_injective Nat.succ_injective;
        · linarith;
      -- Since $|n^{-s}| = n^{-\text{Re}(s)}$, we have $|\zeta(s) - 1| \leq \sum_{n=2}^\infty n^{-\text{Re}(s)}$.
      have h_abs_sum : ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, (1 / ((n + 2 : ℝ) ^ s.re)) := by
        convert norm_tsum_le_tsum_norm _ <;> norm_num;
        · rw [ ← Complex.norm_cpow_eq_rpow_re_of_pos ] <;> norm_cast ; norm_num;
        · have h_abs_sum : Summable (fun n : ℕ => (1 / ((n + 2 : ℝ) ^ s.re))) := by
            exact_mod_cast summable_nat_add_iff 2 |>.2 <| Real.summable_one_div_nat_rpow.2 <| by linarith;
          convert h_abs_sum using 1;
          ext; rw [ ← Complex.norm_cpow_eq_rpow_re_of_pos ( by positivity ) ] ; norm_num;
      -- Since $|n^{-s}| = n^{-\text{Re}(s)}$, we have $|\zeta(s) - 1| \leq \sum_{n=2}^\infty n^{-2}$.
      have h_abs_sum_le : ∑' n : ℕ, (1 / ((n + 2 : ℝ) ^ s.re)) ≤ ∑' n : ℕ, (1 / ((n + 2 : ℝ) ^ 2)) := by
        refine' Summable.tsum_le_tsum _ _ _;
        · exact fun n => one_div_le_one_div_of_le ( by positivity ) ( by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) hs ) );
        · exact_mod_cast summable_nat_add_iff 2 |>.2 <| Real.summable_one_div_nat_rpow.2 <| by linarith;
        · exact_mod_cast summable_nat_add_iff 2 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
      -- Recognize that $\sum_{n=2}^\infty n^{-2}$ is the Basel problem, which evaluates to $\frac{\pi^2}{6} - 1$.
      have h_basel : ∑' n : ℕ, (1 / ((n + 2 : ℝ) ^ 2)) = Real.pi ^ 2 / 6 - 1 := by
        convert HasSum.tsum_eq ( hasSum_nat_add_iff' 2 |>.2 <| hasSum_zeta_two ) using 1 <;> norm_num;
      -- Recognize that $\zeta(2) = \frac{\pi^2}{6}$.
      have h_zeta2 : riemannZeta 2 = Real.pi ^ 2 / 6 := by
        exact riemannZeta_two;
      convert h_abs_sum.trans h_abs_sum_le using 1 ; norm_num [ h_zeta2, h_basel ];
      convert h_basel.symm using 1 ; norm_cast ; norm_num [ h_zeta2, h_basel ];
      · nlinarith only [ Real.pi_gt_three ];
      · norm_num [ Complex.normSq, Complex.norm_def, sq ]

/-
For s with Re(s) >= 2, Re(zeta(s)) > 0.
-/
theorem riemannZeta_re_pos_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    0 < (riemannZeta s).re := by
      -- We know that $|\zeta(s) - 1| \leq \zeta(2) - 1$.
      have h_bound : ‖riemannZeta s - 1‖ ≤ ‖riemannZeta 2 - 1‖ := by
        convert norm_zeta_sub_one_le_zeta_two_sub_one hs using 1;
      -- Since $\zeta(2) = \pi^2/6 \approx 1.645$, we have $\zeta(2) - 1 \approx 0.645 < 1$.
      have h_zeta_two : ‖riemannZeta 2 - 1‖ < 1 := by
        -- Since $\zeta(2) = \pi^2/6$, we have $\zeta(2) - 1 = \pi^2/6 - 1$.
        have h_zeta_two_val : riemannZeta 2 = Real.pi^2 / 6 := by
          exact riemannZeta_two;
        norm_num [ h_zeta_two_val, Complex.norm_def, Complex.normSq ];
        norm_cast ; norm_num [ sq ];
        rw [ Real.sqrt_mul_self ] <;> nlinarith only [ Real.pi_gt_three, show Real.pi < 3.4 by pi_upper_bound [ 7 / 5 ] ];
      norm_num [ Complex.normSq, Complex.norm_def ] at *;
      rw [ Real.sqrt_le_iff ] at h_bound ; nlinarith [ Real.sqrt_nonneg ( ( ( riemannZeta 2 |> Complex.re ) - 1 ) * ( ( riemannZeta 2 |> Complex.re ) - 1 ) + ( riemannZeta 2 |> Complex.im ) * ( riemannZeta 2 |> Complex.im ) ), Real.mul_self_sqrt ( add_nonneg ( mul_self_nonneg ( ( riemannZeta 2 |> Complex.re ) - 1 ) ) ( mul_self_nonneg ( riemannZeta 2 |> Complex.im ) ) ) ]



/-
The norm of log(zeta(2 + iT)) is bounded by a constant for all T.
-/
theorem log_zeta_bounded_on_line_two :
    ∃ C : ℝ, ∀ T : ℝ, ‖Complex.log (riemannZeta (2 + T * Complex.I))‖ ≤ C := by
      -- We'll use that ‖riemannZeta (2 + T * Complex.I) - 1‖ ≤ ‖riemannZeta 2 - 1‖ for all T.
      have h_bound : ∀ T : ℝ, ‖riemannZeta (2 + T * Complex.I) - 1‖ ≤ ‖riemannZeta 2 - 1‖ := by
        exact fun T => norm_zeta_sub_one_le_zeta_two_sub_one <| by norm_num;
      -- Since $|\zeta(2 + iT) - 1| \leq \zeta(2) - 1 < 1$, we have $1 - (\zeta(2) - 1) \leq |\zeta(2 + iT)| \leq 1 + (\zeta(2) - 1)$.
      have h_abs : ∀ T : ℝ, 1 - ‖riemannZeta 2 - 1‖ ≤ ‖riemannZeta (2 + T * Complex.I)‖ ∧ ‖riemannZeta (2 + T * Complex.I)‖ ≤ 1 + ‖riemannZeta 2 - 1‖ := by
        intro T; have := h_bound T; have := norm_sub_le ( riemannZeta ( 2 + T * Complex.I ) ) ( riemannZeta ( 2 + T * Complex.I ) - 1 ) ; ( have := norm_add_le ( riemannZeta ( 2 + T * Complex.I ) - 1 ) 1; ( norm_num at *; constructor <;> linarith; ) );
      -- Since $|\zeta(2 + iT)|$ is bounded above and bounded away from 0, $\log |\zeta(2 + iT)|$ is bounded.
      have h_log_abs : ∃ C : ℝ, ∀ T : ℝ, |Complex.re (Complex.log (riemannZeta (2 + T * Complex.I)))| ≤ C := by
        norm_num [ Complex.log_re ];
        -- Since $|\zeta(2 + iT)|$ is bounded above and bounded away from 0, $\log |\zeta(2 + iT)|$ is bounded. Use this fact.
        have h_log_abs_bounded : ∃ C : ℝ, ∀ T : ℝ, 1 - ‖riemannZeta 2 - 1‖ ≤ ‖riemannZeta (2 + T * Complex.I)‖ ∧ ‖riemannZeta (2 + T * Complex.I)‖ ≤ 1 + ‖riemannZeta 2 - 1‖ ∧ 0 < 1 - ‖riemannZeta 2 - 1‖ := by
          refine' ⟨ 0, fun T => ⟨ h_abs T |>.1, h_abs T |>.2, _ ⟩ ⟩;
          norm_num [ riemannZeta_two ];
          norm_num [ Complex.normSq, Complex.norm_def ];
          norm_cast ; norm_num [ sq ];
          rw [ Real.sqrt_mul_self ] <;> nlinarith [ Real.pi_gt_three, show Real.pi < 3.4 by pi_upper_bound [ 7 / 5 ] ];
        obtain ⟨ C, hC ⟩ := h_log_abs_bounded;
        exact ⟨ |Real.log ( 1 - ‖riemannZeta 2 - 1‖ )| + |Real.log ( 1 + ‖riemannZeta 2 - 1‖ )|, fun T => by rw [ abs_le ] ; constructor <;> cases abs_cases ( Real.log ( 1 - ‖riemannZeta 2 - 1‖ ) ) <;> cases abs_cases ( Real.log ( 1 + ‖riemannZeta 2 - 1‖ ) ) <;> linarith [ Real.log_le_log ( by linarith [ hC T ] ) ( hC T |>.1 ), Real.log_le_log ( by linarith [ hC T ] ) ( hC T |>.2.1 ) ] ⟩;
      -- Since $|\zeta(2 + iT)|$ is bounded above and bounded away from 0, $\arg(\zeta(2 + iT))$ is bounded.
      have h_arg : ∃ C : ℝ, ∀ T : ℝ, |Complex.im (Complex.log (riemannZeta (2 + T * Complex.I)))| ≤ C := by
        -- Since $|\zeta(2 + iT)|$ is bounded above and bounded away from 0, $\arg(\zeta(2 + iT))$ is bounded by $\pi/2$.
        have h_arg_bound : ∀ T : ℝ, |Complex.arg (riemannZeta (2 + T * Complex.I))| ≤ Real.pi / 2 := by
          intro T; rw [ abs_le ] ; constructor <;> norm_num [ Complex.arg_le_pi_div_two_iff, Complex.neg_pi_lt_arg ];
          · rw [ Complex.arg ];
            split_ifs <;> norm_num [ neg_div ];
            · linarith [ Real.neg_pi_div_two_le_arcsin ( ( riemannZeta ( 2 + T * Complex.I ) |> Complex.im ) / ‖riemannZeta ( 2 + T * Complex.I )‖ ) ];
            · linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( ( riemannZeta ( 2 + T * Complex.I ) |> Complex.im ) / ‖riemannZeta ( 2 + T * Complex.I )‖ ) ];
            · have := riemannZeta_re_pos_of_two_le_re ( show 2 ≤ ( 2 + T * Complex.I |> Complex.re ) by norm_num ) ; norm_num at * ; linarith;
          · exact Or.inl ( by simpa using riemannZeta_re_pos_of_two_le_re ( show 2 ≤ ( 2 + T * Complex.I |> Complex.re ) by norm_num ) |> le_of_lt );
        exact ⟨ Real.pi / 2, fun T => by simpa [ Complex.log_im ] using h_arg_bound T ⟩;
      exact ⟨ Real.sqrt ( h_log_abs.choose ^ 2 + h_arg.choose ^ 2 ), fun T => by simpa only [ Complex.norm_def, Complex.normSq_apply ] using Real.sqrt_le_sqrt <| by nlinarith [ abs_le.mp ( h_log_abs.choose_spec T ), abs_le.mp ( h_arg.choose_spec T ), Complex.normSq_apply ( Complex.log ( riemannZeta ( 2 + T * Complex.I ) ) ) ] ⟩

end Aristotle.ZetaAnalyticProperties
