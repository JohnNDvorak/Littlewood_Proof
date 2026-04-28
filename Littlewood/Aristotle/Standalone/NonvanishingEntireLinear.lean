/-
# Nonvanishing entire functions of subquadratic growth are exp(linear)

This file proves: if `f : ℂ → ℂ` is entire, everywhere nonvanishing,
and `‖f z‖ ≤ exp(C (‖z‖ + 1)^α)` for some `α < 2`, then
`f z = exp(A + B * z)` for some constants `A, B : ℂ`.

Used by `HadamardFactorizationCore.lean` to prove `xi_zeros_infinite_hyp`.
-/
import Littlewood.Aristotle.Standalone.HadamardLiouvilleGeneralized
import Littlewood.Aristotle.RiemannXiEntire

open Complex Metric Filter Set Function Topology

noncomputable section

namespace Aristotle.Standalone.NonvanishingEntireLinear

/-! ## Borel-Carathéodory on a disk -/

/-
**Borel-Carathéodory on a disk** (Schwarz lemma proof).
If `f` is differentiable on `ball(0, R)` with `f(0) = 0` and `Re(f(z)) ≤ M`
for all `z ∈ ball(0, R)`, then `‖f(z)‖ ≤ 2M` for `z ∈ ball(0, R/2)`.
-/
theorem borel_caratheodory_disk
    (f : ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hf_diff : DifferentiableOn ℂ f (ball 0 R))
    (hf_zero : f 0 = 0)
    (hf_re : ∀ z ∈ ball (0 : ℂ) R, (f z).re ≤ M) :
    ∀ z ∈ ball (0 : ℂ) (R / 2), ‖f z‖ ≤ 2 * M := by
  intro z hz;
  have h_phi : ‖(f z) / (2 * M - f z)‖ ≤ ‖z‖ / R := by
    have h_phi : DifferentiableOn ℂ (fun z => f z / (2 * M - f z)) (ball (0 : ℂ) R) := by
      exact DifferentiableOn.div hf_diff ( DifferentiableOn.sub ( differentiableOn_const _ ) hf_diff ) fun z hz => sub_ne_zero_of_ne <| by intro H; have := hf_re z hz; norm_num [ show f z = 2 * M by linear_combination H.symm ] at this; linarith;
    have h_phi_maps : ∀ z ∈ ball (0 : ℂ) R, ‖(f z) / (2 * M - f z)‖ ≤ 1 := by
      simp_all +decide [ Complex.norm_def, Complex.normSq ];
      exact fun z hz => div_le_one_of_le₀ ( Real.sqrt_le_sqrt <| by nlinarith [ hf_re z hz ] ) ( Real.sqrt_nonneg _ );
    have := @Complex.dist_le_div_mul_dist_of_mapsTo_ball;
    specialize this h_phi ( show MapsTo ( fun z => f z / ( 2 * M - f z ) ) ( ball 0 R ) ( closedBall ( f 0 / ( 2 * M - f 0 ) ) 1 ) from fun z hz => by simpa [ hf_zero ] using h_phi_maps z hz ) ( show z ∈ ball 0 R from by simpa using hz.out.trans_le ( by linarith ) ) ; simp_all +decide [ div_eq_inv_mul ];
  -- Since ‖z‖ / R ≤ 1 / 2, we have ‖f z / (2 * M - f z)‖ ≤ 1 / 2.
  have h_norm_le_half : ‖f z / (2 * M - f z)‖ ≤ 1 / 2 := by
    exact h_phi.trans ( by rw [ div_le_iff₀ hR ] ; linarith [ mem_ball_zero_iff.mp hz ] );
  norm_num [ Complex.normSq, Complex.norm_def ] at *;
  rw [ div_le_iff₀ ] at h_norm_le_half;
  · rw [ Real.sqrt_le_iff ] at *;
    exact ⟨ by linarith, by nlinarith [ Real.mul_self_sqrt ( add_nonneg ( mul_self_nonneg ( 2 * M - ( f z |> Complex.re ) ) ) ( mul_self_nonneg ( f z |> Complex.im ) ) ) ] ⟩;
  · exact Real.sqrt_pos.mpr ( by nlinarith only [ hM, hf_re z ( by linarith ) ] )

/-! ## Borel-Carathéodory for entire functions -/

/-
Borel-Carathéodory for entire functions with power-type real-part bound.
If `g` is entire and `Re(g(z)) ≤ C (‖z‖ + 1)^α`, then
`‖g z‖ ≤ C' (‖z‖ + 1)^α` for a suitable `C'`.
-/
theorem borel_caratheodory_entire_growth
    (g : ℂ → ℂ) (hg_diff : Differentiable ℂ g)
    (α C : ℝ) (hα : 0 ≤ α) (hC : 0 < C)
    (hRe : ∀ z : ℂ, (g z).re ≤ C * (‖z‖ + 1) ^ α) :
    ∃ C' : ℝ, 0 < C' ∧ SubquadraticGrowth g α C' := by
  -- For any $z$, set $R = 2(‖z‖+1)$. Apply borel_caratheodory_disk to $h(w) = g(w) - g(0)$ on $ball(0, R)$ with $M = C·(R+1)^α + |Re(g(0))|$.
  have h_bc : ∀ z : ℂ, ‖g z - g 0‖ ≤ 2 * (C * (2 * ‖z‖ + 3) ^ α + |(g 0).re|) := by
    intro z
    set R := 2 * (‖z‖ + 1) with hR_def
    have h_bc : ∀ w ∈ ball (0 : ℂ) R, (g w - g 0).re ≤ C * (R + 1) ^ α + |(g 0).re| := by
      intros w hw
      have h_re_bound : (g w).re ≤ C * (R + 1) ^ α := by
        exact le_trans ( hRe w ) ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( by positivity ) ( by linarith [ mem_ball_zero_iff.mp hw, norm_nonneg w ] ) ( by positivity ) ) hC.le );
      norm_num at * ; cases abs_cases ( ( g 0 |> Complex.re ) ) <;> linarith;
    have := borel_caratheodory_disk ( fun w => g w - g 0 ) R ( C * ( R + 1 ) ^ α + |( g 0 |> Complex.re )| ) ?_ ?_ ?_ ?_ ?_ <;> norm_num at *;
    · grind +revert;
    · positivity;
    · positivity;
    · exact hg_diff.differentiableOn;
    · exact h_bc;
  -- Then ‖g(z)‖ ≤ ‖g(0)‖ + 2M ≤ C'(‖z‖+1)^α where C' = 2C·3^α + ‖g(0)‖ + 2|Re(g(0))| + 1 (using (R+1)^α = (2‖z‖+3)^α ≤ 3^α(‖z‖+1)^α and (‖z‖+1)^α ≥ 1).
  have h_bound : ∀ z : ℂ, ‖g z‖ ≤ 2 * C * 3 ^ α * (‖z‖ + 1) ^ α + ‖g 0‖ + 2 * |(g 0).re| + 1 := by
    intro z
    have h_bound_step : ‖g z - g 0‖ ≤ 2 * C * 3 ^ α * (‖z‖ + 1) ^ α + 2 * |(g 0).re| := by
      have h_bound_step : (2 * ‖z‖ + 3) ^ α ≤ 3 ^ α * (‖z‖ + 1) ^ α := by
        rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ) ] ; exact Real.rpow_le_rpow ( by positivity ) ( by linarith [ norm_nonneg z ] ) ( by positivity );
      nlinarith [ h_bc z, show 0 ≤ C * ( 2 * ‖z‖ + 3 ) ^ α by positivity ];
    linarith [ norm_sub_norm_le ( g z ) ( g 0 ) ];
  refine' ⟨ 2 * C * 3 ^ α + ‖g 0‖ + 2 * |( g 0 |> Complex.re )| + 1, _, _ ⟩;
  · positivity;
  · intro z;
    refine' le_trans ( h_bound z ) _;
    nlinarith [ show 1 ≤ ( ‖z‖ + 1 ) ^ α by exact Real.one_le_rpow ( by linarith [ norm_nonneg z ] ) ( by linarith ), show 0 ≤ 2 * C * 3 ^ α by positivity, show 0 ≤ ‖g 0‖ by positivity, show 0 ≤ 2 * |( g 0 |> Complex.re )| by positivity ]

/-! ## Lifting through the exponential covering map -/

/-
If `Q` is entire and everywhere nonvanishing, there exists an entire `g`
with `exp(g(z)) = Q(z)` for all `z`.
-/
theorem entire_nonvanishing_has_log
    (Q : ℂ → ℂ) (hQ_diff : Differentiable ℂ Q) (hQ_ne : ∀ z, Q z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, exp (g z) = Q z := by
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, Continuous g ∧ ∀ z, Complex.exp (g z) = Q z := by
    have h_lift : ∃ g : ℂ → ℂ, Continuous g ∧ ∀ z, Complex.exp (g z) = Q z := by
      have h_covering : IsCoveringMap (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) := by
        exact?
      have := h_covering.existsUnique_continuousMap_lifts ( ContinuousMap.mk ( fun z => ⟨ Q z, hQ_ne z ⟩ ) ( by exact Continuous.subtype_mk ( hQ_diff.continuous ) _ ) ) 0;
      obtain ⟨ g, hg₁, hg₂ ⟩ := this ( Complex.log ( Q 0 ) ) ( by simp +decide [ Complex.exp_log ( hQ_ne 0 ) ] );
      exact ⟨ g, g.continuous, fun z => by simpa using congr_arg Subtype.val ( congr_fun hg₁.2 z ) ⟩;
    exact h_lift;
  refine' ⟨ g, _, hg.2 ⟩;
  have h_diff : ∀ s₀, ∃ ε > 0, ∀ s, ‖s - s₀‖ < ε → DifferentiableAt ℂ g s := by
    intro s₀
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ s, ‖s - s₀‖ < ε → ‖g s - g s₀‖ < Real.pi / 2 := by
      exact Metric.continuous_iff.mp hg.1 s₀ ( Real.pi / 2 ) ( by positivity );
    use ε, hε_pos;
    intro s hs
    have h_diff : DifferentiableAt ℂ (fun s => Complex.log (Q s / Q s₀) + g s₀) s := by
      refine' DifferentiableAt.add _ _;
      · refine' DifferentiableAt.clog _ _;
        · exact DifferentiableAt.div_const ( hQ_diff.differentiableAt ) _;
        · simp_all +decide [ Complex.slitPlane, Complex.exp_ne_zero ];
          have h_diff : Complex.exp (g s - g s₀) = Q s / Q s₀ := by
            rw [ Complex.exp_sub, hg.2, hg.2 ];
          rw [ ← h_diff, Complex.exp_re, Complex.exp_im ];
          exact Or.inl ( mul_pos ( Real.exp_pos _ ) ( Real.cos_pos_of_mem_Ioo ⟨ by linarith [ abs_le.mp ( Complex.abs_im_le_norm ( g s - g s₀ ) ), hε s hs ], by linarith [ abs_le.mp ( Complex.abs_im_le_norm ( g s - g s₀ ) ), hε s hs ] ⟩ ) );
      · exact differentiableAt_const _;
    refine' h_diff.congr_of_eventuallyEq _;
    filter_upwards [ IsOpen.mem_nhds ( isOpen_lt ( continuous_norm.comp ( continuous_sub_right s₀ ) ) continuous_const ) hs ] with z hz;
    have h_eq : Complex.exp (g z - g s₀) = Q z / Q s₀ := by
      rw [ Complex.exp_sub, hg.2, hg.2 ];
    rw [ ← h_eq, Complex.log_exp ];
    · ring;
    · linarith [ abs_le.mp ( Complex.abs_im_le_norm ( g z - g s₀ ) ), hε z hz, Real.pi_pos ];
    · linarith [ abs_le.mp ( Complex.abs_im_le_norm ( g z - g s₀ ) ), hε z hz, Real.pi_pos ];
  exact fun s => by obtain ⟨ ε, ε_pos, hε ⟩ := h_diff s; exact hε s ( by simpa using ε_pos ) ;

/-! ## Main theorem -/

/-- An entire nonvanishing function with subquadratic exponential growth is `exp(linear)`. -/
theorem entire_nonvanishing_subquad_is_exp_linear
    (Q : ℂ → ℂ) (hQ_diff : Differentiable ℂ Q) (hQ_ne : ∀ z, Q z ≠ 0)
    (α C : ℝ) (hα_lt : α < 2) (hα_nn : 0 ≤ α) (hC : 0 < C)
    (hQ_growth : ∀ z, ‖Q z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ α)) :
    ∃ A B : ℂ, ∀ z, Q z = exp (A + B * z) := by
  obtain ⟨g, hg_diff, hg_exp⟩ := entire_nonvanishing_has_log Q hQ_diff hQ_ne
  have hRe_bound : ∀ z : ℂ, (g z).re ≤ C * (‖z‖ + 1) ^ α := by
    intro z
    have h1 : (g z).re = Real.log ‖Q z‖ := by
      rw [← hg_exp z, norm_exp]; exact (Real.log_exp _).symm
    rw [h1]
    calc Real.log ‖Q z‖
        ≤ Real.log (Real.exp (C * (‖z‖ + 1) ^ α)) :=
          Real.log_le_log (norm_pos_iff.mpr (hQ_ne z)) (hQ_growth z)
      _ = C * (‖z‖ + 1) ^ α := Real.log_exp _
  obtain ⟨C', hC'_pos, hC'_bound⟩ :=
    borel_caratheodory_entire_growth g hg_diff α C hα_nn hC hRe_bound
  obtain ⟨A, B, hg_linear⟩ :=
    subquadratic_growth_imp_linear g hg_diff α C' hα_lt hα_nn hC'_pos hC'_bound
  exact ⟨A, B, fun z => by rw [← hg_exp z, hg_linear z]⟩

end Aristotle.Standalone.NonvanishingEntireLinear
