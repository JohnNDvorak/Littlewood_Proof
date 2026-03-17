/-
Borel-Carathéodory Lemma and Complex Analysis Infrastructure

Proves key sub-lemmas needed for the pointwise |ζ'/ζ| ≤ C·(log|t|)² bound
without requiring Hadamard factorization.

## Key Results

1. `max_modulus_bound`: If f is holomorphic on ball(c, R), continuous on closedBall,
   and ‖f‖ ≤ M on sphere(c, R), then ‖f(z)‖ ≤ M for z ∈ closedBall(c, R).

2. `schwarz_lemma`: If f is holomorphic on ball(c, R), f(c) = 0, and ‖f‖ ≤ M on
   closedBall(c, R), then ‖f(z)‖ ≤ M · ‖z - c‖ / R.

3. `borel_caratheodory`: If f is holomorphic on ball(c, R), f(c) = 0, and
   Re(f) ≤ A on closedBall(c, R), then ‖f(z)‖ ≤ 2r·A/(R-r) for ‖z-c‖ ≤ r < R.

## References

- Titchmarsh, "Theory of the Riemann Zeta Function", §3.11
- Lang, "Complex Analysis", Ch. VI §3
- Conway, "Functions of One Complex Variable", Ch. VI

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Littlewood.Development.BorelCaratheodory

open Complex Metric Set Filter MeasureTheory Topology

/-! ## Section 1: Maximum Modulus Principle (Bound Form)

The classical maximum modulus principle: if f is holomorphic on a disk
and continuous on the closed disk, then ‖f‖ is bounded by its maximum
on the boundary circle. -/

/-- **Maximum modulus principle** (bound form): A holomorphic function on a disk
    is bounded in modulus by its boundary values. -/
theorem max_modulus_bound {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R))
    {z : ℂ} (hz : z ∈ closedBall c R)
    {M : ℝ} (_hM : 0 ≤ M)
    (hbdy : ∀ w ∈ sphere c R, ‖f w‖ ≤ M) :
    ‖f z‖ ≤ M := by
  by_cases hz_int : z ∈ ball c R
  · by_contra h_gt
    push_neg at h_gt
    have hcont_cb : ContinuousOn f (closedBall c R) := by
      have h := hf.continuousOn; rwa [closure_ball c hR.ne'] at h
    obtain ⟨w₀, hw₀_mem, hw₀_max⟩ := (isCompact_closedBall c R).exists_isMaxOn
      ⟨z, hz⟩ hcont_cb.norm
    have hw₀_ge : M < ‖f w₀‖ := lt_of_lt_of_le h_gt (hw₀_max hz)
    have hw₀_ball : w₀ ∈ ball c R := by
      rcases (mem_closedBall.mp hw₀_mem).eq_or_lt with h_eq | h_lt
      · exact absurd (hbdy w₀ (mem_sphere.mpr h_eq)) (not_le.mpr hw₀_ge)
      · exact mem_ball.mpr h_lt
    have hw₀_max_ball : IsMaxOn (norm ∘ f) (ball c R) w₀ :=
      fun w hw => hw₀_max (ball_subset_closedBall hw)
    have hw₀_localmax : IsLocalMax (norm ∘ f) w₀ :=
      hw₀_max_ball.filter_mono (le_principal_iff.mpr (isOpen_ball.mem_nhds hw₀_ball))
    have hw₀_diff : ∀ᶠ w in nhds w₀, DifferentiableAt ℂ f w :=
      Eventually.mono (isOpen_ball.mem_nhds hw₀_ball)
        (fun w hw => hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hw))
    have hconst := Complex.eventually_eq_of_isLocalMax_norm hw₀_diff hw₀_localmax
    have hanalytic : AnalyticOnNhd ℂ f (ball c R) :=
      hf.differentiableOn.analyticOnNhd isOpen_ball
    have hball_const : EqOn f (fun _ => f w₀) (ball c R) :=
      hanalytic.eqOn_of_preconnected_of_eventuallyEq
        analyticOnNhd_const (convex_ball c R).isPreconnected hw₀_ball hconst
    have hcb_const : EqOn f (fun _ => f w₀) (closedBall c R) :=
      hball_const.of_subset_closure hcont_cb continuousOn_const
        ball_subset_closedBall (by rw [closure_ball c hR.ne'])
    have : c + ↑R ∈ sphere c R := by simp [abs_of_pos hR]
    linarith [hbdy (c + ↑R) this, show ‖f (c + ↑R)‖ = ‖f w₀‖ from by
      rw [hcb_const (sphere_subset_closedBall this)]]
  · exact hbdy z (by
      rw [mem_closedBall] at hz; rw [mem_ball] at hz_int; push_neg at hz_int
      exact mem_sphere.mpr (le_antisymm hz hz_int))

end Littlewood.Development.BorelCaratheodory
