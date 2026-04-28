import Mathlib

open Complex MeasureTheory Metric Real

noncomputable section

namespace ResidueExtraction

/-- Basic winding number: ∮ 1/(z-w) = 2πi for w inside circle.
This is Mathlib's `circleIntegral.integral_sub_inv_of_mem_ball` restated. -/
theorem circle_integral_inv_sub (c : ℂ) (R : ℝ) (w : ℂ) (_hR : 0 < R)
    (hw : w ∈ ball c R) :
    ∮ z in C(c, R), (z - w)⁻¹ = 2 * π * I := by
  exact circleIntegral.integral_sub_inv_of_mem_ball hw

/-- Simple pole residue: if g is holomorphic on closedBall(c,R) and ρ ∈ ball(c,R),
then ∮ g(z)·(z-ρ)⁻¹ dz = 2πi · g(ρ).

Uses the Cauchy integral formula for ℂ→ℂ functions
(`Complex.circleIntegral_div_sub_of_differentiable_on_off_countable`):
  ∮ f(z)/(z-w) dz = 2πi · f(w). -/
theorem circle_integral_simple_pole (c : ℂ) (R : ℝ) (ρ : ℂ) (g : ℂ → ℂ) (a : ℂ)
    (_hR : 0 < R) (hρ : ρ ∈ ball c R)
    (hg : DifferentiableOn ℂ g (closedBall c R))
    (hg_val : g ρ = a) :
    ∮ z in C(c, R), g z * (z - ρ)⁻¹ = 2 * π * I * a := by
  -- Rewrite multiplication by inverse as division
  rw [show ∮ z in C(c, R), g z * (z - ρ)⁻¹ = ∮ z in C(c, R), g z / (z - ρ) from by
    simp_rw [div_eq_mul_inv]]
  -- Apply CIF: ∮ g(z)/(z-ρ) = 2πi · g(ρ) = 2πi · a
  rw [Complex.circleIntegral_div_sub_of_differentiable_on_off_countable
    (Set.countable_empty) hρ hg.continuousOn (fun z hz => ?_), hg_val]
  -- DifferentiableAt from DifferentiableOn on closedBall + point in ball
  have hzb : z ∈ ball c R := (Set.mem_diff _).mp hz |>.1
  exact hg.differentiableAt
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hzb) ball_subset_closedBall)

/-- Abstract residue extraction: if f equals h(z)·(z-ρ)⁻¹ on the punctured disk,
and h is holomorphic with h(ρ) = a, then ∮ f = 2πi · a.

This handles the common case where the integrand f has a simple pole at ρ
with residue a, proved by replacing f with h(z)/(z-ρ) on the integration contour
(where z ≠ ρ since ρ is strictly inside) and applying the CIF. -/
theorem residue_simple_pole_product (c : ℂ) (R : ℝ) (ρ : ℂ)
    (f h : ℂ → ℂ) (a : ℂ)
    (hR : 0 < R) (hρ : ρ ∈ ball c R)
    (_hf : ContinuousOn f (closedBall c R))
    (hh : DifferentiableOn ℂ h (closedBall c R))
    (h_eq : ∀ z ∈ closedBall c R, z ≠ ρ → f z = h z * (z - ρ)⁻¹)
    (h_val : h ρ = a) :
    ∮ z in C(c, R), f z = 2 * π * I * a := by
  -- On the circle |z-c| = R, z ≠ ρ since dist(ρ,c) < R = dist(z,c)
  have hρ_sphere : ∀ z ∈ sphere c R, z ≠ ρ := by
    intro z hz heq
    rw [mem_sphere] at hz; rw [mem_ball] at hρ
    exact absurd (heq ▸ hz ▸ hρ) (lt_irrefl _)
  -- Replace f by h(z)·(z-ρ)⁻¹ on the circle
  have : ∮ z in C(c, R), f z = ∮ z in C(c, R), h z * (z - ρ)⁻¹ := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    exact h_eq z (sphere_subset_closedBall hz) (hρ_sphere z hz)
  rw [this]
  exact circle_integral_simple_pole c R ρ h a hR hρ hh h_val

/-- `(x : ℂ) ^ s` is differentiable in `s` on any closed ball, for real `x > 0`.
Uses `DifferentiableOn.const_cpow` with `(x : ℂ) ≠ 0`. -/
theorem cpow_differentiableOn_closedBall (x : ℝ) (hx : 0 < x) (c : ℂ) (R : ℝ) :
    DifferentiableOn ℂ (fun s => (x : ℂ) ^ s) (closedBall c R) := by
  apply DifferentiableOn.const_cpow differentiableOn_id
  left
  exact_mod_cast hx.ne'

/-- `s⁻¹` is differentiable on any closed ball not containing `0`.
Uses `DifferentiableOn.inv` applied to the identity function. -/
theorem inv_differentiableOn_closedBall (c : ℂ) (R : ℝ)
    (h0 : (0 : ℂ) ∉ closedBall c R) :
    DifferentiableOn ℂ (fun s => s⁻¹) (closedBall c R) := by
  have : DifferentiableOn ℂ id (closedBall c R) := differentiableOn_id
  have hinv := this.inv (fun x hx => ?_)
  · convert hinv using 1
  · exact fun heq => h0 (heq ▸ hx)

end ResidueExtraction
