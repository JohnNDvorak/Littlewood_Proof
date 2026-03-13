/-
Smooth Hardy theta function via integration of the digamma-based derivative.

The standard definition theta(t) = Im(log Gamma(1/4+it/2)) - (t/2)log pi has jump
discontinuities when Gamma(1/4+it/2) crosses the negative real axis. This makes
`deriv hardyTheta` undefined at those points, blocking the VdC integration-by-parts
needed for B2.

We define a SMOOTH version:
  hardyThetaSmooth(t) = hardyTheta(0) + integral_0^t thetaDeriv(u) du

where thetaDeriv(t) = (1/2)Re(digamma(1/4+it/2)) - (1/2)log pi is already proved
to be the derivative of theta away from branch cuts (via the digamma function, which
is globally analytic on Re(s)>0).

KEY RESULTS:
  continuous_thetaDeriv: thetaDeriv is continuous on R
  differentiable_hardyThetaSmooth: hardyThetaSmooth is differentiable everywhere
  hasDerivAt_hardyThetaSmooth: deriv hardyThetaSmooth t = thetaDeriv t
  hardyThetaSmooth_exp_eq: exp(I * hardyThetaSmooth t) = exp(I * hardyTheta t)

The last identity follows because both functions satisfy the same linear ODE
f'(t) = I*thetaDeriv(t)*f(t) with the same initial condition.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.ThetaDerivAsymptotic
import Littlewood.Aristotle.GammaHalfPlane
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyCosSmooth
import Littlewood.Aristotle.HardyCosExpOmega

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyThetaSmooth

open Complex Real Set Filter Topology MeasureTheory
open ThetaDerivAsymptotic

/-! ## Part 1: Continuity of thetaDeriv

`thetaDeriv t = (1/2) * Re(Gamma'/Gamma(1/4+it/2)) - (1/2)*log pi`

Since Gamma is holomorphic on `{s : C | Re(s) > 0}` (an open set), and this
set avoids all non-positive integers, `DifferentiableOn.analyticOn` gives
analyticity. Then `deriv Gamma` is also analytic there (by `AnalyticAt.deriv`),
hence continuous. The quotient with Gamma (nonzero) is then continuous.

We prove this by showing:
1. `Gamma` is differentiable on the open right half-plane
2. Hence analytic there (by Cauchy integral formula)
3. `deriv Gamma` is analytic there (derivative of analytic is analytic)
4. `t |--> deriv Gamma(1/4+it/2) / Gamma(1/4+it/2)` is continuous
-/

/-- The right half-plane is open. -/
private lemma isOpen_re_pos : IsOpen {s : ℂ | 0 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- Gamma is differentiable on the right half-plane. -/
private lemma differentiableOn_gamma_re_pos :
    DifferentiableOn ℂ Complex.Gamma {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (differentiableAt_Gamma s (fun m => by
    intro h; rw [h] at hs; simp at hs; linarith [Nat.cast_nonneg (α := ℝ) m]
  )).differentiableWithinAt

/-- Gamma is analytic on the right half-plane. -/
private lemma analyticOn_gamma_re_pos :
    AnalyticOnNhd ℂ Complex.Gamma {s : ℂ | 0 < s.re} :=
  differentiableOn_gamma_re_pos.analyticOnNhd isOpen_re_pos

/-- `deriv Gamma` is continuous at every point of the right half-plane. -/
private lemma continuousAt_deriv_gamma_re_pos (s : ℂ) (hs : 0 < s.re) :
    ContinuousAt (deriv Complex.Gamma) s :=
  ((analyticOn_gamma_re_pos s hs).deriv).continuousAt

/-- The affine embedding t |--> 1/4 + it/2 is continuous. -/
private lemma continuous_quarter_affine :
    Continuous (fun t : ℝ => (1/4 + I * (↑t/2) : ℂ)) := by
  apply Continuous.add continuous_const
  exact Continuous.mul continuous_const (Continuous.div_const
    (Complex.continuous_ofReal.comp continuous_id) 2)

set_option maxHeartbeats 3200000 in
/-- `deriv Gamma` is continuous along the curve 1/4+it/2. -/
private lemma continuous_deriv_gamma_quarter :
    Continuous (fun t : ℝ => deriv Complex.Gamma (1/4 + I * (↑t/2) : ℂ)) := by
  -- Analyticity gives us that deriv Gamma is continuous on the right half-plane
  -- We use ContinuousOn.comp with the affine map into the right half-plane
  have hco : ContinuousOn (deriv Complex.Gamma) {s : ℂ | 0 < s.re} := by
    intro s hs
    exact (continuousAt_deriv_gamma_re_pos s hs).continuousWithinAt
  have hφ : Continuous (fun t : ℝ => (1/4 + I * (↑t/2) : ℂ)) := continuous_quarter_affine
  have hrange : ∀ t : ℝ, (1/4 + I * (↑t/2) : ℂ) ∈ {s : ℂ | 0 < s.re} :=
    fun t => GammaHalfPlane.re_quarter_plus_it_half_pos t
  exact (hco.comp_continuous hφ hrange)

/-- `Gamma` is continuous along the curve 1/4+it/2. -/
private lemma continuous_gamma_quarter :
    Continuous (fun t : ℝ => Complex.Gamma (1/4 + I * (↑t/2) : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (GammaHalfPlane.hasDerivAt_gamma_quarter t).continuousAt

/-- The digamma function Gamma'/Gamma is continuous along 1/4+it/2. -/
private lemma continuous_digamma_at_quarter :
    Continuous (fun t : ℝ =>
      deriv Complex.Gamma (1/4 + I * (↑t/2) : ℂ) / Complex.Gamma (1/4 + I * (↑t/2) : ℂ)) :=
  continuous_deriv_gamma_quarter.div continuous_gamma_quarter
    (fun t => GammaHalfPlane.gamma_quarter_ne_zero t)

/-- The real part of the digamma function along 1/4+it/2 is continuous. -/
private lemma continuous_re_digamma_quarter :
    Continuous (fun t : ℝ =>
      (deriv Complex.Gamma (1/4 + I * (↑t/2) : ℂ) / Complex.Gamma (1/4 + I * (↑t/2) : ℂ)).re) :=
  Complex.continuous_re.comp continuous_digamma_at_quarter

/-- `thetaDeriv` is continuous on all of R.
This is the key regularity result: unlike hardyTheta = Im(log Gamma), the derivative
defined via digamma is globally smooth. -/
theorem continuous_thetaDeriv : Continuous thetaDeriv := by
  unfold thetaDeriv
  apply Continuous.sub
  · exact continuous_const.mul continuous_re_digamma_quarter
  · exact continuous_const

/-- `thetaDeriv` is interval-integrable on any interval. -/
theorem thetaDeriv_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable thetaDeriv volume a b :=
  continuous_thetaDeriv.intervalIntegrable a b

/-! ## Part 2: Definition and basic properties of hardyThetaSmooth -/

/-- The smooth Hardy theta function, defined as the antiderivative of thetaDeriv
with initial value hardyTheta(0).

This agrees with hardyTheta at continuity points but is smooth everywhere,
avoiding the 2pi jumps from Im(log Gamma) branch cuts. -/
noncomputable def hardyThetaSmooth (t : ℝ) : ℝ :=
  HardyEstimatesPartial.hardyTheta 0 + ∫ u in (0 : ℝ)..t, thetaDeriv u

/-- hardyThetaSmooth at 0 equals hardyTheta at 0. -/
theorem hardyThetaSmooth_zero :
    hardyThetaSmooth 0 = HardyEstimatesPartial.hardyTheta 0 := by
  simp [hardyThetaSmooth, intervalIntegral.integral_same]

/-- hardyThetaSmooth has derivative thetaDeriv everywhere (FTC). -/
theorem hasDerivAt_hardyThetaSmooth (t : ℝ) :
    HasDerivAt hardyThetaSmooth (thetaDeriv t) t := by
  unfold hardyThetaSmooth
  have hcont : ContinuousAt thetaDeriv t := continuous_thetaDeriv.continuousAt
  have hmeas : StronglyMeasurableAtFilter thetaDeriv (𝓝 t) :=
    continuous_thetaDeriv.aestronglyMeasurable.stronglyMeasurableAtFilter
  have hderiv : HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, thetaDeriv u) (thetaDeriv t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (thetaDeriv_intervalIntegrable 0 t)
      hmeas
      hcont
  exact hderiv.const_add _

/-- hardyThetaSmooth is differentiable everywhere. -/
theorem differentiable_hardyThetaSmooth : Differentiable ℝ hardyThetaSmooth :=
  fun t => (hasDerivAt_hardyThetaSmooth t).differentiableAt

/-- The derivative of hardyThetaSmooth equals thetaDeriv pointwise. -/
theorem deriv_hardyThetaSmooth (t : ℝ) :
    deriv hardyThetaSmooth t = thetaDeriv t :=
  (hasDerivAt_hardyThetaSmooth t).deriv

/-- hardyThetaSmooth is continuous. -/
theorem continuous_hardyThetaSmooth : Continuous hardyThetaSmooth :=
  differentiable_hardyThetaSmooth.continuous

/-! ## Part 3: The exponential bridge

The key identity: exp(I * hardyThetaSmooth t) = exp(I * hardyTheta t).

Both sides satisfy the same linear ODE f'(t) = I*thetaDeriv(t)*f(t):
- LHS: by construction (deriv hardyThetaSmooth = thetaDeriv)
- RHS: because exp(I*theta(t)) = Gamma(s)/norm(Gamma(s)) * exp(-I*(t/2)*log pi) is smooth,
  and its angular velocity is thetaDeriv(t)

They also agree at t=0 (by definition of hardyThetaSmooth). By uniqueness
of solutions to linear ODEs, they agree everywhere.

This is formalized via the quotient argument: if g(t) = f1(t)/f2(t) where
both satisfy the same ODE, then g'(t) = 0 and g(0) = 1, so g = 1.
-/

set_option maxHeartbeats 6400000 in
/-- The exponential of I*hardyThetaSmooth equals the branch-cut-free phase factor.
This is the core bridge: it shows that despite hardyTheta having 2pi jumps,
the smooth version produces the same exponential.

Proof sketch: both sides are continuous, agree at t=0, and satisfy the same ODE.
By uniqueness (quotient has zero derivative + constant), they are equal.

The ODE uniqueness argument requires showing that the branch-cut-free
phase factor Gamma(s)/norm(Gamma(s)) * exp(-I*(t/2)*log(pi)) has angular
velocity thetaDeriv(t), which follows from the derivative computation in
HardyCosExpDeriv.lean and AngularDerivative.lean. -/
theorem hardyThetaSmooth_exp_eq (t : ℝ) :
    Complex.exp (I * ↑(hardyThetaSmooth t))
      = Complex.exp (I * ↑(HardyEstimatesPartial.hardyTheta t)) := by
  -- Step 1: hardyCosExp 0 u = exp(I * hardyTheta u) for all u
  have hG_eq : ∀ u, HardyCosSmooth.hardyCosExp 0 u
      = Complex.exp (I * ↑(HardyEstimatesPartial.hardyTheta u)) := by
    intro u
    rw [HardyCosSmooth.hardyCosExp_eq_cexp_phaseArg 0 u]
    congr 1
    have := HardyCosSmooth.hardyPhaseArg_eq_hardyTheta_sub_log 0 u
    simp only [Nat.cast_zero, zero_add, Real.log_one, mul_zero, sub_zero] at this
    rw [this]
  rw [← hG_eq]
  -- Step 2: Both exp(I * hardyThetaSmooth) and hardyCosExp 0 satisfy the same linear ODE
  -- f'(t) = I * thetaDeriv(t) * f(t), so their difference D satisfies
  -- D'(t) = I * thetaDeriv(t) * D(t), ‖D'(t)‖ ≤ |thetaDeriv(t)| * ‖D(t)‖
  -- By Gronwall with D(0) = 0, D = 0 everywhere.
  -- Define the two functions
  set F : ℝ → ℂ := fun u => Complex.exp (I * ↑(hardyThetaSmooth u)) with hF_def
  set G : ℝ → ℂ := fun u => HardyCosSmooth.hardyCosExp 0 u with hG_def
  set D : ℝ → ℂ := fun u => F u - G u with hD_def
  -- F has derivative I * thetaDeriv * F
  have hF_deriv : ∀ u, HasDerivAt F (I * ↑(thetaDeriv u) * F u) u := by
    intro u
    show HasDerivAt (fun u => Complex.exp (I * ↑(hardyThetaSmooth u)))
      (I * ↑(thetaDeriv u) * Complex.exp (I * ↑(hardyThetaSmooth u))) u
    have h1 : HasDerivAt (fun u => I * ↑(hardyThetaSmooth u)) (I * ↑(thetaDeriv u)) u :=
      (hasDerivAt_hardyThetaSmooth u).ofReal_comp.const_mul I
    have h3 := h1.cexp
    -- h3 : HasDerivAt ... (exp(I * hardyThetaSmooth u) * (I * thetaDeriv u)) u
    exact h3.congr_deriv (by ring)
  -- G has derivative I * thetaDeriv * G (from hardyCosExp_angular_velocity at n=0)
  have hG_deriv : ∀ u, HasDerivAt G (I * ↑(thetaDeriv u) * G u) u := by
    intro u
    have h := Aristotle.HardyCosExpOmega.hardyCosExp_angular_velocity 0 u
    -- The derivative is I * (thetaDeriv u - log(↑(0+1))) * hardyCosExp 0 u
    -- = I * (thetaDeriv u - log 1) * ... = I * (thetaDeriv u - 0) * ...
    -- = I * thetaDeriv u * hardyCosExp 0 u
    have hlog : Real.log (↑(0 + 1 : ℕ) : ℝ) = 0 := by
      simp [Nat.cast_one, Real.log_one]
    simp only [hlog, sub_zero] at h
    exact h
  -- D has derivative I * thetaDeriv * D
  have hD_deriv : ∀ u, HasDerivAt D (I * ↑(thetaDeriv u) * D u) u := by
    intro u
    have hsub := (hF_deriv u).sub (hG_deriv u)
    -- hsub : HasDerivAt (F - G) (I * thetaDeriv u * F u - I * thetaDeriv u * G u) u
    have : I * ↑(thetaDeriv u) * F u - I * ↑(thetaDeriv u) * G u
        = I * ↑(thetaDeriv u) * (F u - G u) := by ring
    rw [this] at hsub
    exact hsub
  -- D(0) = 0
  have hD_zero : D 0 = 0 := by
    show F 0 - G 0 = 0
    rw [sub_eq_zero]
    show Complex.exp (I * ↑(hardyThetaSmooth 0)) = HardyCosSmooth.hardyCosExp 0 0
    rw [hardyThetaSmooth_zero, hG_eq 0]
  -- D is differentiable
  have hD_diff : Differentiable ℝ D := by
    intro u
    exact (hD_deriv u).differentiableAt
  -- D is continuous
  have hD_cont : Continuous D := hD_diff.continuous
  -- ‖D'(u)‖ ≤ |thetaDeriv u| * ‖D u‖
  have hD_norm_deriv : ∀ u, ‖I * ↑(thetaDeriv u) * D u‖ ≤ |thetaDeriv u| * ‖D u‖ := by
    intro u
    rw [show I * ↑(thetaDeriv u) * D u = (I * ↑(thetaDeriv u)) * D u from by ring]
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  -- For t ≥ 0: apply Gronwall on [0, t+1]
  -- For t < 0: apply Gronwall on [t-1, 0] via time reversal
  suffices h : D t = 0 by
    have : F t = G t := sub_eq_zero.mp h
    exact this
  -- Use thetaDeriv is continuous hence bounded on compact intervals
  by_cases ht : 0 ≤ t
  · -- Case t ≥ 0: apply Gronwall on [0, t+1]
    set b := t + 1 with hb_def
    have hab : (0 : ℝ) < b := by linarith
    -- thetaDeriv is continuous on [0, b], hence bounded
    have hK : ∃ K : ℝ, ∀ u ∈ Set.Ico (0 : ℝ) b, |thetaDeriv u| ≤ K := by
      obtain ⟨x, _, hx_max⟩ := isCompact_Icc.exists_isMaxOn
        (Set.nonempty_Icc.mpr (le_of_lt hab))
        ((continuous_abs.comp continuous_thetaDeriv).continuousOn)
      refine ⟨|thetaDeriv x|, fun u hu => ?_⟩
      exact hx_max (Set.Ico_subset_Icc_self hu)
    obtain ⟨K, hK⟩ := hK
    have := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := D)
      (f' := fun u => I * ↑(thetaDeriv u) * D u)
      (K := K)
      (a := 0)
      (b := b)
      (hD_cont.continuousOn.mono (Set.subset_univ _))
      (fun u hu => (hD_deriv u).hasDerivWithinAt)
      hD_zero
      (fun u hu => (hD_norm_deriv u).trans (by
        gcongr
        exact hK u hu))
    exact this t ⟨ht, by linarith⟩
  · -- Case t < 0: apply to D_rev(u) = D(-u) on [0, -t+1]
    push_neg at ht
    set b := -t + 1 with hb_def
    have hab : (0 : ℝ) < b := by linarith
    -- Define reversed function
    set D_rev : ℝ → ℂ := fun u => D (-u) with hDr_def
    -- D_rev has derivative -I * thetaDeriv(-u) * D_rev(u)
    have hDr_deriv : ∀ u, HasDerivAt D_rev (-(I * ↑(thetaDeriv (-u)) * D_rev u)) u := by
      intro u
      -- Both F and G have chain-rule derivatives at -u composed with negation
      have hF_neg : HasDerivAt (fun x => F (-x))
          (-(I * ↑(thetaDeriv (-u)) * F (-u))) u := by
        have hcomp := (hF_deriv (-u)).scomp u (hasDerivAt_neg u)
        simp only [Function.comp_def] at hcomp
        exact hcomp.congr_deriv (by simp)
      have hG_neg : HasDerivAt (fun x => G (-x))
          (-(I * ↑(thetaDeriv (-u)) * G (-u))) u := by
        have hcomp := (hG_deriv (-u)).scomp u (hasDerivAt_neg u)
        simp only [Function.comp_def] at hcomp
        exact hcomp.congr_deriv (by simp)
      have hsub := hF_neg.sub hG_neg
      -- hsub : HasDerivAt (fun x => F(-x) - G(-x)) (...) u
      -- The derivative simplifies to -(I * thetaDeriv(-u) * (F(-u) - G(-u)))
      have : -(I * ↑(thetaDeriv (-u)) * F (-u)) - -(I * ↑(thetaDeriv (-u)) * G (-u))
          = -(I * ↑(thetaDeriv (-u)) * (F (-u) - G (-u))) := by ring
      rw [this] at hsub
      exact hsub
    -- D_rev(0) = D(0) = 0
    have hDr_zero : D_rev 0 = 0 := by
      show D (-0) = 0
      rw [neg_zero]
      exact hD_zero
    -- D_rev is differentiable and continuous
    have hDr_diff : Differentiable ℝ D_rev := by
      intro u; exact (hDr_deriv u).differentiableAt
    have hDr_cont : Continuous D_rev := hDr_diff.continuous
    -- Norm bound for D_rev derivative
    have hDr_norm : ∀ u, ‖-(I * ↑(thetaDeriv (-u)) * D_rev u)‖
        ≤ |thetaDeriv (-u)| * ‖D_rev u‖ := by
      intro u
      rw [norm_neg]
      -- Need: ‖I * thetaDeriv(-u) * D_rev u‖ ≤ |thetaDeriv(-u)| * ‖D_rev u‖
      -- D_rev u = D (-u), so this is the same as hD_norm_deriv applied at -u
      show ‖I * ↑(thetaDeriv (-u)) * D (-u)‖ ≤ |thetaDeriv (-u)| * ‖D (-u)‖
      exact hD_norm_deriv (-u)
    -- Bounded on compact interval
    have hK : ∃ K : ℝ, ∀ u ∈ Set.Ico (0 : ℝ) b, |thetaDeriv (-u)| ≤ K := by
      obtain ⟨x, _, hx_max⟩ := isCompact_Icc.exists_isMaxOn
        (Set.nonempty_Icc.mpr (le_of_lt hab))
        ((continuous_abs.comp (continuous_thetaDeriv.comp continuous_neg)).continuousOn)
      refine ⟨|thetaDeriv (-x)|, fun u hu => ?_⟩
      exact hx_max (Set.Ico_subset_Icc_self hu)
    obtain ⟨K, hK⟩ := hK
    have hDr_eq_zero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := D_rev)
      (f' := fun u => -(I * ↑(thetaDeriv (-u)) * D_rev u))
      (K := K)
      (a := 0)
      (b := b)
      (hDr_cont.continuousOn.mono (Set.subset_univ _))
      (fun u hu => (hDr_deriv u).hasDerivWithinAt)
      hDr_zero
      (fun u hu => (hDr_norm u).trans (by
        gcongr
        exact hK u hu))
    have h_neg_t : -t ∈ Set.Icc (0 : ℝ) b := ⟨le_of_lt (neg_pos.mpr ht), by linarith⟩
    have := hDr_eq_zero (-t) h_neg_t
    -- this : D_rev (-t) = 0, i.e., D (--t) = 0, i.e., D t = 0
    show D t = 0
    have : D (- -t) = 0 := this
    rwa [neg_neg] at this

/-! ## Part 4: Smooth phase for VdC integration by parts -/

/-- Smooth version of the Hardy phase: phi_n(t) = theta_smooth(t) - t*log(n+1).
This is differentiable everywhere (unlike the Im(log Gamma)-based version). -/
noncomputable def hardyPhaseSmooth (n : ℕ) (t : ℝ) : ℝ :=
  hardyThetaSmooth t - t * Real.log (↑n + 1)

/-- The smooth phase is differentiable everywhere. -/
theorem differentiable_hardyPhaseSmooth (n : ℕ) :
    Differentiable ℝ (hardyPhaseSmooth n) := by
  intro t
  exact (differentiable_hardyThetaSmooth.differentiableAt).sub
    (differentiableAt_id.mul (differentiableAt_const _))

/-- HasDerivAt for the smooth phase. -/
theorem hasDerivAt_hardyPhaseSmooth (n : ℕ) (t : ℝ) :
    HasDerivAt (hardyPhaseSmooth n)
      (thetaDeriv t - Real.log (↑n + 1)) t := by
  unfold hardyPhaseSmooth
  have h1 := hasDerivAt_hardyThetaSmooth t
  have h2 : HasDerivAt (fun t => t * Real.log (↑n + 1)) (Real.log (↑n + 1)) t := by
    have := (hasDerivAt_id t).mul_const (Real.log (↑n + 1))
    simp only [id, one_mul] at this
    exact this
  exact h1.sub h2

/-- Pointwise derivative of the smooth phase. -/
theorem deriv_hardyPhaseSmooth (n : ℕ) (t : ℝ) :
    deriv (hardyPhaseSmooth n) t = thetaDeriv t - Real.log (↑n + 1) :=
  (hasDerivAt_hardyPhaseSmooth n t).deriv

/-- The exponential of the smooth phase equals the original Hardy exponential phase.
This connects the smooth phase infrastructure to the existing Hardy chain. -/
theorem exp_hardyPhaseSmooth_eq (n : ℕ) (t : ℝ) :
    Complex.exp (I * ↑(hardyPhaseSmooth n t))
      = Complex.exp (I * ↑(HardyEstimatesPartial.hardyTheta t - t * Real.log (↑n + 1))) := by
  unfold hardyPhaseSmooth
  -- Factor: exp(I*(a-b)) = exp(I*a - I*b) = exp(I*a) * exp(-I*b)
  -- Both sides share the same -I*b factor, so it suffices: exp(I*smooth) = exp(I*theta)
  simp only [Complex.ofReal_sub, Complex.ofReal_mul]
  have key := hardyThetaSmooth_exp_eq t
  -- Rewrite as products
  rw [show I * (↑(hardyThetaSmooth t) - ↑t * ↑(Real.log (↑n + 1))) =
    I * ↑(hardyThetaSmooth t) + (-(I * (↑t * ↑(Real.log (↑n + 1))))) by ring]
  rw [show I * (↑(HardyEstimatesPartial.hardyTheta t) - ↑t * ↑(Real.log (↑n + 1))) =
    I * ↑(HardyEstimatesPartial.hardyTheta t) + (-(I * (↑t * ↑(Real.log (↑n + 1))))) by ring]
  rw [Complex.exp_add, Complex.exp_add, key]

/-- The smooth phase derivative is continuous (for VdC correction integrability). -/
theorem continuous_deriv_hardyPhaseSmooth (n : ℕ) :
    Continuous (deriv (hardyPhaseSmooth n)) := by
  rw [show deriv (hardyPhaseSmooth n) = fun u => thetaDeriv u - Real.log (↑n + 1) from
    funext (deriv_hardyPhaseSmooth n)]
  exact continuous_thetaDeriv.sub continuous_const

end HardyThetaSmooth
