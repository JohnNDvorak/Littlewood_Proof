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

namespace Aristotle.ZeroCountingRectangle

/-
Opening namespaces Complex, MeasureTheory, Set, Filter, and Interval.
-/
open Complex MeasureTheory Set Filter Interval

/-
Defining the rectangle integral, the change in argument of zeta, the number of zeros N(T), and the rectangle boundary.
-/
def RectIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) +
  (I * ∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
  (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) -
  (I * ∫ y in z.im..w.im, f (z.re + y * I))

def deltaArgZeta (ε T : ℝ) : ℝ :=
  (RectIntegral (fun s => deriv riemannZeta s / riemannZeta s) (ε) (1 + ε + I * T)).im

def N (T : ℝ) : ℕ :=
  Set.ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im < T}

def RectBorder (ε T : ℝ) : Set ℂ :=
  {s | (s.im = 0 ∧ ε ≤ s.re ∧ s.re ≤ 1 + ε) ∨
       (s.re = 1 + ε ∧ 0 ≤ s.im ∧ s.im ≤ T) ∨
       (s.im = T ∧ ε ≤ s.re ∧ s.re ≤ 1 + ε) ∨
       (s.re = ε ∧ 0 ≤ s.im ∧ s.im ≤ T)}

/-
The limit of (s-1) * zeta(s) as s approaches 1 is 1.
-/
lemma limit_mul_zeta_sub_one :
  Filter.Tendsto (fun s => (s - 1) * riemannZeta s) (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
  have h1 : Filter.Tendsto (fun s : ℂ => s - 1) (nhdsWithin 1 {1}ᶜ) (nhds 0) := by
    rw [show (0 : ℂ) = 1 - 1 from by ring]
    exact (continuous_id.sub continuous_const).continuousWithinAt
  have h3 : Filter.Tendsto (fun s : ℂ => (s - 1) * (riemannZeta s - 1 / (s - 1)))
      (nhdsWithin 1 {1}ᶜ) (nhds 0) := by
    simpa [zero_mul] using h1.mul tendsto_riemannZeta_sub_one_div
  have h4 : Filter.Tendsto (fun s : ℂ => (s - 1) * (riemannZeta s - 1 / (s - 1)) + 1)
      (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
    simpa using h3.add tendsto_const_nhds
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 1)
  have h_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [mul_sub, one_div, mul_inv_cancel₀ h_ne, sub_add_cancel]

/-
Defining the logarithmic derivative of the Riemann zeta function.
-/
noncomputable def ZetaLogDeriv (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

/-
If a function f has a simple pole at c with residue A, then (z-c)^2 * f'(z) tends to -A as z approaches c.
-/
lemma tendsto_mul_sq_deriv_of_simple_pole {f : ℂ → ℂ} {c A : ℂ}
    (h_diff : ∀ᶠ z in nhdsWithin c {c}ᶜ, DifferentiableAt ℂ f z)
    (h_lim : Filter.Tendsto (fun z => (z - c) * f z) (nhdsWithin c {c}ᶜ) (nhds A)) :
    Filter.Tendsto (fun z => (z - c) ^ 2 * deriv f z) (nhdsWithin c {c}ᶜ) (nhds (-A)) := by
  by_contra h_contra;
  -- Let $g(z) = (z-c)f(z)$ for $z \ne c$, and $g(c) = A$.
  set g : ℂ → ℂ := fun z => if z = c then A else (z - c) * f z;
  -- Since $g$ is differentiable at $c$, we can apply the definition of the derivative to get that $\lim_{z \to c} \frac{g(z) - g(c)}{z - c} = g'(c)$.
  have hg_diff : DifferentiableAt ℂ g c := by
    -- Since $g$ is continuous at $c$, we can apply the definition of the derivative to get that $\lim_{z \to c} \frac{g(z) - g(c)}{z - c} = g'(c)$.
    have hg_cont : ContinuousAt g c := by
      rw [ Metric.tendsto_nhdsWithin_nhds ] at h_lim;
      exact Metric.tendsto_nhds_nhds.mpr fun ε hε => by rcases h_lim ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, by intro z hz; by_cases h : z = c <;> aesop ⟩ ;
    -- Since $g$ is continuous at $c$, we can apply the definition of the derivative to get that $\lim_{z \to c} \frac{g(z) - g(c)}{z - c} = g'(c)$ using the fact that $g$ is differentiable on a punctured neighborhood of $c$.
    have hg_diff_punctured : ∀ᶠ z in nhdsWithin c {c}ᶜ, DifferentiableAt ℂ g z := by
      filter_upwards [ h_diff, self_mem_nhdsWithin ] with z hz hz' using DifferentiableAt.congr_of_eventuallyEq ( DifferentiableAt.mul ( differentiableAt_id.sub_const c ) hz ) ( by filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_singleton.preimage continuous_id' ) hz' ] with x hx using by aesop );
    have hg_diff_punctured : AnalyticAt ℂ g c :=
      analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hg_diff_punctured hg_cont;
    exact hg_diff_punctured.differentiableAt;
  -- Since $g$ is differentiable at $c$, we can apply the definition of the derivative to get that $\lim_{z \to c} \frac{g(z) - g(c)}{z - c} = g'(c)$. Hence, $g'(c) = \lim_{z \to c} \frac{(z - c)f(z) - A}{z - c} = \lim_{z \to c} f(z) - \frac{A}{z - c}$.
  have hg_deriv : Filter.Tendsto (fun z => deriv g z * (z - c) - g z) (nhdsWithin c {c}ᶜ) (nhds (-A)) := by
    have hg_deriv : Filter.Tendsto (fun z => (g z - g c) / (z - c) * (z - c) - g z) (nhdsWithin c {c}ᶜ) (nhds (-A)) := by
      field_simp;
      rw [ Filter.tendsto_congr' ( by filter_upwards [ self_mem_nhdsWithin ] with z hz using by rw [ mul_div_cancel_right₀ _ ( sub_ne_zero_of_ne hz ) ] ) ];
      aesop;
    have hg_deriv : Filter.Tendsto (fun z => (g z - g c) / (z - c)) (nhdsWithin c {c}ᶜ) (nhds (deriv g c)) := by
      have := hg_diff.hasDerivAt;
      rw [ hasDerivAt_iff_tendsto_slope ] at this;
      simpa [ div_eq_inv_mul ] using this;
    have hg_deriv : Filter.Tendsto (fun z => deriv g z) (nhdsWithin c {c}ᶜ) (nhds (deriv g c)) := by
      have hg_deriv : AnalyticAt ℂ g c := by
        apply_rules [ DifferentiableOn.analyticAt, hg_diff ];
        rotate_right;
        exact { z : ℂ | z ≠ c → DifferentiableAt ℂ f z };
        · intro z hz; by_cases h : z = c <;> simp_all +decide [ DifferentiableAt.differentiableWithinAt ] ;
          exact DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.congr_of_eventuallyEq ( DifferentiableAt.mul ( differentiableAt_id.sub_const c ) hz ) ( Filter.eventuallyEq_of_mem ( isOpen_ne.mem_nhds h ) fun x hx => if_neg hx ) );
        · rw [ eventually_nhdsWithin_iff ] at h_diff;
          filter_upwards [ h_diff ] with z hz using by aesop;
      exact hg_deriv.deriv.continuousAt.continuousWithinAt.tendsto;
    have hg_deriv : Filter.Tendsto (fun z => (deriv g z - (g z - g c) / (z - c)) * (z - c)) (nhdsWithin c {c}ᶜ) (nhds 0) := by
      convert Filter.Tendsto.mul ( hg_deriv.sub ‹Filter.Tendsto ( fun z => ( g z - g c ) / ( z - c ) ) ( nhdsWithin c { c } ᶜ ) ( nhds ( deriv g c ) ) › ) ( continuousWithinAt_id.sub_const c ) using 2 ; norm_num;
    convert ‹Filter.Tendsto ( fun z => ( g z - g c ) / ( z - c ) * ( z - c ) - g z ) ( nhdsWithin c { c } ᶜ ) ( nhds ( -A ) ) ›.add hg_deriv using 2 <;> ring;
  -- Since $g(z) = (z - c)f(z)$ for $z \ne c$, we have $deriv g z = deriv ((z - c)f(z)) = f(z) + (z - c)deriv f(z)$.
  have hg_deriv_eq : ∀ᶠ z in nhdsWithin c {c}ᶜ, deriv g z = f z + (z - c) * deriv f z := by
    filter_upwards [ h_diff, self_mem_nhdsWithin ] with z hz hz' using by rw [ show deriv g z = deriv ( fun z => ( z - c ) * f z ) z by exact Filter.EventuallyEq.deriv_eq <| by filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_singleton.preimage continuous_id' ) hz' ] with x hx using if_neg hx ] ; norm_num [ hz, sub_ne_zero.mpr hz' ] ;
  refine' h_contra _;
  refine' hg_deriv.congr' _;
  filter_upwards [ hg_deriv_eq, self_mem_nhdsWithin ] with z hz hz' using by rw [ hz ] ; rw [ show g z = ( z - c ) * f z by aesop ] ; ring;

/-
The residue of the logarithmic derivative of the Riemann zeta function at s=1 is -1.
-/
lemma residue_zeta_log_deriv_at_one :
  Filter.Tendsto (fun s => (s - 1) * ZetaLogDeriv s) (nhdsWithin 1 {1}ᶜ) (nhds (-1)) := by
  have h_lim : Filter.Tendsto (fun s => ((s - 1) ^ 2 * deriv riemannZeta s)) (nhdsWithin 1 {1}ᶜ) (nhds (-1)) := by
    convert tendsto_mul_sq_deriv_of_simple_pole _ _ using 2;
    · exact Filter.eventually_of_mem self_mem_nhdsWithin fun z hz => differentiableAt_riemannZeta hz;
    · convert limit_mul_zeta_sub_one using 1;
  have h_div : Filter.Tendsto (fun s => ((s - 1) ^ 2 * deriv riemannZeta s) / ((s - 1) * riemannZeta s)) (nhdsWithin 1 {1}ᶜ) (nhds (-1)) := by
    convert h_lim.div ( limit_mul_zeta_sub_one ) _ using 1 <;> norm_num;
  convert h_div using 2 ; ring! ; unfold ZetaLogDeriv ; ring!;
  grind

/-
Defining the rectangle boundary and change in argument with a lower imaginary bound y0 to avoid the pole at s=1.
-/
def RectBorder' (ε T y0 : ℝ) : Set ℂ :=
  (Set.Icc ε (1 + ε) ×ℂ {y0}) ∪
  ({1 + ε} ×ℂ Set.Icc y0 T) ∪
  (Set.Icc ε (1 + ε) ×ℂ {T}) ∪
  ({ε} ×ℂ Set.Icc y0 T)

def deltaArgZeta' (ε T y0 : ℝ) : ℝ :=
  (RectIntegral (fun s => deriv riemannZeta s / riemannZeta s) (ε + y0 * I) (1 + ε + T * I)).im

/-
The residue of the logarithmic derivative of the Riemann zeta function at s=1 is -1.
-/
lemma residue_zeta_log_deriv_at_one_aux :
  Filter.Tendsto (fun s => (s - 1) * ZetaLogDeriv s) (nhdsWithin 1 {1}ᶜ) (nhds (-1)) := by
    convert residue_zeta_log_deriv_at_one using 1

end Aristotle.ZeroCountingRectangle

end
