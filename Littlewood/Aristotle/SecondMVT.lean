/-
Second Mean Value Theorem for integrals.

KEY RESULTS:
  second_mean_value_theorem: If f is monotone on [a,b] and g is integrable,
    then ∃ c ∈ [a,b] with ∫_a^b f·g = f(a)·∫_a^c g + f(b)·∫_c^b g
  second_mvt_antitone: Antitone version.

SORRY COUNT: 1 (integral_fg_mem_image_targetFun)
  This sorry encapsulates the Stieltjes integration by parts identity:
    ∫_a^b f·g = f(b)·F(b) - ∫_a^b F·df
  combined with the first MVT for Stieltjes integrals. Closing it requires
  either Lebesgue-Stieltjes integration theory or a careful discretization
  + approximation argument for monotone functions.

APPLICATIONS: Van der Corput tail bounds, oscillatory integral estimates.

Proof architecture:
  Define h(x) = (f(a)-f(b))·F(x) + f(b)·F(b) where F(x) = ∫_a^x g.
  Then h(c) = f(a)·∫_a^c g + f(b)·∫_c^b g for c ∈ [a,b]  (PROVED: targetFun_eq_split).
  h is continuous on [a,b]  (PROVED: continuousOn_targetFun).
  The key analytical content is: ∫_a^b f·g lies in the image of h on [a,b]  (SORRY).
  Given this, the IVT finishes the proof.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace SecondMVT

open MeasureTheory Set intervalIntegral Filter

/-! ### Primitive function and its properties -/

/-- The primitive (antiderivative) of g starting at a: F(x) = ∫_a^x g(t) dt. -/
def primitive (g : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℝ := ∫ t in a..x, g t

@[simp]
lemma primitive_self (g : ℝ → ℝ) (a : ℝ) : primitive g a a = 0 := by
  simp [primitive]

/-- The primitive of an interval-integrable function is continuous on [a,b]. -/
lemma continuousOn_primitive_Icc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (primitive g a) (Icc a b) := by
  have hint : IntegrableOn g (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hg
  have hcont := intervalIntegral.continuousOn_primitive hint
  apply ContinuousOn.congr hcont
  intro x hx
  simp only [primitive]
  rw [integral_of_le hx.1]

/-- Splitting the integral at an intermediate point. -/
lemma integral_split {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hc : c ∈ Icc a b) :
    (∫ t in a..c, g t) + (∫ t in c..b, g t) = ∫ t in a..b, g t := by
  have hc_uIcc : c ∈ uIcc a b := by rwa [uIcc_of_le hab]
  exact integral_add_adjacent_intervals
    (hg.mono_set (uIcc_subset_uIcc_left hc_uIcc))
    (hg.mono_set (uIcc_subset_uIcc_right hc_uIcc))

/-! ### The target function whose value we match -/

/-- The target function: h(x) = (f(a) - f(b))·F(x) + f(b)·F(b).
    This encodes f(a)·∫_a^x g + f(b)·∫_x^b g as an affine function of the primitive F. -/
def targetFun (f g : ℝ → ℝ) (a b : ℝ) (x : ℝ) : ℝ :=
  (f a - f b) * (∫ t in a..x, g t) + f b * (∫ t in a..b, g t)

/-- The target function evaluated at c ∈ [a,b] equals the split integral formula. -/
lemma targetFun_eq_split {f g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hc : c ∈ Icc a b) :
    targetFun f g a b c = f a * (∫ t in a..c, g t) + f b * (∫ t in c..b, g t) := by
  simp only [targetFun]
  have h_eq : ∫ t in a..b, g t = (∫ t in a..c, g t) + (∫ t in c..b, g t) :=
    (integral_split hab hg hc).symm
  rw [h_eq]; ring

lemma targetFun_at_a (f g : ℝ → ℝ) (a b : ℝ) :
    targetFun f g a b a = f b * (∫ t in a..b, g t) := by
  simp [targetFun]

lemma targetFun_at_b (f g : ℝ → ℝ) (a b : ℝ) :
    targetFun f g a b b = f a * (∫ t in a..b, g t) := by
  unfold targetFun; ring

/-- The target function is continuous on [a,b]. -/
lemma continuousOn_targetFun {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (targetFun f g a b) (Icc a b) :=
  ContinuousOn.add
    (continuousOn_const.mul (continuousOn_primitive_Icc hab hg))
    continuousOn_const

/-! ### Comparison bound: the core analytical step

The key result: ∫_a^b f·g lies in the range of targetFun on [a,b].

Proof outline (Stieltjes integration by parts):
  Let F(x) = ∫_a^x g and let μ_f be the Stieltjes measure of f.
  Then: ∫_a^b f·g = f(b)·F(b) - f(a)·F(a) - ∫_a^b F dμ_f
                   = f(b)·F(b) - ∫_{[a,b]} F dμ_f    (since F(a) = 0).

  Since f is monotone increasing, μ_f is a positive measure, so:
    m · μ_f([a,b]) ≤ ∫ F dμ_f ≤ M · μ_f([a,b])
  where m = min F on [a,b] and M = max F on [a,b].

  Now targetFun(x) = (f(a)-f(b))·F(x) + f(b)·F(b), which is an affine function of F(x).
  Its range over [a,b] is {(f(a)-f(b))·t + f(b)·F(b) : t ∈ image(F, [a,b])}.
  Since F is continuous, image(F, [a,b]) = [m, M].

  We need ∫fg ∈ this range, i.e., ∃ ξ ∈ [m,M] with:
    (f(a)-f(b))·ξ + f(b)·F(b) = f(b)·F(b) - ∫ F dμ_f

  i.e., ξ = ∫ F dμ_f / (f(b)-f(a))  (the weighted average of F w.r.t. μ_f).

  This weighted average lies in [m, M] by the first MVT for Stieltjes integrals.

  NOTE: when f(a) = f(b), f is constant and the result is trivial. -/

/-- **Stieltjes comparison bound**: ∫fg lies in the image of targetFun on [a,b].

This is the core analytical content of the second MVT. It requires either:
  (a) Lebesgue-Stieltjes integration by parts for monotone functions, or
  (b) A careful approximation by step functions + Abel summation.
Neither is currently available in Mathlib in the required form. -/
lemma integral_fg_mem_image_targetFun {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf_mono : MonotoneOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume a b) :
    ∫ t in a..b, f t * g t ∈ targetFun f g a b '' (Icc a b) := by
  -- Need: ∃ c ∈ [a,b] with targetFun f g a b c = ∫fg
  -- Equivalently: ∃ c ∈ [a,b] with (f(a)-f(b))·F(c) + f(b)·F(b) = ∫fg
  -- This requires Stieltjes integration by parts for monotone functions
  -- combined with the first MVT for integrals with nonneg weight.
  -- Currently blocked on: Lebesgue-Stieltjes integration in Mathlib.
  sorry

/-! ### Main theorem -/

/-- **Second Mean Value Theorem for Integrals** (du Bois-Reymond).

If f is monotone on [a,b] and g is integrable on [a,b], then there exists c ∈ [a,b] such that
  ∫_a^b f(x)·g(x) dx = f(a)·∫_a^c g(x) dx + f(b)·∫_c^b g(x) dx.

This is sometimes called the generalized Bonnet theorem.

The proof reduces to:
1. The Stieltjes comparison bound: ∫fg ∈ targetFun '' [a,b]
2. Unfolding targetFun at the chosen c to get the split integral formula. -/
theorem second_mean_value_theorem {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf_mono : MonotoneOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume a b) :
    ∃ c ∈ Icc a b, ∫ t in a..b, f t * g t =
      f a * (∫ t in a..c, g t) + f b * (∫ t in c..b, g t) := by
  -- Degenerate case: a = b
  by_cases hab' : a = b
  · exact ⟨a, left_mem_Icc.mpr hab, by simp [hab']⟩
  -- The integral lies in the image of targetFun on [a,b]
  obtain ⟨c, hc, hc_eq⟩ := integral_fg_mem_image_targetFun hab hf_mono hg hfg
  exact ⟨c, hc, by linarith [targetFun_eq_split hab hg hc (f := f)]⟩

/-- **Second MVT for antitone functions**. If f is antitone (monotone decreasing) on [a,b]
    and g is integrable, then the same conclusion holds. -/
theorem second_mvt_antitone {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf_anti : AntitoneOn f (Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume a b) :
    ∃ c ∈ Icc a b, ∫ t in a..b, f t * g t =
      f a * (∫ t in a..c, g t) + f b * (∫ t in c..b, g t) := by
  -- Apply the monotone version to -f, which is monotone
  have hf_neg_mono : MonotoneOn (fun x => -f x) (Icc a b) := by
    intro x hx y hy hxy
    exact neg_le_neg (hf_anti hx hy hxy)
  have hfg_neg : IntervalIntegrable (fun x => (-f x) * g x) volume a b := by
    have : (fun x => (-f x) * g x) = fun x => -(f x * g x) := by ext x; ring
    rw [this]
    exact hfg.neg
  obtain ⟨c, hc, hc_eq⟩ := second_mean_value_theorem hab hf_neg_mono hg hfg_neg
  refine ⟨c, hc, ?_⟩
  -- hc_eq : ∫ -f·g = -f(a)·∫_a^c g + (-f(b))·∫_c^b g
  -- We need: ∫ f·g = f(a)·∫_a^c g + f(b)·∫_c^b g
  have h1 : ∫ t in a..b, (-f t) * g t = -(∫ t in a..b, f t * g t) := by
    have : (fun t => (-f t) * g t) = fun t => -(f t * g t) := by ext t; ring
    rw [this, intervalIntegral.integral_neg]
  linarith

end SecondMVT
