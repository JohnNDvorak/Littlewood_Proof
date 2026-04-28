import Mathlib

/-!
# Analytic Extension of Quotients at Common Zeros

If `f` and `g` are analytic at `z₀` and both vanish to the same order `m ≥ 1`, then the
quotient `f / g` extends to an analytic function at `z₀` whose value equals the ratio of
the leading coefficients.

## Proof strategy

We use `AnalyticAt.analyticOrderAt_eq_natCast` to factor
  `f z = (z - z₀)^m * f₁ z`  and  `g z = (z - z₀)^m * g₁ z`
with `f₁` and `g₁` analytic at `z₀` and nonvanishing there. The analytic extension is then
`h = f₁ / g₁`, which is analytic at `z₀` (via `AnalyticAt.div`, since `g₁(z₀) ≠ 0`) and
satisfies `h z = f z / g z` for `z ≠ z₀` (by cancelling the common `(z - z₀)^m` factor).
-/

open Filter Set
open scoped Topology

variable {f g : ℂ → ℂ} {z₀ : ℂ} {m : ℕ}

/-- If `f` and `g` are analytic at `z₀` and both vanish to the same order `m ≥ 1` at `z₀`,
then `f / g` extends to an analytic function at `z₀`. The extension is constructed by
factoring `f z = (z - z₀)^m * f₁ z` and `g z = (z - z₀)^m * g₁ z` (with `f₁(z₀) ≠ 0`
and `g₁(z₀) ≠ 0`), and defining the extension as `f₁ / g₁`, which has the value
`f₁(z₀) / g₁(z₀)` (the ratio of the leading coefficients). -/
theorem analyticAt_quotient_of_common_order
    (hm : 0 < m)
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀)
    (hof : analyticOrderAt f z₀ = m) (hog : analyticOrderAt g z₀ = m) :
    ∃ (h f₁ g₁ : ℂ → ℂ),
      AnalyticAt ℂ f₁ z₀ ∧ f₁ z₀ ≠ 0 ∧ (∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ m * f₁ z) ∧
      AnalyticAt ℂ g₁ z₀ ∧ g₁ z₀ ≠ 0 ∧ (∀ᶠ z in 𝓝 z₀, g z = (z - z₀) ^ m * g₁ z) ∧
      AnalyticAt ℂ h z₀ ∧
      h z₀ = f₁ z₀ / g₁ z₀ ∧
      (∀ᶠ z in 𝓝[≠] z₀, h z = f z / g z) := by
  -- Factor f and g using the vanishing order characterization
  obtain ⟨f₁, hf₁_an, hf₁_ne, hf₁_eq⟩ := hf.analyticOrderAt_eq_natCast.mp hof
  obtain ⟨g₁, hg₁_an, hg₁_ne, hg₁_eq⟩ := hg.analyticOrderAt_eq_natCast.mp hog
  -- Convert from smul (scalar multiplication) to mul (since ℂ • ℂ = ℂ * ℂ)
  have hf₁_eq' : ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ m * f₁ z := by
    filter_upwards [hf₁_eq] with z hz; rwa [smul_eq_mul] at hz
  have hg₁_eq' : ∀ᶠ z in 𝓝 z₀, g z = (z - z₀) ^ m * g₁ z := by
    filter_upwards [hg₁_eq] with z hz; rwa [smul_eq_mul] at hz
  -- The analytic extension is h = f₁ / g₁, which is analytic since g₁(z₀) ≠ 0
  refine ⟨fun z => f₁ z / g₁ z, f₁, g₁,
    hf₁_an, hf₁_ne, hf₁_eq', hg₁_an, hg₁_ne, hg₁_eq',
    hf₁_an.div hg₁_an hg₁_ne, rfl, ?_⟩
  -- Show f₁/g₁ = f/g on a punctured neighborhood by cancelling (z - z₀)^m
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hf₁_eq', hg₁_eq'] with z hfz hgz hz
  rw [hfz, hgz]
  have hzsub : z - z₀ ≠ 0 := by
    intro heq; apply hz; rw [Set.mem_singleton_iff]; exact sub_eq_zero.mp heq
  have hpow : (z - z₀) ^ m ≠ 0 := pow_ne_zero m hzsub
  field_simp [hpow]

/-- Simplified version: if `f` and `g` are analytic at `z₀` and both vanish to the same
order `m ≥ 1`, then there is an analytic function agreeing with `f / g` in a punctured
neighborhood of `z₀`. -/
theorem analyticAt_extension_quotient_of_common_order
    (hm : 0 < m)
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀)
    (hof : analyticOrderAt f z₀ = m) (hog : analyticOrderAt g z₀ = m) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, h z = f z / g z := by
  obtain ⟨h, _, _, _, _, _, _, _, _, hh_an, _, hh_eq⟩ :=
    analyticAt_quotient_of_common_order hm hf hg hof hog
  exact ⟨h, hh_an, hh_eq⟩
