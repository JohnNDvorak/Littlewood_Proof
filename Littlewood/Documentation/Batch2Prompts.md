# Batch 2 Aristotle Prompts (Independent of Hardy)

*Created 2026-01-31*

## Prompt 4: Riemann-von Mangoldt Uniform

```
Prove the Riemann-von Mangoldt formula with a uniform error constant.

theorem riemann_von_mangoldt_uniform :
    ∃ C : ℝ, C > 0 ∧ ∃ T₀ ≥ 2, ∀ T ≥ T₀,
      |N(T) - (T/(2π)) * log(T/(2πe))| ≤ C * log T

where N(T) = #{ρ : ζ(ρ)=0, 0 < Re(ρ) < 1, 0 < Im(ρ) ≤ T}

CRITICAL: C must NOT depend on T.
```

## Prompt 5: Zero-Free Region Complete

```
Prove the classical zero-free region using the 3-4-1 inequality.

theorem zero_free_region :
    ∃ c : ℝ, c > 0 ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      0 < ρ.re → ρ.re < 1 →
        ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2)

We already have ThreeFourOneV2 with the 3-4-1 inequality.
This prompt completes the region proof.
```

## Prompt 6: Perron Formula Basic

```
Prove Perron's formula for the partial sums of a Dirichlet series.

theorem perron_formula (x : ℝ) (hx : x > 0) (c : ℝ) (hc : c > 1) :
    ∑_{n ≤ x} aₙ = (1/2πi) ∫_{c-i∞}^{c+i∞} F(s) x^s / s ds + error

where F(s) = Σ aₙ n^{-s} is the Dirichlet series.
```
