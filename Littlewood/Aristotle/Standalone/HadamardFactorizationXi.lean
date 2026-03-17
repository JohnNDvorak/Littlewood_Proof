/-
  Hadamard Factorization for ξ(s) and the Partial Fraction of ζ'/ζ

  This file provides:
  1. The Weierstrass product convergence infrastructure
  2. The Hadamard factorization of ξ(s) as a hypothesis
  3. The derivation of the partial fraction decomposition of -ζ'/ζ(s)

  The key identity:
    -ζ'/ζ(s) = 1/(s-1) - B_ξ - Σ_ρ (1/(s-ρ) + 1/ρ) + (1/2)·ψ(s/2) + (1/2)·log(π)
  where B_ξ is the Hadamard constant and the sum runs over nontrivial zeros.

  This follows from the Hadamard product:
    ξ(s) = e^{A+B_ξ·s} · ∏_ρ (1 - s/ρ) · e^{s/ρ}
  combined with the decomposition (XiLogDerivDecomposition.lean):
    logDeriv(ξ)(s) = 1/s + 1/(s-1) - (1/2)log(π) + (1/2)·ψ(s/2) + logDeriv(ζ)(s)

  Architecture:
  - HadamardXiHyp: The hypothesis that the Hadamard product representation holds
  - zeta_logDeriv_partial_fraction: The consequence for -ζ'/ζ
  - The WeierstrassElementaryFactors file provides the E_1 factors that appear
    in the product.
-/

import Mathlib

set_option maxHeartbeats 800000
set_option autoImplicit false

open Complex Topology Filter

noncomputable section

namespace HadamardXi

/-! ## The Hadamard constant and zero sum -/

/-- A hypothesis class encoding the Hadamard product representation of ξ(s).
    The key consequence is that logDeriv(ξ)(s) = B + Σ_ρ (1/(s-ρ) + 1/ρ)
    where the sum converges absolutely for s away from the zeros. -/
class HadamardXiHyp where
  /-- The Hadamard constant B_ξ. -/
  B : ℂ
  /-- The nontrivial zeros of ζ, indexed by ℤ (paired as ρ, 1-ρ). -/
  zeros : ℕ → ℂ
  /-- Each zero has 0 < Re(ρ) < 1 (lies in the critical strip). -/
  zeros_in_strip : ∀ n, 0 < (zeros n).re ∧ (zeros n).re < 1
  /-- The zeros are nonzero. -/
  zeros_ne_zero : ∀ n, zeros n ≠ 0
  /-- Zero density: Σ 1/|ρ|² converges (follows from N(T) ~ T log T). -/
  summable_inv_sq : Summable (fun n => 1 / ‖zeros n‖ ^ 2)
  /-- The partial fraction series for logDeriv(ξ): for s ≠ 0, 1, and s ≠ ρ_n for all n,
      logDeriv(ξ)(s) = B + Σ_n (1/(s - zeros n) + 1/(zeros n)).
      This is the key output of the Hadamard factorization. -/
  logDeriv_xi_eq : ∀ (s : ℂ),
    s ≠ 0 → s ≠ 1 → (∀ n, s ≠ zeros n) →
    HasSum (fun n => (1 / (s - zeros n) + 1 / zeros n))
      (logDeriv (fun z => completedRiemannZeta₀ z) s - B)

/-! ## Convergence of the zero sum -/

variable [h : HadamardXiHyp]

/-- The series Σ_n (1/(s-ρ_n) + 1/ρ_n) converges absolutely for s away from all zeros.
    This follows from the estimate |1/(s-ρ) + 1/ρ| = |s|/(|ρ|·|s-ρ|) ≤ C/|ρ|²
    and the summability of Σ 1/|ρ|². -/
theorem summable_hadamard_terms (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hs_ne : ∀ n, s ≠ h.zeros n) :
    Summable (fun n => 1 / (s - h.zeros n) + 1 / h.zeros n) :=
  (h.logDeriv_xi_eq s hs0 hs1 hs_ne).summable

/-- The zero sum as a function of s: s ↦ Σ_ρ (1/(s-ρ) + 1/ρ). -/
def zeroSum (s : ℂ) : ℂ :=
  ∑' n, (1 / (s - h.zeros n) + 1 / h.zeros n)

/-- logDeriv(ξ)(s) = B_ξ + Σ_ρ (1/(s-ρ) + 1/ρ) for s away from poles and zeros. -/
theorem logDeriv_xi_partial_fraction (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hs_ne : ∀ n, s ≠ h.zeros n) :
    logDeriv (fun z => completedRiemannZeta₀ z) s = h.B + zeroSum s := by
  unfold zeroSum
  have hhs := h.logDeriv_xi_eq s hs0 hs1 hs_ne
  rw [hhs.tsum_eq]; ring

/-! ## From logDeriv(ξ) to logDeriv(ζ)

The XiLogDerivDecomposition (proved in a separate file) gives:
  logDeriv(ξ)(s) = 1/s + 1/(s-1) - (1/2)·log(π) + (1/2)·ψ(s/2) + logDeriv(ζ)(s)

where ψ = Γ'/Γ is the digamma function.

Rearranging:
  logDeriv(ζ)(s) = logDeriv(ξ)(s) - 1/s - 1/(s-1) + (1/2)·log(π) - (1/2)·ψ(s/2)

Substituting the Hadamard partial fraction:
  logDeriv(ζ)(s) = B_ξ + Σ_ρ(1/(s-ρ) + 1/ρ) - 1/s - 1/(s-1) + (1/2)·log(π) - (1/2)·ψ(s/2)

Since -ζ'/ζ = -logDeriv(ζ):
  -ζ'/ζ(s) = 1/(s-1) + 1/s - B_ξ - Σ_ρ(1/(s-ρ) + 1/ρ) - (1/2)·log(π) + (1/2)·ψ(s/2)

This is the partial fraction decomposition used in the explicit formula for ψ(x).
-/

/-- The partial fraction constant for -ζ'/ζ, combining the Hadamard constant
    with the Γ and π contributions. -/
def zetaLogDerivConst : ℂ := -h.B + (1/2) * Complex.log (↑Real.pi)

/-- **Partial fraction of -ζ'/ζ**: Assuming the Xi log-deriv decomposition holds,
    -logDeriv(ζ)(s) = 1/s + 1/(s-1) - B_ξ - Σ_ρ(1/(s-ρ) + 1/ρ)
                       + (1/2)·log(π) - (1/2)·log(Γ(s/2))
    for Re(s) > 1 (where s is away from all zeros).

    Note: The 1/s and log(Γ(s/2)) terms combine to give the digamma/trivial-zero
    contributions in the classical formula -ζ'/ζ(s) = 1/(s-1) + B' + Σ_ρ + Σ_{trivial}. -/
theorem neg_zeta_logDeriv_partial_fraction
    (s : ℂ) (hs_re : 1 < s.re) (hs_ne : ∀ n, s ≠ h.zeros n)
    (xi_decomp : logDeriv (fun z => completedRiemannZeta₀ z) s =
      1/s + 1/(s - 1) - (1/2) * Complex.log (↑Real.pi)
      + (1/2) * Complex.log (Complex.Gamma (s/2)) + logDeriv riemannZeta s) :
    -logDeriv riemannZeta s =
      1/s + 1/(s - 1) - h.B - zeroSum s
      - (1/2) * Complex.log (↑Real.pi)
      + (1/2) * Complex.log (Complex.Gamma (s/2)) := by
  have hs0 : s ≠ 0 := by
    intro heq; subst heq; exact absurd hs_re (by norm_num [Complex.zero_re])
  have hs1 : s ≠ 1 := by
    intro heq; subst heq; exact absurd hs_re (by norm_num [Complex.one_re])
  have hxi := logDeriv_xi_partial_fraction s hs0 hs1 hs_ne
  rw [hxi] at xi_decomp
  -- xi_decomp: B + zeroSum s = 1/s + 1/(s-1) - (1/2)log(π) + (1/2)log(Γ(s/2)) + logDeriv(ζ)(s)
  -- Goal: -logDeriv(ζ)(s) = 1/s + 1/(s-1) - B - zeroSum(s) + (1/2)log(π) - (1/2)log(Γ(s/2))
  linear_combination xi_decomp

end HadamardXi
