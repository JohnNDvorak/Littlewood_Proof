/-
Bridge: Wire HardyCriticalLineZerosHyp → PsiOscillationFromCriticalZerosHyp
via Littlewood's original argument (Landau oscillation theorem).

This provides bridge instances with no local `sorry`, using
`Aristotle/LandauLittlewood.lean` for the atomic analytic steps.

WHY TruncatedExplicitFormulaPsiHyp IS FALSE:
  TruncatedExplicitFormulaPsiHyp.psi_approx says:
    ∀ (S : Finset ℂ) (finite set of critical-line zeros), ∀ ε > 0,
    eventually |ψ(x) - x + Re(∑_{ρ∈S} x^ρ/ρ)| ≤ ε·√x.
  With S = ∅, this gives |ψ(x) - x| ≤ ε·√x eventually.
  But ψ(x) - x = Ω±(√x) by Littlewood's theorem, so this is FALSE.
  The issue: a FIXED finite set S cannot capture the full Ω(√x) oscillation.
  (PiLiDirectOscillation exploits this falsehood: derives False → PiLiOscillationSqrtHyp.)

CORRECT MATHEMATICAL ARGUMENT (Littlewood 1914, via Landau):
  1. -ζ'/ζ(s) - 1/(s-1) = s · ∫₁^∞ (ψ(x)-x) · x^{-s-1} dx for Re(s) > 1.
  2. If ψ(x) - x ≤ c · √x for ALL sufficiently large x, then the integral
     converges absolutely for Re(s) > 1/2.
  3. This gives analytic continuation of -ζ'/ζ(s) to Re(s) > 1/2.
  4. But ζ(s) has zeros on Re(s) = 1/2 (by HardyCriticalLineZerosHyp),
     so -ζ'/ζ has poles there — contradicting analytic continuation.
  5. Therefore ψ(x) - x takes values > c·√x infinitely often: Ω₊(√x).
  6. Similarly for the lower bound: ψ(x) - x < -c·√x infinitely often: Ω₋(√x).

  Steps 5-6 can be done via Landau's oscillation theorem: if ∫ φ(x)/x^s dx
  has a singularity at Re(s) = α, then φ changes sign infinitely often
  (or is identically zero).

REFERENCES:
  - Littlewood, "Sur la distribution des nombres premiers" (1914)
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1
  - Ingham, "Distribution of Prime Numbers", Theorem 20
  - Landau, "Über einen Satz von Tschebyschef" (1905)

DEPENDENCIES:
  - HardyCriticalLineZerosHyp  (Hardy 1914: infinitely many zeros on Re(s) = 1/2)

OUTPUT:
  - PsiOscillationFromCriticalZerosHyp  (ψ(x) - x = Ω±(√x))

SORRY COUNT: 0 in this bridge file.
  Atomic analytic sorries live in `Aristotle/LandauLittlewood.lean`.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.Aristotle.LandauLittlewood

noncomputable section

open Schmidt

/-- Littlewood's theorem: infinitely many critical-line zeros imply
ψ(x) - x = Ω±(√x).

This instance has HIGHER PRIORITY than the one in ExplicitFormulaOscillation.lean,
which goes through the FALSE hypothesis TruncatedExplicitFormulaPsiHyp. -/
instance (priority := 2000) [HardyCriticalLineZerosHyp] :
    PsiOscillationFromCriticalZerosHyp where
  oscillation := by
    exact (Aristotle.LandauLittlewood.psi_oscillation_sqrt_of_hardy).oscillation

/-- Littlewood's theorem for π: infinitely many critical-line zeros imply
π(x) - li(x) = Ω±(√x / log x).

This instance provides PiLiOscillationSqrtHyp DIRECTLY from Hardy's theorem,
bypassing the FALSE TruncatedExplicitFormulaPiHyp (which has the same S=∅
falseness issue as TruncatedExplicitFormulaPsiHyp).

Alternatively, this follows from ψ(x) - x = Ω±(√x) (the instance above)
via the identity π(x) = θ(x)/log x + ∫₂ˣ θ(t)/(t·log²t) dt and
θ(x) = ψ(x) - ψ(x^{1/2}) - ψ(x^{1/3}) - ..., but the direct argument
is cleaner and avoids the quantitative error bound issues in the transfer.

REFERENCES:
  - Littlewood, "Sur la distribution des nombres premiers" (1914)
  - Ingham, "Distribution of Prime Numbers", Chapter V -/
instance (priority := 2000) [HardyCriticalLineZerosHyp] :
    PiLiOscillationSqrtHyp where
  oscillation := by
    exact (Aristotle.LandauLittlewood.pi_li_oscillation_sqrt_log_of_hardy).oscillation
