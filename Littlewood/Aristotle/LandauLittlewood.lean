/- 
# Landau-Littlewood Oscillation Consequences

Proves PsiOscillationFromCriticalZerosHyp and PiLiOscillationSqrtHyp
from HardyCriticalLineZerosHyp, using the contradiction lemmas in
Aristotle/LandauContradiction.lean.

Each direction (Ω₊ and Ω₋) is proved by contradiction:
  ¬Ω₊ → ∀ c>0, eventually f < c·g → one-sided o(g) → contradicts critical zeros.

Mathematical references:
- Littlewood (1914), Landau oscillation method.
- Ingham, Distribution of Prime Numbers, Chapter V.
- Montgomery-Vaughan, Multiplicative Number Theory I, §15.1.
-/

import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.Aristotle.LandauContradiction

noncomputable section

open Schmidt Filter Topology

namespace Aristotle.LandauLittlewood

/-- Landau-Littlewood consequence for ψ at square-root scale. -/
theorem psi_oscillation_sqrt_of_hardy
    [HardyCriticalLineZerosHyp] :
    PsiOscillationFromCriticalZerosHyp where
  oscillation := by
    constructor
    · by_contra h_not
      have h_upper : ∀ c : ℝ, c > 0 →
          ∀ᶠ x in atTop, chebyshevPsi x - x < c * Real.sqrt x := by
        intro c hc
        have h_not_freq : ¬ ∃ᶠ x in atTop, chebyshevPsi x - x ≥ c * Real.sqrt x := by
          intro hfreq
          exact h_not ⟨c, hc, hfreq⟩
        exact (Filter.not_frequently.mp h_not_freq).mono (fun _ hx => lt_of_not_ge hx)
      exact LandauContradiction.psi_upper_contradicts_critical_zeros
        HardyCriticalLineZerosHyp.infinite h_upper
    · by_contra h_not
      have h_lower : ∀ c : ℝ, c > 0 →
          ∀ᶠ x in atTop, chebyshevPsi x - x > -(c * Real.sqrt x) := by
        intro c hc
        have h_not_freq : ¬ ∃ᶠ x in atTop, chebyshevPsi x - x ≤ -(c * Real.sqrt x) := by
          intro hfreq
          have hfreq' : ∃ᶠ x in atTop, chebyshevPsi x - x ≤ -c * Real.sqrt x := by
            simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hfreq
          exact h_not ⟨c, hc, hfreq'⟩
        exact (Filter.not_frequently.mp h_not_freq).mono (fun _ hx => lt_of_not_ge hx)
      exact LandauContradiction.psi_lower_contradicts_critical_zeros
        HardyCriticalLineZerosHyp.infinite h_lower

/-- Landau-Littlewood consequence for π(x) - li(x) at √x/log x scale. -/
theorem pi_li_oscillation_sqrt_log_of_hardy
    [HardyCriticalLineZerosHyp] :
    PiLiOscillationSqrtHyp where
  oscillation := by
    constructor
    · by_contra h_not
      have h_upper : ∀ c : ℝ, c > 0 →
          ∀ᶠ x in atTop,
            (Nat.primeCounting (Nat.floor x) : ℝ) -
              LogarithmicIntegral.logarithmicIntegral x <
            c * (Real.sqrt x / Real.log x) := by
        intro c hc
        have h_not_freq : ¬ ∃ᶠ x in atTop,
            (Nat.primeCounting (Nat.floor x) : ℝ) -
              LogarithmicIntegral.logarithmicIntegral x ≥
            c * (Real.sqrt x / Real.log x) := by
          intro hfreq
          exact h_not ⟨c, hc, hfreq⟩
        exact (Filter.not_frequently.mp h_not_freq).mono (fun _ hx => lt_of_not_ge hx)
      exact LandauContradiction.pi_li_upper_contradicts_critical_zeros
        HardyCriticalLineZerosHyp.infinite h_upper
    · by_contra h_not
      have h_lower : ∀ c : ℝ, c > 0 →
          ∀ᶠ x in atTop,
            (Nat.primeCounting (Nat.floor x) : ℝ) -
              LogarithmicIntegral.logarithmicIntegral x >
            -(c * (Real.sqrt x / Real.log x)) := by
        intro c hc
        have h_not_freq : ¬ ∃ᶠ x in atTop,
            (Nat.primeCounting (Nat.floor x) : ℝ) -
              LogarithmicIntegral.logarithmicIntegral x ≤
            -(c * (Real.sqrt x / Real.log x)) := by
          intro hfreq
          have hfreq' : ∃ᶠ x in atTop,
              (Nat.primeCounting (Nat.floor x) : ℝ) -
                LogarithmicIntegral.logarithmicIntegral x ≤
              -c * (Real.sqrt x / Real.log x) := by
            simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hfreq
          exact h_not ⟨c, hc, hfreq'⟩
        exact (Filter.not_frequently.mp h_not_freq).mono (fun _ hx => lt_of_not_ge hx)
      exact LandauContradiction.pi_li_lower_contradicts_critical_zeros
        HardyCriticalLineZerosHyp.infinite h_lower

end Aristotle.LandauLittlewood
