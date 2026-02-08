import Littlewood.Aristotle.PsiThetaBound
import Littlewood.Basic.ChebyshevFunctions

noncomputable section

open Real Filter Asymptotics
open scoped Chebyshev

namespace Aristotle.PsiThetaCanonicalBound

/-- The local `psi` from `Aristotle.PsiThetaBound` matches the canonical
`chebyshevPsi`. -/
lemma psi_eq_chebyshevPsi (x : ℝ) :
    PsiThetaBound.psi x = chebyshevPsi x := by
  unfold PsiThetaBound.psi chebyshevPsi
  rw [Chebyshev.psi_eq_sum_Icc]
  have hIcc : Finset.Icc 0 (Nat.floor x) = Finset.range (Nat.floor x + 1) := by
    ext n
    constructor
    · intro hn
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hn).2)
    · intro hn
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)⟩
  rw [hIcc]

/-- The local `theta` from `Aristotle.PsiThetaBound` matches the canonical
`chebyshevTheta`. -/
lemma theta_eq_chebyshevTheta (x : ℝ) :
    PsiThetaBound.theta x = chebyshevTheta x := by
  unfold PsiThetaBound.theta chebyshevTheta Chebyshev.theta
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpRange, hpPrime⟩
    have hpPos : 0 < p := hpPrime.pos
    have hpLe : p ≤ Nat.floor x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hpRange)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpPos, hpLe⟩, hpPrime⟩
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpIoc, hpPrime⟩
    have hpIoc' : 0 < p ∧ p ≤ Nat.floor x := Finset.mem_Ioc.mp hpIoc
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpIoc'.2), hpPrime⟩

/-- Canonical `O(√x)` bound for `|ψ(x) - θ(x)|`, transferred from
`Aristotle.PsiThetaBound`. -/
theorem abs_chebyshevPsi_sub_chebyshevTheta_le_const_sqrt :
    ∃ C > 0, ∀ x ≥ 2, |chebyshevPsi x - chebyshevTheta x| ≤ C * Real.sqrt x := by
  obtain ⟨C, hC, hCbound⟩ := PsiThetaBound.psi_theta_bound
  refine ⟨C, hC, ?_⟩
  intro x hx
  simpa [psi_eq_chebyshevPsi x, theta_eq_chebyshevTheta x] using hCbound x hx

/-- Canonical asymptotic form: `(ψ - θ) = O(√x)`. -/
theorem chebyshevPsi_sub_chebyshevTheta_isBigO_sqrt :
    (fun x => chebyshevPsi x - chebyshevTheta x) =O[atTop] (fun x => Real.sqrt x) := by
  obtain ⟨C, hC, hbound⟩ := abs_chebyshevPsi_sub_chebyshevTheta_le_const_sqrt
  refine Asymptotics.IsBigO.of_bound C ?_
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨2, ?_⟩
  intro x hx
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  calc
    ‖chebyshevPsi x - chebyshevTheta x‖
        = |chebyshevPsi x - chebyshevTheta x| := by simp [Real.norm_eq_abs]
    _ ≤ C * Real.sqrt x := hbound x hx
    _ = C * ‖Real.sqrt x‖ := by
          rw [Real.norm_of_nonneg hsqrt_nonneg]

end Aristotle.PsiThetaCanonicalBound
