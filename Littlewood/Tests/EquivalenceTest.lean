/-
Test: Can we prove equivalences between Aristotle local definitions
and project canonical definitions?

This file attempts to:
1. Import both Aristotle and project definitions
2. State and prove equivalence lemmas
3. Identify what bridges are trivial vs hard
-/

import Mathlib
import Littlewood.Aristotle.ThetaLinearBoundV2
import Littlewood.Aristotle.ChebyshevThetaV2
import Littlewood.Aristotle.ZeroCountingNew
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Aristotle.SchmidtNew
import Littlewood.Basic.ChebyshevFunctions
import Littlewood.Basic.LogarithmicIntegral
import Littlewood.ZetaZeros.ZeroCountingFunction

set_option maxHeartbeats 400000

namespace EquivalenceTest

open ChebyshevExt

-- ============================================================
-- TEST 1: theta definitions
-- ============================================================

-- Aristotle ThetaLinearBoundV2.theta : ℕ → ℝ
-- Aristotle ChebyshevThetaV2.theta : ℕ → ℝ
-- Canonical: chebyshevTheta : ℝ → ℝ (wraps Chebyshev.theta : ℝ → ℝ)

-- Are the two ℕ→ℝ Aristotle thetas the same?
-- ThetaLinearBoundV2.theta uses (Finset.range (n+1)).filter Nat.Prime
-- ChebyshevThetaV2.theta uses (Finset.range (n+1)).filter Nat.Prime
-- They should be definitionally equal.

theorem aristotle_thetas_agree (n : ℕ) :
    ThetaLinearBoundV2.theta n = ChebyshevThetaV2.theta n := by
  unfold ThetaLinearBoundV2.theta ChebyshevThetaV2.theta
  rfl

-- Can we bridge Aristotle theta (ℕ→ℝ) to canonical chebyshevTheta (ℝ→ℝ)?
-- chebyshevTheta x = Chebyshev.theta x = ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p
-- Aristotle theta n = ∑ p ∈ (Finset.range (n+1)).filter Nat.Prime, log p
-- Difference: Ioc 0 n (= {1,...,n}) vs range(n+1).filter Prime (= {0,...,n} ∩ Prime)
-- Since 0 is not prime, these give the same sum.

theorem theta_bridge (n : ℕ) :
    chebyshevTheta (n : ℝ) = ThetaLinearBoundV2.theta n := by
  unfold chebyshevTheta Chebyshev.theta ThetaLinearBoundV2.theta
  simp only [Nat.floor_natCast]
  have : (Finset.Ioc 0 n).filter Nat.Prime = (Finset.range (n + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨by omega, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
  rw [this]

-- ============================================================
-- TEST 2: psi definitions
-- ============================================================

-- Aristotle ChebyshevThetaV2.psi : ℕ → ℝ
-- Canonical: chebyshevPsi : ℝ → ℝ (wraps Chebyshev.psi : ℝ → ℝ)

-- Chebyshev.psi x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n
-- ChebyshevThetaV2.psi n = ∑ k ∈ range (n+1), vonMangoldt k
-- Difference: Ioc 0 n vs range(n+1), but vonMangoldt 0 = 0

theorem psi_bridge (n : ℕ) :
    chebyshevPsi (n : ℝ) = ChebyshevThetaV2.psi n := by
  unfold chebyshevPsi Chebyshev.psi ChebyshevThetaV2.psi
  simp only [Nat.floor_natCast]
  -- Need: ∑ k ∈ Ioc 0 n, Λ k = ∑ k ∈ range (n+1), vonMangoldt k
  -- range(n+1) = {0} ∪ Ioc 0 n, and vonMangoldt 0 = 0
  rw [show Finset.range (n + 1) = insert 0 (Finset.Ioc 0 n) from by
    ext k; simp only [Finset.mem_insert, Finset.mem_Ioc, Finset.mem_range]; omega]
  rw [Finset.sum_insert (by simp only [Finset.mem_Ioc]; omega)]
  simp [ArithmeticFunction.map_zero]

-- ============================================================
-- TEST 3: NZeros vs zeroCountingFunction
-- ============================================================

-- Canonical: ZetaZeros.zeroCountingFunction T : ℕ
--   = (zetaNontrivialZerosPos ∩ {s | s.im ≤ T}).ncard
-- Aristotle: NZeros T : ℕ
--   = Set.ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T}

-- These should be equal if zetaNontrivialZerosPos unfolds correctly.

theorem nzeros_bridge (T : ℝ) :
    ZetaZeros.zeroCountingFunction T = NZeros T := by
  unfold ZetaZeros.zeroCountingFunction NZeros
  unfold ZetaZeros.zetaNontrivialZerosPos ZetaZeros.zetaNontrivialZeros
  congr 1
  ext s
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩

-- ============================================================
-- TEST 4: Can we transfer theta_O_n to canonical types?
-- ============================================================

-- ThetaLinearBoundV2.theta_O_n : ∃ C > 0, ∀ n, theta n ≤ C * n
-- We want: ∃ C > 0, ∀ n : ℕ, chebyshevTheta n ≤ C * n

theorem chebyshev_theta_linear_from_aristotle :
    ∃ C : ℝ, ∀ n : ℕ, chebyshevTheta (n : ℝ) ≤ C * n := by
  obtain ⟨C, hbound⟩ := ThetaLinearBoundV2.theta_O_n
  exact ⟨C, fun n => by rw [theta_bridge]; exact hbound n⟩

-- ============================================================
-- TEST 5: Schmidt oscillation — already in canonical types
-- ============================================================

-- schmidt_oscillation uses Finset ℝ, cos, etc. — no project types needed
-- It's already fully canonical (operates on abstract real functions)
#check @schmidt_oscillation

-- ============================================================
-- TEST 6: Hardy Z theorems — already use Mathlib's riemannZeta
-- ============================================================

#check @hardyZV2_real
#check @continuous_hardyZV2
#check @hardyZV2_zero_iff_zeta_zero
#check @hardyZV2_abs_eq_zeta_abs

-- These all use riemannZeta directly from Mathlib — no bridging needed.

end EquivalenceTest
