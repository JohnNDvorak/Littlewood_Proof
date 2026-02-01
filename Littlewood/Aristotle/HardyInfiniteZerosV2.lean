/-
Hardy's theorem: infinitely many zeros on the critical line.

Version 2: Fixed field signatures (endpoints at 1, not arbitrary T₁).

BUG IN V1 (HardyInfiniteZeros.lean):
The mean_square_lower_bound, first_moment_upper_bound, and l1_lower_bound fields
universally quantify over the lower endpoint T₁ ∈ [0,T), requiring the bounds to hold
for ALL such T₁. This is unsatisfiable: for T₁ = T-ε, ∫_{T-ε}^T Z² ≈ ε·Z(T)² → 0,
yet the RHS is c·T·log T. The `grind` proof in V1 works vacuously from sorry = False.

FIX: All integrals are over [1, T] with fixed lower endpoint.

The contradiction argument:
1. Mean square: ∫₁ᵀ Z(t)² dt ≥ c·T·log T
2. First moment: |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2+ε}
3. Z_convexity_bound: |Z(t)| ≤ C'|t|^{1/4+ε}
4. If only finitely many zeros, Z has constant sign on [T₀, ∞)
5. Then |∫_{T₀}^T Z| = ∫_{T₀}^T |Z| (constant sign)
6. So ∫_{T₀}^T |Z| ≤ |∫₁ᵀ Z| + |∫₁^{T₀} Z| ≤ C·T^{1/2+ε₁} + const
7. And ∫₁ᵀ Z² ≤ const + sup_{[T₀,T]}|Z| · ∫_{T₀}^T |Z|
                ≤ const + C'·T^{1/4+ε₂} · (C·T^{1/2+ε₁} + const)
8. So c·T·log T ≤ const + C''·T^{3/4+ε₁+ε₂}
9. For ε₁ + ε₂ < 1/4, exponent 3/4 + ε₁ + ε₂ < 1, so T·log T dominates. Contradiction!

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyInfiniteZerosV2

open Complex Real Set Filter Topology MeasureTheory

/-- Setup for Hardy's Theorem, Version 2 with correct field signatures.
    All integral bounds use fixed lower endpoint 1, not arbitrary T₁. -/
class HardySetupV2 where
  /-- The real-valued Hardy Z function on the critical line -/
  Z : ℝ → ℝ
  /-- Z is continuous -/
  Z_continuous : Continuous Z
  /-- Z(t) = 0 ↔ ζ(1/2+it) = 0 -/
  Z_zero_iff : ∀ t : ℝ, Z t = 0 ↔ riemannZeta (1/2 + I * t) = 0
  /-- Mean square lower bound: ∫₁ᵀ Z² ≥ c·T·log T (fixed endpoint 1) -/
  mean_square_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      c * T * Real.log T ≤ ∫ t in Ioc 1 T, (Z t)^2
  /-- First moment upper bound: |∫₁ᵀ Z| ≤ C·T^{1/2+ε} (fixed endpoint 1) -/
  first_moment_upper :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      |∫ t in Ioc 1 T, Z t| ≤ C * T^(1/2 + ε)
  /-- Convexity bound: |Z(t)| ≤ C|t|^{1/4+ε} -/
  Z_convexity_bound :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∀ t : ℝ, |t| ≥ 2 →
      |Z t| ≤ C * |t|^(1/4 + ε)

variable [inst : HardySetupV2]

/-! ## Step 1: Finitely many zeros implies constant sign -/

/-- If Z has finitely many positive zeros, it has constant sign on [T₀, ∞)
    for some T₀, by continuity and IVT. -/
lemma constant_sign_of_finite (h : Set.Finite {t : ℝ | inst.Z t = 0 ∧ t > 0}) :
    ∃ T₀ : ℝ, T₀ > 0 ∧ ((∀ t : ℝ, t > T₀ → inst.Z t > 0) ∨
                           (∀ t : ℝ, t > T₀ → inst.Z t < 0)) := by
  -- Finite zero set is bounded above; Z is continuous; IVT gives constant sign
  sorry

/-! ## Step 2: Constant sign implies |∫Z| = ∫|Z| -/

/-- When Z has constant sign, |∫Z| = ∫|Z|. -/
lemma abs_integral_eq_of_pos (T₀ T : ℝ) (hT : T > T₀)
    (hsign : ∀ t : ℝ, t > T₀ → inst.Z t > 0) :
    |∫ t in Ioc T₀ T, inst.Z t| = ∫ t in Ioc T₀ T, |inst.Z t| := by
  sorry

/-! ## Step 3: Decompose mean square integral -/

/-- Decompose ∫₁ᵀ Z² = ∫₁^{T₀} Z² + ∫_{T₀}^T Z². -/
lemma mean_square_decomp (T₀ T : ℝ) (hT₀ : T₀ > 1) (hT : T > T₀) :
    ∫ t in Ioc 1 T, (inst.Z t)^2 =
    ∫ t in Ioc 1 T₀, (inst.Z t)^2 + ∫ t in Ioc T₀ T, (inst.Z t)^2 := by
  sorry

/-! ## Step 4: Bound ∫_{T₀}^T Z² using sup|Z| and ∫|Z| -/

/-- ∫_{T₀}^T Z² ≤ sup|Z| · ∫_{T₀}^T |Z| -/
lemma mean_square_le_sup_times_l1 (T₀ T : ℝ) (hT : T > T₀) :
    ∫ t in Ioc T₀ T, (inst.Z t)^2 ≤
    (⨆ t ∈ Ioc T₀ T, |inst.Z t|) * ∫ t in Ioc T₀ T, |inst.Z t| := by
  sorry

/-! ## Step 5: The contradiction -/

/-- Hardy's theorem: infinitely many zeros of ζ on the critical line.
    The proof derives a contradiction from assuming finitely many zeros:
    constant sign → tight integral bounds → T·log T ≤ C·T^α for α < 1. -/
theorem hardy_infinitely_many_zeros_v2 :
    Set.Infinite {t : ℝ | riemannZeta (1/2 + I * t) = 0} := by
  -- Assume finite
  by_contra h_fin
  rw [Set.not_infinite] at h_fin
  -- Transfer to Z zeros using Z_zero_iff
  have h_Z_fin : Set.Finite {t : ℝ | inst.Z t = 0 ∧ t > 0} := by
    exact h_fin.subset fun t ⟨ht_zero, ht_pos⟩ => (inst.Z_zero_iff t).mp ht_zero
  -- Get constant sign after some T₀
  obtain ⟨T₀, hT₀, hsign⟩ := constant_sign_of_finite h_Z_fin
  -- Get the quantitative bounds
  obtain ⟨c, hc, T₁, hT₁, h_ms⟩ := inst.mean_square_lower
  -- Use ε = 1/10 for both first moment and convexity
  obtain ⟨C_fm, hC_fm, T₂, hT₂, h_fm⟩ := inst.first_moment_upper (1/10) (by norm_num)
  obtain ⟨C_cv, hC_cv, h_cv⟩ := inst.Z_convexity_bound (1/10) (by norm_num)
  -- For T ≥ max(T₀, T₁, T₂, 2):
  -- (a) c·T·log T ≤ ∫₁ᵀ Z²                         [mean square lower]
  -- (b) |∫₁ᵀ Z| ≤ C_fm·T^{6/10}                     [first moment upper]
  -- (c) sup|Z| on [T₀,T] ≤ C_cv·T^{35/100}          [convexity]
  -- (d) constant sign on [T₀,∞) → ∫_{T₀}^T |Z| = |∫_{T₀}^T Z|
  --     ≤ |∫₁ᵀ Z| + |∫₁^{T₀} Z| ≤ C_fm·T^{6/10} + const
  -- (e) ∫₁ᵀ Z² = ∫₁^{T₀} Z² + ∫_{T₀}^T Z²
  --            ≤ const + sup|Z| · ∫_{T₀}^T |Z|
  --            ≤ const + C_cv·T^{35/100} · (C_fm·T^{6/10} + const)
  --            ≤ const + C'·T^{95/100}
  -- (f) c·T·log T ≤ const + C'·T^{95/100}
  --     But T·log T / T^{95/100} = T^{1/20}·log T → ∞. Contradiction!
  sorry

end HardyInfiniteZerosV2
