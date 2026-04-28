import Littlewood.Aristotle.AbelSummation
import Littlewood.Aristotle.Standalone.LittlewoodKeyLemma
import Littlewood.ZetaZeros.DistinctMultiplicityCompatibility

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Littlewood.Classical

open scoped BigOperators Real
open ZetaZeros

private lemma positiveImZerosBelow_subset_of_le {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    positiveImZerosBelow T₁ ⊆ positiveImZerosBelow T₂ := by
  intro ρ hρ
  rcases mem_positiveImZerosBelow.mp hρ with ⟨hρzero, hρle⟩
  exact mem_positiveImZerosBelow.mpr ⟨hρzero, hρle.trans hT⟩

private lemma one_le_zeroMultiplicity_of_mem_positiveImZerosBelow {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow T) :
    1 ≤ zeroMultiplicity ρ := by
  rcases mem_positiveImZerosBelow.mp hρ with ⟨hρ_pos, _⟩
  rcases ZetaZeros.mem_zetaNontrivialZerosPos.mp hρ_pos with ⟨hzeta, _⟩
  rcases ZetaZeros.mem_zetaNontrivialZeros.mp hzeta with ⟨hzero, _, hre_lt⟩
  have hρ_ne_one : ρ ≠ 1 := by
    intro h1
    rw [h1] at hre_lt
    norm_num at hre_lt
  rcases Aristotle.ZetaLogDerivInfra.zeta_analytic_order_finite_pos ρ hzero hρ_ne_one with
    ⟨n, hn, horder⟩
  simpa [zeroMultiplicity, horder] using Nat.succ_le_of_lt hn

private lemma zeroMultiplicity_sub_one_nonneg_of_mem_positiveImZerosBelow {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ positiveImZerosBelow T) :
    0 ≤ (zeroMultiplicity ρ : ℝ) - 1 := by
  exact sub_nonneg.mpr (by exact_mod_cast one_le_zeroMultiplicity_of_mem_positiveImZerosBelow hρ)

private lemma sum_zeroMultiplicity_sub_one_positiveImZerosBelow (T : ℝ) :
    ∑ ρ ∈ positiveImZerosBelow T, (zeroMultiplicity ρ - 1) =
      ZetaZeros.zeroCountingMultiplicityExcess T := by
  simpa [positiveImZerosBelow, zeroMultiplicity] using
    (ZetaZeros.zeroCountingMultiplicityExcess_eq_sum T).symm

private lemma sum_zeroMultiplicity_sub_one_positiveImZerosBelow_real (T : ℝ) :
    ∑ ρ ∈ positiveImZerosBelow T, ((zeroMultiplicity ρ : ℝ) - 1) =
      (ZetaZeros.zeroCountingMultiplicityExcess T : ℝ) := by
  calc
    ∑ ρ ∈ positiveImZerosBelow T, ((zeroMultiplicity ρ : ℝ) - 1)
        = ∑ ρ ∈ positiveImZerosBelow T, (((zeroMultiplicity ρ - 1 : ℕ) : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro ρ hρ
            rw [Nat.cast_sub (one_le_zeroMultiplicity_of_mem_positiveImZerosBelow hρ), Nat.cast_one]
    _ = (ZetaZeros.zeroCountingMultiplicityExcess T : ℝ) := by
          simpa [Nat.cast_sum] using
            congrArg (fun n : ℕ => (n : ℝ))
              (sum_zeroMultiplicity_sub_one_positiveImZerosBelow T)

private lemma zeroCountingMultiplicityExcess_nonneg (T : ℝ) :
    0 ≤ (ZetaZeros.zeroCountingMultiplicityExcess T : ℝ) := by
  exact_mod_cast Nat.zero_le (ZetaZeros.zeroCountingMultiplicityExcess T)

private lemma ceil_shell_excess_le (T : ℝ) {m : ℕ} (hm2 : 2 ≤ m) :
    ∑ ρ ∈ positiveImZerosBelow T with Nat.ceil ρ.im = m, ((zeroMultiplicity ρ : ℝ) - 1)
      ≤ (ZetaZeros.zeroCountingMultiplicityExcess (m : ℝ) : ℝ) -
        (ZetaZeros.zeroCountingMultiplicityExcess (((m - 1 : ℕ) : ℝ)) : ℝ) := by
  let sbig : Finset ℂ := positiveImZerosBelow (m : ℝ)
  let ssmall : Finset ℂ := positiveImZerosBelow (((m - 1 : ℕ) : ℝ))
  let sdiff : Finset ℂ := sbig \ ssmall
  have hsubset :
      (positiveImZerosBelow T).filter (fun ρ => Nat.ceil ρ.im = m) ⊆ sdiff := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    rcases hρ with ⟨hρT, hceil⟩
    rcases mem_positiveImZerosBelow.mp hρT with ⟨hρzero, _⟩
    have hγ_le_m : ρ.im ≤ (m : ℝ) := by
      simpa [hceil] using Nat.le_ceil ρ.im
    have hm1_lt_γ : (((m - 1 : ℕ) : ℝ)) < ρ.im := by
      have hlt : m - 1 < Nat.ceil ρ.im := by simpa [hceil] using (show m - 1 < m by omega)
      simpa using Nat.lt_ceil.mp hlt
    refine Finset.mem_sdiff.mpr ?_
    constructor
    · exact mem_positiveImZerosBelow.mpr ⟨hρzero, hγ_le_m⟩
    · intro hρsmall
      have hγ_small : ρ.im ≤ (((m - 1 : ℕ) : ℝ)) := positiveImZerosBelow_im_le hρsmall
      linarith
  have hsubset_big : ssmall ⊆ sbig := by
    exact positiveImZerosBelow_subset_of_le (by
      have hm1_le_m : (((m - 1 : ℕ) : ℝ)) ≤ (m : ℝ) := by
        exact_mod_cast Nat.sub_le m 1
      exact hm1_le_m)
  have hsum_le :
      ∑ ρ ∈ positiveImZerosBelow T with Nat.ceil ρ.im = m, ((zeroMultiplicity ρ : ℝ) - 1)
        ≤ Finset.sum sdiff (fun ρ => ((zeroMultiplicity ρ : ℝ) - 1)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro ρ hρsdiff _
    exact zeroMultiplicity_sub_one_nonneg_of_mem_positiveImZerosBelow
      ((Finset.mem_sdiff.mp hρsdiff).1)
  calc
    ∑ ρ ∈ positiveImZerosBelow T with Nat.ceil ρ.im = m, ((zeroMultiplicity ρ : ℝ) - 1)
        ≤ Finset.sum sdiff (fun ρ => ((zeroMultiplicity ρ : ℝ) - 1)) := hsum_le
    _ = (ZetaZeros.zeroCountingMultiplicityExcess (m : ℝ) : ℝ) -
          (ZetaZeros.zeroCountingMultiplicityExcess (((m - 1 : ℕ) : ℝ)) : ℝ) := by
          dsimp [sdiff, sbig, ssmall]
          have hsdiff :=
            Finset.sum_sdiff hsubset_big (f := fun ρ : ℂ => ((zeroMultiplicity ρ : ℝ) - 1))
          rw [sum_zeroMultiplicity_sub_one_positiveImZerosBelow_real,
            sum_zeroMultiplicity_sub_one_positiveImZerosBelow_real] at hsdiff
          linarith

/-!
# AbelMultiplicityCorrectionBoundHyp placeholder

This file isolates the distinct-vs-multiplicity correction that remains after
feeding the constructive B5a truncated explicit formula into the classical
Littlewood Abel-sum surface.

The distinct-zero B5a sum uses

`∑_{0 < γ ≤ T} sin (γη) / γ`,

while `abelWeightedZeroSumUpTo T 0 η` uses the multiplicity-weighted variant

`∑_{0 < γ ≤ T} m(ρ) * sin (γη) / γ`.

So the bridge needs a uniform oscillatory bound on

`∑_{0 < γ ≤ T} (m(ρ) - 1) * sin (γη) / γ`.

That is the exact content of `AbelMultiplicityCorrectionBoundHyp`.

This surface is intentionally stronger than the zero-counting gap hypothesis
`NmultNGapBoundHyp`. The latter only gives `(Nmult T - N T) = O(log T)`, which
controls the correction by `O(log T)` after the trivial `1 / γ ≤ 1 / 14`
estimate. The active B5a-to-Abel bridge and its PL consumers currently use a
uniform `∃ K, ∀ η,T` correction, so the zero-counting gap leaf does not close
this file on the present theorem surfaces.
-/

/-- Focused uniform oscillatory multiplicity-correction leaf for the B5a-to-Abel
bridge. This is a ψ-lane leaf; it is not the same as the weaker zero-counting
leaf `NmultNGapBoundHyp`. -/
class AbelMultiplicityCorrectionBoundHyp : Prop where
  bound :
    ∃ K > 0, ∀ η T : ℝ, η ≥ 2 → T ≥ 2 →
      |∑ ρ ∈ positiveImZerosBelow T,
          (((zeroMultiplicity ρ : ℝ) - 1) * Real.sin (ρ.im * η) / ρ.im)| ≤ K

-- Instance provided by AbelMultiplicityCorrectionProof.lean (priority 200).
-- Import that file (or a downstream file) to obtain this instance.

end Littlewood.Classical
