import Mathlib

/-!
# Conjugate Pairing Identity for Multiplicity-Weighted Zero Sums

Given a finite set `S` of complex numbers (representing nontrivial zeros of ζ
in the critical strip), closed under conjugation and equipped with a
conjugation-invariant multiplicity function `m` and a conjugation-invariant
real-valued function `f` (representing `ρ ↦ Re(x^ρ/ρ)`), we prove:

  `∑_{ρ ∈ S} m(ρ) · f(ρ) = 2 · ∑_{ρ ∈ S, Im ρ > 0} m(ρ) · f(ρ) + R`

where `R = ∑_{ρ ∈ S, Im ρ = 0} m(ρ) · f(ρ)`, and `|R| ≤ B · ∑_{ρ ∈ S, Im ρ = 0} m(ρ)`
whenever `|f(ρ)| ≤ B` on the real-axis zeros and multiplicities are nonneg.

## Key mathematical facts used

1. `m(ρ̄) = m(ρ)` — conjugate zeros have equal multiplicity (functional equation)
2. `f(ρ̄) = f(ρ)` — for real `x > 0`, `Re(x^{ρ̄}/ρ̄) = Re(x^ρ/ρ)`
3. The imaginary-part trichotomy partitions `S` into positive-, negative-, and zero-Im subsets
4. Conjugation bijects the negative-Im and positive-Im subsets
-/

open Complex BigOperators

noncomputable section

namespace Littlewood.Classical.MultConjugatePairing

/-! ## Partition lemma -/

/-- Any finset of complex numbers decomposes into three disjoint parts
    by the sign of the imaginary part. -/
lemma finset_tripartition_im (S : Finset ℂ) (g : ℂ → ℝ) :
    ∑ ρ ∈ S, g ρ =
      ∑ ρ ∈ S.filter (fun z => 0 < z.im), g ρ +
      ∑ ρ ∈ S.filter (fun z => z.im < 0), g ρ +
      ∑ ρ ∈ S.filter (fun z => z.im = 0), g ρ := by
  simp +decide only [Finset.sum_filter, ← Finset.sum_add_distrib]
  grind

/-! ## Conjugation mapping lemmas -/

/-- Complex conjugation maps negative-Im elements of `S` to positive-Im elements. -/
lemma conj_neg_to_pos (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, (starRingEnd ℂ) ρ ∈ S)
    {ρ : ℂ} (hρ : ρ ∈ S.filter (fun z => z.im < 0)) :
    (starRingEnd ℂ) ρ ∈ S.filter (fun z => 0 < z.im) := by
  aesop

/-- Complex conjugation maps positive-Im elements of `S` to negative-Im elements. -/
lemma conj_pos_to_neg (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, (starRingEnd ℂ) ρ ∈ S)
    {ρ : ℂ} (hρ : ρ ∈ S.filter (fun z => 0 < z.im)) :
    (starRingEnd ℂ) ρ ∈ S.filter (fun z => z.im < 0) := by
  aesop

/-! ## The bijection lemma -/

/-- The sum over negative-Im elements equals the sum over positive-Im elements
    when the summand is invariant under complex conjugation.

    This uses complex conjugation (`starRingEnd ℂ`) as a bijection between
    the negative-Im and positive-Im filters. -/
lemma sum_neg_im_eq_sum_pos_im (S : Finset ℂ) (g : ℂ → ℝ)
    (hS : ∀ ρ ∈ S, (starRingEnd ℂ) ρ ∈ S)
    (hg : ∀ ρ ∈ S, g ((starRingEnd ℂ) ρ) = g ρ) :
    ∑ ρ ∈ S.filter (fun z => z.im < 0), g ρ =
    ∑ ρ ∈ S.filter (fun z => 0 < z.im), g ρ := by
  apply Finset.sum_bij (fun ρ _ => (starRingEnd ℂ) ρ)
  · exact fun ρ hρ => conj_neg_to_pos S hS hρ
  · intro ρ₁ _ ρ₂ _ h
    simpa [Complex.ext_iff, Complex.conj_re, Complex.conj_im] using h
  · intro ρ hρ
    exact ⟨(starRingEnd ℂ) ρ, conj_pos_to_neg S hS hρ, by simp⟩
  · intro ρ hρ
    exact (hg ρ (Finset.mem_of_mem_filter ρ hρ)).symm

/-! ## Main theorem -/

/-- **Conjugate Pairing Identity.**
    The full multiplicity-weighted sum over a conjugation-symmetric finite set
    decomposes as twice the positive-imaginary-part contribution plus a
    real-axis remainder.

    This identity is the key step in reducing explicit-formula sums over
    *all* nontrivial zeros to sums over zeros with positive imaginary part,
    using the functional equation symmetry `m(ρ̄) = m(ρ)` and the
    conjugation identity `Re(x^{ρ̄}/ρ̄) = Re(x^ρ/ρ)` for real `x > 0`. -/
theorem conjugate_pairing_identity
    (S : Finset ℂ) (m f : ℂ → ℝ)
    (hS : ∀ ρ ∈ S, (starRingEnd ℂ) ρ ∈ S)
    (hm : ∀ ρ ∈ S, m ((starRingEnd ℂ) ρ) = m ρ)
    (hf : ∀ ρ ∈ S, f ((starRingEnd ℂ) ρ) = f ρ) :
    ∑ ρ ∈ S, m ρ * f ρ =
      2 * ∑ ρ ∈ S.filter (fun ρ => 0 < ρ.im), m ρ * f ρ +
      ∑ ρ ∈ S.filter (fun ρ => ρ.im = 0), m ρ * f ρ := by
  have hg : ∀ ρ ∈ S, (fun z => m z * f z) ((starRingEnd ℂ) ρ) = (fun z => m z * f z) ρ := by
    intro ρ hρ; simp only [hm ρ hρ, hf ρ hρ]
  rw [finset_tripartition_im S (fun ρ => m ρ * f ρ)]
  rw [sum_neg_im_eq_sum_pos_im S _ hS hg]
  ring

/-! ## Remainder bound -/

/-- **Remainder Bound.**
    The real-axis contribution `R = ∑_{Im ρ = 0} m(ρ) f(ρ)` satisfies
    `|R| ≤ B · (∑_{Im ρ = 0} m(ρ))` whenever `m ≥ 0` and `|f| ≤ B`
    on the real-axis zeros.

    In the analytic number theory application, `B = 2√x` and each `m(ρ)`
    is a positive integer multiplicity, so `|R| ≤ C · √x`. -/
theorem remainder_bound
    (S : Finset ℂ) (m f : ℂ → ℝ) (B : ℝ)
    (hm_nn : ∀ ρ ∈ S.filter (fun z => z.im = 0), 0 ≤ m ρ)
    (hf_bd : ∀ ρ ∈ S.filter (fun z => z.im = 0), |f ρ| ≤ B) :
    |∑ ρ ∈ S.filter (fun z => z.im = 0), m ρ * f ρ| ≤
      B * ∑ ρ ∈ S.filter (fun z => z.im = 0), m ρ := by
  calc |∑ ρ ∈ S.filter (fun z => z.im = 0), m ρ * f ρ|
      ≤ ∑ ρ ∈ S.filter (fun z => z.im = 0), |m ρ * f ρ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ B * ∑ ρ ∈ S.filter (fun z => z.im = 0), m ρ := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun x hx => by
          rw [abs_le]; constructor <;> nlinarith [abs_le.mp (hf_bd x hx), hm_nn x hx]

end Littlewood.Classical.MultConjugatePairing
