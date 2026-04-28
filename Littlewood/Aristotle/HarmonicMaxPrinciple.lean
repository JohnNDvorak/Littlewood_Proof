import Mathlib

set_option autoImplicit false

noncomputable section

open Complex Set Metric Topology

namespace Littlewood.Aristotle.HarmonicMaxPrinciple

/-- Open rectangle in `ℂ`, written as real/imaginary product intervals. -/
def openRect (a b c d : ℝ) : Set ℂ :=
  Set.Ioo a b ×ℂ Set.Ioo c d

/-- Closed rectangle in `ℂ`, written as real/imaginary product intervals. -/
def closedRect (a b c d : ℝ) : Set ℂ :=
  Set.Icc a b ×ℂ Set.Icc c d

private lemma closure_openRect (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    closure (openRect a b c d) = closedRect a b c d := by
  simp [openRect, closedRect, Complex.closure_reProdIm, closure_Ioo, hab.ne, hcd.ne]

/-- `‖exp (-I * z)‖ = exp (Im z)`. -/
private lemma norm_exp_neg_I_mul (z : ℂ) :
    ‖Complex.exp (-Complex.I * z)‖ = Real.exp z.im := by
  rw [Complex.norm_exp]
  have hre : ((-Complex.I) * z).re = z.im := by
    simp [Complex.mul_re]
  rw [hre]

/-- Harmonic maximum principle for the imaginary part of a holomorphic function
on a rectangle, proved via the maximum modulus principle applied to
`exp (-I * f)`. -/
theorem harmonic_im_max_on_rect
    (f : ℂ → ℂ) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hf : DiffContOnCl ℂ f (openRect a b c d))
    (C : ℝ)
    (hleft : ∀ z, z.re = a → c ≤ z.im → z.im ≤ d → (f z).im ≤ C)
    (hright : ∀ z, z.re = b → c ≤ z.im → z.im ≤ d → (f z).im ≤ C)
    (hbottom : ∀ z, a ≤ z.re → z.re ≤ b → z.im = c → (f z).im ≤ C)
    (htop : ∀ z, a ≤ z.re → z.re ≤ b → z.im = d → (f z).im ≤ C)
    (z : ℂ) (hz : z ∈ closedRect a b c d) :
    (f z).im ≤ C := by
  let U : Set ℂ := openRect a b c d
  let g : ℂ → ℂ := fun w => Complex.exp (-Complex.I * f w)
  have hg :
      DiffContOnCl ℂ g U := by
    have hh : DiffContOnCl ℂ (fun w => -Complex.I * f w) U := by
      simpa [U, openRect, smul_eq_mul] using hf.const_smul (-Complex.I)
    simpa [g, U] using differentiable_exp.comp_diffContOnCl hh
  have hnorm_eq : ∀ w : ℂ, ‖g w‖ = Real.exp ((f w).im) := by
    intro w
    simpa [g] using norm_exp_neg_I_mul (f w)
  have hfrontier :
      ∀ w ∈ frontier U, ‖g w‖ ≤ Real.exp C := by
    intro w hw
    change w ∈ frontier (Set.Ioo a b ×ℂ Set.Ioo c d) at hw
    rw [Complex.frontier_reProdIm, closure_Ioo hab.ne, frontier_Ioo hab,
      closure_Ioo hcd.ne, frontier_Ioo hcd] at hw
    rcases hw with hw | hw
    · have hwre : a ≤ w.re := hw.1.1
      have hwre' : w.re ≤ b := hw.1.2
      have hbound : (f w).im ≤ C := by
        rcases (by simpa [Set.mem_insert_iff] using hw.2 : w.im = c ∨ w.im = d) with hbot | htop'
        · exact hbottom w hwre hwre' hbot
        · exact htop w hwre hwre' htop'
      rw [hnorm_eq]
      exact Real.exp_le_exp.mpr hbound
    · have hwim : c ≤ w.im := hw.2.1
      have hwim' : w.im ≤ d := hw.2.2
      have hbound : (f w).im ≤ C := by
        rcases (by simpa [Set.mem_insert_iff] using hw.1 : w.re = a ∨ w.re = b) with hleft' | hright'
        · exact hleft w hleft' hwim hwim'
        · exact hright w hright' hwim hwim'
      rw [hnorm_eq]
      exact Real.exp_le_exp.mpr hbound
  have hz_closure : z ∈ closure U := by
    rw [closure_openRect a b c d hab hcd]
    exact hz
  have hnorm :
      ‖g z‖ ≤ Real.exp C := by
    exact Complex.norm_le_of_forall_mem_frontier_norm_le
      ((Metric.isBounded_Ioo a b).reProdIm (Metric.isBounded_Ioo c d))
      hg
      hfrontier
      hz_closure
  rw [hnorm_eq] at hnorm
  exact Real.exp_le_exp.mp hnorm

end Littlewood.Aristotle.HarmonicMaxPrinciple
