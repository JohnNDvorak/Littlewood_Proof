/-
Preconnectedness of punctured half-planes in ℂ.

The key result: {s : ℂ | α < s.re} \ {1} is preconnected for any α : ℝ.
This is used for the identity principle in the Landau-Schmidt argument.

The proof decomposes the set into 4 convex pieces (upper, lower, right, left)
and applies IsPreconnected.union three times.

SORRY COUNT: 0
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Aristotle.HalfPlaneConnected

open Complex Set

/-! ## Convexity of half-plane pieces via linear preimages -/

/-- {s : ℂ | α < s.re} is convex. -/
private lemma convex_re_gt (α : ℝ) : Convex ℝ {s : ℂ | α < s.re} := by
  have : {s : ℂ | α < s.re} = reCLM ⁻¹' Ioi α := by
    ext s; simp [reCLM_apply]
  rw [this]
  exact (convex_Ioi α).linear_preimage reCLM.toLinearMap

/-- {s : ℂ | s.re < β} is convex. -/
private lemma convex_re_lt (β : ℝ) : Convex ℝ {s : ℂ | s.re < β} := by
  have : {s : ℂ | s.re < β} = reCLM ⁻¹' Iio β := by
    ext s; simp [reCLM_apply]
  rw [this]
  exact (convex_Iio β).linear_preimage reCLM.toLinearMap

/-- {s : ℂ | β < s.im} is convex. -/
private lemma convex_im_gt (β : ℝ) : Convex ℝ {s : ℂ | β < s.im} := by
  have : {s : ℂ | β < s.im} = imCLM ⁻¹' Ioi β := by
    ext s; simp [imCLM_apply]
  rw [this]
  exact (convex_Ioi β).linear_preimage imCLM.toLinearMap

/-- {s : ℂ | s.im < β} is convex. -/
private lemma convex_im_lt (β : ℝ) : Convex ℝ {s : ℂ | s.im < β} := by
  have : {s : ℂ | s.im < β} = imCLM ⁻¹' Iio β := by
    ext s; simp [imCLM_apply]
  rw [this]
  exact (convex_Iio β).linear_preimage imCLM.toLinearMap

/-! ## Main theorem -/

/-- The open half-plane {s : ℂ | α < s.re} minus a single point is preconnected.
If the point is outside the half-plane, the result is immediate (convex → preconnected).
If the point is inside, decompose into 4 convex pieces and union them. -/
theorem halfPlane_diff_singleton_isPreconnected (α : ℝ) (p : ℂ) :
    IsPreconnected ({s : ℂ | α < s.re} \ {p}) := by
  -- Case 1: p ∉ half-plane — diff is the whole convex set
  by_cases hp : α < p.re
  swap
  · have hsub : {s : ℂ | α < s.re} \ {p} = {s : ℂ | α < s.re} := by
      ext s; simp only [mem_diff, mem_setOf_eq, mem_singleton_iff]
      exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun heq => hp (heq ▸ h)⟩⟩
    rw [hsub]
    exact (convex_re_gt α).isPreconnected
  -- Case 2: p ∈ half-plane — 4-piece decomposition
  -- Define pieces
  set U := {s : ℂ | α < s.re ∧ p.im < s.im}
  set L := {s : ℂ | α < s.re ∧ s.im < p.im}
  set R := {s : ℂ | p.re < s.re}
  set W := {s : ℂ | α < s.re ∧ s.re < p.re}
  -- Each piece is convex
  have hU_conv : Convex ℝ U := by
    show Convex ℝ ({s : ℂ | α < s.re} ∩ {s : ℂ | p.im < s.im})
    exact (convex_re_gt α).inter (convex_im_gt p.im)
  have hL_conv : Convex ℝ L := by
    show Convex ℝ ({s : ℂ | α < s.re} ∩ {s : ℂ | s.im < p.im})
    exact (convex_re_gt α).inter (convex_im_lt p.im)
  have hR_conv : Convex ℝ R := convex_re_gt p.re
  have hW_conv : Convex ℝ W := by
    show Convex ℝ ({s : ℂ | α < s.re} ∩ {s : ℂ | s.re < p.re})
    exact (convex_re_gt α).inter (convex_re_lt p.re)
  -- Each piece is preconnected
  have hU_pc : IsPreconnected U := hU_conv.isPreconnected
  have hL_pc : IsPreconnected L := hL_conv.isPreconnected
  have hR_pc : IsPreconnected R := hR_conv.isPreconnected
  have hW_pc : IsPreconnected W := hW_conv.isPreconnected
  -- Show the union equals {Re > α} \ {p}
  -- We'll show {Re > α} \ {p} ⊆ U ∪ R ∪ L ∪ W and vice versa
  -- Then chain the unions: U∪R, then (U∪R)∪L, then ((U∪R)∪L)∪W
  -- Union step 1: U ∪ R (witness: ⟨p.re + 1, p.im + 1⟩)
  have hUR : IsPreconnected (U ∪ R) :=
    hU_pc.union (⟨p.re + 1, p.im + 1⟩ : ℂ)
      ⟨show α < p.re + 1 by linarith, show p.im < p.im + 1 by linarith⟩
      (show p.re < p.re + 1 by linarith) hR_pc
  -- Union step 2: (U ∪ R) ∪ L (witness: ⟨p.re + 1, p.im - 1⟩)
  have hURL : IsPreconnected (U ∪ R ∪ L) :=
    hUR.union (⟨p.re + 1, p.im - 1⟩ : ℂ)
      (Or.inr (show p.re < p.re + 1 by linarith))
      ⟨show α < p.re + 1 by linarith, show p.im - 1 < p.im by linarith⟩ hL_pc
  -- Union step 3: ((U ∪ R) ∪ L) ∪ W (witness: ⟨(α + p.re)/2, p.im + 1⟩)
  have hAll : IsPreconnected (U ∪ R ∪ L ∪ W) :=
    hURL.union (⟨(α + p.re) / 2, p.im + 1⟩ : ℂ)
      (Or.inl (Or.inl (show (⟨(α + p.re) / 2, p.im + 1⟩ : ℂ) ∈ U from
        ⟨by show α < (α + p.re) / 2; linarith, by show p.im < p.im + 1; linarith⟩)))
      ⟨by show α < (α + p.re) / 2; linarith, by show (α + p.re) / 2 < p.re; linarith⟩
      hW_pc
  -- Now show our target set equals U ∪ R ∪ L ∪ W
  suffices h_eq : {s : ℂ | α < s.re} \ {p} = U ∪ R ∪ L ∪ W by
    rw [h_eq]; exact hAll
  ext s
  simp only [mem_diff, mem_setOf_eq, mem_singleton_iff, mem_union]
  constructor
  · intro ⟨hs_re, hs_ne⟩
    -- ((U ∪ R) ∪ L) ∪ W : U=left left left, R=left left right, L=left right, W=right
    rcases lt_trichotomy s.im p.im with him | him | him
    · exact Or.inl (Or.inr ⟨hs_re, him⟩)  -- in L
    · rcases lt_trichotomy s.re p.re with hre | hre | hre
      · exact Or.inr ⟨hs_re, hre⟩  -- in W
      · exact absurd (Complex.ext hre him) hs_ne
      · exact Or.inl (Or.inl (Or.inr hre))  -- in R
    · exact Or.inl (Or.inl (Or.inl ⟨hs_re, him⟩))  -- in U
  · rintro (((⟨hr, hi⟩ | hr) | ⟨hr, hi⟩) | ⟨hr, hr'⟩)
    · exact ⟨hr, fun heq => absurd (by rw [heq] : s.im = p.im) (ne_of_gt hi)⟩
    · exact ⟨by exact lt_trans hp (hr : p.re < s.re),
             fun heq => absurd (by rw [heq] : s.re = p.re) (ne_of_gt hr)⟩
    · exact ⟨hr, fun heq => absurd (by rw [heq] : s.im = p.im) (ne_of_lt hi)⟩
    · exact ⟨hr, fun heq => absurd (by rw [heq] : s.re = p.re) (ne_of_lt hr')⟩

end Aristotle.HalfPlaneConnected
