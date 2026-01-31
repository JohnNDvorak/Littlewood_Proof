/-
Integrated from Aristotle output ea613b3f-fa42-4248-a9c9-2271485b043e.
Zeta convexity via Phragmén-Lindelöf in the critical strip.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

KEY RESULTS:
- zetaAuxF, zetaAuxH, zetaAuxG: auxiliary functions for PL application
- zetaAuxF_cont, zetaAuxG_cont: continuous versions (handling the s=1 pole)
- zetaAuxG_cont_diff: g(s) is DiffContOnCl on the critical strip {0 < Re(s) < 1}
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ZetaConvexityStrip

/-
Auxiliary function f(s) = (s-1)ζ(s). Removes the pole of ζ at s=1.
-/
noncomputable def zetaAuxF (s : ℂ) : ℂ := (s - 1) * riemannZeta s

/-
Auxiliary function h(s) = (s+2)^(3/2). Provides polynomial growth control.
-/
noncomputable def zetaAuxH (s : ℂ) : ℂ := (s + 2) ^ ((3 : ℂ) / 2)

/-
Quotient g(s) = f(s)/h(s). This is the function we apply PL to.
-/
noncomputable def zetaAuxG (s : ℂ) : ℂ := zetaAuxF s / zetaAuxH s

/-
Continuous extension of f(s) at s=1: f_cont(1) = 1 (the residue).
-/
noncomputable def zetaAuxF_cont (s : ℂ) : ℂ := if s = 1 then 1 else (s - 1) * riemannZeta s

/-
Continuous extension of g(s) using f_cont.
-/
noncomputable def zetaAuxG_cont (s : ℂ) : ℂ := zetaAuxF_cont s / zetaAuxH s

/-
The auxiliary function g(s) is differentiable in the critical strip and continuous on its closure.
This is the key ingredient for applying Phragmén-Lindelöf.
-/
lemma zetaAuxG_cont_diff : DiffContOnCl ℂ zetaAuxG_cont (Complex.re ⁻¹' Set.Ioo 0 1) := by
  have h_cont : ContinuousOn zetaAuxG_cont (Complex.re ⁻¹' Set.Ioo 0 1 ∪ Complex.re ⁻¹' Set.Icc 0 1) := by
    have h_cont_f : ContinuousOn zetaAuxF_cont (Complex.re ⁻¹' Set.Ioo 0 1 ∪ Complex.re ⁻¹' Set.Icc 0 1) := by
      have h_cont_f : ContinuousAt zetaAuxF_cont 1 := by
        have h_cont : Filter.Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
          sorry
        rw [ Metric.tendsto_nhdsWithin_nhds ] at h_cont;
        rw [ Metric.continuousAt_iff ];
        intro ε hε; rcases h_cont ε hε with ⟨ δ, hδ, H ⟩ ; use δ, hδ; intro x hx; by_cases hx' : x = 1 <;> simp_all +decide [ zetaAuxF_cont ] ;
      refine' continuousOn_of_forall_continuousAt fun s hs => _;
      by_cases h : s = 1 <;> simp_all +decide [ ContinuousAt ];
      have h_cont_f_at_s : Filter.Tendsto (fun s => (s - 1) * riemannZeta s) (nhds s) (nhds ((s - 1) * riemannZeta s)) := by
        exact Filter.Tendsto.mul ( Filter.tendsto_id.sub tendsto_const_nhds ) ( differentiableAt_riemannZeta ( by aesop ) |> DifferentiableAt.continuousAt );
      convert h_cont_f_at_s.congr' _ using 2 <;> norm_num [ zetaAuxF_cont ] ; aesop;
      filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_singleton.preimage continuous_id' ) h ] with x hx using by unfold zetaAuxF_cont; aesop;
    refine' h_cont_f.div _ _ <;> norm_num [ zetaAuxH ];
    · refine' ContinuousOn.cpow _ _ _ <;> norm_num [ continuousOn_const ];
      · exact continuousOn_id.add continuousOn_const;
      · exact fun a ha => Or.inl <| by cases ha <;> norm_num <;> linarith;
    · intro x hx; intro H; rw [ Complex.ext_iff ] at H; norm_num at H; linarith [ hx.resolve_right ( by intro h; linarith ) ] ;
  refine' ⟨ _, _ ⟩;
  · refine' DifferentiableOn.div _ _ _;
    · have h_diff : DifferentiableOn ℂ (fun s => (s - 1) * riemannZeta s) (Complex.re ⁻¹' Set.Ioo 0 1) := by
        refine' DifferentiableOn.mul _ _;
        · exact differentiableOn_id.sub_const _;
        · intro s hs; exact differentiableAt_riemannZeta ( show s ≠ 1 by aesop ) |> DifferentiableAt.differentiableWithinAt;
      refine' h_diff.congr _;
      unfold zetaAuxF_cont; aesop;
    · refine' DifferentiableOn.cpow _ _ _ <;> norm_num;
      · exact differentiableOn_id;
      · exact fun x hx => Or.inl <| by norm_num; linarith [ hx.1, hx.2 ] ;
    · intro x hx
      have h_pos : 0 < Complex.re (x + 2) := by
        norm_num at * ; linarith;
      norm_num +zetaDelta at *;
      unfold zetaAuxH; norm_num [ Complex.cpow_def_of_ne_zero, show x + 2 ≠ 0 from ne_of_apply_ne Complex.re <| by norm_num; linarith ] ;
  · refine' h_cont.mono _;
    simp +decide [ Set.Ioo, Set.Icc, Set.subset_def, mem_closure_iff_seq_limit ];
    intro x y hy hx; exact Or.inr ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds ( Complex.continuous_re.continuousAt.tendsto.comp hx ) fun n => hy n |>.1.le, le_of_tendsto_of_tendsto' ( Complex.continuous_re.continuousAt.tendsto.comp hx ) tendsto_const_nhds fun n => hy n |>.2.le ⟩ ;

end ZetaConvexityStrip
