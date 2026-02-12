import Littlewood.Basic.ChebyshevFunctions
import Littlewood.Basic.LogarithmicIntegral
import Littlewood.Basic.OmegaNotation

/-!
Infrastructure for the θ → (π - li) transfer.

This file is intentionally hypothesis-free and sorry-free. It packages the exact
decomposition formula needed by `OmegaThetaToPiLiWiring`:

  π(x) - li(x) = (θ(x) - x)/log x + remainder(x)

with an explicit `remainder` definition.
-/

noncomputable section

open Real MeasureTheory Asymptotics Filter
open scoped Chebyshev

namespace Aristotle.ThetaToPiLiTransferInfra

/-- Prime-counting partial summation identity in project notation. -/
lemma primeCounting_eq_theta_div_log_add_integral (x : ℝ) (hx : 2 ≤ x) :
    (Nat.primeCounting (Nat.floor x) : ℝ) =
      chebyshevTheta x / Real.log x
        + ∫ t in Set.Icc 2 x, chebyshevTheta t / (t * (Real.log t) ^ 2) := by
  have h := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  simpa [chebyshevTheta] using h

/-- Integration-by-parts formula for `li` in project notation. -/
lemma logarithmicIntegral_eq_main_plus_correction (x : ℝ) (hx : 2 < x) :
    LogarithmicIntegral.logarithmicIntegral x =
      x / Real.log x - 2 / Real.log 2
        + ∫ t in Set.Icc 2 x, 1 / (Real.log t) ^ 2 := by
  have h :=
    LogarithmicIntegral.logarithmicIntegral_integration_by_parts (x := x) hx
  simpa [LogarithmicIntegral.logarithmicIntegral, integral_Icc_eq_integral_Ioc] using h

/-- The non-main-term contribution in the θ-to-(π-li) decomposition. -/
noncomputable def thetaPiLiRemainder (x : ℝ) : ℝ :=
  (2 / Real.log 2)
    + (∫ t in Set.Icc 2 x, chebyshevTheta t / (t * (Real.log t) ^ 2))
    - (∫ t in Set.Icc 2 x, 1 / (Real.log t) ^ 2)

/-- Psi-analogue of `thetaPiLiRemainder`, used to isolate the `ψ-θ` correction term. -/
noncomputable def psiPiLiRemainder (x : ℝ) : ℝ :=
  (2 / Real.log 2)
    + (∫ t in Set.Icc 2 x, chebyshevPsi t / (t * (Real.log t) ^ 2))
    - (∫ t in Set.Icc 2 x, 1 / (Real.log t) ^ 2)

/-- The correction term between the psi-based and theta-based remainders. -/
noncomputable def psiThetaCorrection (x : ℝ) : ℝ :=
  (∫ t in Set.Icc 2 x, chebyshevPsi t / (t * (Real.log t) ^ 2))
    - (∫ t in Set.Icc 2 x, chebyshevTheta t / (t * (Real.log t) ^ 2))

/-- Exact split: theta remainder = psi remainder - psi/theta correction. -/
theorem thetaPiLiRemainder_eq_psi_split (x : ℝ) :
    thetaPiLiRemainder x = psiPiLiRemainder x - psiThetaCorrection x := by
  simp [thetaPiLiRemainder, psiPiLiRemainder, psiThetaCorrection]
  ring

/-- If the psi-based remainder and psi/theta correction are both little-o at scale `g`,
then the theta-based remainder is little-o at the same scale. -/
theorem thetaPiLiRemainder_isLittleO_of_psi_split
    {g : ℝ → ℝ}
    (hpsi : psiPiLiRemainder =o[atTop] g)
    (hcorr : psiThetaCorrection =o[atTop] g) :
    thetaPiLiRemainder =o[atTop] g := by
  have hEq :
      thetaPiLiRemainder = (fun x => psiPiLiRemainder x - psiThetaCorrection x) := by
    funext x
    exact thetaPiLiRemainder_eq_psi_split x
  rw [hEq]
  exact hpsi.sub hcorr

/-- Exact decomposition of `π(x) - li(x)` into main term plus remainder. -/
theorem pi_li_eq_theta_main_plus_remainder (x : ℝ) (hx : 2 < x) :
    (Nat.primeCounting (Nat.floor x) : ℝ) - LogarithmicIntegral.logarithmicIntegral x
      = (chebyshevTheta x - x) / Real.log x + thetaPiLiRemainder x := by
  have hpi := primeCounting_eq_theta_div_log_add_integral x (le_of_lt hx)
  have hli := logarithmicIntegral_eq_main_plus_correction x hx
  set A : ℝ := chebyshevTheta x / Real.log x
  set B : ℝ := x / Real.log x
  set C : ℝ := 2 / Real.log 2
  set Iθ : ℝ := ∫ t in Set.Icc 2 x, chebyshevTheta t / (t * (Real.log t) ^ 2)
  set I1 : ℝ := ∫ t in Set.Icc 2 x, 1 / (Real.log t) ^ 2
  have hAB : (chebyshevTheta x - x) / Real.log x = A - B := by
    simp [A, B]
    ring
  rw [hpi, hli, thetaPiLiRemainder]
  rw [hAB]
  simp [A, B, C, Iθ, I1]
  ring

/-- `Ω₊` transfer for division by `log x` on the comparison scale. -/
lemma omegaPlus_div_log {f : ℝ → ℝ}
    (h : (fun x => chebyshevTheta x - x) =Ω₊[f]) :
    (fun x => (chebyshevTheta x - x) / Real.log x) =Ω₊[fun x => f x / Real.log x] := by
  rcases h with ⟨c, hc, hfreq⟩
  refine ⟨c, hc, ?_⟩
  refine (Filter.Frequently.and_eventually hfreq (Filter.eventually_gt_atTop (1 : ℝ))).mono ?_
  intro x hx
  have hlog : 0 < Real.log x := Real.log_pos hx.2
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt hlog
  have hdiv : (chebyshevTheta x - x) / Real.log x ≥ (c * f x) / Real.log x := by
    field_simp [hlog_ne]
    exact hx.1
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- `Ω₋` transfer for division by `log x` on the comparison scale. -/
lemma omegaMinus_div_log {f : ℝ → ℝ}
    (h : (fun x => chebyshevTheta x - x) =Ω₋[f]) :
    (fun x => (chebyshevTheta x - x) / Real.log x) =Ω₋[fun x => f x / Real.log x] := by
  rcases h with ⟨c, hc, hfreq⟩
  refine ⟨c, hc, ?_⟩
  refine (Filter.Frequently.and_eventually hfreq (Filter.eventually_gt_atTop (1 : ℝ))).mono ?_
  intro x hx
  have hlog : 0 < Real.log x := Real.log_pos hx.2
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt hlog
  have hdiv : (chebyshevTheta x - x) / Real.log x ≤ (-c * f x) / Real.log x := by
    field_simp [hlog_ne]
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hx.1
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- If `thetaPiLiRemainder` is little-o at the canonical `√x/log x` scale, then
it is little-o at every larger scale `f/log x` with `f ≥ √x` eventually. -/
theorem remainder_isLittleO_of_sqrt
    (hrem : thetaPiLiRemainder =o[atTop] (fun x => Real.sqrt x / Real.log x))
    {f : ℝ → ℝ}
    (hf : ∀ᶠ x in atTop, Real.sqrt x ≤ f x) :
    thetaPiLiRemainder =o[atTop] (fun x => f x / Real.log x) := by
  have hcmp : (fun x => Real.sqrt x / Real.log x) =O[atTop] (fun x => f x / Real.log x) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    refine (Filter.Eventually.and hf (Filter.eventually_gt_atTop (1 : ℝ))).mono ?_
    intro x hx
    have hlog_pos : 0 < Real.log x := Real.log_pos hx.2
    have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hf_nonneg : 0 ≤ f x := le_trans hsqrt_nonneg hx.1
    have hdiv :
        Real.sqrt x / Real.log x ≤ f x / Real.log x :=
      div_le_div_of_nonneg_right hx.1 (le_of_lt hlog_pos)
    have hnorm_left :
        ‖Real.sqrt x / Real.log x‖ = Real.sqrt x / Real.log x := by
      exact Real.norm_of_nonneg (div_nonneg hsqrt_nonneg (le_of_lt hlog_pos))
    have hnorm_right :
        ‖f x / Real.log x‖ = f x / Real.log x := by
      exact Real.norm_of_nonneg (div_nonneg hf_nonneg (le_of_lt hlog_pos))
    calc
      ‖Real.sqrt x / Real.log x‖
          = Real.sqrt x / Real.log x := hnorm_left
      _ ≤ f x / Real.log x := hdiv
      _ = ‖f x / Real.log x‖ := hnorm_right.symm
      _ = (1 : ℝ) * ‖f x / Real.log x‖ := by ring
  exact hrem.trans_isBigO hcmp

/-- If the remainder in the θ→(π-li) decomposition is little-o of `f/log`,
then θ-oscillation at scale `f` transfers to π-li oscillation at scale `f/log`. -/
theorem omega_theta_to_pi_li_of_remainder_isLittleO
    (f : ℝ → ℝ)
    (hf : ∀ᶠ x in atTop, Real.sqrt x ≤ f x)
    (hθ : (fun x => chebyshevTheta x - x) =Ω±[f])
    (hrem : thetaPiLiRemainder =o[atTop] (fun x => f x / Real.log x)) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - LogarithmicIntegral.logarithmicIntegral x)
      =Ω±[fun x => f x / Real.log x] := by
  have hmain : (fun x => (chebyshevTheta x - x) / Real.log x) =Ω±[fun x => f x / Real.log x] := by
    exact ⟨omegaPlus_div_log hθ.1, omegaMinus_div_log hθ.2⟩
  have hg_nonneg : ∀ᶠ x in atTop, 0 ≤ f x / Real.log x := by
    refine (Filter.Eventually.and hf (Filter.eventually_gt_atTop (1 : ℝ))).mono ?_
    intro x hx
    exact div_nonneg (le_trans (Real.sqrt_nonneg x) hx.1) (Real.log_nonneg hx.2.le)
  have hsum :
      (fun x => (chebyshevTheta x - x) / Real.log x + thetaPiLiRemainder x)
        =Ω±[fun x => f x / Real.log x] := by
    exact hmain.add_isLittleO hrem hg_nonneg
  have hEq :
      ∀ᶠ x in atTop,
        (Nat.primeCounting (Nat.floor x) : ℝ) - LogarithmicIntegral.logarithmicIntegral x
          = (chebyshevTheta x - x) / Real.log x + thetaPiLiRemainder x := by
    refine (Filter.eventually_gt_atTop (2 : ℝ)).mono ?_
    intro x hx
    exact pi_li_eq_theta_main_plus_remainder x hx
  rcases hsum with ⟨hplus, hminus⟩
  refine ⟨?_, ?_⟩
  · rcases hplus with ⟨c, hc, hfreq⟩
    refine ⟨c, hc, ?_⟩
    refine (Filter.Frequently.and_eventually hfreq hEq).mono ?_
    intro x hx
    simpa [hx.2] using hx.1
  · rcases hminus with ⟨c, hc, hfreq⟩
    refine ⟨c, hc, ?_⟩
    refine (Filter.Frequently.and_eventually hfreq hEq).mono ?_
    intro x hx
    simpa [hx.2] using hx.1

end Aristotle.ThetaToPiLiTransferInfra
