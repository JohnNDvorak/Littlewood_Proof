import Littlewood.Basic.OmegaNotation
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.Aristotle.PsiThetaCanonicalBound
import Littlewood.Aristotle.ThetaToPiLiTransferInfra
import Littlewood.ExplicitFormulas.ConversionFormulas

noncomputable section

open Real Filter Asymptotics
open scoped Chebyshev

namespace Aristotle.Standalone.PsiThetaLllTransfer

open GrowthDomination
open Aristotle.PsiThetaCanonicalBound
open Aristotle.ThetaToPiLiTransferInfra
open Conversion

/-- The square-root scale is negligible compared with `sqrt(x) * lll(x)`. -/
theorem sqrt_isLittleO_sqrt_mul_lll :
    (fun x => Real.sqrt x) =o[atTop] (fun x => Real.sqrt x * lll x) := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [eventually_ge_lll_const (1 / c)] with x hlll
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hlll_nonneg : 0 ≤ lll x := le_trans (by positivity) hlll
  have hcg : 1 ≤ c * lll x := by
    have := mul_le_mul_of_nonneg_left hlll (le_of_lt hc)
    simpa [hc.ne'] using this
  calc
    ‖Real.sqrt x‖ = Real.sqrt x := Real.norm_of_nonneg hsqrt_nonneg
    _ ≤ (c * lll x) * Real.sqrt x := by
          exact le_mul_of_one_le_left hsqrt_nonneg hcg
    _ = c * (Real.sqrt x * lll x) := by ring
    _ = c * ‖Real.sqrt x * lll x‖ := by
          rw [Real.norm_of_nonneg (mul_nonneg hsqrt_nonneg hlll_nonneg)]

/-- The prime-power correction is little-o at the Littlewood scale. -/
theorem theta_sub_psi_isLittleO_sqrt_mul_lll :
    (fun x => chebyshevTheta x - chebyshevPsi x) =o[atTop]
      (fun x => Real.sqrt x * lll x) := by
  have hsqrt :
      (fun x => chebyshevTheta x - chebyshevPsi x) =O[atTop]
        (fun x => Real.sqrt x) := by
    convert chebyshevPsi_sub_chebyshevTheta_isBigO_sqrt.neg_left using 1
    ext x
    ring
  exact hsqrt.trans_isLittleO sqrt_isLittleO_sqrt_mul_lll

/-- At Littlewood's `sqrt(x) * lll(x)` scale, the `psi -> theta` transfer is
honest: the prime-power correction is negligible. -/
theorem omega_psi_to_theta_lll
    (hpsi :
      (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x]) :
    (fun x => chebyshevTheta x - x) =Ω±[fun x => Real.sqrt x * lll x] := by
  have hsum :=
    hpsi.add_isLittleO theta_sub_psi_isLittleO_sqrt_mul_lll
      sqrt_mul_lll_eventually_nonneg
  convert hsum using 1
  ext x
  ring

/-- The Littlewood-scale RH `ψ -> π-li` transfer, routed through the already
live generic `θ -> π-li` conversion. -/
theorem omega_theta_to_pi_li_lll_of_remainder
    (htheta :
      (fun x => chebyshevTheta x - x) =Ω±[fun x => Real.sqrt x * lll x])
    (hrem :
      thetaPiLiRemainder =o[atTop] (fun x => Real.sqrt x / Real.log x)) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  have hrem_lll :
      thetaPiLiRemainder =o[atTop]
        (fun x => (Real.sqrt x * lll x) / Real.log x) :=
    remainder_isLittleO_of_sqrt hrem sqrt_eventually_le_sqrt_mul_lll
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (omega_theta_to_pi_li_of_remainder_isLittleO
      (f := fun x => Real.sqrt x * lll x)
      sqrt_eventually_le_sqrt_mul_lll htheta hrem_lll)

/-- The Littlewood-scale RH `ψ -> π-li` transfer with the exact Step 5
remainder theorem as an explicit input. -/
theorem omega_psi_to_pi_li_lll_of_remainder
    (hpsi :
      (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x])
    (hrem :
      thetaPiLiRemainder =o[atTop] (fun x => Real.sqrt x / Real.log x)) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  exact omega_theta_to_pi_li_lll_of_remainder (omega_psi_to_theta_lll hpsi) hrem

/-- The Littlewood-scale RH `ψ -> π-li` transfer, routed through the already
live generic `θ -> π-li` conversion. -/
theorem omega_psi_to_pi_li_lll [OmegaThetaToPiLiHyp]
    (hpsi :
      (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x]) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (omega_theta_to_pi_li (f := fun x => Real.sqrt x * lll x)
      sqrt_eventually_le_sqrt_mul_lll (omega_psi_to_theta_lll hpsi))

end Aristotle.Standalone.PsiThetaLllTransfer
