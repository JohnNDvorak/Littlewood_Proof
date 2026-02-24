import Littlewood.Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
import Littlewood.Aristotle.Standalone.RHPiZeroSumAlignmentBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiTargetPhaseArgReduction

open Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiPerronTowerWitness
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge

private lemma mem_zero_finset_nontrivial
    {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (finite_zeros_le T).toFinset) :
    ρ ∈ zetaNontrivialZeros := by
  have hz : ρ ∈ zerosUpTo T := by
    simpa using hρ
  have hz' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
    simpa [zerosUpTo] using hz
  exact (mem_zetaNontrivialZerosPos.1 hz'.1).1

private lemma zero_ne_zero_of_mem_zero_finset
    {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (finite_zeros_le T).toFinset) :
    ρ ≠ 0 := by
  have hρz : ρ ∈ zetaNontrivialZeros := mem_zero_finset_nontrivial hρ
  have hre_pos : 0 < ρ.re := hρz.2.1
  intro h0
  have : (0 : ℝ) < 0 := by
    simpa [h0] using hre_pos
  exact (lt_irrefl 0) this

/-- Unit direction of a nonzero complex number in argument form. -/
lemma unit_dir_eq_exp_arg
    {ρ : ℂ} (hρ : ρ ≠ 0) :
    ρ / ‖ρ‖ = Complex.exp (Complex.arg ρ * Complex.I) := by
  have hnorm : ((‖ρ‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hρ)
  apply (div_eq_iff hnorm).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (Complex.norm_mul_exp_arg_mul_I ρ).symm

/-- Distance between two unit complex exponentials is controlled by distance of
angles. -/
lemma norm_exp_I_sub_exp_I_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ ‖a - b‖ := by
  have hmul :
      Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)
        = Complex.exp (b * Complex.I) *
          (Complex.exp ((a - b) * Complex.I) - 1) := by
    calc
      Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)
          = Complex.exp ((b + (a - b)) * Complex.I) - Complex.exp (b * Complex.I) := by
              congr 1
              ring
      _ = Complex.exp (b * Complex.I + (a - b) * Complex.I) - Complex.exp (b * Complex.I) := by
            congr 1
            ring
      _ = Complex.exp (b * Complex.I) * Complex.exp ((a - b) * Complex.I)
            - Complex.exp (b * Complex.I) := by
              rw [Complex.exp_add]
      _ = Complex.exp (b * Complex.I) * (Complex.exp ((a - b) * Complex.I) - 1) := by
            ring
  calc
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖
        = ‖Complex.exp (b * Complex.I) *
            (Complex.exp ((a - b) * Complex.I) - 1)‖ := by
              rw [hmul]
    _ = ‖Complex.exp (Complex.I * b)‖ * ‖Complex.exp (Complex.I * (a - b)) - 1‖ :=
          by simpa [mul_comm] using (norm_mul (Complex.exp (b * Complex.I))
            (Complex.exp ((a - b) * Complex.I) - 1))
    _ = ‖Complex.exp (Complex.I * (a - b)) - 1‖ := by
          simp [Complex.norm_exp_I_mul_ofReal]
    _ ≤ ‖a - b‖ := by
          simpa using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

/-- Target-phase closeness from a real argument approximation modulo `2π`. -/
lemma phase_close_target_of_arg_approx
    {ρ : ℂ} (hρ : ρ ≠ 0)
    {θ ε : ℝ} {k : ℤ}
    (hθ : ‖θ - Complex.arg ρ - k • (2 * Real.pi)‖ ≤ ε) :
    ‖Complex.exp (θ * Complex.I) - ρ / ‖ρ‖‖ ≤ ε := by
  have hperiod :
      Complex.exp (θ * Complex.I)
        = Complex.exp ((θ - k • (2 * Real.pi)) * Complex.I) := by
    have hperiodC :
        Complex.exp (((θ : ℂ) - k • (2 * (Real.pi : ℂ))) * Complex.I)
          = Complex.exp ((θ : ℂ) * Complex.I) := by
      simpa using (Complex.exp_mul_I_periodic.sub_zsmul_eq (x := (θ : ℂ)) (n := k))
    simpa [Complex.ofReal_zsmul, mul_comm, mul_left_comm, mul_assoc] using hperiodC.symm
  calc
    ‖Complex.exp (θ * Complex.I) - ρ / ‖ρ‖‖
        = ‖Complex.exp ((θ - k • (2 * Real.pi)) * Complex.I)
            - Complex.exp (Complex.arg ρ * Complex.I)‖ := by
              rw [hperiod, unit_dir_eq_exp_arg hρ]
    _ ≤ ‖(θ - k • (2 * Real.pi)) - Complex.arg ρ‖ :=
          by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            (norm_exp_I_sub_exp_I_le (θ - k • (2 * Real.pi)) (Complex.arg ρ))
    _ = ‖θ - Complex.arg ρ - k • (2 * Real.pi)‖ := by
          ring
    _ ≤ ε := hθ

/-- Anti-target direction in argument form. -/
lemma neg_unit_dir_eq_exp_arg_add_pi
    {ρ : ℂ} (hρ : ρ ≠ 0) :
    -(ρ / ‖ρ‖) = Complex.exp ((Complex.arg ρ + Real.pi) * Complex.I) := by
  calc
    -(ρ / ‖ρ‖) = (-1 : ℂ) * (ρ / ‖ρ‖) := by ring
    _ = Complex.exp (Real.pi * Complex.I) * Complex.exp (Complex.arg ρ * Complex.I) := by
          rw [unit_dir_eq_exp_arg hρ]
          simp [Complex.exp_mul_I]
    _ = Complex.exp ((Complex.arg ρ + Real.pi) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          ring

/-- Anti-target phase closeness from a real argument approximation modulo `2π`. -/
lemma phase_close_antitarget_of_arg_approx
    {ρ : ℂ} (hρ : ρ ≠ 0)
    {θ ε : ℝ} {k : ℤ}
    (hθ : ‖θ - (Complex.arg ρ + Real.pi) - k • (2 * Real.pi)‖ ≤ ε) :
    ‖Complex.exp (θ * Complex.I) - (-(ρ / ‖ρ‖))‖ ≤ ε := by
  have hperiod :
      Complex.exp (θ * Complex.I)
        = Complex.exp ((θ - k • (2 * Real.pi)) * Complex.I) := by
    have hperiodC :
        Complex.exp (((θ : ℂ) - k • (2 * (Real.pi : ℂ))) * Complex.I)
          = Complex.exp ((θ : ℂ) * Complex.I) := by
      simpa using (Complex.exp_mul_I_periodic.sub_zsmul_eq (x := (θ : ℂ)) (n := k))
    simpa [Complex.ofReal_zsmul, mul_comm, mul_left_comm, mul_assoc] using hperiodC.symm
  calc
    ‖Complex.exp (θ * Complex.I) - (-(ρ / ‖ρ‖))‖
        = ‖Complex.exp ((θ - k • (2 * Real.pi)) * Complex.I)
            - Complex.exp ((Complex.arg ρ + Real.pi) * Complex.I)‖ := by
              rw [hperiod, neg_unit_dir_eq_exp_arg_add_pi hρ]
    _ ≤ ‖(θ - k • (2 * Real.pi)) - (Complex.arg ρ + Real.pi)‖ :=
          by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            (norm_exp_I_sub_exp_I_le (θ - k • (2 * Real.pi)) (Complex.arg ρ + Real.pi))
    _ = ‖θ - (Complex.arg ρ + Real.pi) - k • (2 * Real.pi)‖ := by
          ring
    _ ≤ ε := hθ

/-- Rewrite `x^(I*y)` on positive reals as an exponential phase. -/
lemma cpow_I_im_eq_exp_I_log_mul
    {x y : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ (Complex.I * y))
      = Complex.exp ((Real.log x * y) * Complex.I) := by
  have hxne : (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hxne]
  rw [← Complex.ofReal_log (le_of_lt hx)]
  congr 1
  ring

/-- Target phase closeness from a logarithmic argument approximation. -/
lemma target_phase_close_of_log_arg_approx
    {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    {ε : ℝ} {k : ℤ}
    (hθ : ‖Real.log x * ρ.im - Complex.arg ρ - k • (2 * Real.pi)‖ ≤ ε) :
    ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε := by
  rw [cpow_I_im_eq_exp_I_log_mul hx]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (phase_close_target_of_arg_approx (ρ := ρ) hρ (θ := Real.log x * ρ.im) (k := k) hθ)

/-- Anti-target phase closeness from a logarithmic argument approximation. -/
lemma antitarget_phase_close_of_log_arg_approx
    {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    {ε : ℝ} {k : ℤ}
    (hθ : ‖Real.log x * ρ.im - (Complex.arg ρ + Real.pi) - k • (2 * Real.pi)‖ ≤ ε) :
    ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε := by
  rw [cpow_I_im_eq_exp_I_log_mul hx]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (phase_close_antitarget_of_arg_approx (ρ := ρ) hρ (θ := Real.log x * ρ.im) (k := k) hθ)

/-- Positive constructive goal recast with real argument approximations. -/
abbrev TargetTowerArgApproxFamily : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    1 < x ∧
    |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤
      Real.sqrt x / Real.log x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ∃ k : ℤ,
          ‖Real.log x * ρ.im - Complex.arg ρ - k • (2 * Real.pi)‖ ≤ ε) ∧
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))))

/-- Negative constructive goal recast with real argument approximations. -/
abbrev AntiTargetTowerArgApproxFamily : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    1 < x ∧
    |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤
      Real.sqrt x / Real.log x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ∃ k : ℤ,
          ‖Real.log x * ρ.im - (Complex.arg ρ + Real.pi) - k • (2 * Real.pi)‖ ≤ ε) ∧
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))))

/-- Convert positive argument-approximation data into the exact positive
phase-coupling family. -/
theorem targetTowerPhaseCouplingFamily_of_argApprox
    (hTargetArg : TargetTowerArgApproxFamily) :
    TargetTowerPhaseCouplingFamily := by
  intro hRH X
  rcases hTargetArg hRH X with
    ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, harg, hxUpper⟩
  refine ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, ?_, hxUpper⟩
  intro ρ hρ
  rcases harg ρ hρ with ⟨k, hk⟩
  have hρne : ρ ≠ 0 := zero_ne_zero_of_mem_zero_finset hρ
  exact target_phase_close_of_log_arg_approx (lt_trans zero_lt_one hx1) hρne hk

/-- Convert negative argument-approximation data into the exact negative
phase-coupling family. -/
theorem antiTargetTowerPhaseCouplingFamily_of_argApprox
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily) :
    AntiTargetTowerPhaseCouplingFamily := by
  intro hRH X
  rcases hAntiTargetArg hRH X with
    ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, harg, hxUpper⟩
  refine ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, ?_, hxUpper⟩
  intro ρ hρ
  rcases harg ρ hρ with ⟨k, hk⟩
  have hρne : ρ ≠ 0 := zero_ne_zero_of_mem_zero_finset hρ
  exact antitarget_phase_close_of_log_arg_approx (lt_trans zero_lt_one hx1) hρne hk

/-- Class-level packaging from the positive argument-approximation family. -/
theorem targetTowerPhaseCouplingFamilyHyp_of_argApprox
    (hTargetArg : TargetTowerArgApproxFamily) :
    TargetTowerPhaseCouplingFamilyHyp :=
  ⟨targetTowerPhaseCouplingFamily_of_argApprox hTargetArg⟩

/-- Class-level packaging from the negative argument-approximation family. -/
theorem antiTargetTowerPhaseCouplingFamilyHyp_of_argApprox
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily) :
    AntiTargetTowerPhaseCouplingFamilyHyp :=
  ⟨antiTargetTowerPhaseCouplingFamily_of_argApprox hAntiTargetArg⟩

/-- Typeclass payload for the positive real-argument approximation family. -/
class TargetTowerArgApproxFamilyHyp : Prop where
  witness : TargetTowerArgApproxFamily

/-- Typeclass payload for the negative real-argument approximation family. -/
class AntiTargetTowerArgApproxFamilyHyp : Prop where
  witness : AntiTargetTowerArgApproxFamily

/-- Package a positive argument-approximation witness family as a typeclass
payload. -/
theorem targetTowerArgApproxFamilyHyp_of_witness
    (hTargetArg : TargetTowerArgApproxFamily) :
    TargetTowerArgApproxFamilyHyp :=
  ⟨hTargetArg⟩

/-- Package a negative argument-approximation witness family as a typeclass
payload. -/
theorem antiTargetTowerArgApproxFamilyHyp_of_witness
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily) :
    AntiTargetTowerArgApproxFamilyHyp :=
  ⟨hAntiTargetArg⟩

/-- Reverse packaging: a typeclass payload for the positive argument-approximation
family yields a `Fact` on the underlying witness proposition. -/
instance (priority := 100)
    [TargetTowerArgApproxFamilyHyp] :
    Fact TargetTowerArgApproxFamily :=
  ⟨TargetTowerArgApproxFamilyHyp.witness⟩

/-- Reverse packaging: a typeclass payload for the negative
argument-approximation family yields a `Fact` on the underlying witness
proposition. -/
instance (priority := 100)
    [AntiTargetTowerArgApproxFamilyHyp] :
    Fact AntiTargetTowerArgApproxFamily :=
  ⟨AntiTargetTowerArgApproxFamilyHyp.witness⟩

/-- Low-priority instance: a positive argument-approximation witness carried as
`Fact` yields the corresponding payload class. -/
instance (priority := 100)
    [Fact TargetTowerArgApproxFamily] :
    TargetTowerArgApproxFamilyHyp :=
  targetTowerArgApproxFamilyHyp_of_witness Fact.out

/-- Low-priority instance: a negative argument-approximation witness carried as
`Fact` yields the corresponding payload class. -/
instance (priority := 100)
    [Fact AntiTargetTowerArgApproxFamily] :
    AntiTargetTowerArgApproxFamilyHyp :=
  antiTargetTowerArgApproxFamilyHyp_of_witness Fact.out

/-- Instance bridge: positive argument-approximation payload implies
`TargetTowerPhaseCouplingFamilyHyp`. -/
instance
    [TargetTowerArgApproxFamilyHyp] :
    TargetTowerPhaseCouplingFamilyHyp where
  witness :=
    targetTowerPhaseCouplingFamily_of_argApprox
      TargetTowerArgApproxFamilyHyp.witness

/-- Instance bridge: negative argument-approximation payload implies
`AntiTargetTowerPhaseCouplingFamilyHyp`. -/
instance
    [AntiTargetTowerArgApproxFamilyHyp] :
    AntiTargetTowerPhaseCouplingFamilyHyp where
  witness :=
    antiTargetTowerPhaseCouplingFamily_of_argApprox
      AntiTargetTowerArgApproxFamilyHyp.witness

/-- End-to-end RH-`pi` witness from the two real argument-approximation
families. -/
theorem rhPiWitnessData_of_argApprox
    (hTargetArg : TargetTowerArgApproxFamily)
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily) :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  exact rhPiWitnessData_of_perron_and_phase_payloads
    (targetTowerPhaseCouplingFamily_of_argApprox hTargetArg)
    (antiTargetTowerPhaseCouplingFamily_of_argApprox hAntiTargetArg)

/-- End-to-end typeclass endpoint built from explicit witness-family goals. -/
theorem rhPiWitnessData_of_argApproxGoals
    (hTargetArg : TargetTowerArgApproxFamily)
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily) :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  letI : TargetTowerArgApproxFamilyHyp :=
    targetTowerArgApproxFamilyHyp_of_witness hTargetArg
  letI : AntiTargetTowerArgApproxFamilyHyp :=
    antiTargetTowerArgApproxFamilyHyp_of_witness hAntiTargetArg
  exact rhPiWitnessData_of_perron_and_phase_payloads
    TargetTowerPhaseCouplingFamilyHyp.witness
    AntiTargetTowerPhaseCouplingFamilyHyp.witness

/-- Typeclass endpoint: once argument-approximation payload classes are
instantiated, RH-`pi` witness data follows automatically. -/
theorem rhPiWitnessData_of_argApproxHyp
    [TargetTowerArgApproxFamilyHyp]
    [AntiTargetTowerArgApproxFamilyHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  exact rhPiWitnessData_of_perron_and_phase_payloads
    TargetTowerPhaseCouplingFamilyHyp.witness
    AntiTargetTowerPhaseCouplingFamilyHyp.witness

/-- `Fact` endpoint: once the two argument-approximation witness propositions
are available as facts, RH-`pi` witness data follows directly. -/
theorem rhPiWitnessData_of_argApproxFacts
    [Fact TargetTowerArgApproxFamily]
    [Fact AntiTargetTowerArgApproxFamily] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  exact rhPiWitnessData_of_argApproxHyp

end Aristotle.Standalone.RHPiTargetPhaseArgReduction
