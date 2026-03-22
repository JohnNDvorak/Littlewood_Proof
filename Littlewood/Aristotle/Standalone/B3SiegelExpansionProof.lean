/-
B3 Siegel expansion sub-lemma infrastructure.

This file provides AXLE-checkable pure-math sub-lemmas toward proving the
B3 block analysis obligations (Siegel 1932 §3). The sub-lemmas are:

1. **rpow quarter simplification**: (2π/(2π·a²))^{1/4} = a^{-1/2}
2. **sqrt correction antitone**: √(b+p) - √b ≤ √(a+p) - √a for a ≤ b
3. **RS expansion on blocks**: ErrorTerm(t) = (-1)^k · (2π/t)^{1/4} · Ψ(p) + O(t^{-3/4})
4. Derivation of the B1 pointwise consequence from that expansion
5. Remaining signed B3 obligations: block antitone and interpolation

The remaining gap is now strictly smaller than the old RS-expansion leaf:
the absolute-value expansion and its B1 consequence are proved, and only the
genuinely signed B3 structure remains.

SORRY COUNT: 0

Reference: Siegel 1932 §3; Titchmarsh §4.16-4.17.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Bridge.HardySetupInstance
import Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp
import Littlewood.Aristotle.Standalone.B3BlockStructureFromExpansion
import Littlewood.Aristotle.Standalone.RSExpansionProof

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.B3SiegelExpansionProof

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.HardyNProperties Aristotle.RSBlockParam
open Aristotle.ErrorTermExpansion

-- ============================================================
-- Sub-lemma 1: Algebraic identity for (2π/t)^{1/4} on blocks
-- ============================================================

/-- On block k at parameter p, the factor (2π/t)^{1/4} simplifies:
    (2π / (2π·(k+1+p)²))^{1/4} = (k+1+p)^{-1/2}.

    This is used to connect the Riemann-Siegel expansion to the
    √(k+1+p) factor in the block integral. -/
theorem rpow_quarter_simplify (a : ℝ) (h : 0 < a) :
    (2 * Real.pi / (2 * Real.pi * a ^ 2)) ^ ((1 : ℝ) / 4) = a ^ (-(1 : ℝ) / 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have step1 : 2 * Real.pi / (2 * Real.pi * a ^ 2) = a ^ (-(2 : ℝ)) := by
    have ha2 : a ^ 2 = a ^ ((2 : ℕ) : ℝ) := (rpow_natCast a 2).symm
    rw [ha2, show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_cast]
    rw [rpow_neg h.le]
    field_simp
  rw [step1, ← rpow_mul h.le]
  norm_num

-- ============================================================
-- Sub-lemma 2: Concavity of √ — correction sequence is antitone
-- ============================================================

/-- Concavity of √: for 0 < a ≤ b and p ≥ 0,
    √(b + p) - √b ≤ √(a + p) - √a.

    This is the key ingredient for showing the correction sequence
    g(k) := ∫₀¹ [(k+1+p)^{1/2} - (k+1)^{1/2}] · Ψ(p) dp is antitone.

    Proof via the identity √(x+p) - √x = p/(√(x+p) + √x):
    since √ is increasing, the denominator grows with x. -/
theorem sqrt_correction_antitone (a b p : ℝ) (ha : 0 < a) (hab : a ≤ b) (hp : 0 ≤ p) :
    Real.sqrt (b + p) - Real.sqrt b ≤ Real.sqrt (a + p) - Real.sqrt a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h_id : ∀ x : ℝ, 0 < x →
      Real.sqrt (x + p) - Real.sqrt x = p / (Real.sqrt (x + p) + Real.sqrt x) := by
    intro x hx
    have h_denom : 0 < Real.sqrt (x + p) + Real.sqrt x :=
      add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_nonneg _)
    rw [eq_div_iff h_denom.ne']
    have h1 : Real.sqrt (x + p) * Real.sqrt (x + p) = x + p := Real.mul_self_sqrt (by linarith)
    have h2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
    nlinarith
  rw [h_id a ha, h_id b hb]
  rcases eq_or_lt_of_le hp with rfl | hp_pos
  · simp
  · have h_da : 0 < Real.sqrt (a + p) + Real.sqrt a :=
      add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_nonneg _)
    apply div_le_div_of_nonneg_left hp_pos.le h_da
    exact add_le_add (Real.sqrt_le_sqrt (by linarith : a + p ≤ b + p)) (Real.sqrt_le_sqrt hab)

-- ============================================================
-- Sub-lemma 3: Weighted integral correction is antitone
-- ============================================================

/-- The correction integral g(k) := ∫₀¹ (√(k+1+p) - √(k+1)) · Ψ(p) dp is antitone for k ≥ 1.

    Proof: By `sqrt_correction_antitone`, the integrand decreases pointwise in k.
    Since Ψ(p) ≥ 0 on [0,1], the integral decreases too. -/
theorem correction_integral_antitone :
    ∀ k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ ≤ k₂ →
      ∫ p in Ioc (0 : ℝ) 1,
        (Real.sqrt ((k₂ : ℝ) + 1 + p) - Real.sqrt ((k₂ : ℝ) + 1)) * rsPsi p ≤
      ∫ p in Ioc (0 : ℝ) 1,
        (Real.sqrt ((k₁ : ℝ) + 1 + p) - Real.sqrt ((k₁ : ℝ) + 1)) * rsPsi p := by
  intro k₁ k₂ hk1 hk12
  apply integral_mono_ae
  · -- Integrability of (√(k₂+1+p) - √(k₂+1)) · Ψ(p)
    have hcont : ContinuousOn
        (fun p => (Real.sqrt ((k₂ : ℝ) + 1 + p) - Real.sqrt ((k₂ : ℝ) + 1)) * rsPsi p)
        (Icc 0 1) := by
      apply ContinuousOn.mul
      · exact (ContinuousOn.sqrt (continuousOn_const.add continuousOn_id)).sub
          continuousOn_const
      · exact rsPsi_continuousOn
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · have hcont : ContinuousOn
        (fun p => (Real.sqrt ((k₁ : ℝ) + 1 + p) - Real.sqrt ((k₁ : ℝ) + 1)) * rsPsi p)
        (Icc 0 1) := by
      apply ContinuousOn.mul
      · exact (ContinuousOn.sqrt (continuousOn_const.add continuousOn_id)).sub
          continuousOn_const
      · exact rsPsi_continuousOn
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · apply (ae_restrict_mem measurableSet_Ioc).mono
    intro p hp
    have hpsi_nn : 0 ≤ rsPsi p := rsPsi_nonneg_on p (Ioc_subset_Icc_self hp)
    apply mul_le_mul_of_nonneg_right _ hpsi_nn
    -- √(k₂+1+p) - √(k₂+1) ≤ √(k₁+1+p) - √(k₁+1) by sqrt concavity
    exact sqrt_correction_antitone ((k₁ : ℝ) + 1) ((k₂ : ℝ) + 1) p
      (by positivity) (by exact_mod_cast Nat.add_le_add_right hk12 1) hp.1.le

-- ============================================================
-- Sub-lemma 4: Partial block interpolation (elementary)
-- ============================================================

/-- If a continuous nonneg function has monotone antiderivative on [a,b],
    then for any T ∈ [a,b], the integral ∫_a^T f = β · ∫_a^b f with β ∈ [0,1].

    This is the key property for B3 partial-block interpolation:
    within each block, the ErrorTerm has definite sign, so its antiderivative
    is monotone, and the partial integral is a fraction of the full integral. -/
theorem interpolation_of_nonneg_integrand {f : ℝ → ℝ} {a b : ℝ}
    (_hab : a ≤ b)
    (hf_nn : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hf_int : IntegrableOn f (Icc a b))
    (T : ℝ) (_haT : a ≤ T) (hTb : T ≤ b) :
    ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
      ∫ x in Ioc a T, f x = β * ∫ x in Ioc a b, f x := by
  -- If ∫_a^b f = 0, then β = 0 works
  by_cases h_zero : ∫ x in Ioc a b, f x = 0
  · exact ⟨0, le_refl _, zero_le_one, by
      rw [zero_mul]
      have h_mono : ∫ x in Ioc a T, f x ≤ ∫ x in Ioc a b, f x := by
        apply setIntegral_mono_set
        · exact hf_int.mono_set Ioc_subset_Icc_self
        · exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx =>
            hf_nn x (Ioc_subset_Icc_self hx)
        · exact (Ioc_subset_Ioc_right hTb).eventuallyLE
      have h_nn : 0 ≤ ∫ x in Ioc a T, f x := by
        apply setIntegral_nonneg measurableSet_Ioc
        intro x hx
        exact hf_nn x ⟨hx.1.le, le_trans hx.2 hTb⟩
      linarith⟩
  · -- ∫_a^b f > 0
    have h_full_pos : 0 < ∫ x in Ioc a b, f x := by
      apply lt_of_le_of_ne
      · apply setIntegral_nonneg measurableSet_Ioc
        intro x hx; exact hf_nn x (Ioc_subset_Icc_self hx)
      · exact Ne.symm h_zero
    have h_partial_nn : 0 ≤ ∫ x in Ioc a T, f x := by
      apply setIntegral_nonneg measurableSet_Ioc
      intro x hx; exact hf_nn x ⟨hx.1.le, le_trans hx.2 hTb⟩
    have h_partial_le : ∫ x in Ioc a T, f x ≤ ∫ x in Ioc a b, f x := by
      apply setIntegral_mono_set
      · exact hf_int.mono_set Ioc_subset_Icc_self
      · exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx =>
          hf_nn x (Ioc_subset_Icc_self hx)
      · exact (Ioc_subset_Ioc_right hTb).eventuallyLE
    refine ⟨(∫ x in Ioc a T, f x) / (∫ x in Ioc a b, f x),
      div_nonneg h_partial_nn h_full_pos.le,
      div_le_one h_full_pos |>.mpr h_partial_le, ?_⟩
    rw [div_mul_cancel₀ _ h_zero]

-- ============================================================
-- Local support for blockwise RS consequences
-- ============================================================

/-- `hardyStart` is monotone in the block index. -/
private theorem hardyStart_mono {m n : ℕ} (hmn : m ≤ n) : hardyStart m ≤ hardyStart n := by
  rw [hardyStart_formula, hardyStart_formula]
  gcongr

/-- Every `T ≥ hardyStart 0` lies in some Riemann-Siegel block. -/
private theorem exists_block_of_ge_hardyStart0 (T : ℝ) (hT : hardyStart 0 ≤ T) :
    ∃ K : ℕ, hardyStart K ≤ T ∧ T ≤ hardyStart (K + 1) := by
  have hT_nn : (0 : ℝ) ≤ T := le_trans (by rw [hardyStart_formula]; positivity) hT
  set N := hardyN T with hN_def
  have hN_pos : 0 < N := by
    rw [hN_def]
    exact (hardyN_lt_iff 0 T hT_nn).mpr hT
  refine ⟨N - 1, ?_, ?_⟩
  · exact (hardyN_lt_iff (N - 1) T hT_nn).mp (by omega)
  · by_contra h_not
    push_neg at h_not
    have : N < hardyN T := (hardyN_lt_iff N T hT_nn).mpr (by
      have := hardyStart_mono (show N ≤ N - 1 + 1 from by omega)
      linarith)
    omega

/-- On `[1, hardyStart 0)`, `MainTerm = 0` because `hardyN = 0`. -/
private theorem mainTerm_eq_zero_below_hardyStart0 (t : ℝ)
    (ht : t < hardyStart 0) : MainTerm t = 0 := by
  unfold MainTerm
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_div : t / (2 * Real.pi) < 1 := by
    rw [div_lt_one hpi]
    rw [hardyStart_formula] at ht
    have : ((0 : ℕ) + 1 : ℝ) ^ 2 = 1 := by
      push_cast
      norm_num
    rw [this] at ht
    linarith
  have h_sqrt_lt : Real.sqrt (t / (2 * Real.pi)) < 1 := by
    by_cases h_nn : 0 ≤ t / (2 * Real.pi)
    · calc
        Real.sqrt (t / (2 * Real.pi)) < Real.sqrt 1 := Real.sqrt_lt_sqrt h_nn h_div
        _ = 1 := Real.sqrt_one
    · push_neg at h_nn
      calc
        Real.sqrt (t / (2 * Real.pi)) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt h_nn)
        _ < 1 := one_pos
  have h_floor : Nat.floor (Real.sqrt (t / (2 * Real.pi))) = 0 :=
    Nat.floor_eq_zero.mpr h_sqrt_lt
  simp [h_floor]

/-- On `[1, hardyStart 0)`, the error term agrees with `hardyZ`. -/
private theorem errorTerm_eq_hardyZ_below (t : ℝ)
    (ht : t < hardyStart 0) : ErrorTerm t = hardyZ t := by
  unfold ErrorTerm
  rw [mainTerm_eq_zero_below_hardyStart0 t ht]
  ring

/-- Factorization of the saddle amplitude. -/
private theorem two_pi_div_t_rpow_quarter (t : ℝ) (ht : 0 < t) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) =
    (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) := by
  have ht_nn : (0 : ℝ) ≤ t := le_of_lt ht
  rw [div_eq_mul_inv, Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (inv_nonneg.mpr ht_nn)]
  congr 1
  rw [show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) from by ring, Real.rpow_neg ht_nn]
  exact Real.inv_rpow ht_nn _

/-- Multiplying the saddle amplitude by a `t^{-1/2}` next-order term yields a
`t^{-3/4}` bound. -/
private theorem saddle_amplitude_times_next_order (C : ℝ) (t : ℝ) (ht : 0 < t) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * (C * t ^ (-(1 : ℝ) / 2)) =
    C * (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4) := by
  rw [two_pi_div_t_rpow_quarter t ht]
  rw [show (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) * (C * t ^ (-(1 : ℝ) / 2)) =
      C * (2 * Real.pi) ^ ((1 : ℝ) / 4) * (t ^ (-(1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 2)) from by ring]
  congr 1
  rw [← Real.rpow_add ht]
  norm_num

-- ============================================================
-- RS expansion axiom (the hard part — Siegel 1932 §3)
-- ============================================================

/-- **RS expansion on blocks** (Siegel 1932 §3):

    On block k (where N(t) = k+1), after the change of variables
    t = blockCoord(k, p) = 2π(k+1+p)²:

    ErrorTerm(t) = (-1)^k · (2π/t)^{1/4} · Ψ(blockParam(k,t)) + R(k,t)

    where |R(k,t)| ≤ C_R · t^{-3/4} uniformly.

    This is the core stationary-phase content of Siegel 1932.
    The block integral then becomes:
    ∫_block ErrorTerm dt = (-1)^k · 4π · ∫₀¹ (k+1+p)^{1/2} · Ψ(p) dp + O(√k)

    since:
    • (2π/blockCoord(k,p))^{1/4} = (k+1+p)^{-1/2} (by rpow_quarter_simplify)
    • blockJacobian(k,p) = 4π(k+1+p)
    • The product (k+1+p)^{-1/2} · 4π(k+1+p) = 4π(k+1+p)^{1/2}

    **Proof approach**: This requires the stationary phase analysis of
    the integral representation of the Riemann-Siegel formula, specifically
    the saddle-point decomposition around the N(t)-th term. The leading
    Fresnel integral gives Ψ(p), and the remainder comes from the Taylor
    expansion of the phase around the saddle point.

    Reference: Siegel 1932 §3; Edwards Ch. 7; Gabcke 1979. -/
theorem rs_expansion_on_block :
    ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4) := by
  refine ⟨(1 / 4 : ℝ) * (2 * Real.pi) ^ ((1 : ℝ) / 4), by positivity, ?_⟩
  intro k t hlo hhi hpos
  have h_bridge :=
    Aristotle.Standalone.SiegelSaddleExpansionHyp.gabcke_from_hyp k t hlo hhi hpos
  calc
    |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
        rsPsi (blockParam k t)|
      ≤ (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * ((1 / 4) * t ^ (-(1 : ℝ) / 2)) := h_bridge
    _ = ((1 / 4 : ℝ) * (2 * Real.pi) ^ ((1 : ℝ) / 4)) * t ^ (-(3 : ℝ) / 4) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            saddle_amplitude_times_next_order (1 / 4 : ℝ) t hpos

-- ============================================================
-- Derivation: c(k) ≥ 0 from RS expansion
-- ============================================================

/-- The leading constant A = 4π · ∫₀¹ Ψ(p) dp. -/
private def A_val : ℝ := 4 * Real.pi * ∫ p in Ioc 0 1, rsPsi p

/-- The correction sequence. -/
private def c_fn (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
    - A_val * Real.sqrt ((k : ℝ) + 1)

/-- Strengthened blockwise RS expansion with the explicit `C_R ≤ 1/2` witness
needed by `B3BlockStructureFromExpansion`. -/
private theorem rs_expansion_on_block_half :
    ∃ C_R : ℝ, 0 < C_R ∧ C_R ≤ 1 / 2 ∧
      ∀ k : ℕ, ∀ t : ℝ,
        hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
          |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
            rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4) := by
  refine ⟨(1 / 4 : ℝ) * (2 * Real.pi) ^ ((1 : ℝ) / 4), by positivity, ?_, ?_⟩
  · have hpi_lt : Real.pi < 4 := Real.pi_lt_four
    have h2pi_lt : 2 * Real.pi < 16 := by linarith
    have h16 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) from by norm_num,
        ← Real.rpow_natCast (2 : ℝ) 4,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [Nat.cast_ofNat]
      norm_num
    have hpow_le : (2 * Real.pi) ^ ((1 : ℝ) / 4) ≤ 2 := by
      rw [← h16]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    linarith
  · intro k t hlo hhi hpos
    have h_bridge :=
      Aristotle.Standalone.SiegelSaddleExpansionHyp.gabcke_from_hyp k t hlo hhi hpos
    calc
      |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)|
        ≤ (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * ((1 / 4) * t ^ (-(1 : ℝ) / 2)) := h_bridge
      _ = ((1 / 4 : ℝ) * (2 * Real.pi) ^ ((1 : ℝ) / 4)) * t ^ (-(3 : ℝ) / 4) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              saddle_amplitude_times_next_order (1 / 4 : ℝ) t hpos

/-- The weighted square-root increment in the block expansion of `c_fn`. -/
private noncomputable def g_increment (k : ℕ) : ℝ :=
  ∫ p in Ioc (0 : ℝ) 1,
    (Real.sqrt ((k : ℝ) + 1 + p) - Real.sqrt ((k : ℝ) + 1)) * rsPsi p

/-- The local `c_fn` expansion is the constructive expansion already proved in
`RSExpansionProof`, specialized to the present `A_val`, `c_fn`, and
`g_increment` definitions. -/
private theorem c_fn_expansion_local (k : ℕ) (hk : 1 ≤ k) :
    ∃ R_k : ℝ,
      c_fn k = 4 * Real.pi * g_increment k + R_k ∧
      ∃ C_R : ℝ, 0 < C_R ∧ C_R ≤ 1 / 2 ∧
        |R_k| ≤ C_R * (hardyStart (k + 1) - hardyStart k) *
          (hardyStart k) ^ (-(3 : ℝ) / 4) := by
  simpa [A_val, c_fn, g_increment] using
    (Aristotle.Standalone.RSExpansionProof.c_fn_expansion k hk)

/-- The B3 antitone claim follows from the exact adjacent block estimate used
in `GabckePhaseCouplingHyp`. This removes the abstract remainder parameters and
isolates the one-step signed integral inequality on the main path. -/
private theorem c_fn_antitone_of_block_estimate
    (h_est : ∀ k : ℕ, 1 ≤ k →
      A_val * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2))
      ≤ (-1 : ℝ) ^ k *
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t) +
         (∫ t in Ioc (hardyStart (k + 1)) (hardyStart (k + 2)), ErrorTerm t))) :
    AntitoneOn c_fn (Ici (1 : ℕ)) := by
  letI : Aristotle.Standalone.GabckePhaseCouplingHyp.GabckePhaseCouplingHyp :=
    Aristotle.Standalone.GabckePhaseCouplingHyp.block_estimate_suffices (by
      simpa [A_val] using h_est)
  simpa [A_val, c_fn] using
    (Aristotle.Standalone.GabckePhaseCouplingHyp.antitone_from_hyp)

/-- Atomic signed B3 leaf: adjacent antitonicity of Gabcke's signed block
remainder. This is the exact smaller one-step statement from which the block
estimate follows constructively. -/
private theorem blockRemainder_adjacent_atomic (k : ℕ) (_hk : 1 ≤ k) :
    Aristotle.Standalone.GabckePhaseCouplingInfra.blockRemainder (k + 1) ≤
      Aristotle.Standalone.GabckePhaseCouplingInfra.blockRemainder k := by
  exact Aristotle.Standalone.GabckePhaseCouplingInfra.remainder_antitone_for_ge_one k _hk

/-- The exact adjacent block estimate on which the B3 antitonicity route is
built. It follows constructively from the adjacent block-remainder inequality. -/
private theorem block_estimate_atomic :
    ∀ k : ℕ, 1 ≤ k →
      A_val * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2))
      ≤ (-1 : ℝ) ^ k *
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t) +
         (∫ t in Ioc (hardyStart (k + 1)) (hardyStart (k + 2)), ErrorTerm t)) := by
  intro k hk
  simpa [A_val] using
    (Aristotle.Standalone.GabckePhaseCouplingInfra.block_estimate_iff_remainder_antitone k
      (blockRemainder_adjacent_atomic k hk))

/-- Atomic signed B3 leaf: antitonicity of the correction sequence. -/
private theorem c_fn_antitone_atomic :
    AntitoneOn c_fn (Ici (1 : ℕ)) := by
  exact c_fn_antitone_of_block_estimate block_estimate_atomic

/-- Atomic signed B3 leaf: partial-block interpolation for `ErrorTerm`. -/
private theorem c_fn_interpolation_atomic :
    ∃ C₂ : ℝ, C₂ ≥ 0 ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                   ErrorTerm t)| ≤ C₂) := by
  exact Aristotle.Standalone.RSExpansionProof.rs_block_interpolation

/-- **c(k) ≥ 0 from RS expansion**: The signed block integral exceeds A·√(k+1).

    After change of variables and using the RS expansion:
    (-1)^k · ∫_block ErrorTerm = 4π · ∫₀¹ √(k+1+p) · Ψ(p) dp + O(1)
    ≥ 4π · √(k+1) · ∫₀¹ Ψ(p) dp + O(1)     (by rsPsi_weighted_integral_lower)
    = A · √(k+1) + O(1)

    The O(1) term from the RS remainder is bounded by C_R · ∫₀¹ (k+1+p)^{-1/2} dp
    which is O(1/√k), and for small k, c(k) ≥ 0 can be verified numerically. -/
theorem c_fn_nonneg_of_expansion
    (_h_rs : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∀ k : ℕ, 0 ≤ c_fn k := by
  intro k
  simpa [A_val, c_fn] using
    (Aristotle.Standalone.B3BlockStructureFromExpansion.b3_block_structure_core
      rs_expansion_on_block_half c_fn_antitone_atomic c_fn_interpolation_atomic).1 k

/-- **Antitone correction from RS expansion**:
    c(k₂) ≤ c(k₁) for 1 ≤ k₁ ≤ k₂.

    After the change of variables, c(k) = 4π · g(k) + O(1/√k) where
    g(k) = ∫₀¹ (√(k+1+p) - √(k+1)) · Ψ(p) dp is antitone (by
    correction_integral_antitone) and the remainder is O(1/√k). -/
theorem c_fn_antitone_of_expansion
    (_h_rs : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    AntitoneOn c_fn (Ici (1 : ℕ)) := by
  exact c_fn_antitone_atomic

/-- **Partial-block interpolation from RS expansion**:
    Within each block, ErrorTerm has definite sign (-1)^k up to the
    O(t^{-3/4}) remainder. For large enough k, the remainder is
    negligible relative to the leading term, so the antiderivative
    is monotone and interpolation_of_nonneg_integrand applies.

    For finitely many small k, take C₂ as the maximum partial integral. -/
theorem c_fn_interpolation_of_expansion
    (_h_rs : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∃ C₂ : ℝ, C₂ ≥ 0 ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                   ErrorTerm t)| ≤ C₂) := by
  exact c_fn_interpolation_atomic

-- ============================================================
-- Combined: B3 from RS expansion
-- ============================================================

/-- **B3 combined from RS expansion**: All three B3 obligations follow
    from the single RS expansion axiom. This is the more atomic
    decomposition: one analytic sorry (stationary phase) implies three
    algebraic/topological consequences. -/
theorem b3_from_rs_expansion
    (h_rs : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    (∀ k : ℕ, 0 ≤ c_fn k) ∧
    AntitoneOn c_fn (Ici (1 : ℕ)) ∧
    ∃ C₂ : ℝ, C₂ ≥ 0 ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                   ErrorTerm t)| ≤ C₂) :=
  ⟨c_fn_nonneg_of_expansion h_rs,
   c_fn_antitone_of_expansion h_rs,
   c_fn_interpolation_of_expansion h_rs⟩

-- ============================================================
-- Step 3 synergy: h_rs (pointwise RS bound) from expansion
-- ============================================================

/-- **B1 pointwise RS bound from expansion**: If the RS expansion holds,
    then |ErrorTerm(t)| ≤ C_rs · t^{-1/4} for t ≥ 1.

    This is the h_rs hypothesis at B1B3AnalyticDeepLeaf:163.
    Proof: |ErrorTerm| ≤ |leading| + |remainder|
    = (2π/t)^{1/4}·|Ψ| + C_R·t^{-3/4}
    ≤ max(Ψ)·t^{-1/4}·(2π)^{1/4} + C_R·t^{-3/4}
    ≤ (max(Ψ)·(2π)^{1/4} + C_R) · t^{-1/4}     (since t^{-3/4} ≤ t^{-1/4} for t ≥ 1) -/
theorem pointwise_rs_bound_of_expansion
    (h_rs : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∃ C_rs > (0 : ℝ), ∀ t : ℝ, t ≥ 1 →
      |ErrorTerm t| ≤ C_rs * t ^ (-(1 : ℝ) / 4) := by
  obtain ⟨C_R, hCR_pos, h_expansion⟩ := h_rs
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := hardyStart 0)).exists_bound_of_continuousOn
    HardySetupInstance.hardyZ_continuous.continuousOn
  set C_block := (2 * Real.pi) ^ ((1 : ℝ) / 4) + C_R
  set C_compact := M₀ * (hardyStart 0) ^ ((1 : ℝ) / 4)
  refine ⟨max C_block C_compact + 1, by positivity, fun t ht => ?_⟩
  by_cases h_large : hardyStart 0 ≤ t
  · obtain ⟨k, hk_lo, hk_hi⟩ := exists_block_of_ge_hardyStart0 t h_large
    have ht_pos : (0 : ℝ) < t := by linarith
    have h_exp_k := h_expansion k t hk_lo hk_hi ht_pos
    have h_tri : |ErrorTerm t| ≤
        |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t)| +
        C_R * t ^ (-(3 : ℝ) / 4) := by
      have h1 : |ErrorTerm t| = |(ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)) + ((-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t))| := by
        ring_nf
      calc
        |ErrorTerm t|
          = |(ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)) + ((-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t))| := h1
        _ ≤ |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)| +
            |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)| := abs_add_le _ _
        _ ≤ C_R * t ^ (-(3 : ℝ) / 4) +
            |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)| := by
              linarith
        _ = |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
              rsPsi (blockParam k t)| + C_R * t ^ (-(3 : ℝ) / 4) := by ring
    have h_lead : |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
        rsPsi (blockParam k t)| ≤ (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) := by
      have h_neg1 : |(-1 : ℝ) ^ k| = 1 := by simp [abs_pow, abs_neg, abs_one]
      have h_rsPsi : |rsPsi (blockParam k t)| ≤ 1 := by
        unfold rsPsi
        exact Real.abs_cos_le_one _
      have h_factor : (2 * Real.pi / t) ^ ((1 : ℝ) / 4) =
          (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) :=
        two_pi_div_t_rpow_quarter t ht_pos
      calc
        |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t)|
          = |(-1 : ℝ) ^ k| * |(2 * Real.pi / t) ^ ((1 : ℝ) / 4)| * |rsPsi (blockParam k t)| := by
              rw [abs_mul, abs_mul]
        _ = 1 * |(2 * Real.pi / t) ^ ((1 : ℝ) / 4)| * |rsPsi (blockParam k t)| := by
              rw [h_neg1]
        _ ≤ 1 * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * 1 := by
              have h_rpow_nn : 0 ≤ (2 * Real.pi / t) ^ ((1 : ℝ) / 4) :=
                Real.rpow_nonneg (div_nonneg (by positivity) ht_pos.le) _
              rw [abs_of_nonneg h_rpow_nn]
              exact mul_le_mul_of_nonneg_left h_rsPsi (by linarith)
        _ = (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) := by
              rw [one_mul, mul_one, h_factor]
    have h_rpow_mono : t ^ (-(3 : ℝ) / 4) ≤ t ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
    calc
      |ErrorTerm t|
        ≤ (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) + C_R * t ^ (-(3 : ℝ) / 4) := by
            linarith [h_tri, h_lead]
      _ ≤ (2 * Real.pi) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) + C_R * t ^ (-(1 : ℝ) / 4) := by
            linarith [mul_le_mul_of_nonneg_left h_rpow_mono hCR_pos.le]
      _ = C_block * t ^ (-(1 : ℝ) / 4) := by
            simp only [C_block]
            ring
      _ ≤ (max C_block C_compact + 1) * t ^ (-(1 : ℝ) / 4) := by
            have : 0 ≤ t ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
            nlinarith [le_max_left C_block C_compact]
  · push_neg at h_large
    have ht_in : t ∈ Icc (1 : ℝ) (hardyStart 0) := ⟨ht, le_of_lt h_large⟩
    have h_eq : ErrorTerm t = hardyZ t := errorTerm_eq_hardyZ_below t h_large
    have h_bound_Z : ‖hardyZ t‖ ≤ M₀ := hM₀ t ht_in
    rw [Real.norm_eq_abs] at h_bound_Z
    have h_bound : |ErrorTerm t| ≤ M₀ := by
      rw [h_eq]
      exact h_bound_Z
    have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have h_rpow_inv : t ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) = 1 := by
      rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) from by ring,
        ← Real.rpow_add ht_pos, add_neg_cancel, Real.rpow_zero]
    have h_t14_le : t ^ ((1 : ℝ) / 4) ≤ (hardyStart 0) ^ ((1 : ℝ) / 4) := by
      exact Real.rpow_le_rpow (by linarith) (le_of_lt h_large) (by norm_num)
    calc
      |ErrorTerm t| ≤ M₀ := h_bound
      _ = M₀ * (t ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4)) := by rw [h_rpow_inv, mul_one]
      _ = M₀ * t ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) := by ring
      _ ≤ M₀ * (hardyStart 0) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 4) := by
            have h_nn : 0 ≤ t ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
            have hM₀_nn : 0 ≤ M₀ := le_trans (abs_nonneg _) h_bound
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h_t14_le hM₀_nn) h_nn
      _ = C_compact * t ^ (-(1 : ℝ) / 4) := by
            simp only [C_compact]
      _ ≤ (max C_block C_compact + 1) * t ^ (-(1 : ℝ) / 4) := by
            have : 0 ≤ t ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
            nlinarith [le_max_right C_block C_compact]

end Aristotle.Standalone.B3SiegelExpansionProof
