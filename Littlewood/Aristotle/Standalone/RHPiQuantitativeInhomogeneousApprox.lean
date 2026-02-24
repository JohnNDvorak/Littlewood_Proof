import Littlewood.Aristotle.DirichletPhaseAlignment

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiQuantitativeInhomogeneousApprox

open Real

/--
Quantitative inhomogeneous one-parameter approximation from an exact seed.

Given frequencies `γ : Fin n → ℝ`, target phases `φ : Fin n → ℝ`, and a seed
time `t0` that solves all congruences exactly modulo `2π`, one can construct an
explicit large point `x = exp t` such that:

1. `x > X` and `1 < x`,
2. all inhomogeneous congruences `log x * γ i ≈ φ i (mod 2π)` hold with error
   at most `ε`,
3. `x` has an explicit upper bound in terms of `t0`, `X`, `ε`, and the
   Dirichlet parameter `N`.

This is the quantitative constructive core used by RH-π inhomogeneous
phase-coupling steps.
-/
theorem quantitative_inhomogeneous_approx_of_exact_seed
    {n : ℕ} (γ φ : Fin n → ℝ)
    {ε X t0 : ℝ} (hε : 0 < ε)
    (hseed : ∀ i : Fin n, ∃ m : ℤ, t0 * γ i - φ i - m • (2 * Real.pi) = 0) :
    ∃ N : ℕ, 0 < N ∧
      ∃ x : ℝ, X < x ∧ 1 < x ∧
        (∀ i : Fin n, ∃ k : ℤ,
          ‖Real.log x * γ i - φ i - k • (2 * Real.pi)‖ ≤ ε) ∧
        x ≤ Real.exp
          (|t0| +
            (((Nat.floor |Real.log (max X 1) - t0| + 2 : ℕ) : ℝ) * ((N : ℝ) ^ n))) := by
  let L : ℝ := Real.log (max X 1)
  let kNat : ℕ := Nat.floor |L - t0| + 2
  let k : ℝ := kNat

  have hkNat_pos : 0 < kNat := by
    dsimp [kNat]
    omega
  have hk_pos : 0 < k := by
    dsimp [k]
    exact_mod_cast hkNat_pos

  have h_abs_lt_k : |L - t0| < k := by
    have h1 : |L - t0| < ((Nat.floor |L - t0| : ℕ) : ℝ) + 1 := by
      exact Nat.lt_floor_add_one _
    have h2 : ((Nat.floor |L - t0| : ℕ) : ℝ) + 1 < k := by
      have h2_nat : (Nat.floor |L - t0| : ℕ) + 1 < (Nat.floor |L - t0| : ℕ) + 2 := by
        omega
      dsimp [k, kNat]
      exact_mod_cast h2_nat
    exact lt_trans h1 h2

  have hL_lt_t0_add_k : L < t0 + k := by
    have hLdiff_le : L - t0 ≤ |L - t0| := by
      simpa using (le_abs_self (L - t0))
    have hLdiff_lt : L - t0 < k := lt_of_le_of_lt hLdiff_le h_abs_lt_k
    linarith

  let R : ℝ := (2 * Real.pi * k) / ε
  obtain ⟨N, hNgt⟩ := exists_nat_gt R
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hN_real_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt hR_nonneg hNgt) (le_rfl)
  have hN_pos : 0 < N := by
    exact_mod_cast hN_real_pos

  rcases Aristotle.DirichletPhaseAlignment.simultaneous_dirichlet_approximation
      (ξ := fun i : Fin n => γ i / (2 * Real.pi)) N hN_pos with
    ⟨q, hq_pos, hq_le, hq_approx⟩

  let t : ℝ := t0 + k * q
  let x : ℝ := Real.exp t

  have hq_ge_one_nat : 1 ≤ q := Nat.succ_le_of_lt hq_pos
  have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hq_ge_one_nat

  have ht0k_le_t : t0 + k ≤ t := by
    dsimp [t]
    have hmul : k ≤ k * (q : ℝ) := by
      calc
        k = k * (1 : ℝ) := by ring
        _ ≤ k * (q : ℝ) := mul_le_mul_of_nonneg_left hq_ge_one (le_of_lt hk_pos)
    linarith

  have hL_lt_t : L < t := lt_of_lt_of_le hL_lt_t0_add_k ht0k_le_t

  have hmax_pos : 0 < max X 1 := lt_of_lt_of_le zero_lt_one (le_max_right X 1)
  have hmax_lt_x : max X 1 < x := by
    dsimp [x, L] at *
    exact (Real.log_lt_iff_lt_exp hmax_pos).1 hL_lt_t

  have hXx : X < x := lt_of_le_of_lt (le_max_left X 1) hmax_lt_x
  have hx1 : 1 < x := lt_of_le_of_lt (le_max_right X 1) hmax_lt_x

  have hq_le_real : (q : ℝ) ≤ (N : ℝ) ^ n := by
    exact_mod_cast hq_le

  have ht_upper : t ≤ |t0| + k * ((N : ℝ) ^ n) := by
    have ht0_le : t0 ≤ |t0| := le_abs_self t0
    have hmul_le : k * (q : ℝ) ≤ k * ((N : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hq_le_real (le_of_lt hk_pos)
    dsimp [t]
    nlinarith

  have hx_upper : x ≤ Real.exp (|t0| + k * ((N : ℝ) ^ n)) := by
    dsimp [x]
    exact Real.exp_le_exp.mpr ht_upper

  have hkN_lt_eps : k * (2 * Real.pi) * ((1 : ℝ) / N) < ε := by
    have hRlt : (2 * Real.pi * k) / ε < (N : ℝ) := by
      simpa [R] using hNgt
    have hmul : k * (2 * Real.pi) < (N : ℝ) * ε := by
      exact (div_lt_iff₀ hε).1 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hRlt)
    have hdiv : (k * (2 * Real.pi)) / (N : ℝ) < ε := by
      exact (div_lt_iff₀ hN_real_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

  refine ⟨N, hN_pos, x, hXx, hx1, ?_, ?_⟩
  · intro i
    rcases hseed i with ⟨m, hm⟩
    rcases hq_approx i with ⟨p, hp⟩
    let K : ℤ := (Int.ofNat kNat) * p + m
    refine ⟨K, ?_⟩

    have hlogx : Real.log x = t := by
      dsimp [x]
      rw [Real.log_exp]
    have hcastK : (K : ℝ) = (kNat : ℝ) * (p : ℝ) + (m : ℝ) := by
      dsimp [K]
      push_cast
      ring
    have hmain :
        Real.log x * γ i - φ i - K • (2 * Real.pi)
          = k * (((q : ℝ) * γ i) - (p : ℝ) * (2 * Real.pi)) := by
      rw [hlogx]
      have hsmulK : K • (2 * Real.pi) = ((K : ℝ) * (2 * Real.pi)) := by
        simp [zsmul_eq_mul]
      rw [hsmulK, hcastK]
      have hseed0 : t0 * γ i - φ i - (m : ℝ) * (2 * Real.pi) = 0 := by
        simpa [zsmul_eq_mul] using hm
      dsimp [t, k]
      nlinarith [hseed0]

    have hgamma :
        ((q : ℝ) * γ i) - (p : ℝ) * (2 * Real.pi)
          = (2 * Real.pi) * (((q : ℝ) * (γ i / (2 * Real.pi))) - (p : ℝ)) := by
      have h2pi_ne : (2 * Real.pi) ≠ 0 := by positivity
      calc
        ((q : ℝ) * γ i) - (p : ℝ) * (2 * Real.pi)
            = (2 * Real.pi) * (((q : ℝ) * γ i) / (2 * Real.pi) - (p : ℝ)) := by
                field_simp [h2pi_ne]
        _ = (2 * Real.pi) * (((q : ℝ) * (γ i / (2 * Real.pi))) - (p : ℝ)) := by ring

    have habs : ‖Real.log x * γ i - φ i - K • (2 * Real.pi)‖ ≤ ε := by
      calc
        ‖Real.log x * γ i - φ i - K • (2 * Real.pi)‖
            = |k * (((q : ℝ) * γ i) - (p : ℝ) * (2 * Real.pi))| := by
                rw [hmain, Real.norm_eq_abs]
        _ = k * |((q : ℝ) * γ i) - (p : ℝ) * (2 * Real.pi)| := by
              rw [abs_mul, abs_of_nonneg (le_of_lt hk_pos)]
        _ = k * (2 * Real.pi) * |((q : ℝ) * (γ i / (2 * Real.pi))) - (p : ℝ)| := by
              rw [hgamma, abs_mul]
              have h2pi_nonneg : 0 ≤ 2 * Real.pi := by positivity
              rw [abs_of_nonneg h2pi_nonneg]
              ring
        _ ≤ k * (2 * Real.pi) * ((1 : ℝ) / N) := by
              gcongr
        _ ≤ ε := le_of_lt hkN_lt_eps
    exact habs
  · simpa [k, kNat, mul_assoc, mul_comm, mul_left_comm] using hx_upper

/-- Convenience specialization of
`quantitative_inhomogeneous_approx_of_exact_seed` for anti-target phases
`φ + π`. -/
theorem quantitative_inhomogeneous_approx_of_exact_seed_add_pi
    {n : ℕ} (γ φ : Fin n → ℝ)
    {ε X t0 : ℝ} (hε : 0 < ε)
    (hseed : ∀ i : Fin n, ∃ m : ℤ,
      t0 * γ i - (φ i + Real.pi) - m • (2 * Real.pi) = 0) :
    ∃ N : ℕ, 0 < N ∧
      ∃ x : ℝ, X < x ∧ 1 < x ∧
        (∀ i : Fin n, ∃ k : ℤ,
          ‖Real.log x * γ i - (φ i + Real.pi) - k • (2 * Real.pi)‖ ≤ ε) ∧
        x ≤ Real.exp
          (|t0| +
            (((Nat.floor |Real.log (max X 1) - t0| + 2 : ℕ) : ℝ) * ((N : ℝ) ^ n))) := by
  simpa using quantitative_inhomogeneous_approx_of_exact_seed
    (γ := γ) (φ := fun i => φ i + Real.pi) (ε := ε) (X := X) (t0 := t0) hε hseed

/-- Finite-set target-phase wrapper of
`quantitative_inhomogeneous_approx_of_exact_seed`. -/
theorem quantitative_inhomogeneous_approx_of_exact_seed_finset
    (S : Finset ℂ)
    {ε X t0 : ℝ} (hε : 0 < ε)
    (hseed : ∀ ρ ∈ S, ∃ m : ℤ, t0 * ρ.im - Complex.arg ρ - m • (2 * Real.pi) = 0) :
    ∃ N : ℕ, 0 < N ∧
      ∃ x : ℝ, X < x ∧ 1 < x ∧
        (∀ ρ ∈ S, ∃ k : ℤ,
          ‖Real.log x * ρ.im - Complex.arg ρ - k • (2 * Real.pi)‖ ≤ ε) ∧
        x ≤ Real.exp
          (|t0| +
            (((Nat.floor |Real.log (max X 1) - t0| + 2 : ℕ) : ℝ) *
              ((N : ℝ) ^ (Fintype.card {ρ // ρ ∈ S}))) ) := by
  let n : ℕ := Fintype.card {ρ // ρ ∈ S}
  let e : Fin n ≃ {ρ // ρ ∈ S} := (Fintype.equivFin {ρ // ρ ∈ S}).symm
  let γ : Fin n → ℝ := fun i => (e i).1.im
  let φ : Fin n → ℝ := fun i => Complex.arg (e i).1
  have hseed_fin : ∀ i : Fin n, ∃ m : ℤ, t0 * γ i - φ i - m • (2 * Real.pi) = 0 := by
    intro i
    simpa [γ, φ] using hseed (e i).1 (e i).2
  rcases quantitative_inhomogeneous_approx_of_exact_seed
      (γ := γ) (φ := φ) (ε := ε) (X := X) (t0 := t0) hε hseed_fin with
    ⟨N, hNpos, x, hXx, hx1, happrox_fin, hxUpper⟩
  refine ⟨N, hNpos, x, hXx, hx1, ?_, ?_⟩
  · intro ρ hρ
    let i : Fin n := e.symm ⟨ρ, hρ⟩
    rcases happrox_fin i with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [γ, φ, i] using hk
  · simpa [n] using hxUpper

/-- Finite-set anti-target-phase wrapper of
`quantitative_inhomogeneous_approx_of_exact_seed_add_pi`. -/
theorem quantitative_inhomogeneous_approx_of_exact_seed_add_pi_finset
    (S : Finset ℂ)
    {ε X t0 : ℝ} (hε : 0 < ε)
    (hseed : ∀ ρ ∈ S, ∃ m : ℤ,
      t0 * ρ.im - (Complex.arg ρ + Real.pi) - m • (2 * Real.pi) = 0) :
    ∃ N : ℕ, 0 < N ∧
      ∃ x : ℝ, X < x ∧ 1 < x ∧
        (∀ ρ ∈ S, ∃ k : ℤ,
          ‖Real.log x * ρ.im - (Complex.arg ρ + Real.pi) - k • (2 * Real.pi)‖ ≤ ε) ∧
        x ≤ Real.exp
          (|t0| +
            (((Nat.floor |Real.log (max X 1) - t0| + 2 : ℕ) : ℝ) *
              ((N : ℝ) ^ (Fintype.card {ρ // ρ ∈ S}))) ) := by
  let n : ℕ := Fintype.card {ρ // ρ ∈ S}
  let e : Fin n ≃ {ρ // ρ ∈ S} := (Fintype.equivFin {ρ // ρ ∈ S}).symm
  let γ : Fin n → ℝ := fun i => (e i).1.im
  let φ : Fin n → ℝ := fun i => Complex.arg (e i).1
  have hseed_fin :
      ∀ i : Fin n, ∃ m : ℤ, t0 * γ i - (φ i + Real.pi) - m • (2 * Real.pi) = 0 := by
    intro i
    simpa [γ, φ] using hseed (e i).1 (e i).2
  rcases quantitative_inhomogeneous_approx_of_exact_seed_add_pi
      (γ := γ) (φ := φ) (ε := ε) (X := X) (t0 := t0) hε hseed_fin with
    ⟨N, hNpos, x, hXx, hx1, happrox_fin, hxUpper⟩
  refine ⟨N, hNpos, x, hXx, hx1, ?_, ?_⟩
  · intro ρ hρ
    let i : Fin n := e.symm ⟨ρ, hρ⟩
    rcases happrox_fin i with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [γ, φ, i] using hk
  · simpa [n] using hxUpper

end Aristotle.Standalone.RHPiQuantitativeInhomogeneousApprox
