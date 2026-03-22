/-
  scratch_dirichlet_proofs_v2.lean

  Agent 2v6 — Inhomogeneous simultaneous Dirichlet approximation
  on the K-torus with |γ_k| ≥ δ hypothesis.

  RESEARCH ONLY — does NOT modify any Littlewood/ files.

  Builds on Agent 2v5's sorry-free sub-lemmas.

  Status summary:
    ALL SORRY-FREE from v1: exists_int_mul_in_interval, one_dim_torus_cover,
      same_cell_frac_close, floor_frac_fin_bound, frac_diff_eq,
      nearest_lattice_point, homogeneous_dirichlet_integers,
      inhomogeneous_one_dim
    NEW SORRY-FREE: am_gm_two_pi, k1_inhomogeneous, length_to_expanded
    K=0 case: SORRY-FREE
    K=1 case: SORRY-FREE (via k1_inhomogeneous + AM-GM clamping)
    K≥2 case: 1 SORRY (statement is FALSE without distinctness — see below)
    Specialized: propagates sorry from K≥2

  KEY FINDING: The theorem statement for K≥2 is FALSE without a hypothesis
  that the γ_k are distinct. Counterexample:
    K=2, γ₁ = γ₂ = 14, δ=14, ε=1/2, φ₁=0, φ₂=π, [a,b]=[0,0.81].
    The orbit stays on the diagonal of the 2-torus and cannot reach (0,π).
  This affects inhomogeneous_dirichlet_on_interval in DirichletApproximation.lean
  as well. The downstream use (PerronExplicitFormulaProvider) applies to distinct
  zeta zero ordinates, so the Littlewood proof is not invalidated.
  FIX: Add `Function.Injective γ` or a minimum gap hypothesis.

  The K≥2 sorry is ALSO blocked by Minkowski's lattice point theorem
  being absent from Mathlib. Even with the corrected statement, pigeonhole
  alone cannot bridge homogeneous→inhomogeneous for K≥2.
-/
import Mathlib

-- ============================================================================
-- SECTION 1: IVT Helper
-- ============================================================================

/-- An interval [c,d] of length ≥ 2π contains some φ + m·2π. -/
lemma exists_int_mul_in_interval (φ c d : ℝ) (hcd : 2 * Real.pi ≤ d - c) :
    ∃ m : ℤ, c ≤ φ + m * (2 * Real.pi) ∧ φ + m * (2 * Real.pi) ≤ d := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set m := ⌈(c - φ) / (2 * Real.pi)⌉ with hm_def
  refine ⟨m, ?_, ?_⟩
  · have h1 : (c - φ) / (2 * Real.pi) ≤ m := Int.le_ceil _
    have h2 : c - φ ≤ m * (2 * Real.pi) := by rwa [div_le_iff₀ hpi] at h1
    linarith
  · have hceil : (↑m : ℝ) < (c - φ) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
    nlinarith [mul_lt_mul_of_pos_right hceil hpi, (div_mul_cancel₀ (c - φ) (ne_of_gt hpi))]

-- ============================================================================
-- SECTION 2: K=1 Exact Hit via IVT
-- ============================================================================

/-- If |γ|·(b-a) ≥ 2π, then ∃ t₀ ∈ [a,b] with γ·t₀ - φ = m·2π exactly. -/
theorem one_dim_torus_cover (γ φ a b : ℝ) (hab : a ≤ b)
    (hcover : 2 * Real.pi ≤ |γ| * (b - a)) :
    ∃ t0 : ℝ, a ≤ t0 ∧ t0 ≤ b ∧ ∃ m : ℤ, γ * t0 - φ = m * (2 * Real.pi) := by
  by_cases hγ : 0 ≤ γ
  · have habs : |γ| = γ := abs_of_nonneg hγ
    rw [habs] at hcover
    obtain ⟨m, hm1, hm2⟩ := exists_int_mul_in_interval φ (γ * a) (γ * b) (by nlinarith)
    have hcont : Continuous (fun t => γ * t) := continuous_const.mul continuous_id
    obtain ⟨t0, ⟨ht0a, ht0b⟩, ht0eq⟩ :
        ∃ t0 ∈ Set.Icc a b, γ * t0 = φ + m * (2 * Real.pi) :=
      intermediate_value_Icc hab hcont.continuousOn ⟨hm1, hm2⟩
    exact ⟨t0, ht0a, ht0b, m, by linarith⟩
  · push_neg at hγ
    have habs : |γ| = -γ := abs_of_neg hγ
    rw [habs] at hcover
    obtain ⟨m, hm1, hm2⟩ := exists_int_mul_in_interval φ (γ * b) (γ * a) (by nlinarith)
    have hcont : Continuous (fun t => γ * t) := continuous_const.mul continuous_id
    obtain ⟨t0, ⟨ht0a, ht0b⟩, ht0eq⟩ :
        ∃ t0 ∈ Set.Icc a b, γ * t0 = φ + m * (2 * Real.pi) :=
      intermediate_value_Icc' hab hcont.continuousOn ⟨hm1, hm2⟩
    exact ⟨t0, ht0a, ht0b, m, by linarith⟩

-- ============================================================================
-- SECTION 3: Pigeonhole Sub-lemmas
-- ============================================================================

/-- Fractional part difference = real difference minus integer difference. -/
private lemma frac_diff_eq (a b : ℝ) :
    Int.fract a - Int.fract b = a - b - (⌊a⌋ - ⌊b⌋ : ℤ) := by
  have ha : Int.fract a = a - ⌊a⌋ := Int.self_sub_floor a |>.symm
  have hb : Int.fract b = b - ⌊b⌋ := Int.self_sub_floor b |>.symm
  rw [ha, hb]; push_cast; ring

/-- Two reals in the same ⌊Q·{·}⌋ cell have fractional parts within 1/Q. -/
lemma same_cell_frac_close (x y : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (h : ⌊(Q : ℝ) * Int.fract x⌋ = ⌊(Q : ℝ) * Int.fract y⌋) :
    |Int.fract x - Int.fract y| < 1 / (Q : ℝ) := by
  have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have h1 := Int.floor_le ((Q : ℝ) * Int.fract x)
  have h2 := Int.lt_floor_add_one ((Q : ℝ) * Int.fract x)
  have h3 := Int.floor_le ((Q : ℝ) * Int.fract y)
  have h4 := Int.lt_floor_add_one ((Q : ℝ) * Int.fract y)
  rw [h] at h1 h2
  have h5 : |Q * Int.fract x - Q * Int.fract y| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  rw [← mul_sub, abs_mul, abs_of_pos hQpos] at h5
  rw [lt_div_iff₀ hQpos]; linarith

/-- Bound for the Fin-valued cell map. -/
private lemma floor_frac_fin_bound (n : ℕ) (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    (⌊(Q : ℝ) * Int.fract (↑n * α)⌋).toNat < Q := by
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hfrac := Int.fract_nonneg (↑n * α)
  have hfrac1 := Int.fract_lt_one (↑n * α)
  have hlt : (Q : ℝ) * Int.fract (↑n * α) < Q := by
    linarith [mul_lt_mul_of_pos_left hfrac1 hQr]
  have hfl : ⌊(Q : ℝ) * Int.fract (↑n * α)⌋ < Q := by
    exact_mod_cast Int.floor_lt.mpr (by exact_mod_cast hlt)
  have hnn : 0 ≤ ⌊(Q : ℝ) * Int.fract (↑n * α)⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (le_of_lt hQr) hfrac)
  omega

/-- Any real x has a nearest point in φ + 2πℤ within distance π. -/
lemma nearest_lattice_point (x φ : ℝ) :
    ∃ m : ℤ, |x - φ - m * (2 * Real.pi)| ≤ Real.pi := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set r := (x - φ) / (2 * Real.pi)
  set m := ⌊r + 1/2⌋
  refine ⟨m, ?_⟩
  have h1 : (m : ℝ) ≤ r + 1/2 := Int.floor_le _
  have h2 : r + 1/2 < m + 1 := Int.lt_floor_add_one _
  have habs : |r - m| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
  have key : x - φ - m * (2 * Real.pi) = (r - m) * (2 * Real.pi) := by
    simp [r]; field_simp
  rw [key, abs_mul, abs_of_pos hpi]
  calc |r - ↑m| * (2 * Real.pi) ≤ 1/2 * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right habs (le_of_lt hpi)
    _ = Real.pi := by ring

-- ============================================================================
-- SECTION 4: Homogeneous Simultaneous Dirichlet (SORRY-FREE)
-- ============================================================================

/-- Classical K-dimensional Dirichlet approximation by pigeonhole on the K-torus.
Given α₁,...,α_K ∈ ℝ and Q ≥ 1, there exist integers q (1 ≤ q ≤ Q^K) and
p₁,...,p_K such that |q·α_k - p_k| < 1/Q for all k. -/
theorem homogeneous_dirichlet_integers
    (K : ℕ) (α : Fin K → ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ^ K ∧
      ∀ k : Fin K, ∃ p : ℤ, |↑q * α k - (p : ℝ)| < 1 / (Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hcard : Fintype.card (Fin K → Fin Q) < Fintype.card (Fin (Q ^ K + 1)) := by
    simp [Fintype.card_fin]
  let cellMap (n : Fin (Q ^ K + 1)) : Fin K → Fin Q :=
    fun k => ⟨(⌊(Q : ℝ) * Int.fract (↑n.val * α k)⌋).toNat,
              floor_frac_fin_bound n.val (α k) Q hQ⟩
  obtain ⟨n₁, n₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt cellMap hcard
  have hfloor : ∀ k, ⌊(Q : ℝ) * Int.fract (↑n₁.val * α k)⌋ =
                      ⌊(Q : ℝ) * Int.fract (↑n₂.val * α k)⌋ := by
    intro k
    have hk := congr_fun heq k
    simp only [cellMap, Fin.mk.injEq] at hk
    have h1 : 0 ≤ ⌊(Q : ℝ) * Int.fract (↑n₁.val * α k)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (le_of_lt hQr) (Int.fract_nonneg _))
    have h2 : 0 ≤ ⌊(Q : ℝ) * Int.fract (↑n₂.val * α k)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (le_of_lt hQr) (Int.fract_nonneg _))
    omega
  rcases Nat.le_or_le n₁.val n₂.val with h | h
  · refine ⟨n₂.val - n₁.val, by omega, by omega, fun k => ?_⟩
    have hclose := same_cell_frac_close (↑n₂.val * α k) (↑n₁.val * α k) Q hQ
      ((hfloor k).symm)
    rw [frac_diff_eq] at hclose
    refine ⟨⌊↑n₂.val * α k⌋ - ⌊↑n₁.val * α k⌋, ?_⟩
    rw [Nat.cast_sub h]; convert hclose using 2; push_cast; ring
  · refine ⟨n₁.val - n₂.val, by omega, by omega, fun k => ?_⟩
    have hclose := same_cell_frac_close (↑n₁.val * α k) (↑n₂.val * α k) Q hQ (hfloor k)
    rw [frac_diff_eq] at hclose
    refine ⟨⌊↑n₁.val * α k⌋ - ⌊↑n₂.val * α k⌋, ?_⟩
    rw [Nat.cast_sub h]; convert hclose using 2; push_cast; ring

-- ============================================================================
-- SECTION 5: K=1 Inhomogeneous via IVT (SORRY-FREE)
-- ============================================================================

/-- AM-GM bound: 2π/ε + 2ε > 2π for any ε > 0.
This is the key inequality that makes the K=1 clamping argument work
for all ε > 0, not just ε ≤ 1.
Proof: (√(2π/ε) - √(2ε))² ≥ 0 gives 2π/ε + 2ε ≥ 2√(4π) > 2π,
where the last step uses 4 > π. -/
lemma am_gm_two_pi (ε : ℝ) (hε : 0 < ε) : 2 * Real.pi / ε + 2 * ε > 2 * Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hh1 : 0 ≤ 2 * Real.pi / ε := by positivity
  have hh2 : 0 ≤ 2 * ε := by positivity
  have hsq : 0 ≤ (Real.sqrt (2 * Real.pi / ε) - Real.sqrt (2 * ε)) ^ 2 := sq_nonneg _
  rw [sub_sq, Real.sq_sqrt hh1, Real.sq_sqrt hh2] at hsq
  have hmul : Real.sqrt (2 * Real.pi / ε) * Real.sqrt (2 * ε) = Real.sqrt (4 * Real.pi) := by
    rw [← Real.sqrt_mul hh1]; congr 1; field_simp; ring
  have hpi_lt : Real.pi < Real.sqrt (4 * Real.pi) := by
    have hsq' : Real.pi ^ 2 < Real.sqrt (4 * Real.pi) ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 4 * Real.pi)]
      nlinarith [sq Real.pi, Real.pi_lt_four]
    nlinarith [Real.sqrt_nonneg (4 * Real.pi), sq_abs (Real.sqrt (4 * Real.pi) - Real.pi)]
  linarith [hmul]

/-- Bridge lemma: the hypotheses of inhomogeneous_dirichlet_on_interval_v2 (K=1)
imply the hypothesis of k1_inhomogeneous. The key step is the AM-GM bound. -/
lemma length_to_expanded (γ ε δ a b : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hγ : δ ≤ |γ|) (hlen : 2 * Real.pi / (ε * δ) ≤ b - a) :
    2 * Real.pi ≤ |γ| * (b - a) + 2 * ε := by
  have hεδ : 0 < ε * δ := mul_pos hε hδ
  have hba : 0 ≤ b - a := le_trans (div_nonneg (by positivity) hεδ.le) hlen
  have hconv : 2 * Real.pi / (ε * δ) * δ = 2 * Real.pi / ε := by field_simp
  have h1a : 2 * Real.pi / (ε * δ) * δ ≤ (b - a) * δ := by nlinarith
  rw [hconv] at h1a
  have h1 : 2 * Real.pi / ε ≤ |γ| * (b - a) := by
    nlinarith [mul_le_mul_of_nonneg_left hγ hba, mul_comm (b - a) |γ|]
  -- 2π ≤ 2π/ε + 2ε ≤ |γ|*(b-a) + 2ε
  linarith [am_gm_two_pi ε hε]

/-- K=1 inhomogeneous: if |γ|*(b-a)+2ε ≥ 2π, then ∃ t₀ ∈ [a,b] with
|t₀·γ - φ - m·2π| ≤ ε.

Proof by "clamping": the ε-expanded image [γ·a-ε, γ·b+ε] has length ≥ 2π,
so it contains some φ + m·2π. Then either γ·a, γ·b, or some interior point
is within ε of the target, using IVT for the interior case. -/
lemma k1_inhomogeneous (γ φ ε a b : ℝ) (hε : 0 < ε) (hab : a ≤ b)
    (hγ : γ ≠ 0) (hlen : 2 * Real.pi ≤ |γ| * (b - a) + 2 * ε) :
    ∃ t0 : ℝ, a ≤ t0 ∧ t0 ≤ b ∧
      ∃ m : ℤ, |t0 * γ - φ - m * (2 * Real.pi)| ≤ ε := by
  by_cases hγpos : 0 < γ
  · have hexplen : 2 * Real.pi ≤ (γ * b + ε) - (γ * a - ε) := by
      rw [abs_of_pos hγpos] at hlen; nlinarith
    obtain ⟨m, hm1, hm2⟩ := exists_int_mul_in_interval φ (γ * a - ε) (γ * b + ε) hexplen
    by_cases h1 : φ + m * (2 * Real.pi) ≤ γ * a
    · exact ⟨a, le_refl _, hab, m, by rw [abs_le]; constructor <;> nlinarith⟩
    · push_neg at h1
      by_cases h2 : γ * b ≤ φ + m * (2 * Real.pi)
      · exact ⟨b, hab, le_refl _, m, by rw [abs_le]; constructor <;> nlinarith⟩
      · push_neg at h2
        have hcont : Continuous (fun t => γ * t) := continuous_const.mul continuous_id
        obtain ⟨t0, ⟨ht0a, ht0b⟩, ht0eq⟩ :
            ∃ t0 ∈ Set.Icc a b, γ * t0 = φ + m * (2 * Real.pi) :=
          intermediate_value_Icc hab hcont.continuousOn ⟨le_of_lt h1, le_of_lt h2⟩
        exact ⟨t0, ht0a, ht0b, m, by
          have : t0 * γ - φ - m * (2 * Real.pi) = 0 := by linarith [ht0eq]
          rw [this, abs_zero]; exact hε.le⟩
  · push_neg at hγpos
    have hγneg : γ < 0 := lt_of_le_of_ne hγpos (fun h => hγ h)
    have hexplen : 2 * Real.pi ≤ (γ * a + ε) - (γ * b - ε) := by
      rw [abs_of_neg hγneg] at hlen; nlinarith
    obtain ⟨m, hm1, hm2⟩ := exists_int_mul_in_interval φ (γ * b - ε) (γ * a + ε) hexplen
    by_cases h1 : φ + m * (2 * Real.pi) ≤ γ * b
    · exact ⟨b, hab, le_refl _, m, by rw [abs_le]; constructor <;> nlinarith⟩
    · push_neg at h1
      by_cases h2 : γ * a ≤ φ + m * (2 * Real.pi)
      · exact ⟨a, le_refl _, hab, m, by rw [abs_le]; constructor <;> nlinarith⟩
      · push_neg at h2
        have hcont : Continuous (fun t => γ * t) := continuous_const.mul continuous_id
        obtain ⟨t0, ⟨ht0a, ht0b⟩, ht0eq⟩ :
            ∃ t0 ∈ Set.Icc a b, γ * t0 = φ + m * (2 * Real.pi) :=
          intermediate_value_Icc' hab hcont.continuousOn ⟨le_of_lt h1, le_of_lt h2⟩
        exact ⟨t0, ht0a, ht0b, m, by
          have : t0 * γ - φ - m * (2 * Real.pi) = 0 := by linarith [ht0eq]
          rw [this, abs_zero]; exact hε.le⟩

-- ============================================================================
-- SECTION 6: General K Inhomogeneous
-- ============================================================================

/-- **Simultaneous inhomogeneous Dirichlet approximation on the K-torus.**

**COUNTEREXAMPLE FOUND (Agent 2v6):** The statement WITHOUT a distinctness
hypothesis on the γ_k is FALSE for K ≥ 2. Counterexample:
  K=2, γ₁ = γ₂ = 14, δ = 14, ε = 1/2, [a,b] = [0, 0.81], φ₁ = 0, φ₂ = π.
The orbit {(14t mod 2π, 14t mod 2π)} stays on the diagonal of the 2-torus,
so it cannot approximate targets far from the diagonal like (0, π).

The downstream use in PerronExplicitFormulaProvider applies this to DISTINCT
zeta zero imaginary parts, so the counterexample doesn't affect the Littlewood
proof. However, the formal statement needs repair:
  Option A: Add `Function.Injective γ` hypothesis
  Option B: Add `∀ i j, i ≠ j → |γ i - γ j| ≥ gap` with gap in the length bound
  Option C: Reformulate using the K-dim Kronecker theorem with a linear independence hypothesis

The K≥2 sorry is thus BLOCKED not only by missing Minkowski theorem in Mathlib
but also by the incorrect statement.

For K=0 and K=1, the theorem is correct and sorry-free.

SORRY STATUS: K=0 and K=1 are sorry-free. K≥2 has one sorry (statement
needs distinctness hypothesis + proof needs geometry of numbers). -/
theorem inhomogeneous_dirichlet_on_interval_v2
    (K : ℕ) (γ φ : Fin K → ℝ) (ε δ : ℝ) (a b : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hγ : ∀ k, δ ≤ |γ k|)
    (hab : a < b)
    (hlen : (2 * Real.pi / (ε * δ)) ^ K ≤ b - a) :
    ∃ t0 : ℝ, a ≤ t0 ∧ t0 ≤ b ∧
      ∀ k : Fin K, ∃ m : ℤ, |t0 * γ k - φ k - m * (2 * Real.pi)| ≤ ε := by
  rcases K with _ | K'
  · -- K = 0: no coordinates, any point works
    exact ⟨a, le_refl a, le_of_lt hab, fun k => Fin.elim0 k⟩
  · rcases K' with _ | K''
    · -- K = 1: use the IVT/clamping argument
      have hγ0 : δ ≤ |γ ⟨0, by omega⟩| := hγ ⟨0, by omega⟩
      have hγne : γ ⟨0, by omega⟩ ≠ 0 := by
        intro h; rw [h, abs_zero] at hγ0; linarith
      have hlen1 : 2 * Real.pi / (ε * δ) ≤ b - a := by
        simpa [pow_succ, pow_zero, one_mul] using hlen
      have hexpanded := length_to_expanded (γ ⟨0, by omega⟩) ε δ a b hε hδ hγ0 hlen1
      obtain ⟨t0, ht0a, ht0b, m, hm⟩ :=
        k1_inhomogeneous (γ ⟨0, by omega⟩) (φ ⟨0, by omega⟩) ε a b hε (le_of_lt hab) hγne hexpanded
      exact ⟨t0, ht0a, ht0b, fun k => by
        have : k = ⟨0, by omega⟩ := by ext; omega
        subst this; exact ⟨m, hm⟩⟩
    · -- K ≥ 2: statement needs distinctness hypothesis (see docstring).
      -- Even with that fix, proof needs Minkowski's theorem (not in Mathlib).
      sorry

-- ============================================================================
-- SECTION 7: Specialization for Littlewood proof
-- ============================================================================

/-- Specialized version matching the signature used in PerronExplicitFormulaProvider.
Uses ε = 1/2 and requires ∀ k, δ ≤ |γ k|. -/
theorem inhomogeneous_dirichlet_on_interval_specialized
    (K : ℕ) (γ φ : Fin K → ℝ) (δ : ℝ) (a b : ℝ)
    (hδ : 0 < δ) (hγ : ∀ k, δ ≤ |γ k|)
    (hab : a < b)
    (hlen : (4 * Real.pi / δ) ^ K ≤ b - a) :
    ∃ t0 : ℝ, a ≤ t0 ∧ t0 ≤ b ∧
      ∀ k : Fin K, ∃ m : ℤ, |t0 * γ k - φ k - m * (2 * Real.pi)| ≤ 1 / 2 := by
  have hε : (0 : ℝ) < 1 / 2 := by norm_num
  apply inhomogeneous_dirichlet_on_interval_v2 K γ φ (1/2) δ a b hε hδ hγ hab
  calc (2 * Real.pi / (1 / 2 * δ)) ^ K = (4 * Real.pi / δ) ^ K := by
        congr 1; field_simp; ring
    _ ≤ b - a := hlen
