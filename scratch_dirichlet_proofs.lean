/-
  scratch_dirichlet_proofs.lean

  Agent 2v5 — Prototype for corrected simultaneous Dirichlet approximation
  on the K-torus with |γ_k| ≥ δ hypothesis.

  RESEARCH ONLY — does NOT modify any Littlewood/ files.

  Status summary:
    SORRY-FREE: exists_int_mul_in_interval, one_dim_torus_cover,
      same_cell_frac_close, floor_frac_fin_bound, frac_diff_eq,
      nearest_lattice_point, homogeneous_dirichlet_integers,
      inhomogeneous_one_dim
    1 SORRY: inhomogeneous_dirichlet_on_interval_v2 (general K, bridge)
    Downstream: inhomogeneous_dirichlet_on_interval_specialized (propagates sorry)
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
    have h2 : ↑m * (2 * Real.pi) < (c - φ) + 2 * Real.pi := by
      have : (c - φ) / (2 * Real.pi) * (2 * Real.pi) = c - φ := by field_simp
      nlinarith [mul_lt_mul_of_pos_right hceil hpi]
    linarith

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
-- SECTION 5: K=1 Inhomogeneous (SORRY-FREE, requires ε ≤ 1)
-- ============================================================================

/-- K=1 inhomogeneous Dirichlet: if |γ| ≥ δ, ε ≤ 1, and b-a ≥ 2π/(εδ),
then there exists t₀ ∈ [a,b] with γ·t₀ ≡ φ (mod 2π) exactly.
The ε tolerance is not even needed — we get an exact hit because
|γ|·(b-a) ≥ δ·2π/(εδ) = 2π/ε ≥ 2π when ε ≤ 1. -/
theorem inhomogeneous_one_dim (γ φ ε δ a b : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hγ : δ ≤ |γ|) (hab : a < b)
    (hlen : 2 * Real.pi / (ε * δ) ≤ b - a) :
    ∃ t0 : ℝ, a ≤ t0 ∧ t0 ≤ b ∧
      ∃ m : ℤ, |t0 * γ - φ - m * (2 * Real.pi)| ≤ ε := by
  have hεδ : 0 < ε * δ := mul_pos hε hδ
  have hba : 0 < b - a := by linarith
  have h_image : 2 * Real.pi ≤ |γ| * (b - a) := by
    nlinarith [div_le_iff₀ hεδ |>.mp hlen,
               mul_le_mul_of_nonneg_left hε1 (le_of_lt (mul_pos hba hδ)),
               mul_le_mul_of_nonneg_left hγ (le_of_lt hba)]
  obtain ⟨t0, ht0a, ht0b, m, hm⟩ := one_dim_torus_cover γ φ a b (le_of_lt hab) h_image
  refine ⟨t0, ht0a, ht0b, m, ?_⟩
  have : t0 * γ - φ - m * (2 * Real.pi) = γ * t0 - φ - m * (2 * Real.pi) := by ring
  rw [this, hm, sub_self, abs_zero]; linarith

-- ============================================================================
-- SECTION 6: General K Inhomogeneous (1 SORRY — bridge to homogeneous)
-- ============================================================================

/-- Corrected simultaneous inhomogeneous Dirichlet approximation on an interval.

Given frequencies γ₁,...,γ_K with |γ_k| ≥ δ > 0, targets φ₁,...,φ_K,
tolerance ε > 0, and interval [a,b] with b-a ≥ (2π/(ε·δ))^K,
there exists t₀ ∈ [a,b] such that for all k, γ_k·t₀ ≈ φ_k (mod 2π)
within tolerance ε.

PROOF STRATEGY (not yet formalized for K ≥ 2):
  For ε ≤ 1, each |γ_k|·(b-a)^{1/K} ≥ 2π/ε ≥ 2π, so sub-intervals of length
  (b-a)^{1/K} give full torus coverage in each coordinate. The challenge is
  simultaneous coverage.

  Approach 1 (induction): Use dimension-by-dimension IVT. Fix coordinate K
  exactly (using one_dim_torus_cover), then the constraint set for coordinate K
  is discrete with spacing 2π/|γ_K| ≤ 2π/δ. With enough points (i.e., large
  enough interval), apply (K-1)-dimensional pigeonhole on the remaining coordinates.

  Approach 2 (direct pigeonhole on interval): Partition [a,b] into N equally
  spaced points. Map to K-torus via t ↦ (γ₁t mod 2π, ..., γ_Kt mod 2π).
  Partition torus into (2π/ε)^K cells. If N > (2π/ε)^K, pigeonhole gives
  the homogeneous result. Then use the approximate period to tile and hit
  the target.

  The K=1 case is proved above (inhomogeneous_one_dim) for ε ≤ 1.
  The homogeneous K-dimensional case is proved (homogeneous_dirichlet_integers).
  The bridge from homogeneous to inhomogeneous is the remaining sorry.
-/
theorem inhomogeneous_dirichlet_on_interval_v2
    (K : ℕ) (γ φ : Fin K → ℝ) (ε δ : ℝ) (a b : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hγ : ∀ k, δ ≤ |γ k|)
    (hab : a < b)
    (hlen : (2 * Real.pi / (ε * δ)) ^ K ≤ b - a) :
    ∃ t0 : ℝ, a ≤ t0 ∧ t0 ≤ b ∧
      ∀ k : Fin K, ∃ m : ℤ, |t0 * γ k - φ k - m * (2 * Real.pi)| ≤ ε := by
  sorry

-- ============================================================================
-- SECTION 7: Specialization for Littlewood proof
-- ============================================================================

/-- Specialized version matching the signature used in PerronExplicitFormulaProvider.
Uses ε = 1/2 and requires ∀ k, δ ≤ |γ k|.

In the downstream application:
- K = number of zeta zeros used
- γ_k = imaginary parts of zeros (all ≥ 14.13...)
- δ = 14.13... (lower bound on |γ_k|)
- [a,b] grows with T → ∞
So (4π/δ)^K ≤ b - a is satisfied for T large enough. -/
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
