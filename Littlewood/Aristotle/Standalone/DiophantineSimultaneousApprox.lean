import Mathlib

noncomputable section

open Real Int Finset

/-!
# Simultaneous Diophantine Approximation with Explicit Height Bound

We prove the simultaneous Dirichlet approximation theorem using the
pigeonhole principle, and derive a triple-exponential upper bound on the
approximation parameter `t`.

## Main Results

* `simultaneous_dirichlet` — For `θ : Fin n → ℝ` and `Q ≥ 1`,
  there exists `q ∈ [1, Q^n]` with `|q·θₖ - pₖ| < 1/Q` for all `k`.

* `diophantine_approximation_triple_exp` — For `θ : Fin n → ℝ` and `ε > 0`,
  there exists `t > 0` with
  `t ≤ exp(exp(exp(n·(7/ε + 1))))` such that each `t·θₖ` is within `ε`
  of an integer multiple of `2π`.

## Proof outline

The core argument is a multi-dimensional pigeonhole principle:

1. Map each `q ∈ {0, ..., Q^n}` to its "box index" in `(Fin Q)^n` via
   `k ↦ ⌊fract(q·θₖ)·Q⌋`.
2. Since `Q^n + 1 > Q^n`, two distinct values `q₁ < q₂` share the same box.
3. Their difference `q₂ − q₁` satisfies the approximation.

The triple-exponential bound arises from:
`q ≤ Q^n ≤ (7/ε + 1)^n ≤ exp(n·(7/ε+1)) ≤ exp(exp(exp(n·(7/ε+1))))`.
-/

/-! ## Box index and helper lemmas -/

/-- The natural floor of `fract(x) * Q` is strictly less than `Q` when `Q > 0`. -/
lemma floor_fract_mul_lt (x : ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ⌊Int.fract x * (Q : ℝ)⌋₊ < Q := by
  rw [ Nat.floor_lt ] <;> nlinarith [ Int.fract_nonneg x, Int.fract_lt_one x, show ( Q : ℝ ) ≥ 1 by norm_cast ]

/-- Box index: which of `Q` equal subdivisions of `[0,1)` does `fract(x)` lie in? -/
def boxIndex (x : ℝ) {Q : ℕ} (hQ : 0 < Q) : Fin Q :=
  ⟨⌊Int.fract x * (Q : ℝ)⌋₊, floor_fract_mul_lt x hQ⟩

/-- Two reals with the same box index have fractional parts within `1/Q`. -/
lemma abs_fract_sub_lt_of_boxIndex_eq {Q : ℕ} (hQ : 0 < Q) (x y : ℝ)
    (h : boxIndex x hQ = boxIndex y hQ) :
    |Int.fract x - Int.fract y| < 1 / (Q : ℝ) := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌊Int.fract x * Q⌋₊ ∧ j = ⌊Int.fract y * Q⌋₊ := by
    exact ⟨ _, rfl, congr_arg Fin.val h ⟩;
  rw [ lt_div_iff₀ ( by positivity ) ];
  cases abs_cases ( fract x - fract y ) <;> nlinarith [ Int.fract_nonneg x, Int.fract_lt_one x, Int.fract_nonneg y, Int.fract_lt_one y, show ( ⌊fract x * Q⌋₊ : ℝ ) = j by exact_mod_cast hj.1.symm, show ( ⌊fract y * Q⌋₊ : ℝ ) = j by exact_mod_cast hj.2.symm, Nat.floor_le ( mul_nonneg ( Int.fract_nonneg x ) <| Nat.cast_nonneg Q ), Nat.lt_floor_add_one ( fract x * Q ), Nat.floor_le ( mul_nonneg ( Int.fract_nonneg y ) <| Nat.cast_nonneg Q ), Nat.lt_floor_add_one ( fract y * Q ) ]

/-- The difference `a - b` equals `fract(a) - fract(b)` plus an integer. -/
lemma sub_eq_fract_sub_add_int (a b : ℝ) :
    ∃ m : ℤ, a - b - ↑m = Int.fract a - Int.fract b := by
  exact ⟨ ⌊a⌋ - ⌊b⌋, by push_cast; linarith [ Int.fract_add_floor a, Int.fract_add_floor b ] ⟩

/-! ## Pigeonhole step -/

/-- The cardinality of `Fin n → Fin Q` equals `Q ^ n`. -/
lemma card_fin_arrow_fin (n Q : ℕ) :
    Fintype.card (Fin n → Fin Q) = Q ^ n := by
  aesop

/-- Among `Q^n + 1` integer multiples of `θ`, two share the same box index.
    This is the multi-dimensional pigeonhole principle. -/
lemma pigeonhole_box {n : ℕ} (θ : Fin n → ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ i j : Fin (Q ^ n + 1), i < j ∧
      (fun k => boxIndex (↑i.val * θ k) hQ) =
      (fun k => boxIndex (↑j.val * θ k) hQ) := by
  by_contra! h;
  have h_card : (Finset.univ.image (fun i : Fin (Q^n + 1) => (fun k => boxIndex (↑i * θ k) hQ))).card = Q^n + 1 := by
    rw [ Finset.card_image_of_injective _ fun i j hij => le_antisymm ( not_lt.1 fun hi => h _ _ hi hij.symm ) ( not_lt.1 fun hj => h _ _ hj hij ), Finset.card_fin ];
  exact h_card.not_lt ( lt_of_le_of_lt ( Finset.card_le_univ _ ) ( by norm_num ) )

/-! ## Simultaneous Dirichlet approximation -/

/-- **Simultaneous Dirichlet Approximation Theorem (Homogeneous).**

For any `n` real numbers `θ₁,...,θₙ` and any positive integer `Q`,
there exists a positive integer `q ≤ Qⁿ` such that for each `k`,
`q·θₖ` is within `1/Q` of an integer.

This is proved by the multi-dimensional pigeonhole principle:
map each `q ∈ {0,...,Qⁿ}` to its box index in `(Fin Q)ⁿ`, observe that
`Qⁿ + 1` pigeons exceed `Qⁿ` holes, and take the difference of the
two integers sharing a box. -/
theorem simultaneous_dirichlet {n : ℕ} (θ : Fin n → ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ^ n ∧
      ∀ k : Fin n, ∃ p : ℤ, |↑q * θ k - ↑p| < 1 / (Q : ℝ) := by
  obtain ⟨ i, j, hij, h ⟩ := pigeonhole_box θ hQ;
  use j.val - i.val;
  refine' ⟨ Nat.sub_pos_of_lt hij, _, _ ⟩;
  · bv_omega;
  · intro k;
    obtain ⟨ p, hp ⟩ := sub_eq_fract_sub_add_int ( j.val * θ k ) ( i.val * θ k );
    use p;
    rw [ Nat.cast_sub hij.le ];
    convert abs_fract_sub_lt_of_boxIndex_eq hQ _ _ ( congr_fun h k ) using 1 ; ring;
    cases abs_cases ( ( j : ℝ ) * θ k + ( - ( i * θ k ) - p ) ) <;> cases abs_cases ( fract ( i * θ k ) - fract ( j * θ k ) ) <;> linarith

/-! ## Triple-exponential bound -/

/-- `⌈2π/ε⌉₊` is positive when `ε > 0`. -/
lemma ceil_two_pi_div_pos {ε : ℝ} (hε : 0 < ε) : 0 < ⌈2 * π / ε⌉₊ := by
  exact Nat.ceil_pos.mpr ( by positivity )

/-- `2π / ⌈2π/ε⌉₊ ≤ ε` when `ε > 0`. -/
lemma two_pi_div_ceil_le {ε : ℝ} (hε : 0 < ε) :
    2 * π / (⌈2 * π / ε⌉₊ : ℝ) ≤ ε := by
  exact div_le_of_le_mul₀ ( by positivity ) ( by positivity ) ( by nlinarith [ Nat.le_ceil ( ( 2:ℝ ) * Real.pi / ε ), mul_div_cancel₀ ( 2*Real.pi ) hε.ne' ] )

/-- The ceiling-based `Q` satisfies the triple-exponential bound:
    `⌈2π/ε⌉₊ ^ n ≤ exp(exp(exp(n · (7/ε + 1))))`. -/
lemma ceil_pow_le_triple_exp {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ((⌈2 * π / ε⌉₊ : ℝ) ^ n : ℝ) ≤ exp (exp (exp (↑n * (7 / ε + 1)))) := by
  refine' le_trans _ ( Real.exp_le_exp.2 <| Real.exp_le_exp.2 <| Real.exp_le_exp.2 <| mul_le_mul_of_nonneg_left _ <| Nat.cast_nonneg _ );
  rotate_left;
  exact ( 2 * Real.pi / ε + 1 );
  · gcongr;
    have h_pi_approx : Real.pi < 3.5 := by
      pi_upper_bound [ 7 / 5 ];
    norm_num at h_pi_approx ; linarith;
  · refine' le_trans _ ( Real.add_one_le_exp _ );
    refine' le_add_of_le_of_nonneg _ zero_le_one;
    rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( Nat.cast_pos.mpr <| Nat.ceil_pos.mpr <| by positivity ) ];
    norm_num;
    exact le_trans ( mul_le_mul_of_nonneg_right ( Real.log_le_sub_one_of_pos ( Nat.cast_pos.mpr <| Nat.ceil_pos.mpr <| by positivity ) ) <| Nat.cast_nonneg _ ) <| by nlinarith [ Real.add_one_le_exp ( n * ( 2 * Real.pi / ε + 1 ) ), show ( n : ℝ ) ≥ 1 by norm_cast, show ( ⌈2 * Real.pi / ε⌉₊ : ℝ ) ≤ 2 * Real.pi / ε + 1 by exact_mod_cast Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt ] ;

/-- **Inhomogeneous Simultaneous Diophantine Approximation with
    Triple-Exponential Height Bound.**

For `n ≥ 1` real numbers `θ₁,...,θₙ` (e.g. imaginary parts of nontrivial zeros
of the Riemann zeta function) and `ε > 0`, there exists a positive real `t`
bounded by `exp(exp(exp(n · (7/ε + 1))))` such that each `t · θₖ` is within `ε`
of an integer multiple of `2π`.

This is the *homogeneous* case of simultaneous Diophantine approximation
(target phases `αₖ = 0`). The general *inhomogeneous* case —
finding `t` with `|t · θₖ − αₖ − mₖ · 2π| ≤ ε` for prescribed phases `αₖ` —
requires additional hypotheses such as ℚ-linear independence of the
`θₖ/(2π)` (Kronecker's theorem). -/
theorem diophantine_approximation_triple_exp
    {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧
      (∀ k : Fin n, ∃ m : ℤ, |t * θ k - ↑m * (2 * π)| ≤ ε) ∧
      t ≤ exp (exp (exp (↑n * (7 / ε + 1)))) := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, 0 < q ∧ q ≤ (⌈2 * Real.pi / ε⌉₊ : ℕ) ^ n ∧ (∀ k, ∃ p : ℤ, |↑q * (θ k / (2 * Real.pi)) - ↑p| < 1 / (⌈2 * Real.pi / ε⌉₊ : ℝ)) := by
    convert simultaneous_dirichlet ( fun k => θ k / ( 2 * Real.pi ) ) ( show 0 < ( ⌈2 * Real.pi / ε⌉₊ : ℕ ) from Nat.ceil_pos.mpr ( by positivity ) ) using 1;
  refine' ⟨ q, mod_cast hq.1, _, _ ⟩;
  · intro k; obtain ⟨ p, hp ⟩ := hq.2.2 k; refine' ⟨ p, _ ⟩ ; rw [ mul_div, div_sub', abs_div ] at hp;
    · rw [ abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 * Real.pi ), div_lt_div_iff₀ ] at hp <;> try positivity;
      rw [ mul_comm _ ( 2 * Real.pi ) ] ; nlinarith [ Nat.le_ceil ( 2 * Real.pi / ε ), Real.pi_pos, mul_div_cancel₀ ( 2 * Real.pi ) hε.ne', show ( ⌈2 * Real.pi / ε⌉₊ : ℝ ) ≥ 1 from Nat.one_le_cast.mpr <| Nat.ceil_pos.mpr <| by positivity ];
    · positivity;
  · have := ceil_pow_le_triple_exp hn hε;
    exact le_trans ( mod_cast hq.2.1 ) this

end
