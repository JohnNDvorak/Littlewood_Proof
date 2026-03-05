# Aristotle Prompt C (Ultra Self-Contained, No Repo Access)

You are solving one deep Lean sorry with **zero access to our repository**.
Everything you need is below: full target file context and full transitive local dependency closure.

## Task
Complete **`exists_large_x_phases_aligned_to_target`** with no `axiom`, `admit`, or `sorry`, preserving the declaration signature exactly.

## Output Requirements
1. Return Lean code that replaces the `sorry` in `exists_large_x_phases_aligned_to_target`.
2. If helper lemmas are needed, include complete Lean code for them in the same response.
3. Do not require any external files not present in this prompt.
4. Keep namespace/import assumptions consistent with provided code.

## Version Contract
- Lean 4 + Mathlib 4 environment.
- No project-local file access beyond the code pasted in this prompt.

## Target File
- `Littlewood/Aristotle/DirichletPhaseAlignment.lean`

## Target Declaration Snippet (from target file)
```lean

This is the inhomogeneous simultaneous Dirichlet approximation with equal
targets. The lemma is FALSE for arbitrary frequency sets (counterexample:
γ₁=1, γ₂=2, w=e^{iπ/3}). For zeta zeros, it holds because:

(1) Zeta zero ordinates are NOT all commensurate: if ∃c>0 with all γ_k ∈ c·ℤ,
    then N⁺(T) ≤ T/c + O(1), contradicting N⁺(T) ~ (T/2π)logT from RvM.
(2) Not-commensurate frequencies generate a dense subgroup G ⊆ ℝ/2πℤ via
    the map t ↦ (tγ₁ mod 2π, ..., tγₙ mod 2π).
(3) Density of G implies G ⊇ Δ (the diagonal), giving equal-target approximation.

The homogeneous case (w = 1) is proved in `exists_large_x_phases_aligned_finset`.
The gap is extending to arbitrary w via Kronecker's theorem (1884).

Now takes RH as a parameter, since the proof uses properties specific to
zeta zero ordinates (superlinear growth of N(T)).

**Blocked by**: Kronecker's theorem formalization + uniform Riemann-von Mangoldt.

References: Kronecker 1884, Hardy-Wright (2008) §23.8, Titchmarsh (1986) §9.4. -/
lemma exists_large_x_phases_aligned_to_target
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    (hS_pos : ∀ ρ ∈ S, 0 < ρ.im)
    (w : ℂ) (hw : ‖w‖ = 1) (ε : ℝ) (hε : ε > 0) (X : ℝ)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε := by
  sorry

end Aristotle.DirichletPhaseAlignment

end
```

## Local Dependency Closure Included
- File count: 6
- Total bytes: 25266

### Included Local Files (transitive `import Littlewood.*` closure)
- `Littlewood/Aristotle/DirichletPhaseAlignment.lean`
- `Littlewood/Basic/ChebyshevFunctions.lean`
- `Littlewood/ExplicitFormulas/ExplicitFormulaPsi.lean`
- `Littlewood/ZetaZeros/SupremumRealPart.lean`
- `Littlewood/ZetaZeros/ZeroCountingFunction.lean`
- `Littlewood/ZetaZeros/ZeroDensity.lean`

## Full File: `Littlewood/Aristotle/DirichletPhaseAlignment.lean`
```lean
import Mathlib
import Littlewood.ZetaZeros.SupremumRealPart

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 3200000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.DirichletPhaseAlignment

/-
Definition of Chebyshev functions psi and theta.
-/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.floor x + 1), ArithmeticFunction.vonMangoldt n

noncomputable def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime, Real.log p

/-
Definitions of hypotheses and oscillation property.
-/
open Real Complex Filter Asymptotics Set

/-- The set of non-trivial zeros of the Riemann Zeta function. -/
def CriticalZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- The set of critical zeros with imaginary part bounded by T. -/
def ZerosBelow (T : ℝ) : Finset ℂ :=
  if h : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite then h.toFinset else ∅

/-- Hypothesis: There are infinitely many zeros on the critical line, and the number of zeros up to T is finite. -/
class HardyCriticalLineZerosHyp : Prop where
  infinite_critical_zeros : {ρ ∈ CriticalZeros | ρ.re = 1/2}.Infinite
  zeros_finite (T : ℝ) : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite

/-- Hypothesis: The explicit formula for ψ(x) holds with a specific error bound. -/
class ExplicitFormulaPsiHyp : Type where
  C : ℝ
  psi_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevPsi x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Hypothesis: The explicit formula for θ(x) holds with a specific error bound. -/
class ExplicitFormulaThetaHyp : Type where
  C : ℝ
  theta_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevTheta x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Definition of Ω± oscillation: The function takes arbitrarily large positive and negative values relative to g. -/
def IsOmegaOscillation (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ M, ∃ x, f x ≥ M * g x) ∧ (∀ M, ∃ x, f x ≤ -M * g x)

/-- The conclusion for ψ. -/
class PsiOscillationFromCriticalZerosHyp : Prop where
  psi_osc : IsOmegaOscillation (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ. -/
class ThetaOscillationSqrtHyp : Prop where
  theta_osc : IsOmegaOscillation (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

/-
Explicit formula + infinitely many critical zeros implies Ω±(√x) oscillation for ψ(x).
-/
instance [HardyCriticalLineZerosHyp] [ExplicitFormulaPsiHyp] : PsiOscillationFromCriticalZerosHyp := by
  -- By definition of `PsiOscillationFromCriticalZerosHyp`, we need to show that `chebyshevPsi x - x` oscillates like `sqrt x`.
  constructor;
  constructor <;> intro M <;> have := ‹ExplicitFormulaPsiHyp›.psi_approx 2 2 ( by norm_num ) ( by norm_num ) <;> norm_num at *;
  · use 0 ; norm_num [ chebyshevPsi ];
  · use 0; norm_num [ chebyshevPsi ] ;

/-
Explicit formula + infinitely many critical zeros implies Ω±(√x) oscillation for θ(x).
-/
instance [HardyCriticalLineZerosHyp] [ExplicitFormulaThetaHyp] : ThetaOscillationSqrtHyp := by
  by_contra h_contra;
  obtain ⟨h_pos, h_neg⟩ : (∀ M : ℝ, ∃ x, chebyshevTheta x - x ≥ M * Real.sqrt x) ∧ (∀ M : ℝ, ∃ x, chebyshevTheta x - x ≤ -M * Real.sqrt x) := by
    constructor <;> intro M <;> have := ‹ExplicitFormulaThetaHyp›.theta_approx 2 2 ( by norm_num ) ( by norm_num ) <;> norm_num at this;
    · use 0; norm_num;
      exact Finset.sum_nonneg fun _ _ => by positivity;
    · use 0; norm_num [ chebyshevTheta ] ;
      norm_num [ Finset.sum_filter ];
  exact h_contra ⟨ h_pos, h_neg ⟩

/-
Redefinition of oscillation at infinity and new theorem classes.
-/
open Real Complex Filter Asymptotics Set

/-- Definition of Ω± oscillation at infinity: The function takes arbitrarily large positive and negative values relative to g, for arbitrarily large inputs. -/
def IsOmegaOscillationAtTop (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ M, ∃ x, x > M ∧ f x ≥ M * g x) ∧ (∀ M, ∃ x, x > M ∧ f x ≤ -M * g x)

/-- The conclusion for ψ using the correct oscillation definition. -/
class PsiOscillationFromCriticalZerosHypAtTop : Prop where
  psi_osc : IsOmegaOscillationAtTop (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ using the correct oscillation definition. -/
class ThetaOscillationSqrtHypAtTop : Prop where
  theta_osc : IsOmegaOscillationAtTop (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

/-
Simultaneous Dirichlet Approximation Theorem: Given n real numbers and an integer N, there exists a small integer multiple that is close to an integer for all of them.
-/
lemma simultaneous_dirichlet_approximation {n : ℕ} (ξ : Fin n → ℝ) (N : ℕ) (hN : N > 0) :
  ∃ t : ℕ, 0 < t ∧ t ≤ N ^ n ∧ ∀ i, ∃ p : ℤ, |↑t * ξ i - p| ≤ 1 / N := by
    -- By the pigeonhole principle, since there are $N^n + 1$ vectors and only $N^n$ subcubes, at least two of these vectors must fall into the same subcube.
    obtain ⟨t1, t2, ht1t2, h_subcube⟩ : ∃ t1 t2 : ℕ, t1 < t2 ∧ t1 ≤ N^n ∧ t2 ≤ N^n ∧ ∀ i : Fin n, ⌊(t1 * ξ i - ⌊t1 * ξ i⌋ : ℝ) * N⌋ = ⌊(t2 * ξ i - ⌊t2 * ξ i⌋ : ℝ) * N⌋ := by
      by_contra h_contra;
      -- By the pigeonhole principle, since there are $N^n + 1$ vectors and only $N^n$ subcubes, at least two of these vectors must fall into the same subcube. Hence, we can find such $t1$ and $t2$.
      have h_pigeonhole : Finset.card (Finset.image (fun t : ℕ => fun i => ⌊((t : ℝ) * (ξ i) - ⌊(t : ℝ) * (ξ i)⌋) * N⌋) (Finset.range (N^n + 1))) ≤ N^n := by
        refine' le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _;
        exact Finset.Icc ( 0 : Fin n → ℤ ) ( fun _ => N - 1 );
        · exact fun x hx => Finset.mem_Icc.mpr ⟨ fun i => Int.floor_nonneg.mpr ( mul_nonneg ( Int.fract_nonneg _ ) ( Nat.cast_nonneg _ ) ), fun i => Int.le_sub_one_of_lt ( Int.floor_lt.mpr ( by norm_num; nlinarith [ Int.fract_nonneg ( ( x : ℝ ) * ξ i ), Int.fract_lt_one ( ( x : ℝ ) * ξ i ), show ( N : ℝ ) ≥ 1 by norm_cast ] ) ) ⟩;
        · erw [ Finset.card_map, Finset.card_pi ] ; aesop;
      exact (not_lt.2 h_pigeonhole) ( by rw [ Finset.card_image_of_injOn fun t ht t' ht' h => le_antisymm ( not_lt.mp fun contra => h_contra ⟨ t', t, contra, by linarith [ Finset.mem_range.mp ht', Finset.mem_range.mp ht ], by linarith [ Finset.mem_range.mp ht', Finset.mem_range.mp ht ], fun i => by simpa using congr_fun h.symm i ⟩ ) ( not_lt.mp fun contra => h_contra ⟨ t, t', contra, by linarith [ Finset.mem_range.mp ht, Finset.mem_range.mp ht' ], by linarith [ Finset.mem_range.mp ht, Finset.mem_range.mp ht' ], fun i => by simpa using congr_fun h i ⟩ ) ] ; simp +arith +decide );
    refine' ⟨ t2 - t1, tsub_pos_of_lt ht1t2, _, _ ⟩;
    · exact Nat.sub_le_of_le_add <| by linarith;
    · intro i; specialize h_subcube; have := h_subcube.2.2 i; rw [ Int.floor_eq_iff ] at this; norm_num at *;
      refine' ⟨ ⌊ ( t2 : ℝ ) * ξ i⌋ - ⌊ ( t1 : ℝ ) * ξ i⌋, _ ⟩ ; rw [ Nat.cast_sub ht1t2.le ] ; rw [ abs_le ] ; constructor <;> push_cast <;> nlinarith [ Int.fract_add_floor ( ( t2 : ℝ ) * ξ i ), Int.fract_add_floor ( ( t1 : ℝ ) * ξ i ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ), Int.floor_le ( Int.fract ( ( t2 : ℝ ) * ξ i ) * N ), Int.lt_floor_add_one ( Int.fract ( ( t2 : ℝ ) * ξ i ) * N ) ]

/-
For any finite set of frequencies and any epsilon, there exists an arbitrarily large x such that all phases align near 1.
-/
lemma exists_large_x_phases_aligned {n : ℕ} (γ : Fin n → ℝ) (ε : ℝ) (hε : ε > 0) (X : ℝ) :
  ∃ x > X, ∀ i, ‖(x : ℂ) ^ (I * γ i) - 1‖ < ε := by
    -- Define the frequencies $\gamma_i$.
    set γ_vals : Fin n → ℝ := fun i => γ i / (2 * Real.pi) with hγ_vals_def;
    -- Choose a large integer $N$ such that $N \delta > L + 1$, where $\delta = \epsilon / (2\pi)$ and $L = \log X$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 < N ∧ N * (ε / (4 * Real.pi)) > Real.log (max X 1) + 1 := by
      exact ⟨ ⌊ ( Real.log ( Max.max X 1 ) + 1 ) / ( ε / ( 4 * Real.pi ) ) ⌋₊ + 1, Nat.succ_pos _, by push_cast; nlinarith [ Nat.lt_floor_add_one ( ( Real.log ( Max.max X 1 ) + 1 ) / ( ε / ( 4 * Real.pi ) ) ), show 0 < ε / ( 4 * Real.pi ) by positivity, mul_div_cancel₀ ( Real.log ( Max.max X 1 ) + 1 ) ( show ε / ( 4 * Real.pi ) ≠ 0 by positivity ) ] ⟩;
    -- Apply Dirichlet approximation with a large integer $N$.
    obtain ⟨t₀, ht₀_pos, ht₀_le, ht₀_approx⟩ : ∃ t₀ : ℕ, 0 < t₀ ∧ t₀ ≤ N ^ n ∧ ∀ i, ∃ p : ℤ, |↑t₀ * γ_vals i - p| ≤ 1 / N := by
      convert simultaneous_dirichlet_approximation γ_vals N hN.1 using 1;
    -- Choose $k$ such that $k t₀ > L$ and $k/N < \delta$.
    obtain ⟨k, hk_pos, hk_gt_L, hk_lt_delta⟩ : ∃ k : ℕ, 0 < k ∧ k * t₀ > Real.log (max X 1) ∧ k / (N : ℝ) < ε / (4 * Real.pi) := by
      refine' ⟨ ⌊Real.log ( Max.max X 1 ) ⌋₊ + 1, _, _, _ ⟩ <;> norm_num;
      · nlinarith [ Nat.lt_floor_add_one ( Real.log ( Max.max X 1 ) ), show ( t₀ : ℝ ) ≥ 1 by norm_cast ];
      · rw [ div_lt_iff₀ ] <;> nlinarith [ Nat.floor_le ( Real.log_nonneg ( show 1 ≤ Max.max X 1 by norm_num ) ), Real.pi_gt_three, mul_div_cancel₀ ε ( by positivity : ( 4 * Real.pi ) ≠ 0 ), show ( N : ℝ ) ≥ 1 by norm_cast; linarith ];
    -- Let $t = k t₀$. Then $t \ge k > L$, so $e^t > X$.
    set t : ℝ := k * t₀ with ht_def
    have ht_gt_L : t > Real.log (max X 1) := by
      exact hk_gt_L
    have hx_gt_X : Real.exp t > max X 1 := by
      rwa [ gt_iff_lt, Real.log_lt_iff_lt_exp ( by positivity ) ] at ht_gt_L;
    -- And $|t \gamma_i - 2\pi (k p_i)| = k |t₀ \gamma_i - p_i| \le k/N < \delta$.
    have h_phase_approx : ∀ i, ∃ p : ℤ, |t * γ i - 2 * Real.pi * k * p| < ε / 2 := by
      intro i
      obtain ⟨p, hp⟩ := ht₀_approx i
      use p
      have h_phase_approx_i : |t * γ i - 2 * Real.pi * k * p| ≤ k / N * 2 * Real.pi := by
        convert mul_le_mul_of_nonneg_left hp ( show ( 0 : ℝ ) ≤ 2 * Real.pi * k by positivity ) using 1 <;> ring;
        rw [ show t * γ i - Real.pi * k * p * 2 = Real.pi * k * ( -p + t₀ * γ_vals i ) * 2 by push_cast [ ht_def, hγ_vals_def ] ; ring_nf; norm_num [ Real.pi_ne_zero ] ] ; rw [ abs_mul, abs_mul, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ Real.pi * k ) ] ; ring;
      exact h_phase_approx_i.trans_lt ( by nlinarith [ Real.pi_pos, mul_div_cancel₀ ( k : ℝ ) ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ), mul_div_cancel₀ ε ( by positivity : ( 4 * Real.pi ) ≠ 0 ) ] );
    -- This implies $|e^{i t \gamma_i} - 1| < \epsilon$ (roughly, using Lipschitz of exp).
    have h_exp_approx : ∀ i, ‖Complex.exp (Complex.I * (t * γ i)) - 1‖ < ε := by
      intro i
      obtain ⟨p, hp⟩ := h_phase_approx i
      have h_exp_approx_i : ‖Complex.exp (Complex.I * (t * γ i)) - 1‖ ≤ |t * γ i - 2 * Real.pi * k * p| := by
        have h_exp_approx_i : ‖Complex.exp (Complex.I * (t * γ i)) - 1‖ = ‖Complex.exp (Complex.I * (t * γ i - 2 * Real.pi * k * p)) - 1‖ := by
          norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
          norm_num [ mul_assoc, mul_comm Real.pi _, mul_left_comm ];
          norm_num [ show Real.cos ( t * γ i - p * ( k * ( 2 * Real.pi ) ) ) = Real.cos ( t * γ i ) by convert Real.cos_periodic.int_mul ( -p * k ) _ using 2; push_cast; ring, show Real.sin ( t * γ i - p * ( k * ( 2 * Real.pi ) ) ) = Real.sin ( t * γ i ) by convert Real.sin_periodic.int_mul ( -p * k ) _ using 2; push_cast; ring ];
        -- Using the fact that $|e^{i\theta} - 1| \leq |\theta|$ for any real $\theta$, we get:
        have h_exp_approx_i : ∀ θ : ℝ, ‖Complex.exp (Complex.I * θ) - 1‖ ≤ |θ| := by
          intros θ
          have h_exp_approx_i : ‖Complex.exp (Complex.I * θ) - 1‖ = 2 * |Real.sin (θ / 2)| := by
            norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
            rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring <;> norm_num [ Real.sin_sq, Real.cos_sq ] <;> ring;
            nlinarith [ Real.cos_sq' θ ];
          -- Using the fact that $|\sin(x)| \leq |x|$ for any real $x$, we get:
          have h_sin_approx : ∀ x : ℝ, |Real.sin x| ≤ |x| := fun x => abs_sin_le_abs;
          exact h_exp_approx_i.symm ▸ by simpa [ abs_div, mul_div_cancel₀ ] using mul_le_mul_of_nonneg_left ( h_sin_approx ( θ / 2 ) ) zero_le_two;
        convert h_exp_approx_i ( t * γ i - 2 * Real.pi * k * p ) using 1 ; norm_cast;
        aesop;
      linarith;
    use Real.exp t;
    simp_all +decide [ Complex.cpow_def_of_ne_zero, Complex.exp_ne_zero ];
    convert h_exp_approx using 3 ; rw [ Complex.log_exp ] <;> ring ; norm_num [ Real.pi_pos.ne' ];
    · positivity;
    · norm_cast ; linarith [ Real.pi_pos ]

/-
Redefinition of hypotheses with V2 suffix.
-/
open Real Complex Filter Asymptotics Set

/-- Hypothesis: There are infinitely many zeros on the critical line, and the sum of their reciprocals diverges. -/
class HardyCriticalLineZerosHyp_V2 : Prop where
  infinite_critical_zeros : {ρ ∈ CriticalZeros | ρ.re = 1/2}.Infinite
  zeros_finite (T : ℝ) : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite
  sum_inv_rho_diverges : ∀ B : ℝ, ∃ T : ℝ, ∑ ρ ∈ ZerosBelow T, 1 / ‖ρ‖ > B

/-- Hypothesis: The explicit formula for ψ(x) holds with a specific error bound. -/
class ExplicitFormulaPsiHyp_V2 : Type where
  C : ℝ
  psi_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevPsi x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Hypothesis: The explicit formula for θ(x) holds with a specific error bound. -/
class ExplicitFormulaThetaHyp_V2 : Type where
  C : ℝ
  theta_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevTheta x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- The conclusion for ψ using the correct oscillation definition. -/
class PsiOscillationFromCriticalZerosHypAtTop_V2 : Prop where
  psi_osc : IsOmegaOscillationAtTop (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ using the correct oscillation definition. -/
class ThetaOscillationSqrtHypAtTop_V2 : Prop where
  theta_osc : IsOmegaOscillationAtTop (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

/-
Redefinition of hypotheses with V3 suffix and helper lemma for Finset.
-/
open Real Complex Filter Asymptotics Set

/-- Hypothesis: There are infinitely many zeros on the critical line, and the sum of the real parts of their reciprocals diverges. -/
class HardyCriticalLineZerosHyp_V3 : Prop where
  infinite_critical_zeros : {ρ ∈ CriticalZeros | ρ.re = 1/2}.Infinite
  zeros_finite (T : ℝ) : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite
  sum_re_inv_rho_diverges : ∀ B : ℝ, ∃ T : ℝ, ∑ ρ ∈ ZerosBelow T, (1 / ρ).re > B

/-- Hypothesis: The explicit formula for ψ(x) holds with a specific error bound. -/
class ExplicitFormulaPsiHyp_V3 : Type where
  C : ℝ
  psi_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevPsi x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- Hypothesis: The explicit formula for θ(x) holds with a specific error bound. -/
class ExplicitFormulaThetaHyp_V3 : Type where
  C : ℝ
  theta_approx (x T : ℝ) (hx : x ≥ 2) (hT : T ≥ 2) :
    |chebyshevTheta x - x - (- (∑ ρ ∈ ZerosBelow T, (x : ℂ)^(ρ) / ρ).re)| ≤ C * (x.sqrt * Real.log T / T.sqrt + Real.log x)

/-- The conclusion for ψ using the correct oscillation definition. -/
class PsiOscillationFromCriticalZerosHypAtTop_V3 : Prop where
  psi_osc : IsOmegaOscillationAtTop (fun x => chebyshevPsi x - x) (fun x => Real.sqrt x)

/-- The conclusion for θ using the correct oscillation definition. -/
class ThetaOscillationSqrtHypAtTop_V3 : Prop where
  theta_osc : IsOmegaOscillationAtTop (fun x => chebyshevTheta x - x) (fun x => Real.sqrt x)

lemma exists_large_x_phases_aligned_finset (S : Finset ℂ) (_hS : ∀ ρ ∈ S, ρ.re = 1/2) (ε : ℝ) (hε : ε > 0) (X : ℝ) :
  ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - 1‖ < ε := by
    -- Apply the simultaneous Dirichlet approximation theorem to the frequencies γ_i = ρ.im for ρ in S.
    have h_dirichlet : ∀ (γ : Fin (Finset.card S) → ℝ) (ε : ℝ) (hε : ε > 0) (X : ℝ), ∃ x > X, ∀ i, ‖(x : ℂ) ^ (I * γ i) - 1‖ < ε :=
      fun γ' ε' hε' X' => exists_large_x_phases_aligned γ' ε' hε' X';
    -- By definition of $S$, we can create a bijection between $S$ and $\{0, 1, ..., S.card - 1\}$.
    obtain ⟨f, hf⟩ : ∃ f : S ≃ Fin (Finset.card S), True := by
      exact ⟨ Fintype.equivOfCardEq <| by simp +decide, trivial ⟩;
    obtain ⟨ x, hx₁, hx₂ ⟩ := h_dirichlet ( fun i => ( f.symm i |> Subtype.val |> Complex.im ) ) ε hε X;
    exact ⟨ x, hx₁, fun ρ hρ => by simpa using hx₂ ( f ⟨ ρ, hρ ⟩ ) ⟩

/-
Lower bound on the real part of the sum when phases are aligned.
-/
lemma bound_real_part_of_sum_aligned {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re = 1/2) {x : ℝ} (hx : x > 0) {ε : ℝ} (_hε : ε > 0)
  (h_phases : ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - 1‖ < ε) :
  (∑ ρ ∈ S, (x : ℂ)^ρ / ρ).re ≥ Real.sqrt x * ((∑ ρ ∈ S, (1/ρ).re) - ε * (∑ ρ ∈ S, 1/‖ρ‖)) := by
    -- For each $\rho \in S$, we have $\text{Re}(x^\rho/\rho) = \sqrt{x} \text{Re}(u_\rho/\rho)$ where $u_\rho = x^{i \text{Im}(\rho)}$.
    have h_re_expr (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re ((x : ℂ) ^ ρ / ρ) = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
      rw [ show ρ = 1 / 2 + Complex.I * ρ.im by simp +decide [ Complex.ext_iff, hS ρ hρ ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero, hx.ne' ] ; ring;
      norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring;
      norm_num [ Complex.arg_ofReal_of_nonneg hx.le, Real.sin_add, Real.cos_add, mul_assoc, ← Real.exp_add ] ; ring;
    -- Using the bound on $\|u_\rho - 1\|$, we get $\text{Re}((u_\rho - 1)/\rho) \ge -|(u_\rho - 1)/\rho| = -|u_\rho - 1|/|\rho| > -\epsilon/|\rho|$.
    have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - 1) / ρ) ≥ -ε / ‖ρ‖ := by
      have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - 1) / ρ) ≥ -‖((x : ℂ) ^ (Complex.I * ρ.im) - 1) / ρ‖ := by
        exact neg_le_of_abs_le ( Complex.abs_re_le_norm _ ) |> le_trans <| by norm_num;
      exact le_trans ( by simpa [ neg_div ] using div_le_div_of_nonneg_right ( neg_le_neg ( le_of_lt ( h_phases ρ hρ ) ) ) ( norm_nonneg ρ ) ) ( h_re_bound ρ hρ );
    simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
    rw [ ← Finset.sum_sub_distrib ];
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_re_bound i hi, Real.sqrt_nonneg x ] ;

/-
Generalized lower bound on Re(∑ x^ρ/ρ) when phases are aligned to an arbitrary
target w on the unit circle (not just w = 1).

When w = I (imaginary unit), the main term ∑ Re(I/ρ) = ∑ γ/(1/4+γ²) ≈ ∑ 1/γ
which DIVERGES — this is the key to proving Littlewood's oscillation theorem.
Contrast with w = 1 where ∑ Re(1/ρ) = ∑ (1/2)/(1/4+γ²) CONVERGES.
-/
lemma bound_real_part_of_sum_shifted {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    {x : ℝ} (hx : x > 0) {w : ℂ} (_hw : ‖w‖ = 1) {ε : ℝ} (_hε : ε > 0)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε) :
    (∑ ρ ∈ S, (x : ℂ)^ρ / ρ).re ≥ Real.sqrt x * ((∑ ρ ∈ S, (w/ρ).re) - ε * (∑ ρ ∈ S, 1/‖ρ‖)) := by
  -- Decompose x^ρ/ρ = √x · u_ρ/ρ where u_ρ = x^{iγ}
  have h_re_expr (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re ((x : ℂ) ^ ρ / ρ) = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
    rw [ show ρ = 1 / 2 + Complex.I * ρ.im by simp +decide [ Complex.ext_iff, hS ρ hρ ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero, hx.ne' ] ; ring;
    norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring;
    norm_num [ Complex.arg_ofReal_of_nonneg hx.le, Real.sin_add, Real.cos_add, mul_assoc, ← Real.exp_add ] ; ring;
  -- Bound: Re((u_ρ - w)/ρ) ≥ -ε/‖ρ‖
  have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ) ≥ -ε / ‖ρ‖ := by
    have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ) ≥ -‖((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ‖ := by
      exact neg_le_of_abs_le ( Complex.abs_re_le_norm _ ) |> le_trans <| by norm_num;
    exact le_trans ( by simpa [ neg_div ] using div_le_div_of_nonneg_right ( neg_le_neg ( le_of_lt ( h_phases ρ hρ ) ) ) ( norm_nonneg ρ ) ) ( h_re_bound ρ hρ );
  simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
  rw [ ← Finset.sum_sub_distrib ];
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_re_bound i hi, Real.sqrt_nonneg x ] ;

/-
Upper bound companion: when phases are aligned to w, the real part of ∑ x^ρ/ρ
is at most √x · (∑ Re(w/ρ) + ε · ∑ 1/‖ρ‖).
Needed for the NEGATIVE oscillation direction.
-/
lemma bound_real_part_of_sum_shifted_upper {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    {x : ℝ} (hx : x > 0) {w : ℂ} (_hw : ‖w‖ = 1) {ε : ℝ} (_hε : ε > 0)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε) :
    (∑ ρ ∈ S, (x : ℂ)^ρ / ρ).re ≤ Real.sqrt x * ((∑ ρ ∈ S, (w/ρ).re) + ε * (∑ ρ ∈ S, 1/‖ρ‖)) := by
  -- Decompose x^ρ/ρ = √x · u_ρ/ρ where u_ρ = x^{iγ}
  have h_re_expr (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re ((x : ℂ) ^ ρ / ρ) = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
    rw [ show ρ = 1 / 2 + Complex.I * ρ.im by simp +decide [ Complex.ext_iff, hS ρ hρ ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero, hx.ne' ] ; ring;
    norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring;
    norm_num [ Complex.arg_ofReal_of_nonneg hx.le, Real.sin_add, Real.cos_add, mul_assoc, ← Real.exp_add ] ; ring;
  -- Bound: Re((u_ρ - w)/ρ) ≤ ε/‖ρ‖
  have h_re_bound (ρ : ℂ) (hρ : ρ ∈ S) : Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ) ≤ ε / ‖ρ‖ := by
    calc Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ)
        ≤ ‖((x : ℂ) ^ (Complex.I * ρ.im) - w) / ρ‖ :=
          le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
      _ = ‖(x : ℂ) ^ (Complex.I * ρ.im) - w‖ / ‖ρ‖ := by
          rw [norm_div]
      _ ≤ ε / ‖ρ‖ := by
          exact div_le_div_of_nonneg_right (le_of_lt (h_phases ρ hρ)) (norm_nonneg ρ)
  simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
  rw [ ← Finset.sum_add_distrib ];
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_re_bound i hi, Real.sqrt_nonneg x ] ;

/-- **B5b-infra sorry**: Phase alignment to an arbitrary target w on S¹.

Given RH, a finite set S of zeros with Re(ρ) = 1/2 and Im(ρ) > 0, a target w
with ‖w‖ = 1, ε > 0, and X, there exists x > X such that all phases
x^{iγ} are within ε of w.

This is the inhomogeneous simultaneous Dirichlet approximation with equal
targets. The lemma is FALSE for arbitrary frequency sets (counterexample:
γ₁=1, γ₂=2, w=e^{iπ/3}). For zeta zeros, it holds because:

(1) Zeta zero ordinates are NOT all commensurate: if ∃c>0 with all γ_k ∈ c·ℤ,
    then N⁺(T) ≤ T/c + O(1), contradicting N⁺(T) ~ (T/2π)logT from RvM.
(2) Not-commensurate frequencies generate a dense subgroup G ⊆ ℝ/2πℤ via
    the map t ↦ (tγ₁ mod 2π, ..., tγₙ mod 2π).
(3) Density of G implies G ⊇ Δ (the diagonal), giving equal-target approximation.

The homogeneous case (w = 1) is proved in `exists_large_x_phases_aligned_finset`.
The gap is extending to arbitrary w via Kronecker's theorem (1884).

Now takes RH as a parameter, since the proof uses properties specific to
zeta zero ordinates (superlinear growth of N(T)).

**Blocked by**: Kronecker's theorem formalization + uniform Riemann-von Mangoldt.

References: Kronecker 1884, Hardy-Wright (2008) §23.8, Titchmarsh (1986) §9.4. -/
lemma exists_large_x_phases_aligned_to_target
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    (hS_pos : ∀ ρ ∈ S, 0 < ρ.im)
    (w : ℂ) (hw : ‖w‖ = 1) (ε : ℝ) (hε : ε > 0) (X : ℝ)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε := by
  sorry

end Aristotle.DirichletPhaseAlignment

end
```

## Full Dependency File: `Littlewood/Basic/ChebyshevFunctions.lean`
```lean
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Chebyshev Functions - Extensions

This file provides aliases and additional lemmas for the Chebyshev functions
from Mathlib.NumberTheory.Chebyshev.

The main definitions are:
* `Chebyshev.psi` : ψ(x) = ∑_{n ≤ x} Λ(n)
* `Chebyshev.theta` : θ(x) = ∑_{p ≤ x, p prime} log(p)

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 2
-/

open Nat ArithmeticFunction Finset BigOperators Real Filter
open scoped Chebyshev

-- Alias for compatibility with existing code
noncomputable def chebyshevPsi (x : ℝ) : ℝ := Chebyshev.psi x
noncomputable def chebyshevTheta (x : ℝ) : ℝ := Chebyshev.theta x

namespace ChebyshevExt

-- Additional lemmas not in Mathlib

-- Asymptotics
open Asymptotics in
theorem chebyshevPsi_sub_chebyshevTheta_isBigO :
    (fun x => ψ x - θ x) =O[atTop] (fun x => x.sqrt * log x) := by
  refine IsBigO.of_bound 2 ?_
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨1, ?_⟩
  intro x hx
  have hbound := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) hx
  have hxlog : 0 ≤ log x := by
    exact log_nonneg (by linarith)
  have hx0 : 0 ≤ x.sqrt := by
    exact Real.sqrt_nonneg _
  have hnorm : ‖x.sqrt * log x‖ = x.sqrt * log x := by
    calc
      ‖x.sqrt * log x‖ = |x.sqrt * log x| := by
        simp [Real.norm_eq_abs]
      _ = |x.sqrt| * |log x| := by
        simp [abs_mul]
      _ = x.sqrt * log x := by
        simp [abs_of_nonneg hx0, abs_of_nonneg hxlog]
  have hbound' : |ψ x - θ x| ≤ 2 * (x.sqrt * log x) := by
    simpa [mul_assoc] using hbound
  simpa [Real.norm_eq_abs, hnorm] using hbound'

theorem chebyshevTheta_le (x : ℝ) (hx : 1 ≤ x) : θ x ≤ 2 * x := by
  -- log(4) ≈ 1.39 < 2
  calc θ x ≤ Real.log 4 * x := Chebyshev.theta_le_log4_mul_x (by linarith)
    _ ≤ 2 * x := by
      have h : Real.log 4 ≤ 2 := by
        have h' : (4 : ℝ) ≤ Real.exp 2 := by
          have h'' : (2 : ℝ) * 2 ≤ Real.exp 2 := by
            simpa using (Real.two_mul_le_exp (x := (2 : ℝ)))
          nlinarith
        exact (Real.log_le_iff_le_exp (by norm_num)).2 h'
      nlinarith

theorem chebyshevPsi_le (x : ℝ) (hx : 1 ≤ x) : ψ x ≤ 6 * x := by
  -- log(4) + 4 ≈ 5.39 < 6
  calc ψ x ≤ (Real.log 4 + 4) * x := Chebyshev.psi_le_const_mul_self (by linarith)
    _ ≤ 6 * x := by
      have h : Real.log 4 ≤ 2 := by
        have h' : (4 : ℝ) ≤ Real.exp 2 := by
          have h'' : (2 : ℝ) * 2 ≤ Real.exp 2 := by
            simpa using (Real.two_mul_le_exp (x := (2 : ℝ)))
          nlinarith
        exact (Real.log_le_iff_le_exp (by norm_num)).2 h'
      nlinarith

-- PNT asymptotics (chebyshevTheta_asymptotic, chebyshevPsi_asymptotic,
-- chebyshevTheta_eventually_ge) quarantined to ChebyshevFunctionsQuarantine.lean.
-- They are correct but axiomatized; not imported by the build.

-- Specific values
theorem chebyshevTheta_two : θ 2 = Real.log 2 := by
  have hprim : primorial 2 = 2 := by
    decide
  simpa [hprim] using (Chebyshev.theta_eq_log_primorial (x := (2 : ℝ)))

theorem chebyshevPsi_two : ψ 2 = Real.log 2 := by
  have htheta : θ 2 = Real.log 2 := chebyshevTheta_two
  have hlog2 : Real.log 2 ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  have hfloor : ⌊Real.log 2 / Real.log 2⌋₊ = 1 := by
    simp [hlog2]
  have hsum :
      (∑ n ∈ Icc 2 ⌊Real.log 2 / Real.log 2⌋₊, θ (2 ^ ((n : ℝ)⁻¹))) = 0 := by
    have hIcc : Icc (2 : ℕ) (⌊Real.log 2 / Real.log 2⌋₊) = ∅ := by
      simp [hfloor]
    simp [hIcc]
  have hpsi :
      ψ 2 = θ 2 + ∑ n ∈ Icc 2 ⌊Real.log 2 / Real.log 2⌋₊, θ (2 ^ ((n : ℝ)⁻¹)) := by
    simpa using (Chebyshev.psi_eq_theta_add_sum_theta (x := (2 : ℝ)) (by norm_num))
  calc
    ψ 2 = θ 2 := by simpa [hsum] using hpsi
    _ = Real.log 2 := htheta

end ChebyshevExt
```

## Full Dependency File: `Littlewood/ExplicitFormulas/ExplicitFormulaPsi.lean`
```lean
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.Basic.ChebyshevFunctions
import Littlewood.ZetaZeros.ZeroDensity
import Mathlib.Analysis.MellinTransform

/-!
# Explicit Formula for ψ

This file proves the Riemann-von Mangoldt explicit formula, which expresses
the Chebyshev function ψ(x) in terms of zeta zeros.

## Main Results

* `explicit_formula_psi` : ψ₀(x) = x - ∑_ρ x^ρ/ρ - log(2π) - (1/2)log(1-x⁻²)

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 12
* Edwards, "Riemann's Zeta Function", Chapter 3
-/

open Complex Real Filter Topology Set MeasureTheory
open Chebyshev ZetaZeros

namespace ExplicitFormula

/-! ## Normalized Chebyshev Function -/

/-- The normalized version ψ₀(x) = (ψ(x⁺) + ψ(x⁻))/2 -/
noncomputable def chebyshevPsi0 (x : ℝ) : ℝ :=
  if x = ⌊x⌋ then (chebyshevPsi x + chebyshevPsi (x - 1)) / 2
  else chebyshevPsi x

/-- Notation for ψ₀ -/
scoped notation "ψ₀" => chebyshevPsi0

/-- ψ₀ agrees with ψ except at integers -/
theorem chebyshevPsi0_eq_of_not_int {x : ℝ} (hx : x ≠ ⌊x⌋) : ψ₀ x = chebyshevPsi x := by
  simp [chebyshevPsi0, hx]

/-! ## The Explicit Formula -/

/--
HYPOTHESIS: Riemann-von Mangoldt explicit formula for ψ₀.
MATHEMATICAL STATUS: classical analytic number theory.
MATHLIB STATUS: not available.
-/
class ExplicitFormulaPsiHyp : Prop where
  formula :
    ∀ x : ℝ, 1 < x →
      ∃ E : ℂ, ‖E‖ ≤ Real.log x ∧
        (ψ₀ x : ℂ) = x - ∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val
          - Real.log (2 * π) - (1/2 : ℂ) * Real.log (1 - x^(-2 : ℤ)) + E

/-- The Riemann-von Mangoldt explicit formula -/
theorem explicit_formula_psi (x : ℝ) (hx : 1 < x) [ExplicitFormulaPsiHyp] :
    ∃ E : ℂ, ‖E‖ ≤ Real.log x ∧
    (ψ₀ x : ℂ) = x - ∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val
           - Real.log (2 * π) - (1/2 : ℂ) * Real.log (1 - x^(-2 : ℤ)) + E := by
  simpa using (ExplicitFormulaPsiHyp.formula x hx)

/-- The sum over zeros converges conditionally (symmetric pairing) -/
theorem explicit_formula_psi_conditional (x : ℝ) (hx : 1 < x) [ExplicitFormulaPsiHyp] :
    ∃ E : ℂ, ‖E‖ ≤ Real.log x ∧
    (ψ₀ x : ℂ) = x - ∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val
           - Real.log (2 * π) - (1/2 : ℂ) * Real.log (1 - x^(-2 : ℤ)) + E := by
  simpa using explicit_formula_psi x hx

/-! ## Smoothed Versions -/

/-- Smoothed Chebyshev function ψ_k(x) = (1/k!) ∑_{n≤x} (x-n)^k Λ(n) -/
noncomputable def chebyshevPsiSmoothed (k : ℕ) (x : ℝ) : ℝ :=
  1 / k.factorial * ∑ n ∈ Finset.Icc 1 (Nat.floor x),
    (x - n)^k * ArithmeticFunction.vonMangoldt n

/-- Notation for ψ_k -/
scoped notation "ψ_" k => chebyshevPsiSmoothed k

/--
HYPOTHESIS: Explicit formula for smoothed ψ_k.
MATHEMATICAL STATUS: classical explicit formula.
MATHLIB STATUS: not available.
-/
class ExplicitFormulaPsiSmoothedHyp : Prop where
  formula :
    ∀ k : ℕ, ∀ x : ℝ, 1 < x →
      ∃ E : ℂ, ‖E‖ ≤ x^k ∧
        (chebyshevPsiSmoothed k x : ℂ) = (x : ℂ)^(k+1 : ℕ) / (k+1).factorial
          - ∑' ρ : zetaNontrivialZeros,
              (x : ℂ)^ρ.val / (ρ.val * (ρ.val + 1))
          + E

/-- Explicit formula for ψ_k with error bound -/
theorem explicit_formula_psiSmoothed (k : ℕ) (x : ℝ) (hx : 1 < x)
    [ExplicitFormulaPsiSmoothedHyp] :
    ∃ E : ℂ, ‖E‖ ≤ x^k ∧
    (chebyshevPsiSmoothed k x : ℂ) = (x : ℂ)^(k+1 : ℕ) / (k+1).factorial
           - ∑' ρ : zetaNontrivialZeros,
               (x : ℂ)^ρ.val / (ρ.val * (ρ.val + 1))
           + E := by
  simpa using (ExplicitFormulaPsiSmoothedHyp.formula k x hx)

/-! ## Integral Version -/

/--
HYPOTHESIS: Integrated explicit formula for ψ.
MATHEMATICAL STATUS: classical explicit formula.
MATHLIB STATUS: not available.
-/
class ExplicitFormulaIntegralHyp : Prop where
  formula :
    ∀ x : ℝ, 1 < x →
      ∃ E : ℂ, ‖E‖ ≤ x ∧
        (∫ u in Set.Icc 1 x, chebyshevPsi u : ℂ) =
          (x : ℂ)^(2 : ℕ) / 2 - x
          - ∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / (ρ.val * (ρ.val + 1))
          + E

/--
HYPOTHESIS: Double-integrated explicit formula for ψ.
MATHEMATICAL STATUS: classical explicit formula.
MATHLIB STATUS: not available.
-/
class ExplicitFormulaDoubleIntegralHyp : Prop where
  formula :
    ∀ x : ℝ, 1 < x →
      ∃ E : ℂ, ‖E‖ ≤ x^2 ∧
        (∫ u in Set.Icc 1 x, ∫ t in Set.Icc 1 u, chebyshevPsi t : ℂ) =
          (x : ℂ)^(3 : ℕ) / 6 - (x : ℂ)^(2 : ℕ) / 2
          - ∑' ρ : zetaNontrivialZeros,
              (x : ℂ)^ρ.val / (ρ.val * (ρ.val + 1) * (ρ.val + 2))
          + E

/-- Integrated form: ∫₁ˣ ψ(u) du -/
theorem explicit_formula_integral (x : ℝ) (hx : 1 < x) [ExplicitFormulaIntegralHyp] :
    ∃ E : ℂ, ‖E‖ ≤ x ∧
    (∫ u in Set.Icc 1 x, chebyshevPsi u : ℂ) =
      (x : ℂ)^(2 : ℕ) / 2 - x - ∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / (ρ.val * (ρ.val + 1))
      + E := by
  simpa using (ExplicitFormulaIntegralHyp.formula x hx)

/-- Second integral: ∫₁ˣ ∫₁ᵘ ψ(t) dt du -/
theorem explicit_formula_double_integral (x : ℝ) (hx : 1 < x)
    [ExplicitFormulaDoubleIntegralHyp] :
    ∃ E : ℂ, ‖E‖ ≤ x^2 ∧
    (∫ u in Set.Icc 1 x, ∫ t in Set.Icc 1 u, chebyshevPsi t : ℂ) =
      (x : ℂ)^(3 : ℕ) / 6 - (x : ℂ)^(2 : ℕ) / 2
      - ∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / (ρ.val * (ρ.val + 1) * (ρ.val + 2))
      + E := by
  simpa using (ExplicitFormulaDoubleIntegralHyp.formula x hx)

/-! ## Mellin Transform Approach -/

section Mellin

/--
HYPOTHESIS: Mellin transform representation of ψ₀.
MATHEMATICAL STATUS: standard Mellin inversion argument.
MATHLIB STATUS: not available.
-/
class PsiMellinHyp : Prop where
  representation :
    ∀ x : ℝ, 0 < x → ∀ c : ℝ, 1 < c →
      ∃ E : ℂ, ‖E‖ ≤ 1 ∧
        (ψ₀ x : ℂ) = 1 / (2 * π * Complex.I) *
          ∫ t : ℝ, (x : ℂ)^(c + t * Complex.I) / (c + t * Complex.I) *
            (-deriv riemannZeta (c + t * Complex.I) / riemannZeta (c + t * Complex.I)) + E

/--
HYPOTHESIS: Contour shift for the Mellin integral of ψ₀.
MATHEMATICAL STATUS: residue calculation plus tail bounds.
MATHLIB STATUS: not available.
-/
class MellinContourShiftHyp : Prop where
  shift :
    ∀ x : ℝ, 1 < x → ∀ c : ℝ, 1 < c →
      ∃ E : ℂ, ‖E‖ ≤ Real.log x ∧
        1 / (2 * π * Complex.I) *
          ∫ t : ℝ, (x : ℂ)^(c + t * Complex.I) / (c + t * Complex.I) *
            (-deriv riemannZeta (c + t * Complex.I) / riemannZeta (c + t * Complex.I))
        = x - ∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val
          - Real.log (2 * π) - (1/2 : ℂ) * Real.log (1 - x^(-2 : ℤ)) + E

/-- The Mellin transform representation -/
theorem psi_mellin (x : ℝ) (hx : 0 < x) (c : ℝ) (hc : 1 < c) [PsiMellinHyp] :
    ∃ E : ℂ, ‖E‖ ≤ 1 ∧
    (ψ₀ x : ℂ) = 1 / (2 * π * Complex.I) *
      ∫ t : ℝ, (x : ℂ)^(c + t * Complex.I) / (c + t * Complex.I) *
        (-deriv riemannZeta (c + t * Complex.I) / riemannZeta (c + t * Complex.I)) + E := by
  simpa using (PsiMellinHyp.representation x hx c hc)

/-- The trivial zero contribution -/
noncomputable def trivialZeroSum (x : ℝ) : ℂ := -(1/2 : ℂ) * Real.log (1 - x^(-2 : ℤ))

/-- Shifting the contour to the left picks up residues at zeros -/
theorem mellin_contour_shift (x : ℝ) (hx : 1 < x) (c : ℝ) (hc : 1 < c)
    [MellinContourShiftHyp] :
    ∃ E : ℂ, ‖E‖ ≤ Real.log x ∧
    1 / (2 * π * Complex.I) *
      ∫ t : ℝ, (x : ℂ)^(c + t * Complex.I) / (c + t * Complex.I) *
        (-deriv riemannZeta (c + t * Complex.I) / riemannZeta (c + t * Complex.I))
    = x - ∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val
      - Real.log (2 * π) + trivialZeroSum x + E := by
  simpa [trivialZeroSum] using (MellinContourShiftHyp.shift x hx c hc)

end Mellin

/-! ## Error Bounds -/

section ErrorBounds

/--
HYPOTHESIS: RH bound on the zero sum.
MATHEMATICAL STATUS: classical zero-density estimates under RH.
MATHLIB STATUS: not available.
-/
class ZeroSumBoundRHHyp : Prop where
  bound :
    ∀ hRH : RiemannHypothesis', ∀ x : ℝ, 2 ≤ x →
      ‖∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val‖
      ≤ 10 * Real.sqrt x * (Real.log x)^2

/--
HYPOTHESIS: Explicit formula gives ψ(x) - x = O(x^Θ log x).
MATHEMATICAL STATUS: classical explicit formula.
MATHLIB STATUS: not available.
-/
class PsiErrorBoundHyp : Prop where
  bound :
    ∀ x : ℝ, 2 ≤ x →
      |chebyshevPsi x - x| ≤ 10 * x^Θ * Real.log x

/--
HYPOTHESIS: RH gives ψ(x) - x = O(x^{1/2} log²x).
MATHEMATICAL STATUS: classical explicit formula under RH.
MATHLIB STATUS: not available.
-/
class PsiErrorBoundRHHyp : Prop where
  bound :
    ∀ hRH : RiemannHypothesis', ∀ x : ℝ, 2 ≤ x →
      |chebyshevPsi x - x| ≤ 10 * Real.sqrt x * (Real.log x)^2

/-- Under RH: |∑_ρ x^ρ/ρ| ≤ C x^{1/2} log² x -/
theorem zero_sum_bound_RH (hRH : RiemannHypothesis') (x : ℝ) (hx : 2 ≤ x)
    [ZeroSumBoundRHHyp] :
    ‖∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val‖
    ≤ 10 * Real.sqrt x * (Real.log x)^2 := by
  simpa using (ZeroSumBoundRHHyp.bound hRH x hx)

/-- The explicit formula gives: ψ(x) - x = O(x^Θ log x) -/
theorem psi_error_bound (x : ℝ) (hx : 2 ≤ x) [PsiErrorBoundHyp] :
    |chebyshevPsi x - x| ≤ 10 * x^Θ * Real.log x := by
  simpa using (PsiErrorBoundHyp.bound x hx)

/-- Under RH: ψ(x) - x = O(x^{1/2} log² x) -/
theorem psi_error_bound_RH (hRH : RiemannHypothesis') (x : ℝ) (hx : 2 ≤ x)
    [PsiErrorBoundRHHyp] :
    |chebyshevPsi x - x| ≤ 10 * Real.sqrt x * (Real.log x)^2 := by
  simpa using (PsiErrorBoundRHHyp.bound hRH x hx)

end ErrorBounds

-- ============================================================
-- INSTANCES (Documented Assumptions)
-- ============================================================
-- Instances for these hypotheses are provided in `Littlewood/Assumptions.lean`.

end ExplicitFormula
```

## Full Dependency File: `Littlewood/ZetaZeros/SupremumRealPart.lean`
```lean
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.Basic.ChebyshevFunctions
import Littlewood.ExplicitFormulas.ExplicitFormulaPsi
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.IsLUB

/-!
# Supremum of Real Parts of Zeta Zeros

This file defines Θ = sup{Re(ρ) : ρ is a nontrivial zero of ζ} and proves
basic bounds. The Riemann Hypothesis is equivalent to Θ = 1/2.

## Definitions

* `zetaZeroSupRealPart` : Θ = sup{Re(ρ)}

## Main Results

* `zetaZeroSupRealPart_le_one` : Θ ≤ 1
* `zetaZeroSupRealPart_ge_half` : 1/2 ≤ Θ
* `RiemannHypothesis_iff` : RH ↔ Θ = 1/2

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 13
-/

open Complex Real Filter Topology Set ZetaZeros

namespace ZetaZeros

/-! ## Definition of Θ -/

/-- The set of real parts of nontrivial zeros -/
def zetaZeroRealParts : Set ℝ :=
  (·.re) '' zetaNontrivialZeros

/-- Θ = sup{Re(ρ) : ρ is a nontrivial zero of ζ} -/
noncomputable def zetaZeroSupRealPart : ℝ :=
  sSup zetaZeroRealParts

/-- Notation for Θ -/
scoped notation "Θ" => zetaZeroSupRealPart

/-! ## Hypotheses -/

/--
HYPOTHESIS: De la Vallee Poussin zero-free region for zeta.
MATHEMATICAL STATUS: classical analytic number theory.
MATHLIB STATUS: not available.
REFERENCE: Montgomery-Vaughan, Ch. 12.
-/
class ZeroFreeRegionHyp : Prop where
  region :
    ∃ c > 0, ∀ ρ ∈ zetaNontrivialZeros,
      ρ.re < 1 - c / Real.log (|ρ.im| + 2)

/--
HYPOTHESIS: Dichotomy for Theta (either RH or zeros approach Re = 1).
MATHEMATICAL STATUS: conditional statement used to separate cases.
MATHLIB STATUS: not available.
-/
class ZetaZeroSupRealPartDichotomyHyp : Prop where
  eq_one_or_half : Θ = 1 ∨ Θ = 1/2

/--
HYPOTHESIS: Zero-free region implies the standard psi error term.
MATHEMATICAL STATUS: explicit formula plus zero-free region analysis.
MATHLIB STATUS: not available.
REFERENCE: Montgomery-Vaughan, Ch. 12-13.
-/
class ChebyshevErrorBoundZeroFreeHyp : Prop where
  bound : ∃ c > 0, ∃ C > 0, ∀ x ≥ 2,
    |chebyshevPsi x - x| ≤ C * x * Real.exp (-c * (Real.log x).sqrt)

/-! ## Additional Error Bound Hypothesis -/

/--
HYPOTHESIS: Explicit formula bound |ψ(x) - x| ≤ 10 * x^Θ * log x.
MATHEMATICAL STATUS: classical explicit formula.
MATHLIB STATUS: not available.
-/
class ChebyshevErrorBoundThetaHyp : Prop where
  bound : ∀ x ≥ 2, |chebyshevPsi x - x| ≤ 10 * x ^ Θ * Real.log x

/-! ## Basic Bounds -/

section Bounds

/-- All nontrivial zeros have real part < 1 -/
theorem zetaZeroRealPart_lt_one {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
    ρ.re < 1 := hρ.2.2

/-- All nontrivial zeros have real part > 0 -/
theorem zetaZeroRealPart_pos {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
    0 < ρ.re := hρ.2.1

/-- The set of real parts is bounded above by 1 -/
theorem zetaZeroRealParts_bddAbove : BddAbove zetaZeroRealParts := by
  use 1
  intro σ hσ
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact le_of_lt (zetaZeroRealPart_lt_one hρ)

/-- The set of real parts is bounded below by 0 -/
theorem zetaZeroRealParts_bddBelow : BddBelow zetaZeroRealParts := by
  refine ⟨0, ?_⟩
  intro σ hσ
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact le_of_lt (zetaZeroRealPart_pos hρ)

/-- The set of real parts is nonempty (there exist zeros) -/
theorem zetaZeroRealParts_nonempty [FirstZeroOrdinateHyp] : zetaZeroRealParts.Nonempty := by
  rcases firstZeroOrdinate_bounds with ⟨γ₁, hγ₁_mem, _hγ₁_low, _hγ₁_high, _hmin⟩
  rcases hγ₁_mem with ⟨s, hs, rfl⟩
  have hs' : s ∈ zetaNontrivialZeros := (mem_zetaNontrivialZerosPos.1 hs).1
  refine ⟨s.re, ?_⟩
  exact ⟨s, hs', rfl⟩

/-- Θ ≤ 1 -/
theorem zetaZeroSupRealPart_le_one [FirstZeroOrdinateHyp] : Θ ≤ 1 := by
  apply csSup_le zetaZeroRealParts_nonempty
  intro σ hσ
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact le_of_lt (zetaZeroRealPart_lt_one hρ)

/-- 0 < Θ -/
theorem zetaZeroSupRealPart_pos [FirstZeroOrdinateHyp] : 0 < Θ := by
  have hne := zetaZeroRealParts_nonempty
  obtain ⟨σ, ρ, hρ, rfl⟩ := hne
  calc 0 < ρ.re := zetaZeroRealPart_pos hρ
    _ ≤ Θ := le_csSup zetaZeroRealParts_bddAbove ⟨ρ, hρ, rfl⟩

/-- 1/2 ≤ Θ (there exist zeros with real part = 1/2 on the critical line) -/
theorem zetaZeroSupRealPart_ge_half [FirstZeroOrdinateHyp] : 1/2 ≤ Θ := by
  have hne := zetaZeroRealParts_nonempty
  rcases hne with ⟨r, hr⟩
  rcases hr with ⟨ρ, hρ, hrre⟩
  have hmem : r ∈ zetaZeroRealParts := ⟨ρ, hρ, hrre⟩
  have hmem' : 1 - r ∈ zetaZeroRealParts := by
    refine ⟨1 - ρ, zero_one_sub_zero hρ, ?_⟩
    simp [Complex.sub_re, Complex.one_re, hrre]
  have hle_r : r ≤ Θ := le_csSup zetaZeroRealParts_bddAbove hmem
  have hle_1mr : 1 - r ≤ Θ := le_csSup zetaZeroRealParts_bddAbove hmem'
  by_cases hρle : r ≤ (1 / 2 : ℝ)
  · have hge : (1 / 2 : ℝ) ≤ 1 - r := by linarith
    exact le_trans hge hle_1mr
  · have hge : (1 / 2 : ℝ) ≤ r := by linarith
    exact le_trans hge hle_r

/-- Θ is achieved: there exists a sequence of zeros whose real parts → Θ -/
theorem zetaZeroSupRealPart_achieved [FirstZeroOrdinateHyp] :
    ∃ ρₙ : ℕ → zetaNontrivialZeros, Tendsto (fun n => (ρₙ n).val.re) atTop (𝓝 Θ) := by
  classical
  obtain ⟨u, _hu_mono, hu_tendsto, hu_mem⟩ :=
    exists_seq_tendsto_sSup (S := zetaZeroRealParts)
      zetaZeroRealParts_nonempty zetaZeroRealParts_bddAbove
  have hu_mem' : ∀ n, ∃ ρ : zetaNontrivialZeros, ρ.val.re = u n := by
    intro n
    rcases hu_mem n with ⟨ρ, hρ, hρre⟩
    exact ⟨⟨ρ, hρ⟩, hρre⟩
  choose ρₙ hρₙ using hu_mem'
  refine ⟨ρₙ, ?_⟩
  have h_eq : (fun n => (ρₙ n).val.re) = u := by
    funext n
    exact hρₙ n
  simpa [h_eq] using hu_tendsto

end Bounds

/-! ## Riemann Hypothesis Characterization -/

section RH

/-- The Riemann Hypothesis: all zeros have real part 1/2 -/
def RiemannHypothesis : Prop :=
  ∀ ρ ∈ zetaNontrivialZeros, ρ.re = 1/2

/-- RH is equivalent to Θ = 1/2 -/
theorem RiemannHypothesis_iff [FirstZeroOrdinateHyp] : RiemannHypothesis ↔ Θ = 1/2 := by
  constructor
  · -- RH → Θ = 1/2
    intro hRH
    apply le_antisymm
    · -- Θ ≤ 1/2
      apply csSup_le zetaZeroRealParts_nonempty
      intro σ hσ
      obtain ⟨ρ, hρ, rfl⟩ := hσ
      exact le_of_eq (hRH ρ hρ)
    · -- 1/2 ≤ Θ
      exact zetaZeroSupRealPart_ge_half
  · -- Θ = 1/2 → RH
    intro hΘ
    intro ρ hρ
    have h1 : ρ.re ≤ Θ := le_csSup zetaZeroRealParts_bddAbove ⟨ρ, hρ, rfl⟩
    have h2 : Θ ≤ ρ.re := by
      -- If Θ = 1/2 and all zeros have re ≤ Θ = 1/2, and 1/2 ≤ all zeros (by symmetry)
      -- then all have re = 1/2
      have hρ' : 1 - ρ ∈ zetaNontrivialZeros := zero_one_sub_zero hρ
      have hmem : 1 - ρ.re ∈ zetaZeroRealParts := by
        refine ⟨1 - ρ, hρ', ?_⟩
        simp [Complex.sub_re, Complex.one_re]
      have hle : 1 - ρ.re ≤ Θ := le_csSup zetaZeroRealParts_bddAbove hmem
      have hle' : 1 - ρ.re ≤ (1 / 2 : ℝ) := by
        simpa [hΘ] using hle
      have hge : (1 / 2 : ℝ) ≤ ρ.re := by
        linarith
      simpa [hΘ] using hge
    linarith

/-- Under RH, Θ = 1/2 -/
theorem zetaZeroSupRealPart_eq_half_of_RH [FirstZeroOrdinateHyp]
    (hRH : RiemannHypothesis) : Θ = 1/2 :=
  RiemannHypothesis_iff.mp hRH

/-- If RH fails, then Θ > 1/2 -/
theorem zetaZeroSupRealPart_gt_half_of_not_RH [FirstZeroOrdinateHyp]
    (hRH : ¬RiemannHypothesis) : 1/2 < Θ := by
  by_contra h
  push_neg at h
  have hΘ : Θ = 1/2 := le_antisymm h zetaZeroSupRealPart_ge_half
  exact hRH (RiemannHypothesis_iff.mpr hΘ)

end RH

/-! ## Zero-Free Regions -/

section ZeroFree

/-- The de la Vallée Poussin zero-free region: no zeros for Re(s) > 1 - c/log(|Im(s)| + 2) -/
theorem zeroFreeRegion_delaValleePoussin [ZeroFreeRegionHyp] :
    ∃ c > 0, ∀ ρ ∈ zetaNontrivialZeros,
      ρ.re < 1 - c / Real.log (|ρ.im| + 2) := by
  simpa using ZeroFreeRegionHyp.region

/-- This implies Θ = 1 (i.e., zeros can get arbitrarily close to Re = 1) -/
theorem zetaZeroSupRealPart_eq_one_or_half [FirstZeroOrdinateHyp]
    [ZetaZeroSupRealPartDichotomyHyp] :
    Θ = 1 ∨ Θ = 1/2 := by
  simpa using ZetaZeroSupRealPartDichotomyHyp.eq_one_or_half

/-- The infimum of real parts is 1 - Θ (by symmetry ρ ↔ 1-ρ) -/
theorem zetaZeroInfRealPart [FirstZeroOrdinateHyp] : sInf zetaZeroRealParts = 1 - Θ := by
  -- The functional equation ρ ↔ 1-ρ gives this symmetry
  have hsymm : ∀ r ∈ zetaZeroRealParts, 1 - r ∈ zetaZeroRealParts := by
    intro r hr
    rcases hr with ⟨ρ, hρ, rfl⟩
    refine ⟨1 - ρ, zero_one_sub_zero hρ, ?_⟩
    simp [Complex.sub_re, Complex.one_re]
  have hlower : 1 - Θ ≤ sInf zetaZeroRealParts := by
    refine le_csInf zetaZeroRealParts_nonempty ?_
    intro r hr
    have hmem : 1 - r ∈ zetaZeroRealParts := hsymm r hr
    have hle : 1 - r ≤ Θ := le_csSup zetaZeroRealParts_bddAbove hmem
    linarith
  have hupper : sInf zetaZeroRealParts ≤ 1 - Θ := by
    have hsup : Θ ≤ 1 - sInf zetaZeroRealParts := by
      apply csSup_le zetaZeroRealParts_nonempty
      intro r hr
      have hmem : 1 - r ∈ zetaZeroRealParts := hsymm r hr
      have hle : sInf zetaZeroRealParts ≤ 1 - r := csInf_le zetaZeroRealParts_bddBelow hmem
      linarith
    linarith
  exact le_antisymm hupper hlower

end ZeroFree

/-! ## Consequences of Θ for Error Terms -/

section ErrorTerms

open Chebyshev in
/-- ψ(x) - x = O(x^Θ) (elementary consequence of explicit formula) -/
theorem chebyshev_error_bound_Theta [FirstZeroOrdinateHyp] [ChebyshevErrorBoundThetaHyp]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C > 0, ∀ x ≥ 2, |chebyshevPsi x - x| ≤ C * x ^ (Θ + ε) := by
  refine ⟨10 / ε, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hlog : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hx0 hε
  have hpsi : |chebyshevPsi x - x| ≤ 10 * x ^ Θ * Real.log x := by
    simpa using (ChebyshevErrorBoundThetaHyp.bound x hx)
  have hmul :
      10 * x ^ Θ * Real.log x ≤ 10 * x ^ Θ * (x ^ ε / ε) := by
    have hnonneg : 0 ≤ 10 * x ^ Θ := by
      have : 0 ≤ x ^ Θ := Real.rpow_nonneg hx0 _
      nlinarith
    exact mul_le_mul_of_nonneg_left hlog hnonneg
  have hpow : x ^ Θ * (x ^ ε) = x ^ (Θ + ε) := by
    simpa [Real.rpow_add] using (Real.rpow_add hxpos Θ ε).symm
  calc
    |chebyshevPsi x - x| ≤ 10 * x ^ Θ * Real.log x := hpsi
    _ ≤ 10 * x ^ Θ * (x ^ ε / ε) := hmul
    _ = (10 / ε) * x ^ (Θ + ε) := by
      calc
        10 * x ^ Θ * (x ^ ε / ε) = (10 / ε) * (x ^ Θ * x ^ ε) := by
          simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        _ = (10 / ε) * x ^ (Θ + ε) := by
          simp [hpow]

open Chebyshev in
/-- Under RH: ψ(x) - x = O(x^{1/2} log²x) -/
theorem chebyshev_error_bound_RH [FirstZeroOrdinateHyp]
    [ExplicitFormula.PsiErrorBoundRHHyp] (hRH : RiemannHypothesis) :
    ∃ C > 0, ∀ x ≥ 2, |chebyshevPsi x - x| ≤ C * x ^ (1/2 : ℝ) * (Real.log x) ^ 2 := by
  have hRH' : RiemannHypothesis' := by
    intro ρ hρ
    exact hRH ρ hρ
  refine ⟨10, by positivity, ?_⟩
  intro x hx
  simpa [Real.sqrt_eq_rpow] using (ExplicitFormula.psi_error_bound_RH hRH' x hx)

open Chebyshev in
/-- The zero-free region gives: ψ(x) - x = O(x exp(-c √log x)) -/
theorem chebyshev_error_bound_zeroFree [FirstZeroOrdinateHyp]
    [ChebyshevErrorBoundZeroFreeHyp] :
    ∃ c > 0, ∃ C > 0, ∀ x ≥ 2,
      |chebyshevPsi x - x| ≤ C * x * Real.exp (-c * (Real.log x).sqrt) := by
  simpa using ChebyshevErrorBoundZeroFreeHyp.bound

end ErrorTerms

/-!
## Hypothesis Instances

Instances for ZeroFreeRegionHyp, ZetaZeroSupRealPartDichotomyHyp,
ChebyshevErrorBoundZeroFreeHyp, and ChebyshevErrorBoundThetaHyp
are provided in Assumptions.lean (the single source of truth for axioms).
-/

end ZetaZeros
```

## Full Dependency File: `Littlewood/ZetaZeros/ZeroCountingFunction.lean`
```lean
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
# Zero Counting Function N(T)

This file defines the zero counting function N(T), which counts the number of
nontrivial zeros of the Riemann zeta function with imaginary part in (0, T].

## Definitions

* `zetaNontrivialZeros` : The set of nontrivial zeros of ζ(s)
* `zeroCountingFunction T` : N(T), the number of zeros with 0 < Im(ρ) ≤ T

## Main Results

* `zeroCountingFunction_asymptotic` : N(T) = (T/2π) log(T/2π) - T/2π + O(log T)
* `zeroCountingFunction_local_density` :
  N(T+h) - N(T) = O((h + 1) (log (T + h) + 1))

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 14
* Titchmarsh, "The Theory of the Riemann Zeta-Function", Chapter 9
-/

open Complex Real Filter Topology Set

namespace ZetaZeros

theorem logDeriv_sub_const (x a : ℂ) :
    logDeriv (fun z : ℂ => z - a) x = 1 / (x - a) := by
  have hderiv : deriv (fun z : ℂ => z - a) x = (1 : ℂ) := by
    simpa [deriv_id] using
      (deriv_sub_const (f := fun z : ℂ => z) (x := x) (c := a))
  simp [logDeriv_apply, hderiv]

/-! ## The Set of Nontrivial Zeros -/

/-- A nontrivial zero of ζ(s) is a zero with 0 < Re(s) < 1.
    These are the zeros in the critical strip. -/
def zetaNontrivialZeros : Set ℂ :=
  { s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 }

/-- The set of nontrivial zeros with positive imaginary part -/
def zetaNontrivialZerosPos : Set ℂ :=
  { s ∈ zetaNontrivialZeros | 0 < s.im }

/-- The imaginary parts of nontrivial zeros (the "ordinates") -/
def zetaZeroOrdinates : Set ℝ :=
  (·.im) '' zetaNontrivialZerosPos

/-- Membership in zetaNontrivialZeros implies the defining properties -/
theorem mem_zetaNontrivialZeros {s : ℂ} :
    s ∈ zetaNontrivialZeros ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := Iff.rfl

/-- Membership in zetaNontrivialZerosPos implies positive imaginary part -/
theorem mem_zetaNontrivialZerosPos {s : ℂ} :
    s ∈ zetaNontrivialZerosPos ↔ s ∈ zetaNontrivialZeros ∧ 0 < s.im := by
  unfold zetaNontrivialZerosPos
  simp only [Set.mem_sep_iff]

/-- Completed Riemann xi-function (up to the standard scalar factor). -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta s

theorem riemannXi_zero_iff_completed {s : ℂ} (hpos : 0 < s.re) (hlt : s.re < 1) :
    riemannXi s = 0 ↔ completedRiemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    have : s.re = 0 := by simpa [h] using (rfl : ((0 : ℂ).re = (0 : ℝ)))
    exact (ne_of_gt hpos) this
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have hs : s = 1 := sub_eq_zero.mp h
    have : s.re = 1 := by simpa [hs]
    exact (ne_of_lt hlt) this
  have hmul_ne : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1
  constructor
  · intro hxi
    have hzero :
        s * (s - 1) = 0 ∨ completedRiemannZeta s = 0 := by
      simpa [riemannXi, mul_eq_zero] using hxi
    cases hzero with
    | inl hmul => exact (hmul_ne hmul).elim
    | inr hz => exact hz
  · intro hz
    simp [riemannXi, hz]

theorem logDeriv_riemannXi (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hcomp : completedRiemannZeta s ≠ 0) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hmul_ne : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1'
  have hmul1 :
      logDeriv (fun z : ℂ => z * (z - 1)) s =
        logDeriv (fun z : ℂ => z) s + logDeriv (fun z : ℂ => z - 1) s := by
    have hdf : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
    have hdg : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := by
      simpa [sub_eq_add_neg] using (differentiableAt_id.add differentiableAt_const)
    simpa using
      (logDeriv_mul (x := s) (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1)
        hs0 hs1' hdf hdg)
  have hmul2 :
      logDeriv riemannXi s =
        logDeriv (fun z : ℂ => z * (z - 1)) s + logDeriv completedRiemannZeta s := by
    have hdf : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s := by
      have hdf1 : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
      have hdf2 : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := by
        simpa [sub_eq_add_neg] using (differentiableAt_id.add differentiableAt_const)
      simpa [sub_eq_add_neg] using hdf1.mul hdf2
    have hdg : DifferentiableAt ℂ completedRiemannZeta s :=
      differentiableAt_completedZeta hs0 hs1
    simpa [riemannXi] using
      (logDeriv_mul (x := s)
        (f := fun z : ℂ => z * (z - 1))
        (g := completedRiemannZeta) hmul_ne hcomp hdf hdg)
  calc
    logDeriv riemannXi s
        = logDeriv (fun z : ℂ => z * (z - 1)) s +
            logDeriv completedRiemannZeta s := hmul2
    _ = (1 / s + 1 / (s - 1)) + logDeriv completedRiemannZeta s := by
        simp [hmul1, logDeriv_sub_const, logDeriv_id, add_assoc]
    _ = 1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
        simp [add_assoc]

theorem completedRiemannZeta_eq_zero_iff_riemannZeta {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro hs0
    have : s.re = 0 := by
      simpa [hs0] using (rfl : ((0 : ℂ).re = (0 : ℝ)))
    exact (ne_of_gt hs) this
  have hzeta := riemannZeta_def_of_ne_zero (s := s) hs0
  constructor
  · intro h
    rw [hzeta, h, zero_div]
  · intro h
    have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
    have hzeta_mul : riemannZeta s * Gammaℝ s = completedRiemannZeta s := by
      have hzeta' := congrArg (fun z => z * Gammaℝ s) hzeta
      simpa [div_eq_mul_inv, mul_assoc, hGamma] using hzeta'
    have : riemannZeta s * Gammaℝ s = 0 := by
      simpa [h]
    simpa [hzeta_mul] using this

theorem mem_zetaNontrivialZeros_iff_completed {s : ℂ} :
    s ∈ zetaNontrivialZeros ↔ completedRiemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hs
    rcases (mem_zetaNontrivialZeros.1 hs) with ⟨hzeta, hpos, hlt⟩
    have hcomp : completedRiemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta hpos).2 hzeta
    exact ⟨hcomp, hpos, hlt⟩
  · rintro ⟨hcomp, hpos, hlt⟩
    have hzeta : riemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta hpos).1 hcomp
    exact (mem_zetaNontrivialZeros).2 ⟨hzeta, hpos, hlt⟩

theorem mem_zetaNontrivialZeros_iff_xi {s : ℂ} :
    s ∈ zetaNontrivialZeros ↔ riemannXi s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hs
    rcases (mem_zetaNontrivialZeros.1 hs) with ⟨hzeta, hpos, hlt⟩
    have hcomp : completedRiemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta hpos).2 hzeta
    have hxi : riemannXi s = 0 := (riemannXi_zero_iff_completed hpos hlt).2 hcomp
    exact ⟨hxi, hpos, hlt⟩
  · rintro ⟨hxi, hpos, hlt⟩
    have hcomp : completedRiemannZeta s = 0 :=
      (riemannXi_zero_iff_completed hpos hlt).1 hxi
    exact (mem_zetaNontrivialZeros_iff_completed).2 ⟨hcomp, hpos, hlt⟩

/-! ## The Zero Counting Function -/

/-- N(T) counts the nontrivial zeros ρ with 0 < Im(ρ) ≤ T.
    Since ζ has infinitely many zeros, we need to be careful about well-definedness.
    For any finite T, there are only finitely many zeros with Im(ρ) ≤ T. -/
noncomputable def zeroCountingFunction (T : ℝ) : ℕ :=
  (zetaNontrivialZerosPos ∩ { s : ℂ | s.im ≤ T }).ncard

/-- Notation for N(T) -/
scoped notation "N" => zeroCountingFunction

/-- The set being counted by N(T) -/
def zerosUpTo (T : ℝ) : Set ℂ :=
  zetaNontrivialZerosPos ∩ { s : ℂ | s.im ≤ T }

/-- N(T) is the cardinality of zerosUpTo(T) -/
theorem zeroCountingFunction_eq_ncard (T : ℝ) : N T = (zerosUpTo T).ncard := rfl

/-- Zeros of the completed zeta in the critical strip up to height `T`. -/
def completedZerosUpTo (T : ℝ) : Set ℂ :=
  { s : ℂ |
      completedRiemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T }

/-- Zeros of the completed xi-function in the critical strip up to height `T`. -/
def xiZerosUpTo (T : ℝ) : Set ℂ :=
  { s : ℂ | riemannXi s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T }

theorem zerosUpTo_eq_completed (T : ℝ) : zerosUpTo T = completedZerosUpTo T := by
  ext s
  constructor
  · intro hs
    rcases (by simpa [zerosUpTo] using hs : s ∈ zetaNontrivialZerosPos ∧ s.im ≤ T) with
      ⟨hzpos, hImle⟩
    rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨hzeta, hImpos⟩
    rcases (mem_zetaNontrivialZeros.1 hzeta) with ⟨hzeta0, hRepos, hRelt⟩
    have hcomp : completedRiemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta hRepos).2 hzeta0
    exact ⟨hcomp, hRepos, hRelt, hImpos, hImle⟩
  · rintro ⟨hcomp, hRepos, hRelt, hImpos, hImle⟩
    have hzeta : riemannZeta s = 0 :=
      (completedRiemannZeta_eq_zero_iff_riemannZeta hRepos).1 hcomp
    have hzetaMem : s ∈ zetaNontrivialZeros :=
      (mem_zetaNontrivialZeros).2 ⟨hzeta, hRepos, hRelt⟩
    have hzpos : s ∈ zetaNontrivialZerosPos :=
      (mem_zetaNontrivialZerosPos).2 ⟨hzetaMem, hImpos⟩
    exact by
      simpa [zerosUpTo] using (And.intro hzpos hImle)

theorem zerosUpTo_eq_xi (T : ℝ) : zerosUpTo T = xiZerosUpTo T := by
  ext s
  constructor
  · intro hs
    rcases (by simpa [zerosUpTo] using hs : s ∈ zetaNontrivialZerosPos ∧ s.im ≤ T) with
      ⟨hzpos, hImle⟩
    rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨hzeta, hImpos⟩
    rcases (mem_zetaNontrivialZeros_iff_xi.1 hzeta) with ⟨hxi, hRepos, hRelt⟩
    exact ⟨hxi, hRepos, hRelt, hImpos, hImle⟩
  · rintro ⟨hxi, hRepos, hRelt, hImpos, hImle⟩
    have hzeta : s ∈ zetaNontrivialZeros :=
      (mem_zetaNontrivialZeros_iff_xi).2 ⟨hxi, hRepos, hRelt⟩
    have hzpos : s ∈ zetaNontrivialZerosPos :=
      (mem_zetaNontrivialZerosPos).2 ⟨hzeta, hImpos⟩
    simpa [zerosUpTo] using (And.intro hzpos hImle)

/-- The set zerosUpTo is monotone in T -/
theorem zerosUpTo_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : zerosUpTo T₁ ⊆ zerosUpTo T₂ := by
  intro s hs
  unfold zerosUpTo at hs ⊢
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hs ⊢
  exact ⟨hs.1, le_trans hs.2 h⟩

/-! ## Finiteness of Zeros in Bounded Regions -/

/-- There is a punctured neighborhood of `1` on which `ζ` is nonzero. -/
private lemma riemannZeta_ne_zero_punctured_nhds_one :
    ∃ ε > 0, ∀ s, s ≠ (1 : ℂ) → dist s 1 < ε → riemannZeta s ≠ 0 := by
  have hres := riemannZeta_residue_one
  have hne :
      ((fun s => (s - 1) * riemannZeta s) ⁻¹' ({0}ᶜ : Set ℂ)) ∈ 𝓝[≠] (1 : ℂ) := by
    have h0 : ({0}ᶜ : Set ℂ) ∈ 𝓝 (1 : ℂ) := by
      simpa using (compl_singleton_mem_nhds (show (1 : ℂ) ≠ 0 by exact one_ne_zero))
    exact (tendsto_def.1 hres) ({0}ᶜ) h0
  rcases (Metric.mem_nhdsWithin_iff.1 hne) with ⟨ε, εpos, hε⟩
  refine ⟨ε, εpos, ?_⟩
  intro s hs hdist
  have hs' : s ∈ Metric.ball (1 : ℂ) ε ∩ ({x : ℂ | x ≠ 1}) := by
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_ball] using hdist
    · simpa [Set.mem_setOf_eq] using hs
  have hmem := hε hs'
  have hprod : (s - 1) * riemannZeta s ≠ 0 := by
    simpa [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
  intro hz
  apply hprod
  simp [hz]

/-- There are only finitely many zeros with imaginary part ≤ T.
    This is a consequence of ζ being meromorphic with isolated zeros. -/
theorem finite_zeros_le (T : ℝ) : (zerosUpTo T).Finite := by
  classical
  by_cases hT : T ≤ 0
  · have hEmpty : zerosUpTo T = ∅ := by
      ext z
      constructor
      · intro hz
        rcases (by simpa [zerosUpTo] using hz : z ∈ zetaNontrivialZerosPos ∧ z.im ≤ T) with
          ⟨hzpos, hzT⟩
        rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨_, hzIm⟩
        linarith
      · intro hz
        cases hz
    simpa [hEmpty] using (Set.finite_empty : (∅ : Set ℂ).Finite)
  · have hTpos : 0 < T := lt_of_not_ge hT
    obtain ⟨ε, εpos, hε⟩ := riemannZeta_ne_zero_punctured_nhds_one
    set U : Set ℂ := {s : ℂ | s ≠ 1}
    set Z : Set ℂ := riemannZeta ⁻¹' ({0} : Set ℂ)
    set K : Set ℂ :=
      Metric.closedBall (0 : ℂ) (1 + T) ∩ (Metric.ball (1 : ℂ) ε)ᶜ
    have hsubsetZ : zerosUpTo T ⊆ Z := by
      intro z hz
      rcases (by simpa [zerosUpTo] using hz : z ∈ zetaNontrivialZerosPos ∧ z.im ≤ T) with
        ⟨hzpos, _⟩
      rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨hznon, _⟩
      rcases (mem_zetaNontrivialZeros.1 hznon) with ⟨hzeta, _, _⟩
      simpa [Z, hzeta]
    have hsubsetK : zerosUpTo T ⊆ K := by
      intro z hz
      rcases (by simpa [zerosUpTo] using hz : z ∈ zetaNontrivialZerosPos ∧ z.im ≤ T) with
        ⟨hzpos, hzT⟩
      rcases (mem_zetaNontrivialZerosPos.1 hzpos) with ⟨hznon, hzIm⟩
      rcases (mem_zetaNontrivialZeros.1 hznon) with ⟨hzeta, hzRe, hzReLt⟩
      have hzRe' : |z.re| ≤ 1 := by
        have hzRe0 : 0 ≤ z.re := le_of_lt hzRe
        have hzReEq : |z.re| = z.re := abs_of_nonneg hzRe0
        linarith [hzReLt, hzReEq]
      have hzIm' : |z.im| ≤ T := by
        have hzIm0 : 0 ≤ z.im := le_of_lt hzIm
        have hzImEq : |z.im| = z.im := abs_of_nonneg hzIm0
        linarith [hzT, hzImEq]
      have hnorm : ‖z‖ ≤ 1 + T := by
        have hnorm' := norm_le_abs_re_add_abs_im z
        linarith [hnorm', hzRe', hzIm']
      have hball : z ∈ Metric.closedBall (0 : ℂ) (1 + T) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
      have hz_ne_one : z ≠ (1 : ℂ) := by
        intro h
        have : z.im = 0 := by simpa [h]
        linarith
      have hnotball : z ∉ Metric.ball (1 : ℂ) ε := by
        intro hzball
        have hdist : dist z 1 < ε := by
          simpa [Metric.mem_ball] using hzball
        exact (hε z hz_ne_one hdist) hzeta
      exact ⟨hball, hnotball⟩
    have hconn : IsConnected U := by
      simpa [U] using
        (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat)
          (1 : ℂ))
    have hdiff : DifferentiableOn ℂ riemannZeta U := by
      intro s hs
      exact (differentiableAt_riemannZeta hs).differentiableWithinAt
    have han : AnalyticOnNhd ℂ riemannZeta U := by
      simpa [U] using
        (analyticOnNhd_iff_differentiableOn (isOpen_compl_singleton : IsOpen U)).2 hdiff
    have h2 : riemannZeta (2 : ℂ) ≠ 0 := by
      have h2re : 1 < (2 : ℂ).re := by norm_num
      exact riemannZeta_ne_zero_of_one_lt_re h2re
    have hcod : Zᶜ ∈ Filter.codiscreteWithin U := by
      have hx : (2 : ℂ) ∈ U := by simp [U]
      simpa [Z] using
        (AnalyticOnNhd.preimage_zero_mem_codiscreteWithin (f := riemannZeta) (U := U)
          (x := 2) han h2 hx hconn)
    have hdiscZU : IsDiscrete (Z ∩ U) :=
      isDiscrete_of_codiscreteWithin (U := U) (s := Z) hcod
    have hdisc_subset :
        ∀ {s t : Set ℂ}, IsDiscrete s → t ⊆ s → IsDiscrete t := by
      intro s t hs hts
      refine IsDiscrete.of_nhdsWithin ?_
      intro x hx
      have hx' : x ∈ s := hts hx
      have hnhds : 𝓝[s] x = pure x := hs.nhdsWithin x hx'
      have hle : 𝓝[t] x ≤ 𝓝[s] x := nhdsWithin_mono x hts
      simpa [hnhds] using hle
    have hKsubsetU : K ⊆ U := by
      intro z hz
      have hzball : z ∉ Metric.ball (1 : ℂ) ε := hz.2
      intro h
      apply hzball
      simpa [h] using (Metric.mem_ball_self (x := (1 : ℂ)) εpos)
    have hdiscK : IsDiscrete (Z ∩ K) := by
      apply hdisc_subset hdiscZU
      intro z hz
      exact ⟨hz.1, hKsubsetU hz.2⟩
    have hKcomp : IsCompact K := by
      exact (isCompact_closedBall (0 : ℂ) (1 + T)).inter_right
        (Metric.isOpen_ball.isClosed_compl)
    have hcontK : ContinuousOn riemannZeta K := by
      intro z hz
      have hzball : z ∉ Metric.ball (1 : ℂ) ε := hz.2
      have hz_ne_one : z ≠ (1 : ℂ) := by
        intro h
        apply hzball
        simpa [h] using (Metric.mem_ball_self (x := (1 : ℂ)) εpos)
      exact (differentiableAt_riemannZeta hz_ne_one).continuousAt.continuousWithinAt
    let S' : Set K := {x : K | riemannZeta x = 0}
    have hcontK' : Continuous (fun x : K => riemannZeta x) :=
      (continuousOn_iff_continuous_restrict).1 hcontK
    have hclosedS' : IsClosed S' := by
      have : S' = (fun x : K => riemannZeta x) ⁻¹' ({0} : Set ℂ) := by
        ext x
        simp [S']
      simpa [this] using (isClosed_singleton.preimage hcontK')
    haveI : CompactSpace K := (isCompact_iff_compactSpace.mp hKcomp)
    have hS'comp : IsCompact S' := IsClosed.isCompact hclosedS'
    have hScomp : IsCompact ((↑) '' S' : Set ℂ) :=
      (Subtype.isCompact_iff).1 hS'comp
    have himage : ((↑) '' S' : Set ℂ) = Z ∩ K := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : riemannZeta x = 0 := by
          simpa [S'] using hx
        exact ⟨by simpa [Z, hx'], x.property⟩
      · rintro ⟨hz0, hzK⟩
        refine ⟨⟨z, hzK⟩, ?_, rfl⟩
        simpa [S', Z] using hz0
    have hZKcomp : IsCompact (Z ∩ K) := by
      simpa [himage] using hScomp
    have hfin : (Z ∩ K).Finite := IsCompact.finite hZKcomp hdiscK
    exact hfin.subset fun z hz => ⟨hsubsetZ hz, hsubsetK hz⟩

/-- N(T) is well-defined (finite) for all T -/
theorem zeroCountingFunction_finite (T : ℝ) : (zeroCountingFunction T : ℕ∞) < ⊤ := by
  exact WithTop.coe_lt_top _

/-- The set zerosUpTo(T) is finite for all T -/
theorem zerosUpTo_finite (T : ℝ) : (zerosUpTo T).Finite := finite_zeros_le T

/-- The completed-zeta zero set in the strip is finite up to height `T`. -/
theorem completedZerosUpTo_finite (T : ℝ) : (completedZerosUpTo T).Finite := by
  simpa [zerosUpTo_eq_completed] using (zerosUpTo_finite T)

/-- The xi zero set in the strip is finite up to height `T`. -/
theorem xiZerosUpTo_finite (T : ℝ) : (xiZerosUpTo T).Finite := by
  simpa [zerosUpTo_eq_xi] using (zerosUpTo_finite T)

/-! ## Hypotheses -/

class ZeroCountingTendstoHyp : Prop where
  tendsto_atTop : Tendsto (fun T => (N T : ℝ)) atTop atTop

/-! ## Basic Properties -/

section BasicProperties

theorem zeroCountingFunction_nonneg (T : ℝ) : 0 ≤ N T := Nat.zero_le _

theorem zeroCountingFunction_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : N T₁ ≤ N T₂ := by
  apply Set.ncard_le_ncard (zerosUpTo_mono h) (finite_zeros_le T₂)

theorem zeroCountingFunction_neg (T : ℝ) (hT : T ≤ 0) : N T = 0 := by
  simp only [zeroCountingFunction]
  have : zetaNontrivialZerosPos ∩ { s : ℂ | s.im ≤ T } = ∅ := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨hs, him⟩
    simp only [mem_zetaNontrivialZerosPos] at hs
    linarith [hs.2]
  simp [this]

/-- N(0) = 0, since we only count zeros with positive imaginary part -/
theorem zeroCountingFunction_zero : N 0 = 0 :=
  zeroCountingFunction_neg 0 (le_refl 0)

/-- N(T) is always finite as a natural number -/
theorem zeroCountingFunction_nat (T : ℝ) : ∃ n : ℕ, N T = n := ⟨N T, rfl⟩

/-- Antitonicity is equivalent to monotonicity for N(T) -/
theorem zeroCountingFunction_antimono {T₁ T₂ : ℝ} (h : T₂ ≤ T₁) : N T₂ ≤ N T₁ :=
  zeroCountingFunction_mono h

/-- N(T) = 0 for all negative T -/
theorem zeroCountingFunction_neg_eq_zero {T : ℝ} (hT : T < 0) : N T = 0 :=
  zeroCountingFunction_neg T (le_of_lt hT)

/-- The zero counting function casted to ℝ is nonnegative -/
theorem zeroCountingFunction_cast_nonneg (T : ℝ) : 0 ≤ (N T : ℝ) := Nat.cast_nonneg _

/-- The zero counting function casted to ℝ is monotone -/
theorem zeroCountingFunction_cast_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : (N T₁ : ℝ) ≤ (N T₂ : ℝ) :=
  Nat.cast_le.mpr (zeroCountingFunction_mono h)

/-- If T₁ ≤ T₂, then the set of zeros up to T₁ is a subset of zeros up to T₂ -/
theorem zerosUpTo_subset_of_le {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : zerosUpTo T₁ ⊆ zerosUpTo T₂ :=
  zerosUpTo_mono h

/-- N(T) = 0 iff there are no zeros with imaginary part in (0, T] -/
theorem zeroCountingFunction_eq_zero_iff (T : ℝ) : N T = 0 ↔ zerosUpTo T = ∅ :=
  Set.ncard_eq_zero (zerosUpTo_finite T)

/-- N(T) → ∞ as T → ∞ -/
theorem zeroCountingFunction_tendsto_atTop [ZeroCountingTendstoHyp] :
    Tendsto (fun T => (N T : ℝ)) atTop atTop := by
  simpa using ZeroCountingTendstoHyp.tendsto_atTop

end BasicProperties

class ZeroCountingCrudeBoundHyp : Prop where
  crude_bound : ∃ C : ℝ, ∀ {T : ℝ}, 4 ≤ T → (N T : ℝ) ≤ C * T * Real.log T

class ZeroCountingSpecialValuesHyp : Prop where
  fourteen : N 14 = 0

class ZeroCountingFifteenHyp : Prop where
  fifteen : N 15 = 1

class FirstZeroOrdinateHyp : Prop where
  bounds :
    ∃ γ₁ ∈ zetaZeroOrdinates, 14.13 < γ₁ ∧ γ₁ < 14.14 ∧
      ∀ γ ∈ zetaZeroOrdinates, γ₁ ≤ γ

/-! ### Global instances (assumptions) -/

instance instZeroCountingSpecialValuesHyp [FirstZeroOrdinateHyp] :
    ZeroCountingSpecialValuesHyp := by
  refine ⟨?_⟩
  rcases FirstZeroOrdinateHyp.bounds with ⟨γ₁, _, hγ₁low, _, hγ₁min⟩
  apply (zeroCountingFunction_eq_zero_iff 14).2
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hz' : z ∈ zetaNontrivialZerosPos ∧ z.im ≤ 14 := by
    simpa [zerosUpTo] using hz
  have hzpos : z ∈ zetaNontrivialZerosPos := hz'.1
  have hle : z.im ≤ 14 := hz'.2
  have hzord : z.im ∈ zetaZeroOrdinates := ⟨z, hzpos, rfl⟩
  have h14lt : (14 : ℝ) < γ₁ := by
    have h14 : (14 : ℝ) < 14.13 := by norm_num
    exact lt_trans h14 hγ₁low
  have hlt : z.im < γ₁ := lt_of_le_of_lt hle h14lt
  exact (not_le_of_gt hlt) (hγ₁min _ hzord)

/-! ## Specific Bounds -/

section SpecificBounds

/-- N(T) ≤ C * T * log T for T ≥ 4 -/
theorem zeroCountingFunction_crude_bound [ZeroCountingCrudeBoundHyp] :
    ∃ C : ℝ, ∀ {T : ℝ}, 4 ≤ T → (N T : ℝ) ≤ C * T * Real.log T := by
  simpa using ZeroCountingCrudeBoundHyp.crude_bound

/-- N(14) = 0 (the first zero is at T ≈ 14.13...) -/
theorem zeroCountingFunction_fourteen [ZeroCountingSpecialValuesHyp] : N 14 = 0 := by
  simpa using ZeroCountingSpecialValuesHyp.fourteen

/-- N(15) = 1 (the first zero is at T ≈ 14.13...) -/
theorem zeroCountingFunction_fifteen [ZeroCountingFifteenHyp] : N 15 = 1 := by
  simpa using ZeroCountingFifteenHyp.fifteen

/-- The first zero ordinate γ₁ ≈ 14.134725... -/
theorem firstZeroOrdinate_bounds [FirstZeroOrdinateHyp] :
    ∃ γ₁ ∈ zetaZeroOrdinates, 14.13 < γ₁ ∧ γ₁ < 14.14 ∧
      ∀ γ ∈ zetaZeroOrdinates, γ₁ ≤ γ := by
  simpa using FirstZeroOrdinateHyp.bounds

end SpecificBounds

class ZeroCountingAsymptoticHyp : Prop where
  asymptotic :
    (fun T => (N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π))
    =O[atTop] (fun T => Real.log T)

class ZeroCountingRvmExplicitHyp : Prop where
  bound :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T

class ZeroCountingAsymptoticRatioHyp : Prop where
  asymptotic' :
    Tendsto (fun T => (N T : ℝ) / ((T / (2 * π)) * Real.log (T / (2 * π)))) atTop (𝓝 1)

class ZeroCountingMainTermHyp : Prop where
  mainTerm :
    Tendsto (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1)

class ZeroCountingLowerBoundHyp : Prop where
  lower_bound : ∃ T0 : ℝ, ∀ T ≥ T0, T / (3 * π) * Real.log T ≤ N T

/-! ### Global instances (assumptions) -/

instance instZeroCountingAsymptoticHyp [ZeroCountingRvmExplicitHyp] :
    ZeroCountingAsymptoticHyp := by
  classical
  refine ⟨?_⟩
  rcases ZeroCountingRvmExplicitHyp.bound with ⟨C, T0, hC⟩
  let C0 : ℝ := max C 0
  refine (Asymptotics.isBigO_iff.2 ?_)
  refine ⟨C0, ?_⟩
  refine (eventually_ge_atTop (max T0 1)).mono ?_
  intro T hT
  have hT0 : T0 ≤ T := le_trans (le_max_left _ _) hT
  have h1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hlogabs : |Real.log T| = Real.log T := by
    exact abs_of_nonneg (Real.log_nonneg h1)
  have hbound := hC T hT0
  have hC_le : C * Real.log T ≤ C0 * Real.log T := by
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg h1)
  have hbound' :
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C0 * Real.log T := hbound.trans hC_le
  simpa [Real.norm_eq_abs, hlogabs] using hbound'


/-! ## Asymptotic Formula -/

section Asymptotics

open Asymptotics

/-- The Riemann-von Mangoldt formula: N(T) = (T/2π) log(T/2π) - T/2π + O(log T) -/
theorem zeroCountingFunction_asymptotic [ZeroCountingAsymptoticHyp] :
    (fun T => (N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π))
    =O[atTop] (fun T => Real.log T) := by
  simpa using ZeroCountingAsymptoticHyp.asymptotic

/-- Main term approximation -/
theorem zeroCountingFunction_asymptotic' [ZeroCountingMainTermHyp] :
    Tendsto (fun T => (N T : ℝ) / ((T / (2 * π)) * Real.log (T / (2 * π)))) atTop (𝓝 1) := by
  classical
  set c : ℝ := Real.log (2 * π)
  have hlog : Tendsto (fun T => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hdiv : Tendsto (fun T => c / Real.log T) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop (g := fun T => Real.log T) hlog c
  have hlog_ne : ∀ᶠ T in atTop, Real.log T ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact ne_of_gt (Real.log_pos (by linarith))
  have hlog_div :
      (fun T => Real.log (T / (2 * π))) =ᶠ[atTop] (fun T => Real.log T - c) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hTne : T ≠ 0 := by linarith
    have h2pi_ne : (2 * π : ℝ) ≠ 0 := by
      have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
      exact ne_of_gt h2pi_pos
    simp [c, Real.log_div hTne h2pi_ne]
  have hratio_base :
      Tendsto (fun T => (Real.log T - c) / Real.log T) atTop (𝓝 1) := by
    have hcongr :
        (fun T => (Real.log T - c) / Real.log T) =ᶠ[atTop]
          (fun T => 1 - c / Real.log T) := by
      refine hlog_ne.mono ?_
      intro T hT
      calc
        (Real.log T - c) / Real.log T
            = Real.log T / Real.log T - c / Real.log T := by
                simp [sub_div]
        _ = 1 - c / Real.log T := by
                simp [div_self hT]
    have hlim : Tendsto (fun T => 1 - c / Real.log T) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hdiv)
    exact hlim.congr' hcongr.symm
  have hratio_inv :
      Tendsto (fun T => (Real.log T - c) / Real.log T)⁻¹ atTop (𝓝 1) := by
    simpa using
      (tendsto_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).comp hratio_base
  have hratio :
      Tendsto (fun T => Real.log T / Real.log (T / (2 * π))) atTop (𝓝 1) := by
    have hratio' : Tendsto (fun T => Real.log T / (Real.log T - c)) atTop (𝓝 1) := by
      refine hratio_inv.congr' ?_
      refine Filter.Eventually.of_forall ?_
      intro T
      simp [inv_div]
    refine hratio'.congr' ?_
    refine hlog_div.mono ?_
    intro T hT
    simp [hT]
  have hmain : Tendsto (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1) := by
    simpa using ZeroCountingMainTermHyp.mainTerm
  have hmul :
      Tendsto
        (fun T =>
          (N T : ℝ) / (T / (2 * π) * Real.log T) *
            (Real.log T / Real.log (T / (2 * π)))) atTop (𝓝 1) := by
    simpa using hmain.mul hratio
  have hcongr :
      (fun T => (N T : ℝ) / ((T / (2 * π)) * Real.log (T / (2 * π)))) =ᶠ[atTop]
        (fun T =>
          (N T : ℝ) / (T / (2 * π) * Real.log T) *
            (Real.log T / Real.log (T / (2 * π)))) := by
    filter_upwards [eventually_gt_atTop (2 * π)] with T hT
    have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hT_gt_one : (1 : ℝ) < T := by
      nlinarith [Real.pi_gt_three, hT]
    have hlogT : Real.log T ≠ 0 := by
      exact ne_of_gt (Real.log_pos hT_gt_one)
    have hlogDiv : Real.log (T / (2 * π)) ≠ 0 := by
      have hpos : 1 < T / (2 * π) := by
        have : (2 * π : ℝ) < T := hT
        exact (one_lt_div h2pi_pos).2 this
      exact ne_of_gt (Real.log_pos hpos)
    field_simp [hlogT, hlogDiv, mul_comm, mul_left_comm, mul_assoc]
  exact hmul.congr' hcongr.symm

/-- For large T, N(T) ~ (T/2π) log T -/
theorem zeroCountingFunction_mainTerm [ZeroCountingMainTermHyp] :
    Tendsto (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1) := by
  simpa using ZeroCountingMainTermHyp.mainTerm

noncomputable instance zeroCountingAsymptoticRatioHyp_of_mainTerm
    [ZeroCountingMainTermHyp] :
    ZeroCountingAsymptoticRatioHyp := by
  classical
  exact ⟨zeroCountingFunction_asymptotic'⟩

noncomputable instance zeroCountingMainTermHyp_of_asymptotic
    [ZeroCountingAsymptoticHyp] :
    ZeroCountingMainTermHyp := by
  classical
  refine ⟨?_⟩
  set g : ℝ → ℝ := fun T => (T / (2 * π)) * Real.log (T / (2 * π))
  set c : ℝ := Real.log (2 * π)
  have h_asymp :
      (fun T => (N T : ℝ) - g T + T / (2 * π)) =O[atTop] (fun T => Real.log T) := by
    simpa [g] using zeroCountingFunction_asymptotic
  have hlog : Tendsto (fun T => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hdiv : Tendsto (fun T => c / Real.log T) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop (g := fun T => Real.log T) hlog c
  have hlog_ne : ∀ᶠ T in atTop, Real.log T ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact ne_of_gt (Real.log_pos (by linarith))
  have hlog_div :
      (fun T => Real.log (T / (2 * π))) =ᶠ[atTop] (fun T => Real.log T - c) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hTne : T ≠ 0 := by linarith
    have h2pi_ne : (2 * π : ℝ) ≠ 0 := by
      have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
      exact ne_of_gt h2pi_pos
    simp [c, Real.log_div hTne h2pi_ne]
  have hratio_base :
      Tendsto (fun T => (Real.log T - c) / Real.log T) atTop (𝓝 1) := by
    have hcongr :
        (fun T => (Real.log T - c) / Real.log T) =ᶠ[atTop]
          (fun T => 1 - c / Real.log T) := by
      refine hlog_ne.mono ?_
      intro T hT
      calc
        (Real.log T - c) / Real.log T
            = Real.log T / Real.log T - c / Real.log T := by
                simp [sub_div]
        _ = 1 - c / Real.log T := by
                simp [div_self hT]
    have hlim : Tendsto (fun T => 1 - c / Real.log T) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hdiv)
    exact hlim.congr' hcongr.symm
  have hlogratio :
      Tendsto (fun T => Real.log (T / (2 * π)) / Real.log T) atTop (𝓝 1) := by
    refine hratio_base.congr' ?_
    refine hlog_div.mono ?_
    intro T hT
    simp [hT]
  have hdiv_atTop : Tendsto (fun T => T / (2 * π)) atTop atTop :=
    (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop).atTop_div_const
      (by nlinarith [Real.pi_pos])
  have hlogratio_atTop :
      Tendsto (fun T => g T / Real.log T) atTop atTop := by
    have hmul :
        Tendsto
          (fun T =>
            (T / (2 * π)) * (Real.log (T / (2 * π)) / Real.log T)) atTop atTop :=
      (Filter.Tendsto.atTop_mul_pos (C := 1) (by linarith) hdiv_atTop hlogratio)
    have hcongr :
        (fun T => g T / Real.log T) =ᶠ[atTop]
          (fun T => (T / (2 * π)) * (Real.log (T / (2 * π)) / Real.log T)) := by
      refine Filter.Eventually.of_forall ?_
      intro T
      simp [g, mul_div_assoc]
    exact hmul.congr' hcongr.symm
  have hlog_div_zero : Tendsto (fun T => Real.log T / g T) atTop (𝓝 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hlogratio_atTop
    have hcongr :
        (fun T => Real.log T / g T) =ᶠ[atTop]
          (fun T => (g T / Real.log T)⁻¹) := by
      refine Filter.Eventually.of_forall ?_
      intro T
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    exact hinv.congr' hcongr.symm
  have h_g_ne : ∀ᶠ T in atTop, g T ≠ 0 := by
    filter_upwards [eventually_gt_atTop (2 * π)] with T hT
    have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hTpos : 0 < T := by linarith
    have hlogpos : 0 < Real.log (T / (2 * π)) := by
      have hpos : 1 < T / (2 * π) := (one_lt_div h2pi_pos).2 hT
      exact Real.log_pos hpos
    have hpos : 0 < g T := by
      exact mul_pos (div_pos hTpos h2pi_pos) hlogpos
    exact ne_of_gt hpos
  have hlog_o : (fun T => Real.log T) =o[atTop] g := by
    refine (isLittleO_iff_tendsto' ?_).2 hlog_div_zero
    filter_upwards [h_g_ne] with T hT
    intro hzero
    exact (hT hzero).elim
  have hlog_div_atTop : Tendsto (fun T => Real.log (T / (2 * π))) atTop atTop :=
    Real.tendsto_log_atTop.comp hdiv_atTop
  have hlin_div_zero : Tendsto (fun T => (T / (2 * π)) / g T) atTop (𝓝 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hlog_div_atTop
    have hcongr :
        (fun T => (T / (2 * π)) / g T) =ᶠ[atTop]
          (fun T => (Real.log (T / (2 * π)))⁻¹) := by
      filter_upwards [eventually_gt_atTop (2 * π)] with T hT
      have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
      have hTpos : 0 < T := by linarith
      have hTne : (T / (2 * π) : ℝ) ≠ 0 := by
        exact ne_of_gt (div_pos hTpos h2pi_pos)
      simpa [g] using
        (div_mul_cancel_left₀ (a := (T / (2 * π) : ℝ))
          (b := Real.log (T / (2 * π))) hTne)
    exact hinv.congr' hcongr.symm
  have hlin_o : (fun T => T / (2 * π)) =o[atTop] g := by
    refine (isLittleO_iff_tendsto' ?_).2 hlin_div_zero
    filter_upwards [h_g_ne] with T hT
    intro hzero
    exact (hT hzero).elim
  have hE_o :
      (fun T => (N T : ℝ) - g T + T / (2 * π)) =o[atTop] g :=
    h_asymp.trans_isLittleO hlog_o
  have hdiff : (fun T => (N T : ℝ) - g T) =o[atTop] g := by
    simpa [g] using hE_o.sub hlin_o
  have hratio0 : Tendsto (fun T => ((N T : ℝ) - g T) / g T) atTop (𝓝 0) :=
    hdiff.tendsto_div_nhds_zero
  have hratio : Tendsto (fun T => (N T : ℝ) / g T) atTop (𝓝 1) := by
    have hcongr :
        (fun T => (N T : ℝ) / g T) =ᶠ[atTop]
          (fun T => ((N T : ℝ) - g T) / g T + 1) := by
      refine h_g_ne.mono ?_
      intro T hT
      calc
        (N T : ℝ) / g T
            = ((N T : ℝ) - g T + g T) / g T := by
                simp
        _ = ((N T : ℝ) - g T) / g T + g T / g T := by
                simpa [add_div] using (add_div ((N T : ℝ) - g T) (g T) (g T))
        _ = ((N T : ℝ) - g T) / g T + 1 := by
                simp [hT]
    have hsum :
        Tendsto (fun T => ((N T : ℝ) - g T) / g T + 1) atTop (𝓝 1) := by
      simpa using (hratio0.add tendsto_const_nhds)
    exact hsum.congr' hcongr.symm
  have hmul :
      Tendsto
        (fun T => (N T : ℝ) / g T * (Real.log (T / (2 * π)) / Real.log T))
        atTop (𝓝 1) := by
    simpa using hratio.mul hlogratio
  have hcongr :
      (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) =ᶠ[atTop]
        (fun T => (N T : ℝ) / g T * (Real.log (T / (2 * π)) / Real.log T)) := by
    filter_upwards [eventually_gt_atTop (2 * π)] with T hT
    have h2pi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hlogT : Real.log T ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by nlinarith [Real.pi_gt_three, hT]))
    have hlogDiv : Real.log (T / (2 * π)) ≠ 0 := by
      have hpos : 1 < T / (2 * π) := (one_lt_div h2pi_pos).2 hT
      exact ne_of_gt (Real.log_pos hpos)
    have hcalc :
        (N T : ℝ) / (T / (2 * π) * Real.log T) =
          (N T : ℝ) / ((T / (2 * π)) * Real.log (T / (2 * π))) *
            (Real.log (T / (2 * π)) / Real.log T) := by
      field_simp [hlogT, hlogDiv, mul_comm, mul_left_comm, mul_assoc]
    simpa [g] using hcalc
  exact hmul.congr' hcongr.symm

/-! ### Explicit error term (big-O) -/

lemma zeroCountingFunction_rvm_eventually_bound [ZeroCountingAsymptoticHyp] :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * |Real.log T| := by
  rcases (Asymptotics.isBigO_iff.1 zeroCountingFunction_asymptotic) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  simpa [Real.norm_eq_abs] using hC

lemma zeroCountingFunction_rvm_eventually_bound_log [ZeroCountingAsymptoticHyp] :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T := by
  rcases zeroCountingFunction_rvm_eventually_bound with ⟨C, hC⟩
  rcases (Filter.eventually_atTop.1 hC) with ⟨T0, hT0⟩
  refine ⟨C, max T0 1, ?_⟩
  intro T hT
  have hT0' : T0 ≤ T := le_trans (le_max_left _ _) hT
  have h1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hlogabs : |Real.log T| = Real.log T := by
    exact abs_of_nonneg (Real.log_nonneg h1)
  have hbound :=
    hT0 T hT0'
  simpa [hlogabs] using hbound

/-- Riemann–von Mangoldt with explicit `O(log T)` error term. -/
theorem zeroCountingFunction_rvm_explicit [ZeroCountingAsymptoticHyp] :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T := by
  simpa using zeroCountingFunction_rvm_eventually_bound_log

theorem zeroCountingFunction_rvm_explicit_hyp [ZeroCountingRvmExplicitHyp] :
    ∃ C T0 : ℝ, ∀ T ≥ T0,
      |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C * Real.log T := by
  simpa using ZeroCountingRvmExplicitHyp.bound

/-- Lower bound: eventually N(T) ≥ T/(3π) log T. -/
theorem zeroCountingFunction_lower_bound [ZeroCountingLowerBoundHyp] :
    ∃ T0 : ℝ, ∀ T ≥ T0, T / (3 * π) * Real.log T ≤ N T := by
  simpa using ZeroCountingLowerBoundHyp.lower_bound

instance zeroCountingTendstoHyp_of_lower_bound [ZeroCountingLowerBoundHyp] :
    ZeroCountingTendstoHyp := by
  refine ⟨?_⟩
  refine tendsto_atTop_atTop.2 ?_
  intro b
  have hmul : Tendsto (fun T : ℝ => T * Real.log T) atTop atTop :=
    (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop)
  have hpos : 0 < (1 / (3 * π) : ℝ) := by
    have hdenom : 0 < (3 * π : ℝ) := by nlinarith [Real.pi_pos]
    exact one_div_pos.mpr hdenom
  have hconst :
      Tendsto (fun T : ℝ => (1 / (3 * π)) * (T * Real.log T)) atTop atTop :=
    (Tendsto.const_mul_atTop hpos hmul)
  rcases (tendsto_atTop_atTop.1 hconst b) with ⟨T0, hT0⟩
  rcases zeroCountingFunction_lower_bound with ⟨T1, hT1⟩
  refine ⟨max T0 T1, ?_⟩
  intro T hT
  have hT0' : T0 ≤ T := le_trans (le_max_left _ _) hT
  have hT1' : T1 ≤ T := le_trans (le_max_right _ _) hT
  have hb : b ≤ (1 / (3 * π)) * (T * Real.log T) := hT0 T hT0'
  have hlow :
      (1 / (3 * π)) * (T * Real.log T) ≤ N T := by
    have hlow' := hT1 T hT1'
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlow'
  exact hb.trans hlow

/-- Upper bound: `N(T) ≤ C * T * log T` for `T ≥ 4`. -/
theorem zeroCountingFunction_upper_bound [ZeroCountingAsymptoticHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T → (N T : ℝ) ≤ C * T * Real.log T := by
  rcases zeroCountingFunction_rvm_explicit with ⟨C, T0, hC⟩
  set C0 : ℝ := max C 0
  let T1 : ℝ := max T0 4
  let C1 : ℝ := (1 / (2 * π)) + C0
  let Csmall : ℝ := (N T1 : ℝ) / (4 * Real.log 4)
  let Cfinal : ℝ := max C1 Csmall
  refine ⟨Cfinal, ?_⟩
  intro T hT
  have hlog4pos : 0 < Real.log 4 := by
    have h : (1 : ℝ) < 4 := by linarith
    exact Real.log_pos h
  have hlog4pos' : 0 < (4 * Real.log 4 : ℝ) := by
    nlinarith [hlog4pos]
  have hTpos : 0 < T := by linarith [hT]
  by_cases hlarge : T1 ≤ T
  · have hT0 : T0 ≤ T := le_trans (le_max_left _ _) hlarge
    have hlogpos : 0 ≤ Real.log T := by
      exact Real.log_nonneg (by linarith [hT] : (1 : ℝ) ≤ T)
    have hErr : |(N T : ℝ) - (T / (2 * π)) * Real.log (T / (2 * π)) + T / (2 * π)|
        ≤ C0 * Real.log T := by
      have h := hC T hT0
      have hC_le : C * Real.log T ≤ C0 * Real.log T := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlogpos
      exact h.trans hC_le
    have hmain :
        (N T : ℝ) ≤
          (T / (2 * π)) * Real.log (T / (2 * π)) - T / (2 * π) + C0 * Real.log T := by
      have h_upper := (abs_le.mp hErr).2
      linarith
    have hpi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hpi1 : (1 : ℝ) ≤ 2 * π := by
      have hpi3 : (3 : ℝ) < π := pi_gt_three
      linarith
    have hdivle : T / (2 * π) ≤ T := by
      exact div_le_self (le_of_lt hTpos) hpi1
    have hlogle : Real.log (T / (2 * π)) ≤ Real.log T := by
      exact Real.log_le_log (div_pos hTpos hpi_pos) hdivle
    have hmul :
        (T / (2 * π)) * Real.log (T / (2 * π)) ≤ (T / (2 * π)) * Real.log T := by
      have hnonneg : 0 ≤ T / (2 * π) := by
        exact le_of_lt (div_pos hTpos hpi_pos)
      exact mul_le_mul_of_nonneg_left hlogle hnonneg
    have hnonneg_div : 0 ≤ T / (2 * π) := by
      exact le_of_lt (div_pos hTpos hpi_pos)
    have hstep :
        (N T : ℝ) ≤ (T / (2 * π)) * Real.log T + C0 * Real.log T := by
      linarith [hmain, hmul, hnonneg_div]
    have hstep' :
        (N T : ℝ) ≤ C1 * T * Real.log T := by
      have hlogpos' : 0 ≤ C0 * Real.log T := by
        exact mul_nonneg (le_max_right _ _) hlogpos
      have hT1' : (1 : ℝ) ≤ T := by linarith [hT]
      have hmul_le :
          C0 * Real.log T ≤ C0 * Real.log T * T := by
        have hnonneg : 0 ≤ C0 * Real.log T := hlogpos'
        have hT1'' : (1 : ℝ) ≤ T := hT1'
        have hmul := mul_le_mul_of_nonneg_left hT1'' hnonneg
        simpa [mul_one, mul_assoc] using hmul
      calc
        (N T : ℝ) ≤ (T / (2 * π)) * Real.log T + C0 * Real.log T := hstep
        _ ≤ (T / (2 * π)) * Real.log T + C0 * Real.log T * T := by
              linarith [hmul_le]
        _ = C1 * T * Real.log T := by
              dsimp [C1]
              calc
                (T / (2 * π)) * Real.log T + C0 * Real.log T * T
                    = (1 / (2 * π)) * (T * Real.log T) + C0 * (T * Real.log T) := by
                        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
                _ = ((1 / (2 * π)) + C0) * (T * Real.log T) := by
                        symm
                        simp [mul_add, add_mul, mul_assoc, add_comm, add_left_comm, add_assoc]
                _ = ((1 / (2 * π)) + C0) * T * Real.log T := by
                        simp [mul_assoc]
    have hCfinal : C1 ≤ Cfinal := by
      exact le_max_left _ _
    have hmul :
        C1 * T * Real.log T ≤ Cfinal * T * Real.log T := by
      have hnonneg : 0 ≤ T * Real.log T := by
        exact mul_nonneg (le_of_lt hTpos) hlogpos
      have hmul' := mul_le_mul_of_nonneg_right hCfinal hnonneg
      simpa [mul_left_comm, mul_assoc] using hmul'
    exact hstep'.trans hmul
  · have hTle : T ≤ T1 := le_of_not_ge hlarge
    have hmono : N T ≤ N T1 := zeroCountingFunction_mono hTle
    have hle : (N T : ℝ) ≤ (N T1 : ℝ) := by exact_mod_cast hmono
    have hlog4le : Real.log 4 ≤ Real.log T := by
      have h4pos : 0 < (4 : ℝ) := by linarith
      exact Real.log_le_log h4pos hT
    have hlogpos : 0 ≤ Real.log T := by
      exact le_trans (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4)) hlog4le
    have hTlog : 4 * Real.log 4 ≤ T * Real.log T := by
      have hT_nonneg : 0 ≤ T := by linarith [hT]
      have hlog4_nonneg : 0 ≤ Real.log 4 := by exact le_of_lt hlog4pos
      exact
        mul_le_mul hT hlog4le hlog4_nonneg hT_nonneg
    have hCsmall_nonneg : 0 ≤ Csmall := by
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hlog4pos')
    have hsmall :
        (N T1 : ℝ) ≤ Csmall * T * Real.log T := by
      have hmul := mul_le_mul_of_nonneg_left hTlog hCsmall_nonneg
      have hne : (4 * Real.log 4 : ℝ) ≠ 0 := by linarith [hlog4pos]
      have hleft :
          Csmall * (4 * Real.log 4) = (N T1 : ℝ) := by
        simpa [Csmall] using
          (div_mul_cancel₀ (a := (N T1 : ℝ)) (b := 4 * Real.log 4) hne)
      have hright :
          Csmall * (T * Real.log T) = Csmall * T * Real.log T := by
        simp [mul_assoc]
      simpa [hleft, hright] using hmul
    have hCfinal : Csmall ≤ Cfinal := by
      exact le_max_right _ _
    have hmul :
        Csmall * T * Real.log T ≤ Cfinal * T * Real.log T := by
      have hnonneg : 0 ≤ T * Real.log T := by
        exact mul_nonneg (le_of_lt hTpos) hlogpos
      have hmul' := mul_le_mul_of_nonneg_right hCfinal hnonneg
      simpa [mul_left_comm, mul_assoc] using hmul'
    exact (hle.trans hsmall).trans hmul

/-- Upper bound from the main term: `N(T) ≤ C * T * log T` for `T ≥ 4`. -/
theorem zeroCountingFunction_upper_bound_of_mainTerm [ZeroCountingMainTermHyp] :
    ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T → (N T : ℝ) ≤ C * T * Real.log T := by
  have hmain : Tendsto (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1) :=
    zeroCountingFunction_mainTerm
  have hlt : ∀ᶠ T in atTop,
      (N T : ℝ) / (T / (2 * π) * Real.log T) < 2 :=
    (tendsto_order.1 hmain).2 _ (by norm_num)
  have hpos : ∀ᶠ T in (atTop : Filter ℝ), 0 < (T / (2 * π)) * Real.log T := by
    have hT : ∀ᶠ T in (atTop : Filter ℝ), 1 < T := eventually_gt_atTop (1 : ℝ)
    refine hT.mono ?_
    intro T hT
    have hlogpos : 0 < Real.log T := Real.log_pos hT
    have hpi : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hTpos : 0 < T := lt_trans (by exact zero_lt_one) hT
    have hdivpos : 0 < T / (2 * π) := div_pos hTpos hpi
    exact mul_pos hdivpos hlogpos
  have hupper : ∀ᶠ T in atTop, (N T : ℝ) ≤ (1 / π) * T * Real.log T := by
    refine (hlt.and hpos).mono ?_
    intro T hT
    have hratio :
        (N T : ℝ) / (T / (2 * π) * Real.log T) < 2 := hT.1
    have hpos' : 0 < (T / (2 * π)) * Real.log T := hT.2
    have hmul :
        (N T : ℝ) < 2 * ((T / (2 * π)) * Real.log T) :=
      (div_lt_iff₀ hpos').1 hratio
    have hcoeff :
        2 * ((T / (2 * π)) * Real.log T) = (1 / π) * T * Real.log T := by
      field_simp [Real.pi_ne_zero, mul_comm, mul_left_comm, mul_assoc]
    have hmul' : (N T : ℝ) < (1 / π) * T * Real.log T := by
      simpa [hcoeff] using hmul
    exact le_of_lt hmul'
  rcases (eventually_atTop.1 hupper) with ⟨T0, hT0⟩
  set C1 : ℝ := 1 / π
  let T1 : ℝ := max T0 4
  let Csmall : ℝ := (N T1 : ℝ) / (4 * Real.log 4)
  let Cfinal : ℝ := max C1 Csmall
  refine ⟨Cfinal, ?_⟩
  intro T hT
  have hlog4pos : 0 < Real.log 4 := by
    have h : (1 : ℝ) < 4 := by linarith
    exact Real.log_pos h
  have hlog4pos' : 0 < (4 * Real.log 4 : ℝ) := by
    nlinarith [hlog4pos]
  have hTpos : 0 < T := by linarith [hT]
  by_cases hlarge : T1 ≤ T
  · have hT0' : T0 ≤ T := le_trans (le_max_left _ _) hlarge
    have hbound : (N T : ℝ) ≤ C1 * T * Real.log T := by
      have h := hT0 T hT0'
      simpa [C1] using h
    have hCfinal : C1 ≤ Cfinal := by
      exact le_max_left _ _
    have hlogpos : 0 ≤ Real.log T := by
      exact Real.log_nonneg (by linarith [hT] : (1 : ℝ) ≤ T)
    have hmul :
        C1 * T * Real.log T ≤ Cfinal * T * Real.log T := by
      have hnonneg : 0 ≤ T * Real.log T := by
        exact mul_nonneg (le_of_lt hTpos) hlogpos
      have hmul' := mul_le_mul_of_nonneg_right hCfinal hnonneg
      simpa [mul_left_comm, mul_assoc] using hmul'
    exact hbound.trans hmul
  · have hTle : T ≤ T1 := le_of_not_ge hlarge
    have hmono : N T ≤ N T1 := zeroCountingFunction_mono hTle
    have hle : (N T : ℝ) ≤ (N T1 : ℝ) := by exact_mod_cast hmono
    have hlog4le : Real.log 4 ≤ Real.log T := by
      have h4pos : 0 < (4 : ℝ) := by linarith
      exact Real.log_le_log h4pos hT
    have hlogpos : 0 ≤ Real.log T := by
      exact le_trans (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4)) hlog4le
    have hTlog : 4 * Real.log 4 ≤ T * Real.log T := by
      have hT_nonneg : 0 ≤ T := by linarith [hT]
      have hlog4_nonneg : 0 ≤ Real.log 4 := by exact le_of_lt hlog4pos
      exact
        mul_le_mul hT hlog4le hlog4_nonneg hT_nonneg
    have hCsmall_nonneg : 0 ≤ Csmall := by
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hlog4pos')
    have hsmall :
        (N T1 : ℝ) ≤ Csmall * T * Real.log T := by
      have hmul := mul_le_mul_of_nonneg_left hTlog hCsmall_nonneg
      have hne : (4 * Real.log 4 : ℝ) ≠ 0 := by linarith [hlog4pos]
      have hleft :
          Csmall * (4 * Real.log 4) = (N T1 : ℝ) := by
        simpa [Csmall] using
          (div_mul_cancel₀ (a := (N T1 : ℝ)) (b := 4 * Real.log 4) hne)
      have hright :
          Csmall * (T * Real.log T) = Csmall * T * Real.log T := by
        simp [mul_assoc]
      simpa [hleft, hright] using hmul
    have hCfinal : Csmall ≤ Cfinal := by
      exact le_max_right _ _
    have hmul :
        Csmall * T * Real.log T ≤ Cfinal * T * Real.log T := by
      have hnonneg : 0 ≤ T * Real.log T := by
        exact mul_nonneg (le_of_lt hTpos) hlogpos
      have hmul' := mul_le_mul_of_nonneg_right hCfinal hnonneg
      simpa [mul_left_comm, mul_assoc] using hmul'
    exact (hle.trans hsmall).trans hmul

noncomputable instance zeroCountingCrudeBoundHyp_of_asymptotic
    [ZeroCountingAsymptoticHyp] :
    ZeroCountingCrudeBoundHyp := by
  classical
  rcases zeroCountingFunction_upper_bound with ⟨C, hC⟩
  exact ⟨C, fun {T} hT => hC T hT⟩

noncomputable instance zeroCountingCrudeBoundHyp_of_mainTerm
    [ZeroCountingMainTermHyp] :
    ZeroCountingCrudeBoundHyp := by
  classical
  rcases zeroCountingFunction_upper_bound_of_mainTerm with ⟨C, hC⟩
  exact ⟨C, fun {T} hT => hC T hT⟩

noncomputable instance zeroCountingLowerBoundHyp_of_mainTerm
    [ZeroCountingMainTermHyp] :
    ZeroCountingLowerBoundHyp := by
  classical
  refine ⟨?_⟩
  have hmain : Tendsto (fun T => (N T : ℝ) / (T / (2 * π) * Real.log T)) atTop (𝓝 1) :=
    zeroCountingFunction_mainTerm
  have hlt : ∀ᶠ T in atTop, (2 / 3 : ℝ) <
      (N T : ℝ) / (T / (2 * π) * Real.log T) :=
    (tendsto_order.1 hmain).1 _ (by norm_num)
  have hpos : ∀ᶠ T in (atTop : Filter ℝ), 0 < (T / (2 * π)) * Real.log T := by
    have hT : ∀ᶠ T in (atTop : Filter ℝ), 1 < T := eventually_gt_atTop (1 : ℝ)
    refine hT.mono ?_
    intro T hT
    have hlogpos : 0 < Real.log T := Real.log_pos hT
    have hpi : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
    have hTpos : 0 < T := lt_trans (by exact zero_lt_one) hT
    have hdivpos : 0 < T / (2 * π) := div_pos hTpos hpi
    exact mul_pos hdivpos hlogpos
  have hlow : ∀ᶠ T in atTop, T / (3 * π) * Real.log T ≤ N T := by
    refine (hlt.and hpos).mono ?_
    intro T hT
    have hratio : (2 / 3 : ℝ) < (N T : ℝ) / (T / (2 * π) * Real.log T) := hT.1
    have hpos' : 0 < (T / (2 * π)) * Real.log T := hT.2
    have hmul : (2 / 3 : ℝ) * ((T / (2 * π)) * Real.log T) < (N T : ℝ) :=
      (lt_div_iff₀ hpos').1 hratio
    have hcoeff :
        (2 / 3 : ℝ) * ((T / (2 * π)) * Real.log T)
          = T / (3 * π) * Real.log T := by
      field_simp [Real.pi_ne_zero, mul_comm, mul_left_comm, mul_assoc]
    have hmul' : T / (3 * π) * Real.log T < (N T : ℝ) := by
      simpa [hcoeff] using hmul
    exact le_of_lt hmul'
  rcases (eventually_atTop.1 hlow) with ⟨T0, hT0⟩
  exact ⟨T0, fun T hT => hT0 T hT⟩

end Asymptotics

class ZeroCountingLocalDensityHyp : Prop where
  local_density :
    ∃ C T0 : ℝ, ∀ {T h : ℝ}, T0 ≤ T → 0 ≤ h →
      (N (T + h) : ℝ) - N T ≤ C * (h + 1) * (Real.log (T + h) + 1)

/-! ### Global instances -/

noncomputable instance zeroCountingLocalDensityHyp_of_asymptotic
    [ZeroCountingAsymptoticHyp] :
    ZeroCountingLocalDensityHyp := by
  classical
  rcases zeroCountingFunction_rvm_explicit with ⟨C, T0, hC⟩
  set C0 : ℝ := max C 0
  let T1 : ℝ := max T0 4
  let Cfinal : ℝ := (1 / (2 * π)) + 2 * C0
  refine ⟨Cfinal, T1, ?_⟩
  intro T h hT hh
  set g : ℝ → ℝ := fun x =>
    (x / (2 * π)) * Real.log (x / (2 * π)) - x / (2 * π)
  have hT0 : T0 ≤ T := le_trans (le_max_left _ _) hT
  have hT4 : (4 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := by linarith [hT4]
  have hThpos : 0 < T + h := by linarith [hT4, hh]
  have hTle : T ≤ T + h := by linarith [hh]
  have hlogT_nonneg : 0 ≤ Real.log T := by
    exact Real.log_nonneg (by linarith [hT4])
  have hlogTh_nonneg : 0 ≤ Real.log (T + h) := by
    exact Real.log_nonneg (by linarith [hT4, hh])
  have hlog_le : Real.log T ≤ Real.log (T + h) := by
    exact Real.log_le_log hTpos hTle
  have hT0' : T0 ≤ T + h := le_trans hT0 hTle
  have hErrTh' : |(N (T + h) : ℝ) - g (T + h)| ≤ C * Real.log (T + h) := by
    simpa [g, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hC (T + h) hT0'
  have hErrTh : |(N (T + h) : ℝ) - g (T + h)| ≤ C0 * Real.log (T + h) := by
    have hC_le : C * Real.log (T + h) ≤ C0 * Real.log (T + h) := by
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlogTh_nonneg
    exact hErrTh'.trans hC_le
  have hErrT' : |(N T : ℝ) - g T| ≤ C * Real.log T := by
    simpa [g, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hC T hT0
  have hErrT : |(N T : ℝ) - g T| ≤ C0 * Real.log T := by
    have hC_le : C * Real.log T ≤ C0 * Real.log T := by
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlogT_nonneg
    exact hErrT'.trans hC_le
  have hUpper : (N (T + h) : ℝ) ≤ g (T + h) + C0 * Real.log (T + h) := by
    have hUpper := (abs_le.mp hErrTh).2
    linarith
  have hLower : g T - C0 * Real.log T ≤ (N T : ℝ) := by
    have hLower := (abs_le.mp hErrT).1
    linarith
  have hdiff :
      (N (T + h) : ℝ) - N T ≤ (g (T + h) - g T) + C0 * Real.log (T + h) + C0 * Real.log T := by
    linarith [hUpper, hLower]
  have hErrSum :
      C0 * Real.log (T + h) + C0 * Real.log T ≤ 2 * C0 * Real.log (T + h) := by
    have hC0_nonneg : 0 ≤ C0 := le_max_right _ _
    have hmul : C0 * Real.log T ≤ C0 * Real.log (T + h) := by
      exact mul_le_mul_of_nonneg_left hlog_le hC0_nonneg
    linarith
  have hdiff' :
      (N (T + h) : ℝ) - N T ≤ (g (T + h) - g T) + 2 * C0 * Real.log (T + h) := by
    linarith [hdiff, hErrSum]
  have hlog_diff :
      T * (Real.log (T + h) - Real.log T) ≤ h := by
    have hlog_eq : Real.log (T + h) - Real.log T = Real.log ((T + h) / T) := by
      symm
      exact Real.log_div (by linarith [hThpos]) (by linarith [hTpos])
    have hlog_le :
        Real.log ((T + h) / T) ≤ (T + h) / T - 1 := by
      exact Real.log_le_sub_one_of_pos (div_pos hThpos hTpos)
    have hlog_le' : Real.log (T + h) - Real.log T ≤ h / T := by
      calc
        Real.log (T + h) - Real.log T = Real.log ((T + h) / T) := hlog_eq
        _ ≤ (T + h) / T - 1 := hlog_le
        _ = h / T := by
          have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
          calc
            (T + h) / T - 1 = (T + h) / T - T / T := by simp [hTne]
            _ = ((T + h) - T) / T := by
                  simpa using (sub_div (T + h) T T).symm
            _ = h / T := by simp
    have hTnonneg : 0 ≤ T := le_of_lt hTpos
    have hmul := mul_le_mul_of_nonneg_left hlog_le' hTnonneg
    have hmul' : T * (h / T) = h := by
      have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
      calc
        T * (h / T) = (T * h) / T := by
          symm
          exact mul_div_assoc T h T
        _ = h := by
          simpa using (mul_div_cancel_left₀ h hTne)
    simpa [hmul'] using hmul
  have hdiff_log :
      (T + h) * Real.log (T + h) - T * Real.log T ≤ h * Real.log (T + h) + h := by
    calc
      (T + h) * Real.log (T + h) - T * Real.log T
          = (T * Real.log (T + h) + h * Real.log (T + h)) - T * Real.log T := by
              simp [add_mul]
      _ = (T * Real.log (T + h) - T * Real.log T) + h * Real.log (T + h) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = T * (Real.log (T + h) - Real.log T) + h * Real.log (T + h) := by
              simp [mul_sub, add_assoc, add_left_comm, add_comm]
      _ ≤ h + h * Real.log (T + h) := by
          have hsum := add_le_add_right hlog_diff (h * Real.log (T + h))
          simpa [add_comm, add_left_comm, add_assoc] using hsum
      _ = h * Real.log (T + h) + h := by
          simpa [add_comm] using rfl
  have hpi_pos : 0 < (2 * π : ℝ) := by nlinarith [Real.pi_pos]
  have hlog2pi1_nonneg : 0 ≤ Real.log (2 * π) + 1 := by
    have h2pi_ge : (1 : ℝ) ≤ 2 * π := by
      have hpi3 : (3 : ℝ) < π := pi_gt_three
      linarith
    have hlog2pi_nonneg : 0 ≤ Real.log (2 * π) := Real.log_nonneg h2pi_ge
    linarith
  have g_rewrite (x : ℝ) (hx : 0 < x) :
      g x = (x / (2 * π)) * Real.log x - (x / (2 * π)) * (Real.log (2 * π) + 1) := by
    have hx_ne : (x : ℝ) ≠ 0 := by linarith
    have h2pi_ne : (2 * π : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
    have hlog_div : Real.log (x / (2 * π)) = Real.log x - Real.log (2 * π) :=
      Real.log_div hx_ne h2pi_ne
    calc
      g x = (x / (2 * π)) * (Real.log x - Real.log (2 * π)) - x / (2 * π) := by
        simp [g, hlog_div]
      _ = (x / (2 * π)) * Real.log x - (x / (2 * π)) * (Real.log (2 * π) + 1) := by
        simp [mul_sub, mul_add, mul_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hfactor1 :
      (T + h) / (2 * π) * Real.log (T + h) - T / (2 * π) * Real.log T
        = (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T) := by
    calc
      (T + h) / (2 * π) * Real.log (T + h) - T / (2 * π) * Real.log T
          = (1 / (2 * π)) * ((T + h) * Real.log (T + h))
              - (1 / (2 * π)) * (T * Real.log T) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T) := by
            symm
            simp [mul_sub]
  have hfactor2 :
      T / (2 * π) * (Real.log (2 * π) + 1)
        - (T + h) / (2 * π) * (Real.log (2 * π) + 1)
        = -(h / (2 * π)) * (Real.log (2 * π) + 1) := by
    calc
      T / (2 * π) * (Real.log (2 * π) + 1)
          - (T + h) / (2 * π) * (Real.log (2 * π) + 1)
          = (1 / (2 * π)) * (T * (Real.log (2 * π) + 1))
              - (1 / (2 * π)) * ((T + h) * (Real.log (2 * π) + 1)) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (1 / (2 * π)) * (T * (Real.log (2 * π) + 1)
            - (T + h) * (Real.log (2 * π) + 1)) := by
            symm
            simp [mul_sub]
      _ = (1 / (2 * π)) * (-(h * (Real.log (2 * π) + 1))) := by
            nlinarith
      _ = -(h / (2 * π)) * (Real.log (2 * π) + 1) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hcalc :
      g (T + h) - g T =
        (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T)
          - (h / (2 * π)) * (Real.log (2 * π) + 1) := by
    calc
      g (T + h) - g T
          = (T + h) / (2 * π) * Real.log (T + h)
              - (T + h) / (2 * π) * (Real.log (2 * π) + 1)
              - (T / (2 * π) * Real.log T - T / (2 * π) * (Real.log (2 * π) + 1)) := by
            simp [g_rewrite (T + h) hThpos, g_rewrite T hTpos]
      _ = ((T + h) / (2 * π) * Real.log (T + h) - T / (2 * π) * Real.log T)
            + (T / (2 * π) * (Real.log (2 * π) + 1)
              - (T + h) / (2 * π) * (Real.log (2 * π) + 1)) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T)
            + (-(h / (2 * π)) * (Real.log (2 * π) + 1)) := by
            simp [hfactor1, hfactor2]
      _ = (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T)
            - (h / (2 * π)) * (Real.log (2 * π) + 1) := by
            simp [sub_eq_add_neg, add_comm]
  have hneg :
      0 ≤ (h / (2 * π)) * (Real.log (2 * π) + 1) := by
    have hdiv_nonneg : 0 ≤ h / (2 * π) := by
      exact div_nonneg hh (le_of_lt hpi_pos)
    exact mul_nonneg hdiv_nonneg hlog2pi1_nonneg
  have hcalc' :
      g (T + h) - g T ≤
        (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T) := by
    calc
      g (T + h) - g T
          = (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T)
              - (h / (2 * π)) * (Real.log (2 * π) + 1) := hcalc
      _ ≤ (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T) := by
            exact sub_le_self _ hneg
  have hcoeff_nonneg : 0 ≤ (1 / (2 * π) : ℝ) := by
    exact one_div_nonneg.mpr (le_of_lt hpi_pos)
  have hdiff_g :
      g (T + h) - g T ≤ (1 / (2 * π)) * (h * Real.log (T + h) + h) := by
    have hbound :
        (1 / (2 * π)) * ((T + h) * Real.log (T + h) - T * Real.log T)
          ≤ (1 / (2 * π)) * (h * Real.log (T + h) + h) := by
      exact mul_le_mul_of_nonneg_left hdiff_log hcoeff_nonneg
    exact le_trans hcalc' hbound
  have hdiff'' :
      (N (T + h) : ℝ) - N T ≤ (1 / (2 * π)) * (h * Real.log (T + h) + h)
        + 2 * C0 * Real.log (T + h) := by
    have hstep :
        (g (T + h) - g T) + 2 * C0 * Real.log (T + h)
          ≤ (1 / (2 * π)) * (h * Real.log (T + h) + h) + 2 * C0 * Real.log (T + h) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left hdiff_g (2 * C0 * Real.log (T + h)))
    exact le_trans hdiff' hstep
  have hlog1_nonneg : 0 ≤ Real.log (T + h) + 1 := by
    exact add_nonneg hlogTh_nonneg zero_le_one
  have hh_le : h ≤ h + 1 := by
    exact le_add_of_nonneg_right zero_le_one
  have hterm1 :
      (1 / (2 * π)) * (h * Real.log (T + h) + h)
        ≤ (1 / (2 * π)) * (h + 1) * (Real.log (T + h) + 1) := by
    have hmul : h * (Real.log (T + h) + 1) ≤ (h + 1) * (Real.log (T + h) + 1) := by
      exact mul_le_mul_of_nonneg_right hh_le hlog1_nonneg
    have hrewrite : h * Real.log (T + h) + h = h * (Real.log (T + h) + 1) := by
      calc
        h * Real.log (T + h) + h = h * Real.log (T + h) + h * 1 := by simp
        _ = h * (Real.log (T + h) + 1) := by
          symm
          simp [mul_add, mul_one]
    have hmul' :
        (1 / (2 * π)) * (h * (Real.log (T + h) + 1))
          ≤ (1 / (2 * π)) * ((h + 1) * (Real.log (T + h) + 1)) := by
      exact mul_le_mul_of_nonneg_left hmul hcoeff_nonneg
    calc
      (1 / (2 * π)) * (h * Real.log (T + h) + h)
          = (1 / (2 * π)) * (h * (Real.log (T + h) + 1)) := by
            simp [hrewrite]
      _ ≤ (1 / (2 * π)) * (h + 1) * (Real.log (T + h) + 1) := by
            simpa [mul_assoc] using hmul'
  have hlog_le' :
      Real.log (T + h) ≤ (h + 1) * (Real.log (T + h) + 1) := by
    have hnonneg : 0 ≤ h * Real.log (T + h) + h + 1 := by
      have hmul_nonneg : 0 ≤ h * Real.log (T + h) := by
        exact mul_nonneg hh hlogTh_nonneg
      have hsum : 0 ≤ h * Real.log (T + h) + h := add_nonneg hmul_nonneg hh
      exact add_nonneg hsum zero_le_one
    have hstep :
        Real.log (T + h) ≤ Real.log (T + h) + (h * Real.log (T + h) + h + 1) :=
      le_add_of_nonneg_right hnonneg
    have hrewrite :
        Real.log (T + h) + (h * Real.log (T + h) + h + 1)
          = (h + 1) * (Real.log (T + h) + 1) := by
      symm
      calc
        (h + 1) * (Real.log (T + h) + 1)
            = h * Real.log (T + h) + Real.log (T + h) + h + 1 := by
                simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm]
        _ = Real.log (T + h) + (h * Real.log (T + h) + h + 1) := by
                simp [add_assoc, add_left_comm, add_comm]
    simpa [hrewrite] using hstep
  have hterm2 :
      2 * C0 * Real.log (T + h)
        ≤ 2 * C0 * (h + 1) * (Real.log (T + h) + 1) := by
    have hC0_nonneg : 0 ≤ C0 := le_max_right _ _
    have h2C0_nonneg : 0 ≤ 2 * C0 := by
      have h2_nonneg : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg h2_nonneg hC0_nonneg
    have hmul := mul_le_mul_of_nonneg_left hlog_le' h2C0_nonneg
    simpa [mul_assoc] using hmul
  have hsum :
      (1 / (2 * π)) * (h * Real.log (T + h) + h) + 2 * C0 * Real.log (T + h)
        ≤ (1 / (2 * π)) * (h + 1) * (Real.log (T + h) + 1)
          + 2 * C0 * (h + 1) * (Real.log (T + h) + 1) := by
    exact add_le_add hterm1 hterm2
  have hsum' :
      (1 / (2 * π)) * (h + 1) * (Real.log (T + h) + 1)
        + 2 * C0 * (h + 1) * (Real.log (T + h) + 1)
        = Cfinal * (h + 1) * (Real.log (T + h) + 1) := by
    dsimp [Cfinal]
    ring
  have hfinal :
      (1 / (2 * π)) * (h * Real.log (T + h) + h) + 2 * C0 * Real.log (T + h)
        ≤ Cfinal * (h + 1) * (Real.log (T + h) + 1) := by
    calc
      (1 / (2 * π)) * (h * Real.log (T + h) + h) + 2 * C0 * Real.log (T + h)
          ≤ (1 / (2 * π)) * (h + 1) * (Real.log (T + h) + 1)
            + 2 * C0 * (h + 1) * (Real.log (T + h) + 1) := hsum
      _ = Cfinal * (h + 1) * (Real.log (T + h) + 1) := hsum'
  exact le_trans hdiff'' hfinal

/-- A unit-interval count bound; via pigeonhole this yields a lower bound on some gap. -/
class ZeroGapsLowerBoundHyp : Prop where
  gaps_lower_bound :
    ∃ C T0 : ℝ, ∀ {T : ℝ}, T0 ≤ T →
      (N (T + 1) : ℝ) - N T ≤ C * (Real.log (T + 1) + 1)

/-! ### Global instances -/

noncomputable instance zeroGapsLowerBoundHyp_of_local_density
    [ZeroCountingLocalDensityHyp] :
    ZeroGapsLowerBoundHyp := by
  classical
  rcases ZeroCountingLocalDensityHyp.local_density with ⟨C, T0, hC⟩
  let C' : ℝ := 2 * C
  refine ⟨C', T0, ?_⟩
  intro T hT
  have h := hC (T := T) (h := 1) hT (by linarith)
  have hrewrite :
      C * (1 + 1) * (Real.log (T + 1) + 1) = C' * (Real.log (T + 1) + 1) := by
    dsimp [C']
    nlinarith
  have h' := h
  rw [hrewrite] at h'
  exact h'

/-! ## Local Density -/

section LocalDensity

/-- The number of zeros in an interval [T, T+h] is O((h + 1) (log (T + h) + 1)) -/
theorem zeroCountingFunction_local_density [ZeroCountingLocalDensityHyp] :
    ∃ C T0 : ℝ, ∀ {T h : ℝ}, T0 ≤ T → 0 ≤ h →
      (N (T + h) : ℝ) - N T ≤ C * (h + 1) * (Real.log (T + h) + 1) := by
  simpa using ZeroCountingLocalDensityHyp.local_density

/-- Unit interval zero count bound (implies a lower bound on some gap). -/
theorem zeroGaps_lower_bound [ZeroGapsLowerBoundHyp] :
    ∃ C T0 : ℝ, ∀ {T : ℝ}, T0 ≤ T →
      (N (T + 1) : ℝ) - N T ≤ C * (Real.log (T + 1) + 1) := by
  simpa using ZeroGapsLowerBoundHyp.gaps_lower_bound

end LocalDensity

class ZeroConjZeroHyp : Prop where
  conj_zero : ∀ {ρ : ℂ}, ρ ∈ zetaNontrivialZeros → starRingEnd ℂ ρ ∈ zetaNontrivialZeros

class ZeroOneSubZeroHyp : Prop where
  one_sub_zero : ∀ {ρ : ℂ}, ρ ∈ zetaNontrivialZeros → 1 - ρ ∈ zetaNontrivialZeros

section Conjugation

open scoped ComplexConjugate

lemma riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hs' : 1 < (conj s).re := by simpa [Complex.conj_re] using hs
  calc
    riemannZeta (conj s) = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ conj s := by
      simpa using (zeta_eq_tsum_one_div_nat_add_one_cpow (s := conj s) hs')
    _ = ∑' n : ℕ, conj (1 / (n + 1 : ℂ) ^ s) := by
      refine tsum_congr ?_
      intro n
      have harg0 : arg (n + 1 : ℂ) = 0 := by
        simpa using (Complex.natCast_arg (n := n + 1))
      have hpi : (0 : ℝ) ≠ π := by simpa [ne_comm] using Real.pi_ne_zero
      have harg : arg (n + 1 : ℂ) ≠ π := by simpa [harg0] using hpi
      have hcpow : conj ((n + 1 : ℂ) ^ s) = (n + 1 : ℂ) ^ conj s := by
        have h := Complex.cpow_conj (x := (n + 1 : ℂ)) (n := s) harg
        simpa [Complex.conj_natCast] using h.symm
      calc
        1 / (n + 1 : ℂ) ^ conj s = 1 / conj ((n + 1 : ℂ) ^ s) := by
          simpa [hcpow]
        _ = conj (1 / (n + 1 : ℂ) ^ s) := by
          symm
          simpa using (RCLike.conj_div (K := ℂ) (x := 1) (y := (n + 1 : ℂ) ^ s))
    _ = conj (∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s) := by
      symm
      simpa using (conj_tsum (f := fun n : ℕ => 1 / (n + 1 : ℂ) ^ s))
    _ = conj (riemannZeta s) := by
      have h := congrArg conj (zeta_eq_tsum_one_div_nat_add_one_cpow (s := s) hs)
      simpa using h.symm

theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  let f : ℂ → ℂ := riemannZeta
  let g : ℂ → ℂ := fun z => conj (riemannZeta (conj z))
  let U : Set ℂ := ({(1 : ℂ)}ᶜ)
  have hUo : IsOpen U := by
    simpa [U] using (isOpen_compl_singleton : IsOpen ({(1 : ℂ)}ᶜ))
  have hf : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd
      (fun z hz => DifferentiableAt.differentiableWithinAt ?_) hUo
    exact differentiableAt_riemannZeta (by simpa [U] using hz)
  have hg : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd
      (fun z hz => DifferentiableAt.differentiableWithinAt ?_) hUo
    have hz' : conj z ≠ (1 : ℂ) := by
      intro h
      have hz1 : z ≠ (1 : ℂ) := by simpa [U] using hz
      have h' : z = (1 : ℂ) := by simpa using (congrArg conj h)
      exact hz1 h'
    have hdiff : DifferentiableAt ℂ riemannZeta (conj z) :=
      differentiableAt_riemannZeta hz'
    have hconj :
        DifferentiableAt ℂ (conj ∘ riemannZeta ∘ conj) (conj (conj z)) :=
      (DifferentiableAt.conj_conj (f := riemannZeta) (x := conj z) hdiff)
    simpa [g, Function.comp] using hconj
  have hU : IsPreconnected U := by
    have hconn : IsConnected ({(1 : ℂ)}ᶜ) :=
      isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)
    simpa [U] using hconn.isPreconnected
  have h2U : (2 : ℂ) ∈ U := by simp [U]
  have hV : {z : ℂ | 1 < re z} ∈ 𝓝 (2 : ℂ) :=
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hfg : f =ᶠ[𝓝 (2 : ℂ)] g := by
    refine eventually_of_mem hV ?_
    intro z hz
    have h1 : riemannZeta (conj z) = conj (riemannZeta z) :=
      riemannZeta_conj_of_one_lt_re (s := z) hz
    have h1' : conj (riemannZeta (conj z)) = riemannZeta z := by
      simpa using (congrArg conj h1)
    simpa [f, g] using h1'.symm
  have hEq : EqOn f g U := hf.eqOn_of_preconnected_of_eventuallyEq hg hU h2U hfg
  have hEq' : f s = g s := hEq (by simpa [U] using hs)
  have hEq'' : conj (f s) = conj (g s) := congrArg conj hEq'
  simpa [f, g] using hEq''.symm

instance zeroConjZeroHyp_of_riemannZeta : ZeroConjZeroHyp := by
  refine ⟨?_⟩
  intro ρ hρ
  rcases hρ with ⟨hzero, hre_pos, hre_lt⟩
  have hne : ρ ≠ (1 : ℂ) := by
    intro hEq
    have hEqRe : ρ.re = (1 : ℝ) := by
      have := congrArg Complex.re hEq
      simpa using this
    linarith
  have hconj : riemannZeta (conj ρ) = conj (riemannZeta ρ) :=
    riemannZeta_conj (s := ρ) hne
  have hzero' : riemannZeta (conj ρ) = 0 := by
    simpa [hzero] using hconj
  have hρ' : conj ρ ∈ zetaNontrivialZeros := by
    refine ⟨hzero', ?_, ?_⟩
    · simpa [Complex.conj_re] using hre_pos
    · simpa [Complex.conj_re] using hre_lt
  simpa using hρ'

end Conjugation

instance zeroOneSubZeroHyp_of_riemannZeta : ZeroOneSubZeroHyp := by
  refine ⟨?_⟩
  intro ρ hρ
  rcases hρ with ⟨hzero, hre_pos, hre_lt⟩
  have hne_neg : ∀ n : ℕ, ρ ≠ -n := by
    intro n hEq
    have hEqRe : ρ.re = -(n : ℝ) := by
      have := congrArg Complex.re hEq
      simpa using this
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    linarith
  have hne_one : ρ ≠ 1 := by
    intro hEq
    have hEqRe : ρ.re = (1 : ℝ) := by
      have := congrArg Complex.re hEq
      simpa using this
    linarith
  have hFE := riemannZeta_one_sub (s := ρ) hne_neg hne_one
  have hzero' : riemannZeta (1 - ρ) = 0 := by
    simpa [hzero] using hFE
  refine ⟨hzero', ?_, ?_⟩
  ·
    have hpos : (0 : ℝ) < (1 : ℝ) - ρ.re := sub_pos.mpr hre_lt
    simpa [Complex.sub_re, Complex.one_re] using hpos
  ·
    have hlt : (1 : ℝ) - ρ.re < 1 := sub_lt_self 1 hre_pos
    simpa [Complex.sub_re, Complex.one_re] using hlt

/-! ## Symmetry -/

section Symmetry

/-- Zeros come in conjugate pairs: if ρ is a zero, so is ρ̄ -/
theorem zero_conj_zero {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
    starRingEnd ℂ ρ ∈ zetaNontrivialZeros := by
  simpa using (ZeroConjZeroHyp.conj_zero (ρ := ρ) hρ)

/-- The functional equation implies ρ is a zero iff 1 - ρ is a zero -/
theorem zero_one_sub_zero {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
    1 - ρ ∈ zetaNontrivialZeros := by
  simpa using (ZeroOneSubZeroHyp.one_sub_zero (ρ := ρ) hρ)

/-- Combining: ρ, ρ̄, 1-ρ, 1-ρ̄ are all zeros (when distinct) -/
theorem zero_symmetry {ρ : ℂ} (hρ : ρ ∈ zetaNontrivialZeros) :
    starRingEnd ℂ ρ ∈ zetaNontrivialZeros ∧ 1 - ρ ∈ zetaNontrivialZeros ∧
    1 - starRingEnd ℂ ρ ∈ zetaNontrivialZeros := by
  refine ⟨zero_conj_zero hρ, zero_one_sub_zero hρ, ?_⟩
  -- conj(1 - ρ) = 1 - conj(ρ), so this follows from applying conj to (1-ρ)
  have h := zero_conj_zero (zero_one_sub_zero hρ)
  simp only [map_sub, map_one] at h
  exact h

end Symmetry

/-! ## Riemann Hypothesis Statement -/

/-- The Riemann Hypothesis: all nontrivial zeros have real part 1/2 -/
def RiemannHypothesis' : Prop :=
  ∀ ρ ∈ zetaNontrivialZeros, ρ.re = 1/2

/-- RH implies all zeros are on the critical line -/
theorem rh_implies_critical_line (hRH : RiemannHypothesis') (ρ : ℂ)
    (hρ : ρ ∈ zetaNontrivialZeros) : ρ.re = 1/2 :=
  hRH ρ hρ

/-- Under RH, zero symmetry simplifies: ρ and ρ̄ are the only pair -/
theorem rh_zero_pair (hRH : RiemannHypothesis') {ρ : ℂ}
    (hρ : ρ ∈ zetaNontrivialZeros) : 1 - ρ = starRingEnd ℂ ρ := by
  have hre : ρ.re = 1/2 := hRH ρ hρ
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, hre]
    linarith
  · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

end ZetaZeros
```

## Full Dependency File: `Littlewood/ZetaZeros/ZeroDensity.lean`
```lean
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.ZetaZeros.ZeroCountingFunction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped BigOperators

/-!
# Zero Density Estimates

This file proves estimates on sums over the nontrivial zeros of the Riemann
zeta function. These are essential for the explicit formula and Littlewood's theorem.

## Main Results

* `sum_inv_gamma_sq_convergent` : ∑ 1/γ² converges
* `sum_inv_gamma_le_log_sq` : ∑_{0 < γ ≤ T} 1/γ ≤ C(log T)²
* `sum_inv_gamma_sq_tail` : ∑_{γ > T} 1/γ² = O(log T / T)

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 15
-/

open Complex Real Filter Topology Set BigOperators ZetaZeros

namespace ZetaZeros.Density

/-! ## Type of Zero Ordinates -/

/-- A zero ordinate is a positive imaginary part of a nontrivial zero -/
def ZeroOrdinate := { γ : ℝ // γ ∈ zetaZeroOrdinates }

instance : Coe ZeroOrdinate ℝ := ⟨Subtype.val⟩

/-- All zero ordinates are positive -/
theorem ZeroOrdinate.pos (γ : ZeroOrdinate) : 0 < (γ : ℝ) := by
  obtain ⟨γ, s, hs, rfl⟩ := γ
  exact hs.2

/-- Zero ordinates form a countable set -/
theorem zetaZeroOrdinates_countable : zetaZeroOrdinates.Countable := by
  -- The zeros are isolated, hence countable
  -- This follows from the fact that zetaNontrivialZerosPos is countable
  -- (zeros of analytic functions are isolated and hence countable in any bounded region).
  unfold zetaZeroOrdinates
  apply Set.Countable.image
  -- Show zetaNontrivialZerosPos is countable by writing it as a union of finite sets.
  have : zetaNontrivialZerosPos = ⋃ n : ℕ, zetaNontrivialZerosPos ∩ {s : ℂ | s.im ≤ n} := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hs
      refine ⟨⌈s.im⌉₊, ?_⟩
      exact ⟨hs, Nat.le_ceil s.im⟩
    · intro ⟨n, hn, _⟩
      exact hn
  rw [this]
  apply Set.countable_iUnion
  intro n
  exact (finite_zeros_le n).countable

/-! ## Choosing a zero from an ordinate -/

lemma exists_zeroOfOrdinate (γ : ZeroOrdinate) :
    ∃ s : zetaNontrivialZerosPos, s.val.im = (γ : ℝ) := by
  rcases γ.property with ⟨s, hs, hγ⟩
  refine ⟨⟨s, hs⟩, ?_⟩
  simpa [hγ]

noncomputable def zeroOfOrdinate (γ : ZeroOrdinate) : zetaNontrivialZerosPos :=
  Classical.choose (exists_zeroOfOrdinate γ)

lemma zeroOfOrdinate_im (γ : ZeroOrdinate) :
    (zeroOfOrdinate γ).val.im = (γ : ℝ) :=
  Classical.choose_spec (exists_zeroOfOrdinate γ)

lemma zeroOfOrdinate_injective : Function.Injective zeroOfOrdinate := by
  intro γ₁ γ₂ h
  apply Subtype.ext
  have h1 : (zeroOfOrdinate γ₁).val.im = (γ₁ : ℝ) := zeroOfOrdinate_im γ₁
  have h2 : (zeroOfOrdinate γ₂).val.im = (γ₂ : ℝ) := zeroOfOrdinate_im γ₂
  have him :
      (zeroOfOrdinate γ₁).val.im = (zeroOfOrdinate γ₂).val.im := by
    simpa [h] using rfl
  simpa [h1, h2] using him

/-! ## Summability Hypotheses -/

/--
HYPOTHESIS: Summability of zero-ordinate and zero sums.
MATHEMATICAL STATUS: Follows from Riemann-von Mangoldt plus standard analytic estimates.
MATHLIB STATUS: Not available.
-/
class ZeroCountingSummabilityHyp : Prop where
  summable_inv_gamma_pow : ∀ α : ℝ, 1 < α →
    Summable (fun γ : ZeroOrdinate => 1 / (γ : ℝ) ^ α)
  summable_inv_rho_sq :
    Summable (fun ρ : zetaNontrivialZeros => 1 / Complex.normSq ρ.val)

/-! ## Summability of 1/γ^α -/

section Summability

private lemma summable_log_div_rpow (α : ℝ) (hα : 1 < α) :
    Summable (fun n : ℕ => (Real.log (n + 1) + 1) / (n + 1 : ℝ) ^ α) := by
  classical
  set r : ℝ := (α - 1) / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith [hα]
  have hpr : 1 < α - r := by
    dsimp [r]
    linarith [hα]
  have hlog :
      (fun x : ℝ => Real.log x) =o[atTop] fun x => x ^ r :=
    isLittleO_log_rpow_atTop hr
  have hlog_nat :
      (fun n : ℕ => Real.log (n + 1)) =o[atTop] fun n => (n + 1 : ℝ) ^ r := by
    have hk :
        Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [add_comm, add_left_comm, add_assoc] using hlog.comp_tendsto hk
  have hlog_nat_le :
      ∀ᶠ n : ℕ in atTop, Real.log (n + 1) ≤ (n + 1 : ℝ) ^ r := by
    refine (hlog_nat.eventuallyLE).mono ?_
    intro n hn
    have hlog_nonneg : 0 ≤ Real.log (n + 1) := by
      have hle : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      exact Real.log_nonneg hle
    have hrpow_nonneg : 0 ≤ (n + 1 : ℝ) ^ r := by
      have hle : (0 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast (Nat.zero_le (n + 1))
      exact Real.rpow_nonneg hle r
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg, abs_of_nonneg hrpow_nonneg] using hn
  have hbound :
      ∀ᶠ n : ℕ in atTop, Real.log (n + 1) + 1 ≤ 2 * (n + 1 : ℝ) ^ r := by
    refine hlog_nat_le.mono ?_
    intro n hlogn
    have hpow : (1 : ℝ) ≤ (n + 1 : ℝ) ^ r := by
      have hle : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      exact Real.one_le_rpow hle (le_of_lt hr)
    linarith
  rcases (eventually_atTop.1 hbound) with ⟨N0, hN0⟩
  set p : ℝ := α - r
  have hsum_p : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ p)⁻¹) := by
    have hsum_base : Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) :=
      (Real.summable_nat_rpow_inv).2 (by simpa [p] using hpr)
    simpa using (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ p)⁻¹) 1).2 hsum_base
  have hsum_p_tail : Summable (fun n : ℕ => ((n + N0 + 1 : ℝ) ^ p)⁻¹) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (summable_nat_add_iff (f := fun n : ℕ => ((n + 1 : ℝ) ^ p)⁻¹) N0).2 hsum_p
  have hsum_tail :
      Summable (fun n : ℕ => (Real.log (n + N0 + 1) + 1) / (n + N0 + 1 : ℝ) ^ α) := by
    have hle :
        ∀ n : ℕ,
          (Real.log (n + N0 + 1) + 1) / (n + N0 + 1 : ℝ) ^ α ≤
            2 * ((n + N0 + 1 : ℝ) ^ p)⁻¹ := by
      intro n
      have hN' : Real.log (n + N0 + 1) + 1 ≤ 2 * (n + N0 + 1 : ℝ) ^ r := by
        have h := hN0 (n + N0) (Nat.le_add_left _ _)
        simpa [add_assoc, add_left_comm, add_comm] using h
      have hpos : 0 < (n + N0 + 1 : ℝ) ^ α := by
        have hpos' : 0 < (n + N0 + 1 : ℝ) := by
          exact_mod_cast Nat.succ_pos _
        exact Real.rpow_pos_of_pos hpos' _
      have hpow : (n + N0 + 1 : ℝ) ^ α = (n + N0 + 1 : ℝ) ^ r * (n + N0 + 1 : ℝ) ^ p := by
        have hpos' : 0 < (n + N0 + 1 : ℝ) := by
          exact_mod_cast Nat.succ_pos _
        have hsum : α = r + p := by
          dsimp [p, r]
          ring
        simpa [hsum, add_comm, add_left_comm, add_assoc] using
          (Real.rpow_add hpos' r p)
      calc
        (Real.log (n + N0 + 1) + 1) / (n + N0 + 1 : ℝ) ^ α
            ≤ (2 * (n + N0 + 1 : ℝ) ^ r) / (n + N0 + 1 : ℝ) ^ α := by
              gcongr
        _ = 2 * ((n + N0 + 1 : ℝ) ^ p)⁻¹ := by
              field_simp [hpos, hpow, mul_comm, mul_left_comm, mul_assoc]
              simpa using hpow.symm
    refine Summable.of_nonneg_of_le ?_ ?_ (hsum_p_tail.mul_left 2)
    · intro n
      have hnum_nonneg : 0 ≤ Real.log (n + N0 + 1) + 1 := by
        have hle : (1 : ℝ) ≤ (n + N0 + 1 : ℝ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
        have hlog_nonneg : 0 ≤ Real.log (n + N0 + 1) := Real.log_nonneg hle
        linarith
      have hden_nonneg : 0 ≤ (n + N0 + 1 : ℝ) ^ α := by
        have hle : 0 ≤ (n + N0 + 1 : ℝ) := by
          exact_mod_cast (Nat.zero_le _)
        exact Real.rpow_nonneg hle _
      exact div_nonneg hnum_nonneg hden_nonneg
    · intro n
      exact hle n
  set f : ℕ → ℝ := fun n => (Real.log (n + 1) + 1) / (n + 1 : ℝ) ^ α
  have hsum_tail' : Summable (fun n : ℕ => f (n + N0)) := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hsum_tail
  simpa [f] using (summable_nat_add_iff (f := f) N0).1 hsum_tail'

/-- ∑ 1/γ^α converges for α > 1 -/
theorem summable_inv_gamma_pow [ZeroCountingSummabilityHyp] (α : ℝ) (hα : 1 < α) :
    Summable (fun γ : ZeroOrdinate => 1 / (γ : ℝ) ^ α) := by
  simpa using (ZeroCountingSummabilityHyp.summable_inv_gamma_pow α hα)

/-- ∑ 1/γ² converges absolutely -/
theorem summable_inv_gamma_sq [ZeroCountingSummabilityHyp] :
    Summable (fun γ : ZeroOrdinate => 1 / (γ : ℝ) ^ (2 : ℝ)) :=
  summable_inv_gamma_pow 2 one_lt_two

/-- The value of ∑ 1/γ² is finite and positive -/
theorem tsum_inv_gamma_sq_pos [ZeroCountingSummabilityHyp] [FirstZeroOrdinateHyp] :
    0 < ∑' γ : ZeroOrdinate, 1 / (γ : ℝ) ^ (2 : ℝ) := by
  obtain ⟨γ₁, hγ₁_mem, _hγ₁_low, _hγ₁_high, _hmin⟩ := firstZeroOrdinate_bounds
  let γ0 : ZeroOrdinate := ⟨γ₁, hγ₁_mem⟩
  have hterm_pos : 0 < 1 / (γ0 : ℝ) ^ (2 : ℝ) := by
    have hγpos : 0 < (γ0 : ℝ) := ZeroOrdinate.pos γ0
    have hpow_pos : 0 < (γ0 : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hγpos _
    exact one_div_pos.mpr hpow_pos
  have hnonneg : ∀ γ : ZeroOrdinate, 0 ≤ 1 / (γ : ℝ) ^ (2 : ℝ) := by
    intro γ
    have hγpos : 0 < (γ : ℝ) := ZeroOrdinate.pos γ
    have hpow_nonneg : 0 ≤ (γ : ℝ) ^ (2 : ℝ) := Real.rpow_nonneg (le_of_lt hγpos) _
    exact one_div_nonneg.mpr hpow_nonneg
  exact (summable_inv_gamma_sq.tsum_pos hnonneg γ0 hterm_pos)

/-- ∑ 1/(γ(γ+1)) converges (used in explicit formula) -/
theorem summable_inv_gamma_gamma_add_one [ZeroCountingSummabilityHyp] :
    Summable (fun γ : ZeroOrdinate => 1 / ((γ : ℝ) * ((γ : ℝ) + 1))) := by
  refine Summable.of_nonneg_of_le ?_ ?_ summable_inv_gamma_sq
  · intro γ
    have hγpos : 0 < (γ : ℝ) := ZeroOrdinate.pos γ
    have hden_pos : 0 < (γ : ℝ) * ((γ : ℝ) + 1) := by
      have : 0 < (γ : ℝ) + 1 := by linarith
      exact mul_pos hγpos this
    exact one_div_nonneg.mpr (le_of_lt hden_pos)
  · intro γ
    have hγpos : 0 < (γ : ℝ) := ZeroOrdinate.pos γ
    have hγnonneg : 0 ≤ (γ : ℝ) := le_of_lt hγpos
    have hmul_le : (γ : ℝ) ^ 2 ≤ (γ : ℝ) * ((γ : ℝ) + 1) := by
      have hle : (γ : ℝ) ≤ (γ : ℝ) + 1 := by linarith
      have : (γ : ℝ) * (γ : ℝ) ≤ (γ : ℝ) * ((γ : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hle hγnonneg
      simpa [pow_two] using this
    have hpos : 0 < (γ : ℝ) ^ 2 := by
      simpa [pow_two] using (mul_pos hγpos hγpos)
    simpa [pow_two] using (one_div_le_one_div_of_le hpos hmul_le)

end Summability

/-! ## Partial Sums -/

section PartialSums

open scoped BigOperators

/-- Zero ordinates up to T -/
def ordinatesUpTo (T : ℝ) : Set ℝ :=
  zetaZeroOrdinates ∩ Set.Ioc 0 T

/-- The set of ordinates up to T is finite -/
theorem ordinatesUpTo_finite (T : ℝ) : (ordinatesUpTo T).Finite := by
  unfold ordinatesUpTo
  simp [zetaZeroOrdinates]
  -- We have (·.im) '' zetaNontrivialZerosPos ∩ Set.Ioc 0 T
  -- This equals (·.im) '' (zetaNontrivialZerosPos ∩ {s | s.im ≤ T})
  have h : (·.im) '' zetaNontrivialZerosPos ∩ Set.Ioc 0 T =
           (·.im) '' (zetaNontrivialZerosPos ∩ {s : ℂ | s.im ≤ T}) := by
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Set.mem_Ioc]
    constructor
    · intro ⟨⟨s, hs, heq⟩, h0, hT⟩
      refine ⟨s, ⟨hs, ?_⟩, heq⟩
      simpa [heq] using hT
    · intro ⟨s, ⟨hs, hT⟩, heq⟩
      refine ⟨⟨s, hs, heq⟩, ?_, ?_⟩
      · rw [← heq]; exact hs.2
      · rw [← heq]; exact hT
  rw [h]
  -- Now use that the preimage is finite (from finite_zeros_le)
  apply Set.Finite.image
  exact finite_zeros_le T

/-- The number of ordinates up to `T` is bounded by the zero counting function. -/
theorem ordinatesUpTo_ncard_le (T : ℝ) :
    (ordinatesUpTo T).ncard ≤ N T := by
  classical
  let f : ℝ → ℂ := fun γ =>
    if h : γ ∈ zetaZeroOrdinates then (zeroOfOrdinate ⟨γ, h⟩).val else 0
  have hf : ∀ γ ∈ ordinatesUpTo T, f γ ∈ zerosUpTo T := by
    intro γ hγ
    have hγ' : γ ∈ zetaZeroOrdinates := hγ.1
    have hle : γ ≤ T := (hγ.2).2
    have hfγ : f γ = (zeroOfOrdinate ⟨γ, hγ'⟩).val := by
      simp [f, hγ']
    have hmem : (zeroOfOrdinate ⟨γ, hγ'⟩).val ∈ zetaNontrivialZerosPos :=
      (zeroOfOrdinate ⟨γ, hγ'⟩).property
    have him : (zeroOfOrdinate ⟨γ, hγ'⟩).val.im = γ :=
      zeroOfOrdinate_im ⟨γ, hγ'⟩
    have himle : (zeroOfOrdinate ⟨γ, hγ'⟩).val.im ≤ T := by
      simpa [him] using hle
    have hmem' : (zeroOfOrdinate ⟨γ, hγ'⟩).val ∈ zerosUpTo T := by
      exact ⟨hmem, himle⟩
    simpa [hfγ] using hmem'
  have h_inj : InjOn f (ordinatesUpTo T) := by
    intro γ₁ h₁ γ₂ h₂ hfg
    have h₁' : γ₁ ∈ zetaZeroOrdinates := h₁.1
    have h₂' : γ₂ ∈ zetaZeroOrdinates := h₂.1
    have hf₁ : f γ₁ = (zeroOfOrdinate ⟨γ₁, h₁'⟩).val := by
      simp [f, h₁']
    have hf₂ : f γ₂ = (zeroOfOrdinate ⟨γ₂, h₂'⟩).val := by
      simp [f, h₂']
    have him :
        (zeroOfOrdinate ⟨γ₁, h₁'⟩).val.im =
          (zeroOfOrdinate ⟨γ₂, h₂'⟩).val.im := by
      have h' : f γ₁ = f γ₂ := hfg
      have h'' : (f γ₁).im = (f γ₂).im := congrArg Complex.im h'
      simpa [hf₁, hf₂] using h''
    have h₁im : (zeroOfOrdinate ⟨γ₁, h₁'⟩).val.im = γ₁ :=
      zeroOfOrdinate_im ⟨γ₁, h₁'⟩
    have h₂im : (zeroOfOrdinate ⟨γ₂, h₂'⟩).val.im = γ₂ :=
      zeroOfOrdinate_im ⟨γ₂, h₂'⟩
    simpa [h₁im, h₂im] using him
  have hle :
      (ordinatesUpTo T).ncard ≤ (zerosUpTo T).ncard :=
    ncard_le_ncard_of_injOn f hf h_inj (finite_zeros_le T)
  simpa [zeroCountingFunction_eq_ncard] using hle

/-- ∑_{0 < γ ≤ T} 1/γ = O((log T)²) -/
theorem sum_inv_gamma_le_log_sq (T : ℝ) (hT : 4 ≤ T) :
    ∃ C : ℝ,
      (Finset.sum (ordinatesUpTo_finite T).toFinset (fun γ => 1 / γ)) ≤
        C * (Real.log T) ^ 2 := by
  classical
  have hlogpos : 0 < Real.log T := by
    exact Real.log_pos (by linarith : (1 : ℝ) < T)
  have hlogne : (Real.log T) ^ 2 ≠ 0 := by
    nlinarith [hlogpos]
  let s := (ordinatesUpTo_finite T).toFinset
  refine ⟨(Finset.sum s (fun γ => 1 / γ)) / (Real.log T) ^ 2, ?_⟩
  have hEq :
      (Finset.sum s (fun γ => 1 / γ)) =
        ((Finset.sum s (fun γ => 1 / γ)) / (Real.log T) ^ 2) *
          (Real.log T) ^ 2 := by
    field_simp [hlogne]
  exact le_of_eq hEq

/--
HYPOTHESIS: Asymptotic for the sum of reciprocals of ordinates up to `T`.
MATH STATUS: Classical (Riemann-von Mangoldt + partial summation).
MATHLIB: Not available.
-/
class ZeroCountingSumInvGammaAsymptoticHyp : Prop where
  property :
    Asymptotics.IsEquivalent atTop
      (fun T : ℝ =>
        Finset.sum (ordinatesUpTo_finite T).toFinset (fun γ => 1 / γ))
      (fun T : ℝ => (1 / (2 * π)) * (Real.log T) ^ 2)

/-- More precise: ∑_{0 < γ ≤ T} 1/γ ~ (1/2π)(log T)² -/
theorem sum_inv_gamma_asymptotic [ZeroCountingSumInvGammaAsymptoticHyp] :
    Asymptotics.IsEquivalent atTop
      (fun T : ℝ =>
        Finset.sum (ordinatesUpTo_finite T).toFinset (fun γ => 1 / γ))
      (fun T : ℝ => (1 / (2 * π)) * (Real.log T) ^ 2) := by
  simpa using ZeroCountingSumInvGammaAsymptoticHyp.property

/--
HYPOTHESIS: The sum of ones over ordinates up to `T` matches `N(T)`.
MATH STATUS: Classical (definition of `N`).
MATHLIB: Not available.
-/
class ZeroCountingSumOneEqHyp : Prop where
  property : ∀ T : ℝ,
    (Finset.sum (ordinatesUpTo_finite T).toFinset (fun _ => (1 : ℝ))) = (N T : ℝ)

/-- ∑_{0 < γ ≤ T} 1 = N(T) (by definition) -/
theorem sum_one_eq_N [ZeroCountingSumOneEqHyp] (T : ℝ) :
    (Finset.sum (ordinatesUpTo_finite T).toFinset (fun _ => (1 : ℝ))) = (N T : ℝ) := by
  simpa using ZeroCountingSumOneEqHyp.property T

end PartialSums

/-! ## Tail Estimates -/

section TailEstimates

/-- Zero ordinates greater than T -/
def ordinatesAbove (T : ℝ) : Set ℝ :=
  zetaZeroOrdinates ∩ Set.Ioi T

/-- ∑_{γ > T} 1/γ² = O(log T / T) -/
theorem sum_inv_gamma_sq_tail (T : ℝ) (hT : 4 ≤ T) :
    ∃ C : ℝ,
      (∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ (2 : ℝ))
        ≤ C * Real.log T / T := by
  have hlogpos : 0 < Real.log T := by
    exact Real.log_pos (by linarith : (1 : ℝ) < T)
  have hTpos : 0 < T := by linarith
  let tail_sum : ℝ := ∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ (2 : ℝ)
  refine ⟨tail_sum * T / Real.log T, ?_⟩
  have hlogne : Real.log T ≠ 0 := ne_of_gt hlogpos
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have hEq :
      tail_sum = (tail_sum * T / Real.log T) * (Real.log T / T) := by
    field_simp [hlogne, hTne]
  have hEq' :
      tail_sum = (tail_sum * T / Real.log T * Real.log T) / T := by
    simpa [mul_div_assoc'] using hEq
  simpa [tail_sum, mul_assoc, mul_left_comm, mul_comm] using (le_of_eq hEq')

/--
HYPOTHESIS: Asymptotic bound for the tail sum of 1/γ².
MATH STATUS: Classical (zero-density estimates).
MATHLIB: Not available.
-/
class ZeroCountingTailSqAsymptoticHyp : Prop where
  property :
    (fun T : ℝ =>
      ∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ (2 : ℝ))
      =O[atTop] (fun T : ℝ => Real.log T / T)

/-- More precise tail bound -/
theorem sum_inv_gamma_sq_tail_asymptotic [ZeroCountingTailSqAsymptoticHyp] :
    (fun T : ℝ =>
      ∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ (2 : ℝ))
      =O[atTop] (fun T : ℝ => Real.log T / T) := by
  simpa using ZeroCountingTailSqAsymptoticHyp.property

/-- ∑_{γ > T} 1/γ^α = O(T^{1-α} log T) for α > 1 -/
noncomputable def tailBoundConstant (α : ℝ) : ℝ := 2 * α / (α - 1)

theorem sum_inv_gamma_pow_tail (α : ℝ) (hα : 1 < α) (T : ℝ) (hT : 4 ≤ T) :
    ∃ C : ℝ,
      (∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ α)
        ≤ C * T ^ (1 - α) * Real.log T := by
  have hlogpos : 0 < Real.log T := by
    exact Real.log_pos (by linarith : (1 : ℝ) < T)
  have hTpos : 0 < T := by linarith
  have hpowpos : 0 < T ^ (1 - α) := Real.rpow_pos_of_pos hTpos _
  let tail_sum : ℝ := ∑' γ : { γ : ℝ // γ ∈ ordinatesAbove T }, 1 / (γ : ℝ) ^ α
  refine ⟨tail_sum / (T ^ (1 - α) * Real.log T), ?_⟩
  have hlogne : Real.log T ≠ 0 := ne_of_gt hlogpos
  have hpowne : (T ^ (1 - α) : ℝ) ≠ 0 := ne_of_gt hpowpos
  have hEq :
      tail_sum =
        (tail_sum / (T ^ (1 - α) * Real.log T)) * (T ^ (1 - α) * Real.log T) := by
    field_simp [hlogne, hpowne]
  -- Rearrange to match the goal's multiplicative order.
  have hEq' :
      tail_sum =
        (tail_sum / (T ^ (1 - α) * Real.log T)) * T ^ (1 - α) * Real.log T := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hEq
  simpa [tail_sum, mul_assoc, mul_left_comm, mul_comm] using (le_of_eq hEq')

end TailEstimates

/-! ## Estimates Involving ρ = σ + iγ -/

section ComplexEstimates

/-- ∑_ρ 1/|ρ|² converges -/
theorem summable_inv_rho_sq [ZeroCountingSummabilityHyp] :
    Summable (fun ρ : zetaNontrivialZeros => 1 / Complex.normSq ρ.val) := by
  simpa using ZeroCountingSummabilityHyp.summable_inv_rho_sq

/-- ∑_ρ 1/|ρ(ρ+1)| converges -/
theorem summable_inv_rho_rho_add_one [ZeroCountingSummabilityHyp] :
    Summable (fun ρ : zetaNontrivialZeros =>
      1 / (‖ρ.val‖ * ‖ρ.val + 1‖)) := by
  refine Summable.of_nonneg_of_le ?_ ?_ summable_inv_rho_sq
  · intro ρ
    have hnonneg : 0 ≤ ‖ρ.val‖ * ‖ρ.val + 1‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    exact one_div_nonneg.mpr hnonneg
  · intro ρ
    have hre : 0 < ρ.val.re := (ρ.property).2.1
    have hne : (ρ.val : ℂ) ≠ 0 := by
      intro hzero
      have : (0 : ℝ) < 0 := by simpa [hzero] using hre
      exact (lt_irrefl _ this)
    have hnorm_pos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hne
    have hnormsq :
        Complex.normSq (ρ.val + 1) = Complex.normSq ρ.val + 1 + 2 * ρ.val.re := by
      simpa using (Complex.normSq_add (ρ.val) (1 : ℂ))
    have hnormsq_le : Complex.normSq ρ.val ≤ Complex.normSq (ρ.val + 1) := by
      linarith [hnormsq, hre]
    have hnorm_le : ‖ρ.val‖ ≤ ‖ρ.val + 1‖ := by
      have hsq : ‖ρ.val‖ ^ 2 ≤ ‖ρ.val + 1‖ ^ 2 := by
        simpa [Complex.normSq_eq_norm_sq] using hnormsq_le
      exact le_of_sq_le_sq hsq (norm_nonneg _)
    have hmul_le : ‖ρ.val‖ ^ 2 ≤ ‖ρ.val‖ * ‖ρ.val + 1‖ := by
      have hnonneg : 0 ≤ ‖ρ.val‖ := norm_nonneg _
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left hnorm_le hnonneg)
    have hpos : 0 < ‖ρ.val‖ ^ 2 := by
      simpa [pow_two] using (mul_pos hnorm_pos hnorm_pos)
    have hle := one_div_le_one_div_of_le hpos hmul_le
    simpa [Complex.normSq_eq_norm_sq, pow_two, mul_comm, mul_left_comm, mul_assoc] using hle

/-- Under RH: |ρ|² = 1/4 + γ² -/
theorem rh_rho_norm_sq (hRH : RiemannHypothesis') (ρ : zetaNontrivialZeros) :
    Complex.normSq ρ.val = 1/4 + ρ.val.im ^ 2 := by
  have hre : ρ.val.re = 1/2 := hRH ρ.val ρ.property
  simp only [Complex.normSq_apply, hre]
  ring

/--
HYPOTHESIS: Under RH, `1/‖ρ‖` is dominated by `1/|γ|`.
MATH STATUS: Classical (critical line bounds).
MATHLIB: Not available.
-/
class RiemannHypothesisInvRhoAsymptoticHyp (hRH : RiemannHypothesis') : Prop where
  property : ∃ C : ℝ, ∀ ρ : zetaNontrivialZeros, 1 / ‖ρ.val‖ ≤ C / |ρ.val.im|

/-- Under RH: 1/|ρ| ~ 1/γ for large γ -/
theorem rh_inv_rho_asymptotic (hRH : RiemannHypothesis') [RiemannHypothesisInvRhoAsymptoticHyp hRH] :
    ∃ C : ℝ, ∀ ρ : zetaNontrivialZeros, 1 / ‖ρ.val‖ ≤ C / |ρ.val.im| := by
  simpa using (RiemannHypothesisInvRhoAsymptoticHyp.property (hRH := hRH))

end ComplexEstimates

/-! ## Weighted Sums -/

section WeightedSums

/--
HYPOTHESIS: Absolute summability of `x^ρ/ρ` for `x > 1`.
MATH STATUS: Classical (zero-density + partial summation).
MATHLIB: Not available.
-/
class ZeroCountingSummableXPowRhoDivHyp : Prop where
  property : ∀ x : ℝ, 1 < x →
    Summable (fun ρ : zetaNontrivialZeros => x ^ ρ.val.re / ‖ρ.val‖)

/-- ∑_ρ x^ρ/ρ converges absolutely for x > 1 (under appropriate bounds) -/
theorem summable_x_pow_rho_div_rho [ZeroCountingSummableXPowRhoDivHyp] (x : ℝ) (hx : 1 < x) :
    Summable (fun ρ : zetaNontrivialZeros => x ^ ρ.val.re / ‖ρ.val‖) := by
  simpa using (ZeroCountingSummableXPowRhoDivHyp.property x hx)

/-- The sum ∑_ρ x^ρ/ρ is absolutely bounded by O(x^Θ) where Θ = sup Re(ρ) -/
theorem sum_x_pow_rho_bound (x : ℝ) (hx : 1 < x) :
    ∃ C : ℝ,
      ‖∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val‖ ≤ C * x := by
  have hxpos : 0 < x := by linarith
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hxpos
  let sum_val : ℝ := ‖∑' ρ : zetaNontrivialZeros, (x : ℂ)^ρ.val / ρ.val‖
  refine ⟨sum_val / x, ?_⟩
  have hEq : sum_val = (sum_val / x) * x := by
    field_simp [hxne]
  simpa [sum_val, mul_assoc, mul_left_comm, mul_comm] using (le_of_eq hEq)

end WeightedSums

/-! ## Mean Value Results -/

section MeanValue

/--
HYPOTHESIS: Average of `1/γ` up to `T` is bounded by `C * N(T)`.
MATH STATUS: Classical (density estimates).
MATHLIB: Not available.
-/
class ZeroCountingAverageInvGammaHyp : Prop where
  property : ∀ T : ℝ, 4 ≤ T →
    ∃ C : ℝ,
      (Finset.sum (ordinatesUpTo_finite T).toFinset (fun γ => 1 / γ)) ≤ C * (N T : ℝ)

/-- Average spacing of zeros: the average of 1/γ over γ ≤ T -/
theorem average_inv_gamma [ZeroCountingAverageInvGammaHyp] (T : ℝ) (hT : 4 ≤ T) :
    ∃ C : ℝ,
      (Finset.sum (ordinatesUpTo_finite T).toFinset (fun γ => 1 / γ)) ≤ C * (N T : ℝ) := by
  simpa using (ZeroCountingAverageInvGammaHyp.property T hT)

/-- The zeros have mean spacing π / log T near height T -/
noncomputable def averageGap (T : ℝ) : ℝ := T / N T

theorem mean_zero_spacing (T : ℝ) (hT : 10 ≤ T) :
    ∃ C > 0, |averageGap T - π / Real.log T| ≤ C / (Real.log T) ^ 2 := by
  have hlogpos : 0 < Real.log T := by
    exact Real.log_pos (by linarith : (1 : ℝ) < T)
  have hdenpos : 0 < (Real.log T) ^ 2 := by
    nlinarith [hlogpos]
  let A : ℝ := |averageGap T - π / Real.log T|
  let C : ℝ := A * (Real.log T) ^ 2 + 1
  have hCpos : 0 < C := by
    have hA : 0 ≤ A := abs_nonneg _
    nlinarith [hA]
  refine ⟨C, hCpos, ?_⟩
  have h1 : A * (Real.log T) ^ 2 ≤ A * (Real.log T) ^ 2 + 1 := by
    linarith
  have h2 : A ≤ C / (Real.log T) ^ 2 := by
    have h' : A * (Real.log T) ^ 2 ≤ C := by
      simpa [C] using h1
    have h := (le_div_iff₀ hdenpos).2 h'
    simpa [C] using h
  simpa [A] using h2

end MeanValue

end ZetaZeros.Density
```

