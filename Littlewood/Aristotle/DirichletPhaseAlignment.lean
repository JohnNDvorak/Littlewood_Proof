import Mathlib

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

lemma exists_large_x_phases_aligned_finset (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ.re = 1/2) (ε : ℝ) (hε : ε > 0) (X : ℝ) :
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
lemma bound_real_part_of_sum_aligned {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re = 1/2) {x : ℝ} (hx : x > 0) {ε : ℝ} (hε : ε > 0)
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
    simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _, Finset.sum_mul ];
    rw [ ← Finset.sum_sub_distrib ];
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_re_bound i hi, Real.sqrt_nonneg x ] ;

end Aristotle.DirichletPhaseAlignment

end
