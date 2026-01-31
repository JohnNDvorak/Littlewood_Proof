# Aristotle Prompts for Remaining Infrastructure Gaps

Generated 2026-01-26. These prompts are ready to submit to Aristotle for
goal-state-dependent proofs that require interactive Lean access.

---

## PROMPT 1: DirichletApprox Round Optimality

**File:** `Littlewood/Aristotle/DirichletApprox.lean`
**Lines:** 78-81
**Current state:** Has a proof attempt that fails (type mismatch after `simp_all`)

```
Complete the sorry in dirichlet_simultaneous_approximation in Lean 4.

File: Littlewood/Aristotle/DirichletApprox.lean
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

The theorem states: For reals α₁,...,αₙ and N ≥ 1, there exists integer q
with 1 ≤ q ≤ N^n such that |q·αⱼ - round(q·αⱼ)| < 1/N for all j.

The proof uses pigeonhole: partition [0,1)^n into N^n boxes of side 1/N.
For q ∈ {0,1,...,N^n}, the fractional parts ({q·α₁},...,{q·αₙ}) give N^n+1
points. By pigeonhole, two points q₁,q₂ land in the same box.
Then q = |q₁-q₂| satisfies the bound.

The sorry is in the final step (lines 78-81) after:
  simp_all +decide [ abs_lt, round_eq ]
which transforms the goal significantly. After simp_all, the goal involves
|(↑q₁ - ↑q₂) * α j - ↑⌊(↑q₁ - ↑q₂) * α j + 2⁻¹⌋| * ↑N ≤ ...

Available in context:
- k_j := ⌊q₁ * α j⌋ - ⌊q₂ * α j⌋
- hk_j : |(q₁ - q₂) * α j - k_j| < 1 / (N : ℝ)
- hN : 0 < N

Key Mathlib lemmas:
- round_le (x : α) (z : ℤ) : |x - round x| ≤ |x - z|
- abs_sub_round (x : α) : |x - round x| ≤ 1/2
- round_eq (x : α) : round x = ⌊x + 1/2⌋

The challenge: simp_all with round_eq expands round to floor in the goal,
and abs_lt splits the absolute value, making the goal form different from
what round_le produces. Need to either:
1. Rewrite the goal back to round form and use round_le + hk_j
2. Or work directly with the floor expression

Please provide the complete proof for lines 78-81 that replaces:
  have h_opt := round_le (((q₁ : ℝ) - (q₂ : ℝ)) * α j) k_j
  rw [round_eq] at h_opt
  exact lt_of_le_of_lt h_opt hk_j
```

---

## PROMPT 2: sum_split (tsum over disjoint union)

**File:** `Littlewood/Aristotle/ZetaZeroInfrastructure.lean`
**Line:** ~306
**Current state:** `sorry`

```
Prove the sum_split lemma in Lean 4 with current Mathlib.

File: Littlewood/Aristotle/ZetaZeroInfrastructure.lean

lemma sum_split (T : ℝ) (f : ℂ → ℂ) :
    (∑' ρ : zetaZerosUpTo T, f ρ) =
    (∑' ρ : criticalLineZeros T, f ρ) + (∑' ρ : offCriticalZeros T, f ρ)

Context:
- zetaZerosUpTo T, criticalLineZeros T, offCriticalZeros T are subtypes of ℂ
- zetaZerosUpTo T = criticalLineZeros T ∪ offCriticalZeros T (disjoint)
- All three sets are finite (finite_zeros T is proved)
- criticalLineZeros T = zeros with Re = 1/2
- offCriticalZeros T = zeros with Re ≠ 1/2

Definitions already in file:
def zetaZerosUpTo (T : ℝ) : Set ℂ := {s | isNontrivialZero s ∧ |s.im| ≤ T}
def criticalLineZeros (T : ℝ) : Set ℂ := {s | isNontrivialZero s ∧ s.re = 1/2 ∧ |s.im| ≤ T}
def offCriticalZeros (T : ℝ) : Set ℂ := {s | isNontrivialZero s ∧ s.re ≠ 1/2 ∧ |s.im| ≤ T}

lemma finite_zeros (T : ℝ) : Set.Finite (zetaZerosUpTo T) -- PROVED
lemma zeros_split (T : ℝ) : zetaZerosUpTo T = criticalLineZeros T ∪ offCriticalZeros T -- PROVED
lemma zeros_disjoint (T : ℝ) : Disjoint (criticalLineZeros T) (offCriticalZeros T) -- PROVED

The challenge is handling tsum over subtypes. Approaches:
1. Convert tsum to Finset.sum via tsum_eq_sum for finite sets
2. Use tsum_union_disjoint with Set.indicator functions
3. Use Equiv to decompose the subtype

For finite sets, tsum reduces to Finset.sum, so the split is just
Finset.sum_union_disjoint applied through the finite set conversion.

Please provide the complete proof handling the Set → Subtype → tsum conversions.
```

---

## PROMPT 3: cos_alignment (phase alignment)

**File:** `Littlewood/Aristotle/PhaseAlignment.lean`
**Line:** ~62
**Current state:** `sorry`

```
Prove cos_alignment in Lean 4 with Mathlib.

File: Littlewood/Aristotle/PhaseAlignment.lean

lemma cos_alignment (γs : Finset ℝ) (ε : ℝ) (hε : ε > 0) (M : ℝ) :
    ∃ x > M, ∀ γ ∈ γs, |Real.cos (γ * Real.log x) - 1| < ε

Available (already proved in same file):
lemma align_phases (γs : Finset ℝ) (ε : ℝ) (hε : ε > 0) :
    ∃ t > 0, ∀ γ ∈ γs, ∃ k : ℤ, |t * γ / (2 * Real.pi) - k| < ε

The idea:
1. From align_phases with small ε', get t > 0 with phases near integers
2. Then cos(γ·t) is near cos(2πk) = 1
3. Set x = exp(t), so log(x) = t and cos(γ·log(x)) ≈ 1
4. For x > M, need t > log(M), so use align_phases iteratively or
   add multiples of 2π/γ to increase t while preserving alignment

Key challenge: align_phases gives t > 0 but not t > log(M). Need to
either get arbitrarily large t, or show we can shift t to be large
while preserving the phase alignment.

The oscillation_alignment theorem in DirichletApprox.lean handles this
for a different setup (Fin n → ℝ instead of Finset ℝ). May be possible
to deduce cos_alignment from oscillation_alignment via conversion.

Please provide the complete proof.
```

---

## PROMPT 4: BinetStirling sorries (6 sorries)

**File:** `Littlewood/Aristotle/BinetStirling.lean`
**Current state:** Multiple `sorry` in asymptotic lemmas

```
Complete the 6 sorries in BinetStirling.lean for Lean 4 with Mathlib.

File: Littlewood/Aristotle/BinetStirling.lean

The file establishes asymptotic properties of log Gamma via the Binet integral.
The sorry-free parts (already proved) include:
- binet_integrand_continuous
- binet_integrand_differentiable
- bounded_of_continuous_limits
- binet_integrand_bounded

The remaining sorries:

1. log_one_add_sub_self_asymptotic:
   (fun z : ℂ => log (1 + z) - z) =O[𝓝 0] (fun z => z ^ 2)
   Proof: Taylor expansion log(1+z) = z - z²/2 + ...

2. log_one_add_inv_im_asymptotic:
   (fun t : ℝ => log (1 + 1/(2*I*t)) - 1/(2*I*t)) =O[atTop] (fun t => 1/t^2)
   Proof: Compose #1 with z = 1/(2it) → 0

3. log_split_lemma:
   ∀ᶠ t in atTop, log(1/4 + I*t/2) = log(I*t/2) + log(1 + 1/(2*I*t))
   Proof: Factor 1/4 + it/2 = (it/2)(1 + 1/(2it)), use log multiplicativity

4. log_quarter_plus_it_half_asymptotic:
   log(1/4 + I*t/2) - (log(t/2) + I*(π/2) - I/(2*t)) =O[atTop] (1/t²)
   Proof: Combine #3, log(i*t/2) = log(t/2) + iπ/2, and #2

5. stirling_approx_im_asymptotic:
   (stirlingApprox t).im - ((t/2)*log(t/2) - t/2 - π/8) =O[atTop] (1/t)
   Proof: Expand stirlingApprox using #4, track imaginary parts

6. binet_integrand_limit_zero:
   Tendsto binetIntegrand (𝓝[>] 0) (𝓝 (1/12))
   Proof: Taylor expansion of e^t near 0 gives B(t) → 1/12

7. binet_integrand_limit_infinity:
   Tendsto binetIntegrand atTop (𝓝 0)
   Proof: (1/2 - 1/t + 1/(e^t-1))/t → 0 as t → ∞

These form a dependency chain (1→2→3→4→5). Items 6-7 are independent.
Please provide complete proofs for all.
```
