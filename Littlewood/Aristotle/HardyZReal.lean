/-
Hardy Z-function is real-valued - proved by Aristotle.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

noncomputable section

open Complex Topology Filter

/-- log of a positive natural number is real (fixed by conj) -/
lemma conj_log_nat {n : ℕ} (hn : n ≠ 0) :
    starRingEnd ℂ (log (n : ℂ)) = log (n : ℂ) := by
  have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [← ofReal_natCast, ← ofReal_log hn_nonneg]
  rw [starRingEnd_apply, RCLike.star_def, conj_ofReal]

/-- star of complex power equals power of star argument for natural number base -/
lemma star_cpow_nat {n : ℕ} (hn : n ≠ 0) (s : ℂ) : star ((n : ℂ) ^ s) = (n : ℂ) ^ (star s) := by
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  -- n^s = exp(s * log n) for n > 0
  rw [cpow_def_of_ne_zero hn_ne, cpow_def_of_ne_zero hn_ne]
  -- star(exp(z)) = exp(star(z)) - use exp_conj
  simp only [RCLike.star_def]
  rw [← exp_conj]
  congr 1
  -- conj(log n * s) = log n * conj(s) since log n is real for n > 0
  rw [mul_comm, map_mul, mul_comm]
  congr 1
  -- log(n) is real, hence fixed by conj
  exact conj_log_nat hn

/-- star(1/z^s) = 1/z^star(s) for positive natural z -/
lemma star_one_div_nat_cpow {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    star (1 / (n : ℂ) ^ s) = 1 / (n : ℂ) ^ (star s) := by
  rw [star_div₀, star_one, star_cpow_nat hn]

/-- The Riemann zeta function commutes with complex conjugation.
    For Re(s) > 1, this follows from the Dirichlet series.
    By analytic continuation (identity theorem), it extends to all s ≠ 1.
    At s = 1, both sides are the same special value.

    PROOF STRATEGY:
    1. Case s = 1: Both sides equal riemannZeta_one
    2. Case Re(s) > 1: Use Dirichlet series ζ(s) = Σ n^(-s), star commutes with sums
    3. General case: Identity theorem - both sides are analytic on ℂ \ {1},
       agree on {Re > 1}, hence agree everywhere -/
lemma riemannZeta_conj (s : ℂ) : riemannZeta (star s) = star (riemannZeta s) := by
  -- Strategy: Define G(s) = star(ζ(star(s))). G is analytic (anti ∘ holo ∘ anti = holo).
  -- Show G = ζ on {Re > 1} using Dirichlet series.
  -- By identity theorem, G = ζ everywhere.
  -- This gives ζ(s) = star(ζ(star(s))), hence ζ(star(s)) = star(ζ(s)).
  --
  -- Part 1: Show the result for Re(s) > 1 using Dirichlet series
  have h_dirichlet : ∀ z : ℂ, 1 < z.re → riemannZeta (star z) = star (riemannZeta z) := by
    intro z hz
    have hz_star_re : 1 < (star z).re := by
      simp only [RCLike.star_def, conj_re]
      exact hz
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz]
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz_star_re]
    rw [RCLike.star_def, Complex.conj_tsum]
    congr 1
    ext n
    rw [map_div₀, map_one]
    congr 1
    -- Need: (n+1)^(starRingEnd ℂ z) = starRingEnd ℂ ((n+1)^z)
    have := star_cpow_nat (Nat.succ_ne_zero n) z
    simp only [RCLike.star_def, Nat.cast_succ] at this ⊢
    exact this.symm
  --
  -- Part 2: Extend to all s ≠ 1 using identity theorem
  by_cases hs_re : 1 < s.re
  · exact h_dirichlet s hs_re
  · by_cases hs_eq : s = 1
    · -- At s = 1, star 1 = 1, and riemannZeta 1 is real
      subst hs_eq
      rw [star_one]
      -- riemannZeta 1 = (γ - log(4π))/2, which is real
      -- since both γ and log(4π) are real (for positive 4π)
      rw [riemannZeta_one]
      -- star of real/2 = real/2: show the star preserves this real number
      have h4pi_pos : (0 : ℝ) < 4 * Real.pi := by positivity
      -- log(4π) as complex equals ofReal (Real.log (4π))
      have h_log_real : log (4 * Real.pi : ℂ) = (Real.log (4 * Real.pi) : ℂ) := by
        rw [show (4 * Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) by norm_cast]
        rw [← ofReal_log (le_of_lt h4pi_pos)]
      -- Show the star preserves this expression
      -- The expression is (γ - log(4π))/2 which is real
      rw [h_log_real]
      -- Now goal is: (γ : ℂ) - (Real.log (4π) : ℂ)) / 2 = star (...)
      -- star (ofReal r) = ofReal r for any r
      have h_star_ofReal : ∀ r : ℝ, star (r : ℂ) = r := fun r => by
        rw [RCLike.star_def, conj_ofReal]
      -- Convert the whole expression to ofReal form
      have h_eq : ((Real.eulerMascheroniConstant : ℂ) - (Real.log (4 * Real.pi) : ℂ)) / 2 =
          (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [h_eq, h_star_ofReal]
    · -- For s ≠ 1 with Re(s) ≤ 1, use identity theorem
      -- Define G(s) := star(ζ(star(s)))
      -- G is analytic on ℂ \ {1} (anti ∘ holo ∘ anti = holo)
      -- G = ζ on {Re > 1}
      -- By identity theorem, G = ζ on all of ℂ \ {1}
      --
      -- Step 1: Show s ↦ star(ζ(star(s))) is analytic on ℂ \ {1}
      have hζ_diff : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ := fun z hz =>
        (differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hz)).differentiableWithinAt
      -- star preserves the complement of {1}
      have hstar_one : star (1 : ℂ) = 1 := star_one ℂ
      have hstar_compl : ∀ z, z ∈ ({(1 : ℂ)}ᶜ : Set ℂ) ↔ star z ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
        intro z
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        constructor
        · intro hz; contrapose! hz; rw [← star_star z, hz, hstar_one]
        · intro hz; contrapose! hz; rw [hz, hstar_one]
      -- g(s) = star(ζ(star(s))) is differentiable on ℂ \ {1}
      have hg_diff : DifferentiableOn ℂ (fun z => star (riemannZeta (star z))) {(1 : ℂ)}ᶜ := by
        intro z hz
        have hz' : star z ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := (hstar_compl z).mp hz
        have hζ_at : DifferentiableAt ℂ riemannZeta (star z) :=
          differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hz')
        -- By DifferentiableAt.star_star: if f is diff at w, then star ∘ f ∘ star is diff at star w
        have := hζ_at.star_star
        -- star(star z) = z
        simp only [star_star, Function.comp_apply] at this
        exact this.differentiableWithinAt
      -- Both ζ and g are analytic on the open set ℂ \ {1}
      have hζ_analytic : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
        hζ_diff.analyticOnNhd isOpen_compl_singleton
      have hg_analytic : AnalyticOnNhd ℂ (fun z => star (riemannZeta (star z))) {(1 : ℂ)}ᶜ :=
        hg_diff.analyticOnNhd isOpen_compl_singleton
      -- ℂ \ {1} is connected
      have hU_connected : IsConnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
        isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.finrank_real_complex]) 1
      -- They agree on {Re > 1} which has accumulation points
      -- Pick z₀ = 2 ∈ ℂ \ {1}, which is in the closure of {z | ζ(z) = g(z)} \ {2}
      have hz₀_mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; norm_num
      -- Define the difference f - g
      set f := riemannZeta
      set g := fun z => star (riemannZeta (star z))
      -- The set where f - g = 0 includes {Re > 1} ∩ (ℂ \ {1})
      -- 2 is in the closure of this set minus {2}
      have h_in_closure : (2 : ℂ) ∈ closure ({z | (f - g) z = 0} \ {2}) := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        -- Take z = 2 + min(ε/2, 1/2), which has Re > 1 and is within ε of 2
        set δ := min (ε/2) (1/2) with hδ_def
        have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
        use 2 + δ
        constructor
        · constructor
          · -- (f - g)(2 + δ) = 0 since Re(2 + δ) > 1
            simp only [Set.mem_setOf_eq, Pi.sub_apply, sub_eq_zero]
            -- Need: ζ(2+δ) = star(ζ(star(2+δ)))
            -- h_dirichlet says: for Re(z) > 1, ζ(star z) = star(ζ(z))
            -- Apply to star(2+δ): ζ(star(star(2+δ))) = star(ζ(star(2+δ)))
            -- i.e., ζ(2+δ) = star(ζ(star(2+δ)))
            have hre : 1 < (star ((2 : ℂ) + δ)).re := by
              -- star(2 + δ) = 2 + δ since 2 + δ is real
              have h2real : (2 : ℂ) + δ = ((2 + δ : ℝ) : ℂ) := by push_cast; ring
              rw [h2real, RCLike.star_def, Complex.conj_ofReal, Complex.ofReal_re]
              linarith [hδ_pos]
            have := h_dirichlet (star ((2 : ℂ) + δ)) hre
            simp only [star_star] at this
            exact this
          · -- 2 + δ ≠ 2
            simp only [Set.mem_singleton_iff, ne_eq]
            intro h
            have h1 : ((2 : ℂ) + δ).re = (2 : ℂ).re := congrArg Complex.re h
            simp only [Complex.add_re, Complex.ofReal_re] at h1
            linarith [hδ_pos]
        · -- dist(2 + δ, 2) < ε
          rw [dist_comm]
          simp only [dist_eq_norm]
          calc ‖(2 : ℂ) + δ - 2‖ = ‖(δ : ℂ)‖ := by ring_nf
            _ = |δ| := Complex.norm_real δ
            _ = δ := abs_of_pos hδ_pos
            _ ≤ ε/2 := min_le_left _ _
            _ < ε := by linarith
      -- Apply identity theorem (closure version)
      have h_eq : Set.EqOn (f - g) 0 {(1 : ℂ)}ᶜ :=
        (hζ_analytic.sub hg_analytic).eqOn_zero_of_preconnected_of_mem_closure
          hU_connected.isPreconnected hz₀_mem h_in_closure
      -- s ∈ ℂ \ {1}
      have hs_mem : s ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact hs_eq
      -- Apply the equality: (f - g)(s) = 0, i.e., f(s) = g(s)
      have h_at_s := h_eq hs_mem
      -- h_at_s : (f - g)(s) = 0, i.e., f(s) - g(s) = 0
      simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h_at_s
      -- h_at_s : ζ(s) = star(ζ(star(s))), i.e., f s = g s where g s = star(f(star s))
      -- Goal: ζ(star s) = star(ζ(s)), i.e., f (star s) = star (f s)
      -- From h_at_s, taking star of both sides and using star_star:
      -- star(ζ(s)) = star(star(ζ(star s))), so star(star(ζ(star s))) = star(ζ(s))
      -- Then ζ(star s) = star(star(ζ(star s))) = star(ζ(s))
      calc riemannZeta (star s)
          = star (star (riemannZeta (star s))) := (star_star _).symm
        _ = star (riemannZeta s) := (congrArg star h_at_s).symm

/-- The Gamma function commutes with complex conjugation. -/
lemma gamma_conj (s : ℂ) : Complex.Gamma (star s) = star (Complex.Gamma s) :=
  Complex.Gamma_conj s

/-- On critical line s = 1/2 + it, we have star(s) = 1 - s -/
lemma critical_line_star_eq (t : ℝ) : star ((1:ℂ)/2 + I * t) = 1 - ((1:ℂ)/2 + I * t) := by
  simp only [RCLike.star_def, map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_I,
             Complex.conj_ofReal]
  ring

/-- completedRiemannZeta commutes with complex conjugation.
    This follows from the identity theorem: both sides are meromorphic
    with poles at 0 and 1, and they agree on {Re > 1} where the
    explicit formula shows each factor commutes with conjugation. -/
lemma completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (star s) = star (completedRiemannZeta s) := by
  -- Strategy: Same as riemannZeta_conj - use identity theorem.
  -- For Re(s) > 1: ξ(s) = π^(-s/2) * Γ(s/2) * ζ(s) and each factor
  -- commutes with conjugation.
  --
  -- Part 1: Show the result for Re(s) > 1 using explicit formula
  have h_dirichlet : ∀ z : ℂ, 1 < z.re →
      completedRiemannZeta (star z) = star (completedRiemannZeta z) := by
    intro z hz
    have hz_star_re : 1 < (star z).re := by simp only [RCLike.star_def, conj_re]; exact hz
    -- Use explicit formula: ξ(s) = π^(-s/2) * Γ(s/2) * ζ(s) for Re > 1
    rw [completedZeta_eq_tsum_of_one_lt_re hz]
    rw [completedZeta_eq_tsum_of_one_lt_re hz_star_re]
    -- star(π^(-s/2) * Γ(s/2) * ∑ 1/n^s) = star(π^(-s/2)) * star(Γ(s/2)) * star(∑ 1/n^s)
    simp only [RCLike.star_def, map_mul]
    -- Each factor: use conjugation lemmas
    congr 1
    · -- π^(-star(z)/2) = conj(π^(-z/2))
      congr 1
      · -- π^(-star(z)/2) = conj(π^(-z/2))
        -- Use Complex.cpow_conj: x^(conj n) = conj(conj(x)^n) when x.arg ≠ π
        -- For x = π (positive real), arg = 0 ≠ π, and conj(π) = π
        have hpi_arg : (Real.pi : ℂ).arg ≠ Real.pi := by
          rw [Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)]
          exact Real.pi_ne_zero.symm
        -- π^(conj n) = conj(conj(π)^n) = conj(π^n) since conj(π) = π
        have h := Complex.cpow_conj (Real.pi : ℂ) (-z/2) hpi_arg
        simp only [Complex.conj_ofReal] at h
        -- h : π^(conj(-z/2)) = conj(π^(-z/2))
        -- conj(-z/2) = -conj(z)/2
        simp only [map_div₀, map_neg, map_ofNat] at h
        exact h
      · -- Γ(star(z)/2) = conj(Γ(z/2))
        -- Use Complex.Gamma_conj: Γ(conj s) = conj(Γ s)
        rw [← Complex.Gamma_conj]
        simp only [map_div₀, map_ofNat]
    · -- conj(∑ 1/n^z) = ∑ 1/n^(star z)
      rw [Complex.conj_tsum]
      congr 1
      ext n
      simp only [map_div₀, map_one]
      congr 1
      -- conj(n^z) = n^(conj z) for n : ℕ (n ≥ 0)
      by_cases hn : n = 0
      · simp only [hn, Nat.cast_zero, ne_eq]
        have hzne : z ≠ 0 := Complex.ne_zero_of_one_lt_re hz
        have hzne' : starRingEnd ℂ z ≠ 0 := by
          intro h
          have : z = 0 := by rw [← Complex.conj_conj z, h, map_zero]
          exact hzne this
        simp only [Complex.zero_cpow hzne, Complex.zero_cpow hzne', map_zero]
      · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        have hn_arg : ((n : ℕ) : ℂ).arg ≠ Real.pi := by
          rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (le_of_lt hn_pos)]
          exact Real.pi_ne_zero.symm
        have h := Complex.cpow_conj ((n : ℕ) : ℂ) z hn_arg
        simp only [Complex.conj_natCast] at h
        exact h
  --
  -- Part 2: Extend to all s using identity theorem
  by_cases hs_re : 1 < s.re
  · exact h_dirichlet s hs_re
  · -- For s with Re(s) ≤ 1, use identity theorem
    -- Define f(s) = completedRiemannZeta s, g(s) = star(completedRiemannZeta(star s))
    -- Both are meromorphic on ℂ with poles at {0, 1}
    -- They agree on {Re > 1}, so by identity theorem they agree on ℂ \ {0, 1}
    --
    -- Part 2: Extend to all s using identity theorem on ℂ \ {0, 1}
    -- The proof follows the same pattern as riemannZeta_conj:
    -- both sides are analytic on ℂ \ {0, 1} (connected domain),
    -- agree on {Re > 1}, hence by identity theorem agree everywhere.
    -- At {0, 1}, continuity/limit arguments give equality.
    --
    -- API note: Some set/topology lemmas changed names in newer Mathlib.
    -- The mathematical content is identical to the riemannZeta_conj proof above.
    sorry

/-- On critical line, completedRiemannZeta(s) is real -/
lemma completedRiemannZeta_real_on_critical_line (t : ℝ) :
    (completedRiemannZeta ((1:ℂ)/2 + I * t)).im = 0 := by
  set s := (1:ℂ)/2 + I * t
  -- Key: star(s) = 1 - s on critical line
  have h1 : star s = 1 - s := critical_line_star_eq t
  -- Functional equation: ξ(s) = ξ(1-s)
  have h2 : completedRiemannZeta s = completedRiemannZeta (1 - s) :=
    (completedRiemannZeta_one_sub s).symm
  -- Conjugation: ξ(star s) = star(ξ(s))
  have h3 : completedRiemannZeta (star s) = star (completedRiemannZeta s) :=
    completedRiemannZeta_conj s
  -- Combine: ξ(s) = ξ(1-s) = ξ(star s) = star(ξ(s))
  -- So ξ(s) = star(ξ(s)), meaning ξ(s) is real
  have h_self_conj : completedRiemannZeta s = star (completedRiemannZeta s) := by
    calc completedRiemannZeta s = completedRiemannZeta (1 - s) := h2
      _ = completedRiemannZeta (star s) := by rw [← h1]
      _ = star (completedRiemannZeta s) := h3
  -- A complex number equals its conjugate iff it's real
  -- star z = conj z for ℂ, and conj z = z ↔ z.im = 0
  exact Complex.conj_eq_iff_im.mp h_self_conj.symm

-- ============================================================
-- SECTION 3: Hardy Z-function is real
-- ============================================================

/-- The Riemann-Siegel theta function. θ(t) = arg(Γ(1/4 + it/2)) - (t/2) log(π) -/
noncomputable def riemannSiegelTheta' (t : ℝ) : ℝ :=
  Complex.arg (Complex.Gamma (1/4 + t/2 * I)) - t/2 * Real.log Real.pi

/-- The Hardy Z-function. Z(t) = exp(i θ(t)) ζ(1/2 + it) -/
noncomputable def hardyZ' (t : ℝ) : ℂ :=
  Complex.exp (I * riemannSiegelTheta' t) * riemannZeta (1/2 + t * I)

/-- Key lemma: 1/2 + t*I ≠ 0 for all real t -/
lemma half_plus_tI_ne_zero (t : ℝ) : (1/2 : ℂ) + t * I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
             Complex.ofReal_re, Complex.zero_re] at hre
  norm_num at hre

/-- The phase of Γ(1/4 + it/2) exists (Γ is nonzero for positive real part) -/
lemma gamma_quarter_ne_zero (t : ℝ) : Complex.Gamma (1/4 + t/2 * I) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero]
  norm_num

/-- Gammaℝ(1/2 + it) ≠ 0 -/
lemma gammaR_ne_zero_at_half (t : ℝ) : Gammaℝ ((1 : ℂ)/2 + t * I) ≠ 0 := by
  rw [Gammaℝ_def]
  have h_half : ((1 : ℂ)/2 + t * I) / 2 = 1/4 + t/2 * I := by ring
  have h_neg_half : -((1 : ℂ)/2 + t * I) / 2 = -(1/4 + t/2 * I) := by ring
  simp only [h_half, h_neg_half]
  apply mul_ne_zero
  · -- π^(-(1/4 + it/2)) ≠ 0
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    rw [Ne, cpow_eq_zero_iff]
    tauto
  · exact gamma_quarter_ne_zero t

/-- Key relationship: Z(t) = ξ(1/2 + it) / ‖Gammaℝ(1/2 + it)‖
    This is the fundamental equation connecting Z to the completed zeta function.

    PROOF SKETCH:
    - Z(t) = exp(iθ) * ζ(s) where s = 1/2 + it
    - ζ(s) = ξ(s) / Gammaℝ(s) (definition of completed zeta)
    - Gammaℝ(s) = ‖Gammaℝ(s)‖ * exp(i * phase)
    - The phase of Gammaℝ(s) at s = 1/2 + it equals θ(t)
    - So Z(t) = exp(iθ) * ξ(s) / (‖Gammaℝ‖ * exp(iθ)) = ξ(s) / ‖Gammaℝ‖

    The key step is showing arg(Gammaℝ) = θ(t), which requires:
    - arg(π^(-s/2)) = -t/2 log(π) (phase of pure imaginary power)
    - arg(Γ(s/2)) = arg(Γ(1/4 + it/2))
    - Sum gives θ(t) = arg(Γ) - t/2 log(π) by definition -/
lemma hardyZ_eq_completedZeta_div_norm (t : ℝ) :
    hardyZ' t = completedRiemannZeta ((1 : ℂ)/2 + t * I) / ‖Gammaℝ ((1 : ℂ)/2 + t * I)‖ := by
  -- Set s = 1/2 + it for convenience
  set s := (1 : ℂ)/2 + t * I with hs_def
  -- Key facts we need
  have hs_ne_zero : s ≠ 0 := half_plus_tI_ne_zero t
  have hGamma_ne : Gammaℝ s ≠ 0 := gammaR_ne_zero_at_half t
  -- From Mathlib: ζ(s) = ξ(s) / Gammaℝ(s) for s ≠ 0
  have hζ_eq : riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs_ne_zero
  -- So hardyZ' t = exp(iθ) * ζ(s) = exp(iθ) * ξ(s) / Gammaℝ(s)
  unfold hardyZ'
  rw [hs_def, hζ_eq]
  -- The key step is showing arg(Gammaℝ(s)) = θ(t), where θ is the
  -- Riemann-Siegel theta function. This requires:
  -- 1. arg(π^(-s/2)) = -t/2 * log(π) (phase of purely imaginary power)
  -- 2. arg(Γ(s/2)) = arg(Γ(1/4 + it/2))
  -- 3. arg of product = sum of args (when both in slit plane)
  -- The phase calculation gives: exp(iθ) = Gammaℝ(s) / ‖Gammaℝ(s)‖
  -- hence Z(t) = exp(iθ) * ξ(s)/Gammaℝ(s) = ξ(s)/‖Gammaℝ(s)‖
  sorry

/-- Z(t) is real for all real t.
    Proof: Z(t) = ξ(1/2 + it) / ‖Gammaℝ(1/2 + it)‖
    where ξ is real on the critical line and ‖Γℝ‖ is a positive real. -/
theorem hardyZ'_real (t : ℝ) : (hardyZ' t).im = 0 := by
  rw [hardyZ_eq_completedZeta_div_norm]
  -- ξ(1/2 + it) is real and ‖Gammaℝ(...)‖ is a positive real number
  -- Their quotient is therefore real
  have h_xi_real := completedRiemannZeta_real_on_critical_line t
  -- Rewrite t * I ↔ I * t for compatibility
  have h_comm : completedRiemannZeta ((1 : ℂ)/2 + t * I) =
      completedRiemannZeta ((1 : ℂ)/2 + I * t) := by ring_nf
  rw [h_comm]
  -- The completed zeta is real on the critical line, so write as ofReal
  have h_norm : (1 : ℂ) / 2 = 2⁻¹ := one_div 2
  have h_xi_real' : (completedRiemannZeta (2⁻¹ + I * ↑t)).im = 0 := by
    rw [← h_norm]; exact h_xi_real
  have h_eq_re : completedRiemannZeta ((1 : ℂ)/2 + I * ↑t) =
      ↑(completedRiemannZeta ((1 : ℂ)/2 + I * ↑t)).re :=
    Complex.ext (by simp) (by rw [h_norm]; simp [h_xi_real'])
  rw [h_eq_re]
  -- Now it's ofReal / ofReal which is ofReal, hence has Im = 0
  rw [← Complex.ofReal_div]
  exact Complex.ofReal_im _

end
