import Mathlib

set_option autoImplicit false

lemma sum_inv_sq_plus_sq_bound (A : ℝ) (hA : 1 ≤ A) :
    (∑' n : ℕ, 1 / (A ^ 2 + (n : ℝ) ^ 2)) ≤ (1 + Real.pi / 2) / A := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hA_ne : A ≠ 0 := ne_of_gt hA0
  have h_bound_partial :
      ∀ N : ℕ, (∑ i ∈ Finset.range N, 1 / (A ^ 2 + (i : ℝ) ^ 2)) ≤ (1 + Real.pi / 2) / A := by
    intro N
    cases N with
    | zero =>
        have hconst : 0 ≤ (1 + Real.pi / 2) / A := by positivity
        simpa using hconst
    | succ N =>
        set f : ℕ → ℝ := fun k => 1 / (A ^ 2 + (k : ℝ) ^ 2)
        have hanti :
            AntitoneOn (fun x : ℝ => (A ^ 2 + x ^ 2)⁻¹) (Set.Icc (0 : ℝ) ((0 : ℝ) + N)) := by
          intro x hx y hy hxy
          have hx0 : 0 ≤ x := hx.1
          have hy0 : 0 ≤ y := le_trans hx0 hxy
          have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
          have hden : A ^ 2 + x ^ 2 ≤ A ^ 2 + y ^ 2 := by linarith
          have hdx : 0 < A ^ 2 + x ^ 2 := by positivity
          have hdy : 0 < A ^ 2 + y ^ 2 := by positivity
          exact (inv_le_inv₀ hdy hdx).2 hden
        have h_shift :
            (∑ i ∈ Finset.range N, f (i + 1))
              ≤ ∫ x in (0 : ℝ)..N, (A ^ 2 + x ^ 2)⁻¹ := by
          simpa [f, one_div, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
            (AntitoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := N)
              (f := fun x : ℝ => (A ^ 2 + x ^ 2)⁻¹) hanti)
        have h_split :
            (∑ i ∈ Finset.range (N + 1), f i) =
              (∑ i ∈ Finset.range N, f (i + 1)) + f 0 :=
          Finset.sum_range_succ' f N
        have h0 : f 0 ≤ 1 / A := by
          have hA_le_sq : A ≤ A ^ 2 := by nlinarith
          have hA_sq_pos : 0 < A ^ 2 := by positivity
          have h_inv : (A ^ 2)⁻¹ ≤ A⁻¹ := (inv_le_inv₀ hA_sq_pos hA0).2 hA_le_sq
          simpa [f, one_div] using h_inv
        have h_int_eq :
            (∫ x in (0 : ℝ)..N, (A ^ 2 + x ^ 2)⁻¹)
              = A⁻¹ * Real.arctan (N / A) := by
          simpa using (integral_inv_sq_add_sq (a := (0 : ℝ)) (b := N) (c := A) hA_ne)
        have h_arctan_le : Real.arctan (N / A) ≤ Real.pi / 2 :=
          (Real.arctan_lt_pi_div_two (N / A)).le
        have h_int_le :
            (∫ x in (0 : ℝ)..N, (A ^ 2 + x ^ 2)⁻¹) ≤ (Real.pi / 2) / A := by
          rw [h_int_eq]
          have hA_inv_nonneg : 0 ≤ A⁻¹ := inv_nonneg.mpr hA0.le
          have hmul : A⁻¹ * Real.arctan (N / A) ≤ A⁻¹ * (Real.pi / 2) :=
            mul_le_mul_of_nonneg_left h_arctan_le hA_inv_nonneg
          simpa [one_div, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hmul
        calc
          (∑ i ∈ Finset.range (N + 1), 1 / (A ^ 2 + (i : ℝ) ^ 2))
              = ∑ i ∈ Finset.range (N + 1), f i := by simp [f]
          _ = (∑ i ∈ Finset.range N, f (i + 1)) + f 0 := h_split
          _ ≤ (∫ x in (0 : ℝ)..N, (A ^ 2 + x ^ 2)⁻¹) + 1 / A := add_le_add h_shift h0
          _ ≤ ((Real.pi / 2) / A) + 1 / A := add_le_add h_int_le le_rfl
          _ = (1 + Real.pi / 2) / A := by ring
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) ?_
  intro N
  exact h_bound_partial N
