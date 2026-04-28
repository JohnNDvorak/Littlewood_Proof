/-
# Jensen's Formula and Zero Counting for Entire Functions

If f is an entire function with |f(s)| ≤ exp(C|s|^{3/2}) for |s| ≥ 2, and f(0) ≠ 0,
then the number of zeros of f in |s| ≤ R satisfies N(R) ≤ C'·R^{3/2}.

The proof applies Jensen's formula (MeromorphicOn.circleAverage_log_norm) to f on the
disk of radius 2R. The circle average of log|f| is bounded by C·(2R)^{3/2}. Each zero
in |s|≤R contributes log(2R/|ρ|) ≥ log 2 to the sum. So N(R)·log 2 ≤ C·(2R)^{3/2}.
-/
import Mathlib

open MeromorphicOn Metric Real Filter Complex Topology

noncomputable section

/-! ## Definition of zero count -/

/-- The total number of zeros (counting multiplicity) of `f` in `closedBall 0 R`. -/
def zeroCount (f : ℂ → ℂ) (R : ℝ) : ℤ :=
  ∑ᶠ u, divisor f (closedBall (0 : ℂ) R) u

/-! ## Helper lemmas -/

/-- For an entire function, divisor values are non-negative. -/
lemma divisor_nonneg_of_entire {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (U : Set ℂ) (z : ℂ) :
    (0 : ℤ) ≤ divisor f U z := by
  by_cases hU : MeromorphicOn f U ∧ z ∈ U
  · rw [divisor_apply (AnalyticOnNhd.meromorphicOn (fun w _ => hf w)) hU.2]
    have h := (hf z).meromorphicOrderAt_nonneg
    cases hord : (meromorphicOrderAt f z) with
    | top => simp [WithTop.untop₀]
    | coe v =>
      simp [WithTop.untop₀]
      rw [hord] at h
      exact_mod_cast h
  · simp [divisor_def, hU]

/-- For an entire function with f(0) ≠ 0, divisor at 0 is zero. -/
lemma divisor_zero_of_ne_zero {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (hf0 : f 0 ≠ 0) (U : Set ℂ) (h0 : (0 : ℂ) ∈ U) :
    divisor f U (0 : ℂ) = 0 := by
  rw [divisor_apply (AnalyticOnNhd.meromorphicOn (fun w _ => hf w)) h0]
  rw [(hf 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf0]
  simp

/-- For an entire function with f(0) ≠ 0, the trailing coefficient at 0 is f(0). -/
lemma trailingCoeff_of_ne_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0) :
    meromorphicTrailingCoeffAt f 0 = f 0 :=
  hf.meromorphicTrailingCoeffAt_of_ne_zero hf0

/-- The divisor values on `closedBall 0 R` and `closedBall 0 R'` agree for points in the
    smaller ball, when f is entire. -/
lemma divisor_restrict_eq {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    {R R' : ℝ} (hRR' : R ≤ R') (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) :
    divisor f (closedBall (0 : ℂ) R') z = divisor f (closedBall (0 : ℂ) R) z := by
  have hf_mer : ∀ (S : Set ℂ), MeromorphicOn f S :=
    fun S => AnalyticOnNhd.meromorphicOn (fun w _ => hf w)
  have hz' : z ∈ closedBall (0 : ℂ) R' := closedBall_subset_closedBall hRR' hz
  rw [divisor_apply (hf_mer _) hz', divisor_apply (hf_mer _) hz]

/-- Entire functions are meromorphic on any set. -/
lemma entire_meromorphicOn {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (U : Set ℂ) : MeromorphicOn f U :=
  AnalyticOnNhd.meromorphicOn (fun w _ => hf w)

/-- The divisor of an entire function vanishes outside its domain. -/
lemma divisor_eq_zero_outside {f : ℂ → ℂ} (U : Set ℂ) (z : ℂ) (hz : z ∉ U) :
    divisor f U z = 0 := by
  simp [divisor_def, hz]

/-
For u ∈ closedBall 0 R with R ≥ 1, log(2R * ‖u‖⁻¹) ≥ log 2 when ‖u‖ ≤ R and u ≠ 0.
-/
lemma log_ratio_ge_log_two {R : ℝ} (hR : 1 ≤ R) {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) R) (hu0 : u ≠ 0) :
    Real.log 2 ≤ Real.log (2 * R * ‖(0 : ℂ) - u‖⁻¹) := by
      gcongr;
      rw [ ← div_eq_mul_inv, le_div_iff₀ ] <;> aesop

/-
Pointwise bound: each term from the small ball contributes at least div * log 2.
-/
lemma jensen_term_lower_bound {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (hf0 : f 0 ≠ 0) {R : ℝ} (hR : 1 ≤ R) (u : ℂ) :
    (divisor f (closedBall (0 : ℂ) R) u : ℝ) * Real.log 2 ≤
      (divisor f (closedBall (0 : ℂ) (2 * R)) u : ℝ) *
        Real.log (2 * R * ‖(0 : ℂ) - u‖⁻¹) := by
          by_cases hu : u ∈ Metric.closedBall ( 0 : ℂ ) R <;> simp_all +decide [ divisor_eq_zero_outside ];
          · by_cases hu0 : u = 0;
            · simp_all +decide [ divisor_zero_of_ne_zero ];
            · gcongr;
              · exact_mod_cast divisor_nonneg_of_entire hf _ _;
              · rw [ divisor_restrict_eq ( hf := hf ) ( show R ≤ 2 * R by linarith ) u ( by simpa using hu ) ];
              · rw [ ← div_eq_mul_inv, le_div_iff₀ ] <;> linarith [ norm_pos_iff.mpr hu0 ];
          · by_cases hu' : u ∈ closedBall 0 (2 * R);
            · field_simp;
              refine' mul_nonneg _ _;
              · exact_mod_cast divisor_nonneg_of_entire hf _ _;
              · exact Real.log_nonneg ( by rw [ le_div_iff₀ ( by linarith ) ] ; linarith [ mem_closedBall_zero_iff.mp hu' ] );
            · simp_all +decide [ divisor_eq_zero_outside ]

/-
The sum of divisor terms in Jensen's formula is bounded below by
    `zeroCount f R * log 2`.
-/
lemma jensen_sum_lower_bound {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (hf0 : f 0 ≠ 0) {R : ℝ} (hR : 1 ≤ R) :
    (zeroCount f R : ℝ) * Real.log 2 ≤
      ∑ᶠ u, (divisor f (closedBall (0 : ℂ) (2 * R)) u : ℝ) *
        Real.log (2 * R * ‖(0 : ℂ) - u‖⁻¹) := by
          have h_bound : (∑ᶠ u, (divisor f (closedBall 0 R) u : ℝ) * Real.log 2) ≤ (∑ᶠ u, (divisor f (closedBall 0 (2 * R)) u : ℝ) * Real.log (2 * R * ‖(0 : ℂ) - u‖⁻¹)) := by
            have h_finite_support : Set.Finite {u : ℂ | divisor f (closedBall 0 R) u ≠ 0} ∧ Set.Finite {u : ℂ | divisor f (closedBall 0 (2 * R)) u ≠ 0} := by
              constructor <;> apply_rules [ Function.locallyFinsuppWithin.finiteSupport ];
              · exact ProperSpace.isCompact_closedBall _ _;
              · exact ProperSpace.isCompact_closedBall _ _;
            rw [ finsum_eq_sum_of_support_subset, finsum_eq_sum_of_support_subset ];
            case s => exact h_finite_support.2.toFinset ∪ h_finite_support.1.toFinset;
            any_goals exact h_finite_support.2.toFinset ∪ h_finite_support.1.toFinset;
            · refine Finset.sum_le_sum fun u hu => ?_;
              convert jensen_term_lower_bound hf hf0 hR u using 1;
            · intro u hu; contrapose! hu; aesop;
            · intro u hu; aesop;
          simp_all +decide [ zeroCount ];
          convert h_bound using 1;
          erw [ finsum_eq_sum_of_support_subset, finsum_eq_sum_of_support_subset ];
          any_goals exact Finset.filter ( fun u => ( divisor f ( closedBall 0 R ) ) u ≠ 0 ) ( ( divisor f ( closedBall 0 R ) |> Function.locallyFinsuppWithin.finiteSupport <| isCompact_closedBall _ _ ) |> Set.Finite.toFinset );
          · norm_num [ Finset.sum_mul _ _ _ ];
          · intro u hu; aesop;
          · aesop_cat

/-- The circle average of log ‖f‖ is bounded by the growth condition. -/
lemma circleAverage_log_norm_bound {f : ℂ → ℂ} {C : ℝ}
    (hbound : ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ ^ (3 / 2 : ℝ))
    (hf : ∀ z, AnalyticAt ℂ f z) {R : ℝ} (hR : 1 ≤ R) :
    circleAverage (fun s => Real.log ‖f s‖) 0 (2 * R) ≤ C * (2 * R) ^ (3 / 2 : ℝ) := by
  apply circleAverage_mono_on_of_le_circle
  · apply circleIntegrable_log_norm_meromorphicOn
    exact fun z hz => (hf z |> AnalyticAt.meromorphicAt)
  · simp +zetaDelta at *
    exact fun x hx => by
      simpa [abs_of_nonneg (zero_le_one.trans hR), hx] using
        hbound x (by rw [hx]; rw [abs_of_nonneg (zero_le_one.trans hR)]; linarith)

/-! ## Main theorem -/

/-
**Zero-counting bound for entire functions of order 3/2.**
If f is entire with |f(s)| ≤ exp(C|s|^{3/2}) for |s| ≥ 2, and f(0) ≠ 0,
then the number of zeros of f in |s| ≤ R is O(R^{3/2}).
-/
theorem entire_zero_count_bound {f : ℂ → ℂ} {C : ℝ}
    (hf : ∀ z, AnalyticAt ℂ f z)
    (hC : 0 < C)
    (hbound : ∀ s : ℂ, 2 ≤ ‖s‖ → ‖f s‖ ≤ Real.exp (C * ‖s‖ ^ (3 / 2 : ℝ)))
    (hf0 : f 0 ≠ 0) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ R : ℝ, 1 ≤ R →
        (zeroCount f R : ℝ) ≤ C' * R ^ (3 / 2 : ℝ) := by
          -- By Jensen's formula, we have:
          have jensen {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z) (hf0 : f 0 ≠ 0) {R : ℝ} (hR : 1 ≤ R) :
              circleAverage (fun s => Real.log ‖f s‖) 0 (2 * R) =
              ∑ᶠ u, (divisor f (closedBall (0 : ℂ) (2 * R)) u : ℝ) * Real.log (2 * R * ‖(0 : ℂ) - u‖⁻¹) +
              divisor f (closedBall (0 : ℂ) (2 * R)) (0 : ℂ) * Real.log (2 * R) +
              Real.log ‖(meromorphicTrailingCoeffAt f (0 : ℂ))‖ := by
                convert MeromorphicOn.circleAverage_log_norm _ _ using 1;
                · rw [ abs_of_nonneg ( by positivity ) ];
                · positivity;
                · exact entire_meromorphicOn hf (closedBall 0 |2 * R|);
          -- Apply Jensen's formula to the function $f$ on the disk of radius $2R$ centered at $0$.
          have h_jensen : ∀ R : ℝ, 1 ≤ R → circleAverage (fun s => Real.log ‖f s‖) 0 (2 * R) ≤ C * (2 * R) ^ (3 / 2 : ℝ) := by
            apply circleAverage_log_norm_bound;
            · exact fun s hs => if h : f s = 0 then by norm_num [ h ] ; positivity else by simpa [ h ] using Real.log_le_log ( norm_pos_iff.mpr h ) ( hbound s hs ) ;
            · assumption;
          -- By combining the results from Jensen's formula and the bound on the circle average, we get:
          have h_combined : ∀ R : ℝ, 1 ≤ R → (zeroCount f R : ℝ) * Real.log 2 ≤ C * (2 * R) ^ (3 / 2 : ℝ) - Real.log ‖(meromorphicTrailingCoeffAt f (0 : ℂ))‖ := by
            intro R hR
            have h_combined : (zeroCount f R : ℝ) * Real.log 2 ≤ circleAverage (fun s => Real.log ‖f s‖) 0 (2 * R) - Real.log ‖(meromorphicTrailingCoeffAt f (0 : ℂ))‖ := by
              rw [ jensen hf hf0 hR ];
              convert jensen_sum_lower_bound hf hf0 hR using 1;
              rw [ divisor_zero_of_ne_zero hf hf0 ( closedBall ( 0 : ℂ ) ( 2 * R ) ) ( by norm_num; linarith ) ] ; norm_num;
            exact h_combined.trans ( sub_le_sub_right ( h_jensen R hR ) _ );
          -- Let's choose $C' = \frac{C \cdot 2^{3/2}}{\log 2} + \frac{| \log \| \text{meromorphicTrailingCoeffAt } f 0 \| |}{\log 2} + 1$.
          use (C * 2 ^ (3 / 2 : ℝ) / Real.log 2) + (|Real.log ‖(meromorphicTrailingCoeffAt f (0 : ℂ))‖| / Real.log 2) + 1;
          refine' ⟨ _, _ ⟩;
          · positivity;
          · intro R hR; specialize h_combined R hR; rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] at h_combined; ring_nf at h_combined ⊢;
            field_simp;
            cases abs_cases ( Real.log ‖meromorphicTrailingCoeffAt f 0‖ ) <;> nlinarith [ Real.log_pos one_lt_two, show ( 1 : ℝ ) ≤ R ^ ( 3 / 2 : ℝ ) by exact Real.one_le_rpow hR ( by norm_num ) ]

end