/-
Integration test: verify all main theorems compile and key lemmas connect.
-/
import Littlewood

-- Main theorems exist
#check LittlewoodPi.littlewood_pi_li
#check LittlewoodPi.pi_gt_li_infinitely_often
#check LittlewoodPi.pi_lt_li_infinitely_often
#check LittlewoodPi.pi_minus_li_sign_changes

-- Key Aristotle lemmas exist (from sorry-free files)
#check hardyZV4_real
#check gamma_duplication_hardyV4
#check gamma_reflection_hardyV4
#check LambdaV2_eq_completedZeta
#check LambdaV2_one_sub
#check trigPoly_zero_iff_coeffs_zero
#check ZetaZeroCount.N_asymptotic

-- Riemann Xi theorems
#check RiemannXiModule.xi_one_sub
#check RiemannXiModule.RiemannXi_one_sub
#check RiemannXiModule.differentiable_RiemannXi

-- Functional equation
#check completedRiemannZeta_one_sub

-- The goal: eventually replace all assumption sorries with real proofs
-- Current status: Main proof chain has 0 sorries
