/-
# Swiss cheese integral — infrastructure catalog

The Swiss cheese decomposition for the Perron contour integral is ALREADY
PROVED in `RectArgumentPrinciple.lean` (1368 lines, 0 sorry).

Key theorems:
1. `logDeriv_decompose_rect_mult`: logDeriv f = Σ (order/(s-z)) + holomorphic h
2. `argument_principle_rect_entire_mult`: logIntegralRect = zeroCountRectMult
3. `cauchy_goursat_rect`: ∫∂R h = 0 for holomorphic h
4. `rect_winding_number_eq_one`: (1/2πi) ∫∂R 1/(s-z) = 1

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.RectArgumentPrinciple

-- Verify all key theorems are accessible:
open RectArgumentPrinciple

#check @logDeriv_decompose_rect
#check @logDeriv_decompose_rect_mult
#check @argument_principle_rect_entire_mult
#check @argument_principle_rect_entire_mult_sum
#check @cauchy_goursat_rect
#check @rect_winding_number_eq_one
