# Aristotle Prompt 4: ZetaMeanSquareHalfBound Global Constructor

You are Aristotle. Return exactly one Lean file and nothing else.

Hard constraints:
- No `axiom`, `postulate`, `sorry`, `admit`.
- Keep names/signatures unchanged.

```lean
import Mathlib
open Filter Asymptotics

set_option relaxedAutoImplicit false
set_option autoImplicit false
noncomputable section

namespace Aristotle

constant mean_square_zeta : ℝ → ℝ → ℝ

class ZetaMeanSquareHalfBound where
  bound :
    (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
      =O[Filter.atTop] (fun T : ℝ => T)

class ZetaMeanSquareHalfBoundRootPayload : Prop where
  witness :
    (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
      =O[Filter.atTop] (fun T : ℝ => T)

theorem zetaMeanSquareHalfBound_of_explicit
    (hhalf :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
        =O[Filter.atTop] (fun T : ℝ => T)) :
    ZetaMeanSquareHalfBound :=
  ⟨hhalf⟩

theorem zetaMeanSquareHalfBound_of_rootPayload
    [ZetaMeanSquareHalfBoundRootPayload] :
    ZetaMeanSquareHalfBound :=
  zetaMeanSquareHalfBound_of_explicit ZetaMeanSquareHalfBoundRootPayload.witness

instance (priority := 100)
    [ZetaMeanSquareHalfBoundRootPayload] :
    ZetaMeanSquareHalfBound :=
  zetaMeanSquareHalfBound_of_rootPayload

#check zetaMeanSquareHalfBound_of_explicit
#synth ZetaMeanSquareHalfBound

end Aristotle
```
