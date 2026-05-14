/-
# Foundation.R8.Judgment.Information — R 8 specializations of the
information judgment.

Per `r8.md` v0.2 §9, the parametric three-layer information judgment
(overlap / direction / signature) from
`Foundation/R/Judgment/Information.lean` specialised to `R 8 = R (2 * 4)`.

This is a thin wrapper: it just re-exports the relevant `R N`-level
functions with `R 8`-typed signatures.

## Doctrinal anchor

* `r8.md` v0.2 §9.1 (three layers), §9.2 (judgment functions),
  §9.3 (information average), §9.4 (information conservation).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear
import SSBX.Foundation.R.Judgment.Information

namespace SSBX.Foundation.R8.Judgment

open SSBX.Foundation.R
open SSBX.Foundation.R.Judgment

namespace Information

/-! ## § 1 Layer 0 — overlap on R 8 -/

/-- Information overlap on `R 8` (Layer 0, dot product). -/
def overlap8 (u v : R 8) : Bool := Information.overlap u v

theorem overlap8_symm (u v : R 8) : overlap8 u v = overlap8 v u :=
  Information.overlap_symm u v

theorem overlap8_zero (v : R 8) : overlap8 (0 : R 8) v = false :=
  Information.overlap_zero v

/-! ## § 2 Layer 1 — direction on R 8 -/

/-- Information direction on `R 8` (Layer 1, symplectic σ). -/
def direction8 (u v : R 8) : Bool := Information.direction (k := 4) u v

theorem direction8_alternating (v : R 8) : direction8 v v = false :=
  Information.direction_alternating (k := 4) v

theorem direction8_symm (u v : R 8) : direction8 u v = direction8 v u :=
  Information.direction_symm (k := 4) u v

/-! ## § 3 Layer 2 — signature on R 8 -/

/-- Information signature on `R 8` (Layer 2, quadratic refinement). -/
def signature8 (c : Fin 4 → Bool) (v : R 8) : Bool :=
  Information.signature (k := 4) c v

theorem signature8_zero (c : Fin 4 → Bool) : signature8 c (0 : R 8) = false :=
  Information.signature_zero (k := 4) c

/-- The Arf invariant of the quadratic refinement on R 8. -/
def signature8_arf (c : Fin 4 → Bool) : Bool :=
  Information.signature_arf (k := 4) c

/-! ## § 4 R 8 has 16 quadratic refinements split into 2 Arf classes -/

theorem signature8_variant_count :
    (Finset.univ : Finset (Fin 4 → Bool)).card = 16 := by decide

theorem signature8_arf_zero_count :
    (Finset.univ.filter (fun c : Fin 4 → Bool => signature8_arf c = false)).card = 8 := by
  decide

theorem signature8_arf_one_count :
    (Finset.univ.filter (fun c : Fin 4 → Bool => signature8_arf c = true)).card = 8 := by
  decide

end Information

end SSBX.Foundation.R8.Judgment
