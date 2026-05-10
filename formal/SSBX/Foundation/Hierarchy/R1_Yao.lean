/-
# R₁ Yao — re-export from `SSBX.Foundation.Yi.Yi` (R-index alias)

Strict-uniform R₀..R₈ enumeration entry for R₁ = 爻.

R₁ = Yao (yin/yang); |Yao| = 2 = (Z/2)¹.

This file is a thin re-export shim: it imports `Yi/Yi.lean` and
re-publishes the `Yao` inductive under `SSBX.Foundation.Hierarchy.R1`
for R-index navigability. No new logic.
-/
import SSBX.Foundation.Yi.Yi

namespace SSBX.Foundation.Hierarchy.R1

/-- R₁ (爻) carrier alias: Yao = yin | yang. -/
abbrev Yao : Type := SSBX.Foundation.Yi.Yi.Yao

end SSBX.Foundation.Hierarchy.R1
