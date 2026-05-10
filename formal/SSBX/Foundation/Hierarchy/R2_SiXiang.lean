/-
# R₂ SiXiang — re-export from `SSBX.Foundation.Bagua.BaguaAlgebra` (R-index alias)

Strict-uniform R₀..R₈ enumeration entry for R₂ = 四象.

R₂ = SiXiang (Yao × Yao); |SiXiang| = 4 = (Z/2)².

This file is a thin re-export shim: it imports `BaguaAlgebra.lean`
and re-publishes `SiXiang` under `SSBX.Foundation.Hierarchy.R2` for
R-index navigability. No new logic.
-/
import SSBX.Foundation.Bagua.BaguaAlgebra

namespace SSBX.Foundation.Hierarchy.R2

/-- R₂ (四象) carrier alias: SiXiang structure (太阳/少阴/少阳/太阴). -/
abbrev SiXiang : Type := SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang

end SSBX.Foundation.Hierarchy.R2
