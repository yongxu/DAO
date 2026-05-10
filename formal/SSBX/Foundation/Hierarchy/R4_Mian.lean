/-
# R₄ Mian — re-export from `SSBX.Foundation.Bagua.BenZheng` (R-index alias)

Strict-uniform R₀..R₈ enumeration entry for R₄ = 面 (Ben × Zheng).

R₄ = Mian = Ben × Zheng; |Mian| = 4 × 4 = 16 = (Z/2)⁴.

This file is a thin re-export shim: it imports `BenZheng.lean` and
re-publishes `Mian` (and the constituent `Ben`/`Zheng`) under
`SSBX.Foundation.Hierarchy.R4` for R-index navigability. No new logic.
-/
import SSBX.Foundation.Bagua.BenZheng

namespace SSBX.Foundation.Hierarchy.R4

/-- R₄ (面) carrier alias: Mian = Ben × Zheng (16 cells). -/
abbrev Mian : Type := SSBX.Foundation.Bagua.BenZheng.Mian

/-- Constituent: 本 (4 elements). -/
abbrev Ben : Type := SSBX.Foundation.Bagua.BenZheng.Ben

/-- Constituent: 征 (4 elements). -/
abbrev Zheng : Type := SSBX.Foundation.Bagua.BenZheng.Zheng

end SSBX.Foundation.Hierarchy.R4
