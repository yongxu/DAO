/-
# R₆ Hexagram — re-export from `SSBX.Foundation.Yi.Yi` (R-index alias)

Strict-uniform R₀..R₈ enumeration entry for R₆ = 六爻 (hexagram).

R₆ = Hexagram (6 yao); |Hexagram| = 64 = (Z/2)⁶.

This file is a thin re-export shim: it imports `Yi/Yi.lean` and
re-publishes the `Hexagram` structure under `SSBX.Foundation.Hierarchy.R6`
for R-index navigability. No new logic.
-/
import SSBX.Foundation.Yi.Yi

namespace SSBX.Foundation.Hierarchy.R6

/-- R₆ (六爻卦) carrier alias: Hexagram structure (6-yao). -/
abbrev Hexagram : Type := SSBX.Foundation.Yi.Yi.Hexagram

end SSBX.Foundation.Hierarchy.R6
