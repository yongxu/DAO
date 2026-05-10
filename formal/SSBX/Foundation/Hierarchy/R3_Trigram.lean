/-
# R₃ Trigram — re-export from `SSBX.Foundation.Yi.Yi` (R-index alias)

Strict-uniform R₀..R₈ enumeration entry for R₃ = 八卦 (trigram).

R₃ = Trigram (3 yao); |Trigram| = 8 = (Z/2)³.

This file is a thin re-export shim: it imports `Yi/Yi.lean` and
re-publishes the `Trigram` structure under `SSBX.Foundation.Hierarchy.R3`
for R-index navigability. No new logic.
-/
import SSBX.Foundation.Yi.Yi

namespace SSBX.Foundation.Hierarchy.R3

/-- R₃ (三爻八卦) carrier alias: Trigram structure (3-yao). -/
abbrev Trigram : Type := SSBX.Foundation.Yi.Yi.Trigram

end SSBX.Foundation.Hierarchy.R3
