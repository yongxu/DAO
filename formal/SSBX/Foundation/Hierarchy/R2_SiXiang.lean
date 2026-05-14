/-
# R₂ SiXiang — R-index alias for the 4-element 四象 layer

Strict-uniform R₀..R₈ enumeration entry for R₂ = 四象.

R₂ = SiXiang (Yao × Yao); |SiXiang| = 4 = (Z/2)².

Per the v0.6 R-Family doctrine, the canonical R₂ carrier is the
language-independent `R 2 = Fin 2 → Bool` (see `Foundation/R/Basic.lean`)
with Shi V₄ naming in `Foundation/Atlas/Yi/ShiV4.lean`.  This file is
a thin R-index navigation shim and does not import the legacy
Yi/Bagua stack.
-/
import SSBX.Foundation.Atlas.Yi.Names

namespace SSBX.Foundation.Hierarchy.R2

/-- R₂ (四象) carrier alias: `R 2 = Fin 2 → Bool` (per `Foundation.R`). -/
abbrev SiXiang : Type := SSBX.Foundation.Atlas.Yi.Shi

end SSBX.Foundation.Hierarchy.R2
