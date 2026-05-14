/-
# R₁ Yao — re-export alias (R-index)

Strict-uniform R₀..R₈ enumeration entry for R₁ = 爻.

R₁ = Yao (yin/yang); |Yao| = 2 = (Z/2)¹.

Per the v0.6 R-Family doctrine and Atlas separation, the canonical
Yao type is the Yi-naming overlay `SSBX.Foundation.Atlas.Yi.Yao`
(= `Bool` = `R 1`).  This file is a thin re-export shim for R-index
navigability.
-/
import SSBX.Foundation.Atlas.Yi.Names

namespace SSBX.Foundation.Hierarchy.R1

/-- R₁ (爻) carrier alias: `Yao = Bool` (per `Foundation.Atlas.Yi.Names`). -/
abbrev Yao : Type := SSBX.Foundation.Atlas.Yi.Yao

end SSBX.Foundation.Hierarchy.R1
