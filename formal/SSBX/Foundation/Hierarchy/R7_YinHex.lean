/-
# R₇ YinHex — R-index alias placeholder

Strict-uniform R₀..R₈ enumeration entry for R₇.

R₇ = Hexagram × YinBit; |R₇| = 64 × 2 = 128 = (Z/2)⁷.

Per the v0.6 R-Family doctrine, R₇'s canonical carrier is the
language-independent `R 7 = Fin 7 → Bool` (see `Foundation/R/Basic.lean`).
The Yi-flavored imprint/project/flipⁿ operators live in
`Foundation/Bagua/R7.lean` (legacy) and will migrate to
`Foundation/Atlas/` as application-layer overlays.

This file is a placeholder retained only for R-index navigability
(the RHierarchy umbrella imports it).  No content is re-exported here.
-/
import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Hierarchy.R7

open SSBX.Foundation.R

/-- R₇ carrier alias: `R 7 = Fin 7 → Bool`. -/
abbrev R7 : Type := R 7

end SSBX.Foundation.Hierarchy.R7
