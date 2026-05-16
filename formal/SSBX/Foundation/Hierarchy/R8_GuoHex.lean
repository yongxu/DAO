/-
# R₈ GuoHex — R-index alias placeholder

Strict-uniform R₀..R₈ enumeration entry for R₈.

R₈ = Hexagram × Shi; |R₈| = 64 × 4 = 256 = (Z/2)⁸.
Shi = R 2 Klein-four (dao/ji/jin/wei) ≅ YinBit × GuoBit.

Per the v0.6 R-Family doctrine, R₈'s canonical carrier is the
language-independent `R 8 = Fin 8 → Bool` (see `Foundation/R/Basic.lean`).
The Yi-flavored imprint/project/flipⁿ/Cayley operators live in
`Foundation/Bagua/R8.lean` (legacy) and will migrate to
`Foundation/Atlas/` as application-layer overlays.

This file is a placeholder retained only for R-index navigability
(the RHierarchy umbrella imports it).  No content is re-exported here.
-/
import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Hierarchy.R8

open SSBX.Foundation.R

/-- R₈ carrier alias: `R 8 = Fin 8 → Bool`. -/
abbrev R8 : Type := R 8

end SSBX.Foundation.Hierarchy.R8
