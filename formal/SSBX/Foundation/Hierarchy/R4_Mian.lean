/-
# R₄ Mian — R-index alias for the 16-element 面 layer

Strict-uniform R₀..R₈ enumeration entry for R₄ = 面 (Mian).

R₄ = Mian (16 cells); |Mian| = 16 = (Z/2)⁴.

Per the v0.6 R-Family doctrine, the canonical R₄ carrier is the
language-independent `R 4 = Fin 4 → Bool` (see `Foundation/R/Basic.lean`).
The legacy Ben × Zheng decomposition lives in `Foundation/Bagua/BenZheng.lean`
and is not re-published here (this file is a pure R-index navigation alias).
-/
import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Hierarchy.R4

open SSBX.Foundation.R

/-- R₄ (面) carrier alias: `R 4 = Fin 4 → Bool`. -/
abbrev Mian : Type := R 4

end SSBX.Foundation.Hierarchy.R4
