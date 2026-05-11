/-
# R₈ GuoHex — re-export from `SSBX.Foundation.Bagua.R8` (R-index alias)

Strict-uniform R₀..R₈ enumeration entry for R₈ = 果卦 (R8).

R₈ = R8 = Hexagram × Shi; |R8| = 64 × 4 = 256 = (Z/2)⁸.
Shi = V₄ Klein-four (dao/ji/jin/wei) ≅ YinBit × GuoBit.

This file is a thin re-export shim: it imports `R8.lean` and
re-publishes the carriers + atomic operators + Cayley action under
`SSBX.Foundation.Hierarchy.R8` for R-index navigability. No new logic.
-/
import SSBX.Foundation.Bagua.R8

open SSBX.Foundation.Bagua.R8

namespace SSBX.Foundation.Hierarchy.R8

/-- R₈ outer bit (8th coordinate): GuoBit = Bool. -/
abbrev GuoBit : Type := SSBX.Foundation.Bagua.R8.GuoBit

/-- R₈ Klein-four block: Shi (dao / ji / jin / wei) ≅ YinBit × GuoBit. -/
abbrev Shi : Type := SSBX.Foundation.Bagua.R8.Shi

/-- R₈ (果卦) carrier alias: R8 = Hexagram × Shi (256 cells). -/
abbrev R8 : Type := SSBX.Foundation.Bagua.R8.R8

/-! ## XOR-mask atomic operators on R₈

  Re-exposed from `R8` namespace for R-index discoverability.
  These are the strict (Z/2)⁸ XOR-mask atoms (imprint / project) and the
  Hexagram-side propagation atoms (flip1..6 + hexCuo/hexZong/hexHu)
  plus the Shi-side atoms (shiCuo / shiZong / shiCuoZong). -/

/-- 印 (imprint): XOR with `imprint_mask = (heaven, ji)`; flips the 7th coord (YinBit). -/
def imprint (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.imprint c

/-- 投 (project): XOR with `project_mask = (heaven, wei)`; flips the 8th coord (GuoBit). -/
def project (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.project c

/-- flip1..6 + hexCuo/hexZong/hexHu propagated to R8. -/
def flip1 (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.flip1 c
def flip2 (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.flip2 c
def flip3 (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.flip3 c
def flip4 (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.flip4 c
def flip5 (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.flip5 c
def flip6 (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.flip6 c

def hexCuo (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.hexCuo c
def hexZong (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.hexZong c
def hexHu (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.hexHu c

/-- Shi-side 错: complement on the V₄ block. -/
def shiCuo (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.shiCuo c

/-- Shi-side 综: reverse on the V₄ block. -/
def shiZong (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.shiZong c

/-- Shi-side 错综: complement ∘ reverse on the V₄ block. -/
def shiCuoZong (c : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.shiCuoZong c

/-- Group XOR on R8 = (Z/2)⁸. -/
def xor (a b : R8) : R8 := SSBX.Foundation.Bagua.R8.R8.xor a b

/-- Cayley left-action: `cayley c s = c ⊕ s` (regular representation of (Z/2)⁸). -/
def cayley (c : R8) : R8 → R8 := SSBX.Foundation.Bagua.R8.R8.cayley c

end SSBX.Foundation.Hierarchy.R8
