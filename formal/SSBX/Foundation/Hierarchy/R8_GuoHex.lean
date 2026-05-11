/-
# R₈ GuoHex — re-export from `SSBX.Foundation.Bagua.Cell256` (R-index alias)

Strict-uniform R₀..R₈ enumeration entry for R₈ = 果卦 (Cell256).

R₈ = Cell256 = Hexagram × Shi; |Cell256| = 64 × 4 = 256 = (Z/2)⁸.
Shi = V₄ Klein-four (dao/ji/jin/wei) ≅ YinBit × GuoBit.

This file is a thin re-export shim: it imports `Cell256.lean` and
re-publishes the carriers + atomic operators + Cayley action under
`SSBX.Foundation.Hierarchy.R8` for R-index navigability. No new logic.
-/
import SSBX.Foundation.Bagua.Cell256

open SSBX.Foundation.Bagua.Cell256

namespace SSBX.Foundation.Hierarchy.R8

/-- R₈ outer bit (8th coordinate): GuoBit = Bool. -/
abbrev GuoBit : Type := SSBX.Foundation.Bagua.Cell256.GuoBit

/-- R₈ Klein-four block: Shi (dao / ji / jin / wei) ≅ YinBit × GuoBit. -/
abbrev Shi : Type := SSBX.Foundation.Bagua.Cell256.Shi

/-- R₈ (果卦) carrier alias: Cell256 = Hexagram × Shi (256 cells). -/
abbrev Cell256 : Type := SSBX.Foundation.Bagua.Cell256.Cell256

/-! ## XOR-mask atomic operators on R₈

  Re-exposed from `Cell256` namespace for R-index discoverability.
  These are the strict (Z/2)⁸ XOR-mask atoms (yin / tou) and the
  Hexagram-side propagation atoms (flip1..6 + hexCuo/hexZong/hexHu)
  plus the Shi-side atoms (shiCuo / shiZong / shiCuoZong). -/

/-- 印 (yin): XOR with `yin_mask = (heaven, ji)`; flips the 7th coord (YinBit). -/
def yin (c : Cell256) : Cell256 := Cell256.yin c

/-- 投 (tou): XOR with `tou_mask = (heaven, wei)`; flips the 8th coord (GuoBit). -/
def tou (c : Cell256) : Cell256 := Cell256.tou c

/-- flip1..6 + hexCuo/hexZong/hexHu propagated to Cell256. -/
def flip1 (c : Cell256) : Cell256 := Cell256.flip1 c
def flip2 (c : Cell256) : Cell256 := Cell256.flip2 c
def flip3 (c : Cell256) : Cell256 := Cell256.flip3 c
def flip4 (c : Cell256) : Cell256 := Cell256.flip4 c
def flip5 (c : Cell256) : Cell256 := Cell256.flip5 c
def flip6 (c : Cell256) : Cell256 := Cell256.flip6 c

def hexCuo (c : Cell256) : Cell256 := Cell256.hexCuo c
def hexZong (c : Cell256) : Cell256 := Cell256.hexZong c
def hexHu (c : Cell256) : Cell256 := Cell256.hexHu c

/-- Shi-side 错: complement on the V₄ block. -/
def shiCuo (c : Cell256) : Cell256 := Cell256.shiCuo c

/-- Shi-side 综: reverse on the V₄ block. -/
def shiZong (c : Cell256) : Cell256 := Cell256.shiZong c

/-- Shi-side 错综: complement ∘ reverse on the V₄ block. -/
def shiCuoZong (c : Cell256) : Cell256 := Cell256.shiCuoZong c

/-- Group XOR on Cell256 = (Z/2)⁸. -/
def xor (a b : Cell256) : Cell256 := Cell256.xor a b

/-- Cayley left-action: `cayley c s = c ⊕ s` (regular representation of (Z/2)⁸). -/
def cayley (c : Cell256) : Cell256 → Cell256 := Cell256.cayley c

end SSBX.Foundation.Hierarchy.R8
