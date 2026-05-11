/-
# R₇ YinHex — re-export from `SSBX.Foundation.Bagua.Cell128` (R-index alias)

Strict-uniform R₀..R₈ enumeration entry for R₇ = 阴卦 (Cell128).

R₇ = Cell128 = Hexagram × YinBit; |Cell128| = 64 × 2 = 128 = (Z/2)⁷.

This file is a thin re-export shim: it imports `Cell128.lean` and
re-publishes the carriers + atomic operators under
`SSBX.Foundation.Hierarchy.R7` for R-index navigability. No new logic.
-/
import SSBX.Foundation.Bagua.Cell128

namespace SSBX.Foundation.Hierarchy.R7

/-- R₇ inner bit: YinBit = Bool. -/
abbrev YinBit : Type := SSBX.Foundation.Bagua.Cell128.YinBit

/-- R₇ (阴卦) carrier alias: Cell128 = Hexagram × YinBit (128 cells). -/
abbrev Cell128 : Type := SSBX.Foundation.Bagua.Cell128.Cell128

/-! ## Atomic operators on R₇

  Re-exposed from `Cell128` namespace for R-index discoverability.
  These are the strict (Z/2)⁷ XOR-mask atoms (yin + flip1..6) plus
  the trigram-level outer operators (hexCuo / hexZong / hexHu). -/

/-- 印 (yin): toggle the YinBit (Z/2 involution on the 7th coord). -/
def yin (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.yin c

/-- flip1: toggle yao 1 (inner-下) of the hexagram component. -/
def flip1 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip1 c

/-- flip2: toggle yao 2 (inner-中) of the hexagram component. -/
def flip2 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip2 c

/-- flip3: toggle yao 3 (inner-上) of the hexagram component. -/
def flip3 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip3 c

/-- flip4: toggle yao 4 (outer-下) of the hexagram component. -/
def flip4 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip4 c

/-- flip5: toggle yao 5 (outer-中) of the hexagram component. -/
def flip5 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip5 c

/-- flip6: toggle yao 6 (outer-上) of the hexagram component. -/
def flip6 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip6 c

/-- 错 (hexCuo): hexagram-wise complement (yao-by-yao negation). -/
def hexCuo (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.hexCuo c

/-- 综 (hexZong): hexagram-wise reversal (top-bottom flip). -/
def hexZong (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.hexZong c

/-- 互 (hexHu): hexagram-wise interlace (inner trigram from yao 2/3/4, outer from 3/4/5). -/
def hexHu (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.hexHu c

end SSBX.Foundation.Hierarchy.R7
