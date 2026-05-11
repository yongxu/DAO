/-
# R₇ YinHex — re-export from `SSBX.Foundation.Bagua.R7` (R-index alias)

Strict-uniform R₀..R₈ enumeration entry for R₇ = 阴卦 (R7).

R₇ = R7 = Hexagram × YinBit; |R7| = 64 × 2 = 128 = (Z/2)⁷.

This file is a thin re-export shim: it imports `R7.lean` and
re-publishes the carriers + atomic operators under
`SSBX.Foundation.Hierarchy.R7` for R-index navigability. No new logic.
-/
import SSBX.Foundation.Bagua.R7

namespace SSBX.Foundation.Hierarchy.R7

/-- R₇ inner bit: YinBit = Bool. -/
abbrev YinBit : Type := SSBX.Foundation.Bagua.R7.YinBit

/-- R₇ (阴卦) carrier alias: R7 = Hexagram × YinBit (128 cells). -/
abbrev R7 : Type := SSBX.Foundation.Bagua.R7.R7

/-! ## Atomic operators on R₇

  Re-exposed from `R7` namespace for R-index discoverability.
  These are the strict (Z/2)⁷ XOR-mask atoms (imprint + flip1..6) plus
  the trigram-level outer operators (hexCuo / hexZong / hexHu). -/

/-- 印 (imprint): toggle the YinBit (Z/2 involution on the 7th coord). -/
def imprint (c : R7) : R7 := SSBX.Foundation.Bagua.R7.imprint c

/-- flip1: toggle yao 1 (inner-下) of the hexagram component. -/
def flip1 (c : R7) : R7 := SSBX.Foundation.Bagua.R7.flip1 c

/-- flip2: toggle yao 2 (inner-中) of the hexagram component. -/
def flip2 (c : R7) : R7 := SSBX.Foundation.Bagua.R7.flip2 c

/-- flip3: toggle yao 3 (inner-上) of the hexagram component. -/
def flip3 (c : R7) : R7 := SSBX.Foundation.Bagua.R7.flip3 c

/-- flip4: toggle yao 4 (outer-下) of the hexagram component. -/
def flip4 (c : R7) : R7 := SSBX.Foundation.Bagua.R7.flip4 c

/-- flip5: toggle yao 5 (outer-中) of the hexagram component. -/
def flip5 (c : R7) : R7 := SSBX.Foundation.Bagua.R7.flip5 c

/-- flip6: toggle yao 6 (outer-上) of the hexagram component. -/
def flip6 (c : R7) : R7 := SSBX.Foundation.Bagua.R7.flip6 c

/-- 错 (hexCuo): hexagram-wise complement (yao-by-yao negation). -/
def hexCuo (c : R7) : R7 := SSBX.Foundation.Bagua.R7.hexCuo c

/-- 综 (hexZong): hexagram-wise reversal (top-bottom flip). -/
def hexZong (c : R7) : R7 := SSBX.Foundation.Bagua.R7.hexZong c

/-- 互 (hexHu): hexagram-wise interlace (inner trigram from yao 2/3/4, outer from 3/4/5). -/
def hexHu (c : R7) : R7 := SSBX.Foundation.Bagua.R7.hexHu c

end SSBX.Foundation.Hierarchy.R7
