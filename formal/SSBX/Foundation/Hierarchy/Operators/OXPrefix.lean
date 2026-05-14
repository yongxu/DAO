/-
# Operators · OXPrefix — variable-length o/x prefix placeholder

The `OX["..."]` surface and its variable-length prefix readings (R₁
yao, R₂ kernel, R₃ trigram, R₄ Mian) used to live here but referenced
the legacy Yi.Yi / Bagua types directly.

Per the v0.6 Atlas-separation doctrine, the OX prefix machinery
belongs with the bit-string macro in
`Foundation/Notation/OXNotation.lean`.  This file remains as a
placeholder for the R-index umbrella.
-/
import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Hierarchy.Operators.OXPrefix

/-- A front `o/x` prefix of length `n`, represented as Boolean
    coordinates.  `false` is `o`; `true` is `x`. -/
abbrev OXPrefix (n : Nat) : Type := Fin n → Bool

end SSBX.Foundation.Hierarchy.Operators.OXPrefix
