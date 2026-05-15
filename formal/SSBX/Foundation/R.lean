/-
# `SSBX.Foundation.R` — umbrella import for the R-Family tower core

Canonical doctrine: `docs-next/10_formal_形式/wen-algebra.md` v0.6 +
`docs-next/10_formal_形式/v4-foundation.md` v0.5.

`R N := Fin N → Bool` is the language-independent parametric carrier. All
semantic naming (Yi 道/错/综, Pauli I/X/Y/Z, Boolean operators, GF(256))
is **Atlas**-level (built in P3); nothing in this subtree is Chinese-
or English-name-bound.

This umbrella pulls the whole subtree in one import.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Parametric
import SSBX.Foundation.R.DirectSum
import SSBX.Foundation.R.Tensor
import SSBX.Foundation.R.Hom
import SSBX.Foundation.R.Bilinear
import SSBX.Foundation.R.Aut
import SSBX.Foundation.R.Phantom
import SSBX.Foundation.R.DirectDecomp
import SSBX.Foundation.R.BeyondR8
import SSBX.Foundation.R.Squaring
import SSBX.Foundation.R.SubTower
import SSBX.Foundation.R.Judgment.Information
import SSBX.Foundation.R.Judgment.Attractor
import SSBX.Foundation.R.Judgment.Behavior
import SSBX.Foundation.R.RFamilyStructure
import SSBX.Foundation.R.PhaseZero
import SSBX.Foundation.R.OperationMonism
import SSBX.Foundation.R.ClaimZ
