/-
# Foundation.Lang.Partial — umbrella import for the PartialCell Lang substrate

A NEW Lang-style surface, independent of `Foundation/Lang/L1..L7`, that
compiles "Wenyan sentences" directly into `Wen.Core` (PartialCell 8)
programs.  This is the §3.7 operation-monism partner to the legacy
total-cell Lang layers: instead of (Z/2)ⁿ XOR rewriting, computation is
the PartialCell algebra of `merge` / `restrict` / `toFull?` lifted into
the ISA.

The legacy `Foundation/Lang/L1..L7` files remain untouched and continue
to provide the R₁..R₇ total-cell language tower.  This umbrella exposes
the parallel partial-cell track.

## Modules

* `Partial.Core`  — type aliases, parser/printer, compile, runners
* `Partial.Demo`  — small showcase: 3-token sentence → 3-instr program → run
-/

import SSBX.Foundation.Lang.Partial.Core
import SSBX.Foundation.Lang.Partial.Demo
