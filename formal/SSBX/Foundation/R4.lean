/-
# `SSBX.Foundation.R4` — umbrella import for the R 4 layer

Canonical doctrine: `docs-next/10_formal_形式/r4.md` v0.2 ("R 4 — the
minimum complete unit").  This umbrella pulls in the eight R 4-specific
files:

* `R4.Enumeration` — the 16 bit-pattern atoms `oooo / ooox / … / xxxx`.
* `R4.RankStratification` — 1 + 9 + 6 rank decomposition (§4).
* `R4.GL2Embedding` — the 6 rank-2 elements = `GL(2, F_2) ≃ S_3` (§5).
* `R4.AutA8` — `|Aut(R 4)| = 20160 = |A_8|` (§6, numeric only).
* `R4.Bilinear` — three-layer bilinear forms specialized to R 4 (§7).
* `R4.EndR2` — `R 4 = End(R 2)`: `asMatrix`, `applyR2`, `composeR2` (§8).
* `R4.StateOp` — State / Op phantom-mode dual identity (§9).
* `R4.HomMat` — `Hom(R 2n, R 2m) ≃ Mat_{m × n}(R 4)` (§10).

All files are language-independent: only bit-pattern atom names
(`o/x`), no Yi / Pauli / Boolean semantic mappings here (those live
under `Foundation/Atlas/`, P3 work).
-/

import SSBX.Foundation.R4.Enumeration
import SSBX.Foundation.R4.RankStratification
import SSBX.Foundation.R4.GL2Embedding
import SSBX.Foundation.R4.AutA8
import SSBX.Foundation.R4.Bilinear
import SSBX.Foundation.R4.EndR2
import SSBX.Foundation.R4.StateOp
import SSBX.Foundation.R4.HomMat
