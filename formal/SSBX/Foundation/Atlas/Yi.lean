/-
# Foundation.Atlas.Yi — umbrella import for the Yi naming Atlas overlay

Per `wen-algebra` v0.6 §9 (Atlas separation) and `v4-foundation` v0.5
§15 (external traditions):

> Atlas modules are application-layer overlays providing semantic
> names for `R_N` elements.  Each binding is opt-in.  The core
> (`Foundation/R/`) is language-independent; Atlas provides the
> cultural / domain / formal-tradition mappings.

This umbrella collects the Yi-tradition bindings on top of the
R-Family core:

* `Atlas/Yi/Names`      — core: `Yao` (= R 1), `Trigram` (= R 3),
                          `Hexagram` (= R 6), `Shi` (= R 2).
* `Atlas/Yi/Bagua`      — the 8 trigram names (qian/dui/.../kun) on R 3.
* `Atlas/Yi/Hexagrams`  — 4 distinguished hexagrams + King-Wen order.
* `Atlas/Yi/ShiV4`      — V₄ naming {dao, ji, jin, wei} on R 2.
* `Atlas/Yi/Operators`  — V₄ operators (cuo / zong / cuoZong) and `hu`.
* `Atlas/Yi/DaoSource`  — Phase β port of «道源» onto the clean stack:
                          11-instr Wen.Core program judging «是道非道»
                          with the five 相 (形/解/印/执/义) all proven.
* `Atlas/Yi/Diagonal`   — 理之不完备 / 哥德尔在 R 8: halting-undecidability
                          diagonal on `Wen.Core` (Atlas-Yi form of
                          `GodelLi.lean`).
* `Atlas/Yi/Positions`  — Hexagram position helpers (atPos, wellPos,
                          isYangPos, yingResponds, biAdj, allHex).
* `Atlas/Yi/Sheng`      — SiXiang (= Shi = R 2) + Trigram flips
                          (motion / middleFlip / topFlip), involutivity,
                          Hamming distance (R-Family port of
                          `Classical/Algebra/BaguaAlgebra`).
* `Atlas/Yi/Cell128`    — R₇ = Hexagram × YinBit with full (Z/2)⁷
                          group, imprint, projection, V₄ hex actions,
                          Cayley representation (R-Family port of
                          `Classical/Cells/R7`).
* `Atlas/Yi/Cell256`    — R₈ = Hexagram × Shi with full (Z/2)⁸ group,
                          V₄ Shi + Hexagram actions, projections to
                          Cell128 / Hexagram, Cayley representation
                          (R-Family port of `Classical/Cells/R8`).

Per doctrine, nothing else in the codebase imports this module: it is
opt-in.  This umbrella exists for convenience and as a discoverability
anchor.

## Layering

This module does **not** depend on the legacy `Foundation/Yi/` or
`Foundation/Bagua/` packages.  It is a clean re-implementation purely
on top of `Foundation/R/`.  Consumers should migrate to this Atlas
overlay; legacy code is preserved in `Atlas/Yi/Classical/` (5 semantic
sub-clusters) as a co-equal classical formalization.
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Bagua
import SSBX.Foundation.Atlas.Yi.Hexagrams
import SSBX.Foundation.Atlas.Yi.ShiV4
import SSBX.Foundation.Atlas.Yi.Operators
import SSBX.Foundation.Atlas.Yi.DaoSource
import SSBX.Foundation.Atlas.Yi.Diagonal
import SSBX.Foundation.Atlas.Yi.Positions
import SSBX.Foundation.Atlas.Yi.Sheng
import SSBX.Foundation.Atlas.Yi.Cell128
import SSBX.Foundation.Atlas.Yi.Cell256
import SSBX.Foundation.Atlas.Yi.Cell256Partial
import SSBX.Foundation.Atlas.Yi.ConstraintDemoYi
