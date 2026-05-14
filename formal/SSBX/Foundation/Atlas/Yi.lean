/-
# Foundation.Atlas.Yi — umbrella import for the Yi naming Atlas overlay

Per `wen-algebra` v0.6 §9 (Atlas separation) and `v4-foundation` v0.5
§15 (external traditions):

> Atlas modules are application-layer overlays providing semantic
> names for `R_N` elements.  Each binding is opt-in.  The core
> (`Foundation/R/`) is language-independent; Atlas provides the
> cultural / domain / formal-tradition mappings.

This umbrella collects the four Yi-tradition bindings on top of the
R-Family core:

* `Atlas/Yi/Names`      — core: `Yao` (= R 1), `Trigram` (= R 3),
                          `Hexagram` (= R 6), `Shi` (= R 2).
* `Atlas/Yi/Bagua`      — the 8 trigram names (qian/dui/.../kun) on R 3.
* `Atlas/Yi/Hexagrams`  — 4 distinguished hexagrams + King-Wen order.
* `Atlas/Yi/ShiV4`      — V₄ naming {dao, ji, jin, wei} on R 2.
* `Atlas/Yi/Operators`  — V₄ operators (cuo / zong / cuoZong) and `hu`.

Per doctrine, nothing else in the codebase imports this module: it is
opt-in.  This umbrella exists for convenience and as a discoverability
anchor.

## Layering

This module does **not** depend on the legacy `Foundation/Yi/` or
`Foundation/Bagua/` packages.  It is a clean re-implementation purely
on top of `Foundation/R/`.  Phase γ (a later step) will delete the
legacy modules; consumers should migrate to this Atlas overlay.
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Bagua
import SSBX.Foundation.Atlas.Yi.Hexagrams
import SSBX.Foundation.Atlas.Yi.ShiV4
import SSBX.Foundation.Atlas.Yi.Operators
