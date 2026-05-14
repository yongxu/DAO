/-
# `SSBX.Foundation.Atlas` — umbrella import for the Atlas (Application Layer)

Per `wen-algebra` v0.6 §9 and `v4-foundation` v0.5 §15:

> Atlas modules are **application-layer overlays** providing semantic
> names for `R_N` elements.  Each binding is **opt-in**.  The core
> (`Foundation/R/`) is language-independent; Atlas provides the
> cultural / domain / formal-tradition mappings.

Per the v0.6 doctrine, nothing else in the codebase imports from
`Atlas/`.  Consumers explicitly opt in to a specific binding (e.g.,
`import SSBX.Foundation.Atlas.Pauli`).  This umbrella exists for
convenience and to gather the available bindings.

## Non-Yi bindings (Phase 3.1)

* `Atlas/Pauli`    — R 2 ↔ {I, X, Y, Z} (Pauli mod phase)
* `Atlas/Greimas`  — R 2 ↔ {A, ¬A, B, ¬B} (semiotic square)
* `Atlas/Boolean`  — R 4 ↔ 16 Boolean functions of 2 vars
* `Atlas/Fano`     — R 3 ↔ PG(2, 2) Fano plane (7 points, 7 lines)
* `Atlas/Hamming`  — R 7 ⊇ Hamming(7, 4) perfect code (16 codewords)
* `Atlas/GF256`    — R 8 ↔ GF(256) Rijndael field structure

## Yi bindings (Phase α — Yi naming bridge)

* `Atlas/Yi`       — umbrella for the Yi naming Atlas overlay
                     (Yao = R 1, Trigram = R 3, Hexagram = R 6,
                     Shi = R 2, 8 Bagua + 64 hexagrams + V₄ ops).
-/

import SSBX.Foundation.Atlas.Pauli
import SSBX.Foundation.Atlas.Greimas
import SSBX.Foundation.Atlas.Boolean
import SSBX.Foundation.Atlas.Fano
import SSBX.Foundation.Atlas.Hamming
import SSBX.Foundation.Atlas.GF256
import SSBX.Foundation.Atlas.Yi
