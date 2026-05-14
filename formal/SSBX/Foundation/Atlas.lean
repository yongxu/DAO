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

## Atlas/Yi/Classical/ — co-equal classical axiomatization (Phase γ)

Per `wen-algebra` v0.6 the project now carries **two co-equal Yi
Atlas overlays**:

* `Atlas/Yi/{Names, Bagua, Hexagrams, Operators, ShiV4, Diagonal,
  DaoSource}` — **R-Family axiomatization** (`Yao := Bool`,
  `Hexagram := R 6 = Fin 6 → Bool`).  Doctrinally aligned with v0.6;
  integrates with R-Family bilinear algebra + Squaring tower;
  `Diagonal` uses `KleeneInverter` as a `Prop` hypothesis, not an
  axiom.

* `Atlas/Yi/Classical/` — **classical axiomatization**
  (`inductive Yao`, `structure Hexagram { positions : Fin 6 → Yao }`).
  Supports `cases h with | mk y₁..y₆ =>` exhaustive splits used by
  ~50 Wenyan parser / interpreter consumer files and by the
  load-bearing `kleene_recursion_axiom`.  Organized into 5 semantic
  sub-clusters:
    * `Classical/Core/`        — Yi.lean + YiCore.lean (basic types & ops)
    * `Classical/Algebra/`     — BaguaAlgebra, BenZheng, CuoInvariance, Newman
    * `Classical/Cells/`       — R7, R8, R8Stratify (Hex × YinBit, Hex × Shi)
    * `Classical/Computation/` — BaguaTuring, BaguaWenSpec, ChunkedDecide,
                                 FuelDiscipline
    * `Classical/Diagonal/`    — GodelLi, KleeneInternal

Both formalizations are mathematically valid; the long-term direction
per v0.6 is the R-Family side, with `Classical/` preserved for theorems
and consumers depending on the inductive encoding.

`Classical/` is **not** included in this umbrella; consumers explicitly
opt in to specific modules (e.g.
`import SSBX.Foundation.Atlas.Yi.Classical.Core.Yi`).
-/

import SSBX.Foundation.Atlas.Pauli
import SSBX.Foundation.Atlas.Greimas
import SSBX.Foundation.Atlas.Boolean
import SSBX.Foundation.Atlas.Fano
import SSBX.Foundation.Atlas.Hamming
import SSBX.Foundation.Atlas.GF256
import SSBX.Foundation.Atlas.Yi
