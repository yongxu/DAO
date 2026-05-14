/-
# Wen.SquaringTower — canonical 𝕏ⁿ kernel (v0.2)

The canonical kernel of `wen-algebra` v0.2: the atomic `Image` (= V₄)
plus the n-fold image family `X n := Fin n → Image`, with bit-pattern
primary identity (`oo / xo / ox / xx` for image atoms; `OX!"oxoxox"`
for X k cells).

## Architecture

```
        Bit ─────────► Image ─────────► X ─────► OX
                       (V₄ atom)      (Fin n → Image)
                          │              │
                          │              ├─► Squaring
                          │              ├─► Dot
                          │              └─► Layers
                          │                    │
                          ▼                    ▼
                       Mapping/{Math, Pauli, English, Chinese}
```

* `Bit.lean`     — substrate `BitLike` typeclass + `Bool` default + `Qbit` placeholder.
* `Image.lean`   — V₄ atom with bit-pattern constructors `oo/xo/ox/xx`,
                   `CommGroup`, F₂-bilinear `Image.dot`.
* `X.lean`       — `X n := Fin n → Image`; `CommGroup`, `Fintype`,
                   `DecidableEq` inherited from `Pi`; `X.equivImage`
                   is the atomic-↔-family bridge `X 1 ≃ Image`.
* `OX.lean`      — `OX!"..."` macro: even-length `o/x` string → `X k`
                   (k = string.length / 2).
* `Squaring.lean`— `X (a + b) ≃ X a × X b` and the canonical squaring
                   chain `X 2 ≃ X 1 × X 1`, `X 4 ≃ X 2 × X 2`,
                   `X 8 ≃ X 4 × X 4`; the temporal split
                   `TemporalHexagram ≃ Hexagram × Image1`; the
                   four-factor `quarticEquiv : X 4 ≃ X 1⁴`.
* `Dot.lean`     — F₂-bilinear `X.dot`, canonical basis, recovery
                   theorems (Sense 1 + Sense 2 of v0.2 §5.4),
                   non-degeneracy as forward implication
                   (`nondegenerate`) and as iff
                   (`nondegenerate_iff` matching v0.2 §6.1).
* `Layers.lean`  — five interface aliases:
                   `Origin`, `Image1`, `PairedImage`, `Hexagram`,
                   `TemporalHexagram` + cardinality theorems.

Multi-domain mappings (Layer 2, all overlay-style):

* `Mapping/Math.lean`    — V₄ `{e, a, b, ab}`.
* `Mapping/Pauli.lean`   — Pauli `{I, X, Z, Y}` (mod phase) + `tensor4`.
* `Mapping/English.lean` — V4Atoms `{Identity, ContentFlip, …}`,
                           TimeImage `{Atemporal, NotYet, Already,
                           CompositeNow}`, HexagramAnchors `{Heaven,
                           Earth, AfterCompletion, BeforeCompletion}`.
* `Mapping/Chinese.lean` — V4Atoms `{道, 错, 综, 错综}` (notation),
                           SiXiang `{太阳, 少阳, 少阴, 太阴}`,
                           TimeImage `{道, 未, 已, 今}`,
                           HexagramAnchors `{乾, 坤, 既济, 未济}`.

## Cardinality table

```
   Origin            X 0       1
   Image1            X 1       4
   PairedImage       X 2      16
   Hexagram          X 3      64
   TemporalHexagram  X 4     256
```

Per v0.2 §3.1 the family is **IR-internal** beyond `n = 4`; the kernel
provides the `X n` family for all `n` but only the five surface layers
are aliased.

## Doctrinal pointers

* `wen-algebra` v0.2 (canonical): `/Users/ren/Downloads/wen-algebra (2).md`
  — §0.2 naming, §1 three perspectives, §2 algebraic completeness,
  §3 interface vs intermediate, §4 information-completeness per layer,
  §5 lossless dot product, §6.1 Lean skeleton.
* `docs-next/10_formal_形式/yi-RO-hierarchy.md` — repo-internal v3
  doctrine (the squaring-tower layer of the canonical R-hierarchy).
-/

import SSBX.Foundation.Wen.SquaringTower.Bit
import SSBX.Foundation.Wen.SquaringTower.Image
import SSBX.Foundation.Wen.SquaringTower.X
import SSBX.Foundation.Wen.SquaringTower.OX
import SSBX.Foundation.Wen.SquaringTower.Squaring
import SSBX.Foundation.Wen.SquaringTower.Dot
import SSBX.Foundation.Wen.SquaringTower.Layers
import SSBX.Foundation.Wen.SquaringTower.Mapping.Math
import SSBX.Foundation.Wen.SquaringTower.Mapping.Pauli
import SSBX.Foundation.Wen.SquaringTower.Mapping.English
import SSBX.Foundation.Wen.SquaringTower.Mapping.Chinese
