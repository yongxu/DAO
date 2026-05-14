/-
# Wen.Xiang — canonical 𝕏ⁿ kernel (v0.4)

The canonical kernel of `wen-algebra` v0.4: the atomic `Image` (= V₄)
plus the n-fold image family `X n := Fin n → Image`, with bit-pattern
primary identity (`oo / xo / ox / xx` for image atoms; `OX!"oxoxox"`
for X k cells).

## Architecture

```
        Bit ─────► Image ─────► X ─────► OX
                   (V₄ atom)  (Fin n → Image)
                      │           │
                      │           ├─► Squaring
                      │           ├─► Dot          (Layer 0)
                      │           ├─► Symplectic   (Layer 1, σ + L)
                      │           ├─► Quadratic    (Layer 2, q + Arf)
                      │           ├─► SubTower     (§3.5 {道,错综}ⁿ)
                      │           ├─► Hom          (§6 Mat(对象))
                      │           └─► Layers
                      │                 │
                      ▼                 ▼
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
* `Dot.lean`     — F₂-bilinear `X.dot` (Layer 0), canonical basis,
                   recovery theorems (Sense 1 + Sense 2 of v0.4 §5.4),
                   non-degeneracy.
* `Symplectic.lean` — Layer 1 alternating form σ + diagonal `L`
                   (v0.4 §5.6): `Image.symplectic`, `Image.L`, the
                   decomposition `dot = σ ⊕ L⊗L`, the tower lifts
                   `X.symplectic` and `X.Lfold`, and the global
                   decomposition `dot = σⁿ ⊕ Lfold` (v0.4 §5.6.4).
* `Quadratic.lean`— Layer 2 quadratic refinements + Arf invariant
                   (v0.4 §5.7): `Image.q0`, `Image.q1`, polarisation
                   theorems, `Image.arf` (Arf(q₀) = 0, Arf(q₁) = 1);
                   tower lift `X.qC` parametrised by `Choice n`,
                   total Arf `X.arfTotal_qC = Choice.parity`.
* `SubTower.lean` — the {道, 错综}ⁿ intrinsic sub-tower (v0.4 §3.5):
                   predicate, `Image.L`-kernel characterisation,
                   `subTowerEquiv : SubTower n ≃ (Fin n → Bool)`,
                   cardinality `|SubTower n| = 2ⁿ`.
* `Hom.lean`      — `Op = X 2` as `Image` endomorphism (`applyOp`),
                   `Op.comp` with id / assoc / id-laws, and
                   `HomMat n m` matrix representation of
                   `Hom_F₂(X n, X m)` per v0.4 §6.
* `Layers.lean`  — five interface aliases:
                   `Origin`, `Image1`, `PairedImage`, `Hexagram`,
                   `TemporalHexagram` + cardinality theorems.

Multi-domain mappings (overlay-style):

* `Mapping/Math.lean`    — V₄ `{e, a, b, ab}`.
* `Mapping/Pauli.lean`   — Pauli `{I, X, Z, Y}` (mod phase) + `tensor4`.
* `Mapping/English.lean` — XAtoms `{Identity, ContentFlip, …}`,
                           TimeImage `{Atemporal, NotYet, Already,
                           CompositeNow}`, HexagramAnchors `{Heaven,
                           Earth, AfterCompletion, BeforeCompletion}`.
* `Mapping/Chinese.lean` — XAtoms `{道, 错, 综, 错综}` (notation),
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

Per v0.4 §3.1 the family is **IR-internal** beyond `n = 4`; the kernel
provides the `X n` family for all `n` but only the five surface layers
are aliased.

## Doctrinal pointers

* `wen-algebra` v0.4 (canonical): `/Users/ren/Downloads/wen-algebra (3).md`
  — §0.2 naming, §1 three perspectives, §2 algebraic completeness,
  §3 interface vs intermediate, §3.5 sub-tower, §4
  information-completeness per layer, §5.1–5.5 lossless dot product
  (Layer 0), §5.6 σ + L⊗L (Layer 1), §5.7 quadratic refinement + Arf
  (Layer 2), §6 Hom representation, §7.1 Lean skeleton.
* `docs-next/10_formal_形式/yi-RO-hierarchy.md` — repo-internal v3
  doctrine (the Xiang layer of the canonical R-hierarchy).
-/

import SSBX.Foundation.Wen.Xiang.Bit
import SSBX.Foundation.Wen.Xiang.Image
import SSBX.Foundation.Wen.Xiang.X
import SSBX.Foundation.Wen.Xiang.OX
import SSBX.Foundation.Wen.Xiang.Squaring
import SSBX.Foundation.Wen.Xiang.Dot
import SSBX.Foundation.Wen.Xiang.Symplectic
import SSBX.Foundation.Wen.Xiang.Quadratic
import SSBX.Foundation.Wen.Xiang.SubTower
import SSBX.Foundation.Wen.Xiang.Hom
import SSBX.Foundation.Wen.Xiang.Layers
import SSBX.Foundation.Wen.Xiang.Mapping.Math
import SSBX.Foundation.Wen.Xiang.Mapping.Pauli
import SSBX.Foundation.Wen.Xiang.Mapping.English
import SSBX.Foundation.Wen.Xiang.Mapping.Chinese
