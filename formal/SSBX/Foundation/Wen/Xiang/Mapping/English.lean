/-
# Wen.Xiang.Mapping.English — English-language reading

Per `wen-algebra` v0.4 §0.2: the canonical English (primary) names for
the V₄ atoms and Time-Image atoms.

## V₄ atoms (operator role at `Image`)

| Lean              | bit         | 文     | role                    |
|-------------------|-------------|--------|-------------------------|
| `Identity`        | `Image.oo`  | 道     | V₄ identity             |
| `ContentFlip`     | `Image.xo`  | 错     | α-axis content flip     |
| `FrameFlip`       | `Image.ox`  | 综     | β-axis frame flip       |
| `CompoundFlip`    | `Image.xx`  | 错综   | diagonal (= ∘ of above) |

## Time-Image atoms (temporal role at `Image`)

| Lean              | bit         | 文 | role                   |
|-------------------|-------------|----|------------------------|
| `Atemporal`       | `Image.oo`  | 道 | timeless               |
| `NotYet`          | `Image.xo`  | 未 | future                 |
| `Already`         | `Image.ox`  | 已 | past                   |
| `CompositeNow`    | `Image.xx`  | 今 | present-as-fusion      |

Per v0.4 §4.4 the temporal atoms occupy the **fourth** image-coordinate
of `TemporalHexagram = X 4`; the first three are the `Hexagram` factor.

**Note on legacy `R8.Shi` discrepancy.** The legacy `Foundation/Bagua/R8.lean`
encodes `Shi.ji = (true, false)` as 已 (Already) and `Shi.wei = (false,
true)` as 未 (Not-Yet), opposite of v0.4's `未 = (1, 0), 已 = (0, 1)`.
The Xiang kernel commits to v0.4; legacy code retains its own
convention.

## Hexagram anchors (X 3 cells)

Four named `Hexagram = X 3` cells corresponding to 乾 / 坤 / 既济 / 未济
in the classical I-Ching tradition:

| Lean                | OX!         | bit pattern  | image factors        |
|---------------------|-------------|--------------|----------------------|
| `Heaven` (乾)        | `"oooooo"`  | all-yang     | (Identity)³          |
| `Earth` (坤)         | `"xxxxxx"`  | all-yin      | (CompoundFlip)³      |
| `AfterCompletion` (既济) | `"oxoxox"` | yang/yin alt | (FrameFlip)³         |
| `BeforeCompletion` (未济) | `"xoxoxo"` | yin/yang alt | (ContentFlip)³       |

The "elegance" here is structural: each of the four canonical hexagrams
has all three image-coordinates equal to the same V₄ atom — a uniform
hexagram in V₄-coordinate language.
-/

import SSBX.Foundation.Wen.Xiang.Image
import SSBX.Foundation.Wen.Xiang.X
import SSBX.Foundation.Wen.Xiang.OX
import SSBX.Foundation.Wen.Xiang.Layers

namespace SSBX.Foundation.Wen.Xiang.Mapping.English

open SSBX.Foundation.Wen.Xiang

/-! ## § 1 V₄ atoms — operator role -/

namespace XAtoms

/-- V₄ identity (= `Image.oo` = 道 = `e` = Pauli I). -/
abbrev Identity : Image := .oo

/-- V₄ content-axis generator (= `Image.xo` = 错 = `a` = Pauli X). -/
abbrev ContentFlip : Image := .xo

/-- V₄ frame-axis generator (= `Image.ox` = 综 = `b` = Pauli Z). -/
abbrev FrameFlip : Image := .ox

/-- V₄ diagonal element (= `Image.xx` = 错综 = `ab` = Pauli Y). -/
abbrev CompoundFlip : Image := .xx

end XAtoms

/-! ## § 2 Time-Image atoms — temporal role -/

namespace TimeImage

/-- Time-image identity, the timeless / atemporal atom (= `Image.oo`,
    = 道 in the temporal reading). -/
abbrev Atemporal : Image := .oo

/-- Time-image future atom (= `Image.xo`, = 未, per v0.4 convention). -/
abbrev NotYet : Image := .xo

/-- Time-image past atom (= `Image.ox`, = 已, per v0.4 convention). -/
abbrev Already : Image := .ox

/-- Time-image present-as-fusion atom (= `Image.xx`, = 今, the PT
    composite of `NotYet` and `Already`). -/
abbrev CompositeNow : Image := .xx

end TimeImage

/-! ## § 3 Hexagram anchors — named `X 3` cells -/

namespace HexagramAnchors

/-- 乾 / Heaven — the all-yang hexagram, = `(Identity, Identity, Identity)`. -/
def Heaven : Hexagram := OX!"oooooo"

/-- 坤 / Earth — the all-yin hexagram, = `(CompoundFlip)³`. -/
def Earth : Hexagram := OX!"xxxxxx"

/-- 既济 / AfterCompletion — the alternating yang/yin hexagram,
    = `(FrameFlip)³`. -/
def AfterCompletion : Hexagram := OX!"oxoxox"

/-- 未济 / BeforeCompletion — the alternating yin/yang hexagram,
    = `(ContentFlip)³`. -/
def BeforeCompletion : Hexagram := OX!"xoxoxo"

end HexagramAnchors

/-! ## § 4 Cross-reading sanity checks -/

example : XAtoms.Identity = TimeImage.Atemporal := rfl
example : XAtoms.ContentFlip = TimeImage.NotYet := rfl
example : XAtoms.FrameFlip = TimeImage.Already := rfl
example : XAtoms.CompoundFlip = TimeImage.CompositeNow := rfl

example : ∀ i, HexagramAnchors.Heaven i = XAtoms.Identity := by decide
example : ∀ i, HexagramAnchors.Earth i = XAtoms.CompoundFlip := by decide
example : ∀ i, HexagramAnchors.AfterCompletion i = XAtoms.FrameFlip := by
  decide
example : ∀ i, HexagramAnchors.BeforeCompletion i = XAtoms.ContentFlip := by
  decide

end SSBX.Foundation.Wen.Xiang.Mapping.English
