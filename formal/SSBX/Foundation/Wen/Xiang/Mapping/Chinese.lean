/-
# Wen.Xiang.Mapping.Chinese — Chinese-character reading

Per `wen-algebra` v0.4 §0.2: Chinese-character readings of the
canonical bit-pattern atoms.  Lean does not allow Han characters as
identifier heads, so the canonical Lean names are pinyin (`abbrev`s)
and the Chinese characters are layered on top via **scoped
`notation`** declarations.

Three parallel readings are recorded against `Image`, plus the four
classical hexagram anchors at `Hexagram = X 3`:

| Sub-namespace      | atoms                              |
|--------------------|------------------------------------|
| `XAtoms`          | 道 / 错 / 综 / 错综  (operator)     |
| `SiXiang`          | 太阳 / 少阳 / 少阴 / 太阴  (image)  |
| `TimeImage`        | 道 / 未 / 已 / 今  (temporal)       |
| `HexagramAnchors`  | 乾 / 坤 / 既济 / 未济              |

Every notation is `scoped` so that `open scoped XAtoms` (etc.) brings
the Chinese-character notation in without clobbering names from other
sub-namespaces.

## Bit pattern → V₄ → Chinese reading

| bit | V₄        | 文 (XAtoms) | 文 (SiXiang) | 文 (TimeImage)   |
|-----|-----------|--------------|--------------|------------------|
| oo  | identity  | 道           | 太阳         | 道 (Atemporal)   |
| xo  | a (α-gen) | 错           | 少阳         | 未 (Not-Yet)     |
| ox  | b (β-gen) | 综           | 少阴         | 已 (Already)     |
| xx  | ab        | 错综         | 太阴         | 今 (Composite-Now) |

The legacy `R8.Shi` convention swaps 未/已; v0.4 (and this file)
commits to `未 = Image.xo, 已 = Image.ox`.

## Hexagram anchors

The four classical "uniform-V₄" hexagrams: each has all three
image-coordinates equal.

| 文     | OX!        | bit pattern | image factors |
|--------|------------|-------------|---------------|
| 乾     | `"oooooo"` | all-yang    | (道)³         |
| 坤     | `"xxxxxx"` | all-yin     | (错综)³       |
| 既济   | `"oxoxox"` | yang/yin    | (综)³         |
| 未济   | `"xoxoxo"` | yin/yang    | (错)³         |
-/

import SSBX.Foundation.Wen.Xiang.Image
import SSBX.Foundation.Wen.Xiang.X
import SSBX.Foundation.Wen.Xiang.OX
import SSBX.Foundation.Wen.Xiang.Layers

namespace SSBX.Foundation.Wen.Xiang.Mapping.Chinese

open SSBX.Foundation.Wen.Xiang

/-! ## § 1 V₄ atoms — operator role at `Image` (道/错/综/错综) -/

namespace XAtoms

/-- 道 (dào) — V₄ identity, `Image.oo`. -/
abbrev dao : Image := .oo

/-- 错 (cuò) — V₄ α-axis content flip, `Image.xo`. -/
abbrev cuo : Image := .xo

/-- 综 (zōng) — V₄ β-axis frame flip, `Image.ox`. -/
abbrev zong : Image := .ox

/-- 错综 (cuòzōng) — V₄ diagonal element, `Image.xx` (= cuo ∘ zong). -/
abbrev cuozong : Image := .xx

/-- Chinese-character notation for `dao` (道). -/
scoped notation "道" => dao
/-- Chinese-character notation for `cuo` (错). -/
scoped notation "错" => cuo
/-- Chinese-character notation for `zong` (综). -/
scoped notation "综" => zong
/-- Chinese-character notation for `cuozong` (错综). -/
scoped notation "错综" => cuozong

end XAtoms

/-! ## § 2 SiXiang atoms — 易传 image role at `Image` (太阳/少阳/少阴/太阴)

The 四象 of the classical Yi tradition.  Bit ordering: position 0 = 初爻
(bottom), position 1 = 上爻 (top), with 'o' = yang, 'x' = yin. -/

namespace SiXiang

/-- 太阳 (tàiyáng) — both yao yang, `Image.oo`. -/
abbrev taiyang : Image := .oo

/-- 少阳 (shàoyáng) — bottom yin, top yang, `Image.xo`. -/
abbrev shaoyang : Image := .xo

/-- 少阴 (shàoyīn) — bottom yang, top yin, `Image.ox`. -/
abbrev shaoyin : Image := .ox

/-- 太阴 (tàiyīn) — both yao yin, `Image.xx`. -/
abbrev taiyin : Image := .xx

scoped notation "太阳" => taiyang
scoped notation "少阳" => shaoyang
scoped notation "少阴" => shaoyin
scoped notation "太阴" => taiyin

end SiXiang

/-! ## § 3 Time-Image atoms — temporal role at `Image` (道/未/已/今)

Per v0.4 §0.2, the fourth-coordinate (`X 4` time slot) reading.  The
identity here is also called 道 (atemporal); the namespace separation
keeps it disjoint from `XAtoms.dao` even though both alias `Image.oo`. -/

namespace TimeImage

/-- 道 (dào) in the temporal reading — atemporal / timeless,
    `Image.oo`. -/
abbrev atemporal : Image := .oo

/-- 未 (wèi) — not-yet / future, `Image.xo` per v0.4 (legacy R8.Shi
    swaps wei/yi). -/
abbrev wei : Image := .xo

/-- 已 (yǐ) — already / past, `Image.ox` per v0.4. -/
abbrev yi : Image := .ox

/-- 今 (jīn) — composite-now / PT fusion, `Image.xx`. -/
abbrev jin : Image := .xx

/-- Chinese-character notation for `atemporal` (道, scoped to
    `TimeImage`). -/
scoped notation "道" => atemporal
scoped notation "未" => wei
scoped notation "已" => yi
scoped notation "今" => jin

end TimeImage

/-! ## § 4 Hexagram anchors — named `X 3` cells (乾/坤/既济/未济) -/

namespace HexagramAnchors

/-- 乾 (qián) / Heaven — all-yang hexagram, = (道, 道, 道). -/
def qian : Hexagram := OX!"oooooo"

/-- 坤 (kūn) / Earth — all-yin hexagram, = (错综, 错综, 错综). -/
def kun : Hexagram := OX!"xxxxxx"

/-- 既济 (jìjì) / After-Completion — alternating yang/yin,
    = (综, 综, 综). -/
def jiji : Hexagram := OX!"oxoxox"

/-- 未济 (wèijì) / Before-Completion — alternating yin/yang,
    = (错, 错, 错). -/
def weiji : Hexagram := OX!"xoxoxo"

scoped notation "乾" => qian
scoped notation "坤" => kun
scoped notation "既济" => jiji
scoped notation "未济" => weiji

end HexagramAnchors

/-! ## § 5 Cross-reading sanity checks

The same bit pattern is named differently in each role, but the
underlying `Image` atom is identical.  These `rfl` examples are the
architecture's payoff: cross-reading translation is mechanical at the
bit-pattern level. -/

example : XAtoms.dao = SiXiang.taiyang := rfl
example : XAtoms.dao = TimeImage.atemporal := rfl
example : XAtoms.cuo = SiXiang.shaoyang := rfl
example : XAtoms.cuo = TimeImage.wei := rfl
example : XAtoms.zong = SiXiang.shaoyin := rfl
example : XAtoms.zong = TimeImage.yi := rfl
example : XAtoms.cuozong = SiXiang.taiyin := rfl
example : XAtoms.cuozong = TimeImage.jin := rfl

example : ∀ i, HexagramAnchors.qian i = XAtoms.dao := by decide
example : ∀ i, HexagramAnchors.kun i = XAtoms.cuozong := by decide
example : ∀ i, HexagramAnchors.jiji i = XAtoms.zong := by decide
example : ∀ i, HexagramAnchors.weiji i = XAtoms.cuo := by decide

end SSBX.Foundation.Wen.Xiang.Mapping.Chinese
