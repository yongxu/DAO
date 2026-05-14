/-
# Foundation.Atlas.Yi.Positions — structure-style positional helpers on Hexagram

This module adds compatibility helpers that read a `Hexagram` in
position-oriented style.  Each helper is purely derived from the core
`Hexagram = R 6 = Fin 6 → Bool` abbreviation — no new doctrinal content.

## Position polarity (爻位之刚柔)

In the classical reading of the I Ching, positions in a hexagram
alternate yang and yin:

| 1-based position | 0-based | polarity |
|------------------|---------|----------|
| 初 (1)           | 0       | yang     |
| 二 (2)           | 1       | yin      |
| 三 (3)           | 2       | yang     |
| 四 (4)           | 3       | yin      |
| 五 (5)           | 4       | yang     |
| 上 (6)           | 5       | yin      |

So `isYangPos i = (i.val % 2 = 0)` (yang at 0, 2, 4 — i.e. positions
1, 3, 5 in 1-based counting).

## API

* `positions`, `atPos`           — read the yao at position `i`.
* `isYangPos`                    — position polarity.
* `wellPos`                      — 当位: yao polarity matches position polarity.
* `yingResponds`                 — 应: two yao of opposite polarity.
* `biAdj`                        — 比: adjacent yao of opposite polarity.
* `allHex`                       — enumeration of all 64 hexagrams.

These helpers are pure conveniences for consumers who prefer the
positional / structural view; the canonical API remains `y1..y6`.
-/

import SSBX.Foundation.Atlas.Yi.Names

namespace SSBX.Foundation.Atlas.Yi

open SSBX.Foundation.R

namespace Hexagram

/-! ## § 1 Position polarity -/

/-- `isYangPos i = true` iff position `i` (0-indexed) is a yang position.

    0-indexed `0, 2, 4` correspond to 1-indexed positions 1, 3, 5
    (初, 三, 五) which are the classical yang positions. -/
def isYangPos (i : Fin 6) : Bool := i.val % 2 == 0

/-- Read the yao at position `i`.  Structure-style alias of `h i`. -/
def atPos (h : Hexagram) (i : Fin 6) : Yao := h i

/-! ## § 2 当位 (well-placed), 应 (responds), 比 (adjacent) -/

/-- 当位 (`wellPos`): the yao at position `i` is "well-placed" iff its
    polarity (yang/yin) matches the position's polarity. -/
def wellPos (h : Hexagram) (i : Fin 6) : Bool :=
  (decide (h i = Yao.yang)) == isYangPos i

/-- 应 (`yingResponds`): two yao at positions `i, j` "respond" iff they
    have opposite polarity (i.e. one yin, one yang).

    Classically this relation is checked between corresponding inner /
    outer positions `(1,4), (2,5), (3,6)`; the predicate itself is
    symmetric and defined for arbitrary `i j`. -/
def yingResponds (h : Hexagram) (i j : Fin 6) : Bool := h i ≠ h j

/-- 比 (`biAdj`): adjacent yao at positions `i, i+1` differ in polarity.
    `i : Fin 5` ensures `i + 1` stays in range. -/
def biAdj (h : Hexagram) (i : Fin 5) : Bool :=
  h ⟨i.val, by omega⟩ ≠ h ⟨i.val + 1, by omega⟩

/-! ## § 3 Enumeration of all 64 hexagrams -/

/-- All 64 hexagrams, generated from the 6-bit Cartesian product.

    The order is `(y1, y2, y3, y4, y5, y6)` with `y6` (top) varying
    fastest.  This is **not** the King-Wen order; for the King-Wen
    sequence see `Hexagrams.xuGua`.  Use this enumeration when an
    exhaustive list is needed without the doctrinal ordering. -/
def allHex : List Hexagram :=
  (do
    let a ← [Yao.yang, Yao.yin]
    let b ← [Yao.yang, Yao.yin]
    let c ← [Yao.yang, Yao.yin]
    let d ← [Yao.yang, Yao.yin]
    let e ← [Yao.yang, Yao.yin]
    let f ← [Yao.yang, Yao.yin]
    pure (mk a b c d e f))

/-- `allHex` has 64 entries. -/
theorem allHex_length : allHex.length = 64 := by decide

end Hexagram

end SSBX.Foundation.Atlas.Yi
