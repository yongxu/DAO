/-
# Foundation.Atlas.Yi.BenZheng — 本/征 product decomposition on R 6

Per `wen-algebra` v0.6 §9 (Atlas separation) and the R-Family product
structure of `Hexagram = R 6`:

    R 6  ≃  R 2  ×  R 4
            ─┬─    ─┬─
            本     征
        (substrate)(mark)

This module is the **R-Family port** of the classical `Atlas/Yi/
Classical/Algebra/BenZheng.lean` 4-decomposition.  The classical
version uses an inductive 4-substrate / 4-mark type built from the
reverse-fixed / reverse-mobile trigram split.  Here we expose the
underlying **structural product** that gives the cleanest expression
of the 本/征 split in the R-Family stack:

    `Ben    := R 2`  — 前 2 爻 (inner-bottom 2 yao, y1/y2)
    `Zheng  := R 4`  — 后 4 爻 (the remaining 4 yao, y3/y4/y5/y6)
    `Mian   := Ben × Zheng ≃ R 6 = Hexagram`

The 4 named Ben values `(yangyang, yangyin, yinyang, yinyin)` partition
`Hexagram` into the four 16-cell quadrants used in the classical 64-卦
analysis (each Ben has |Zheng| = 16 hexagrams sitting above it).

## Bit-pattern convention

Per project convention (`o = false = yang`, `x = true = yin`):

  - `yangyang : Ben = (false, false) = ⚏ in Pauli-flavour`
  - `yangyin  : Ben = (false, true)`
  - `yinyang  : Ben = (true,  false)`
  - `yinyin   : Ben = (true,  true)`

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9 (Atlas separation), §1 (R-Family Tower).
* `v4-foundation.md` v0.5 §15 (external-tradition bindings).
* Project memory: 元/爻 配对原则 — `R_{2n} = R_n × R_n` two-factor decomposition.
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Hexagrams
import SSBX.Foundation.Atlas.Yi.Operators

namespace SSBX.Foundation.Atlas.Yi.BenZheng

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 Ben (本) — R 2 = 前 2 爻 (substrate) -/

/-- `Ben := R 2` — the **本 (substrate)** factor of a hexagram, i.e.
    the inner-bottom 2 yao (`y1`, `y2`). -/
abbrev Ben : Type := R 2

namespace Ben

/-- Read the 1st yao of a Ben (= y1 of the parent hexagram). -/
def y1 (b : Ben) : Yao := b ⟨0, by decide⟩

/-- Read the 2nd yao of a Ben (= y2 of the parent hexagram). -/
def y2 (b : Ben) : Yao := b ⟨1, by decide⟩

/-- Build a Ben from its two yao components. -/
def mk (a b : Yao) : Ben := fun i =>
  match i with
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

@[simp] theorem y1_mk (a b : Yao) : y1 (mk a b) = a := rfl
@[simp] theorem y2_mk (a b : Yao) : y2 (mk a b) = b := rfl

/-- Ben extensionality through its 2 yao components. -/
theorem ext (b c : Ben) (h1 : y1 b = y1 c) (h2 : y2 b = y2 c) : b = c := by
  funext i
  match i with
  | ⟨0, _⟩ => exact h1
  | ⟨1, _⟩ => exact h2

/-! ### § 1.1 The 4 named substrates -/

/-- `yangyang : Ben = (yang, yang)` — the all-yang substrate. -/
@[match_pattern] def yangyang : Ben := mk Yao.yang Yao.yang

/-- `yangyin  : Ben = (yang, yin)`. -/
@[match_pattern] def yangyin  : Ben := mk Yao.yang Yao.yin

/-- `yinyang  : Ben = (yin, yang)`. -/
@[match_pattern] def yinyang  : Ben := mk Yao.yin  Yao.yang

/-- `yinyin   : Ben = (yin, yin)` — the all-yin substrate. -/
@[match_pattern] def yinyin   : Ben := mk Yao.yin  Yao.yin

/-- The 4 substrates in canonical (Pauli-flavour) order. -/
def all : List Ben := [yangyang, yangyin, yinyang, yinyin]

theorem all_length : all.length = 4 := rfl

/-! ### § 1.2 Cardinality and distinctness -/

/-- |本| = 4. -/
theorem card : Fintype.card Ben = 4 := R.R2_card

theorem yangyang_ne_yangyin : (yangyang : Ben) ≠ yangyin := by
  intro h; have := congrFun h ⟨1, by decide⟩; cases this

theorem yangyang_ne_yinyang : (yangyang : Ben) ≠ yinyang := by
  intro h; have := congrFun h ⟨0, by decide⟩; cases this

theorem yangyang_ne_yinyin : (yangyang : Ben) ≠ yinyin := by
  intro h; have := congrFun h ⟨0, by decide⟩; cases this

theorem yangyin_ne_yinyang : (yangyin : Ben) ≠ yinyang := by
  intro h; have := congrFun h ⟨0, by decide⟩; cases this

theorem yangyin_ne_yinyin : (yangyin : Ben) ≠ yinyin := by
  intro h; have := congrFun h ⟨0, by decide⟩; cases this

theorem yinyang_ne_yinyin : (yinyang : Ben) ≠ yinyin := by
  intro h; have := congrFun h ⟨1, by decide⟩; cases this

/-- Encode a Ben as a 2-bit `Nat` (0..3) for distinctness proofs. -/
def toNat (b : Ben) : Nat :=
  (if b.y1 then 2 else 0) + (if b.y2 then 1 else 0)

@[simp] theorem toNat_yangyang : toNat yangyang = 0 := rfl
@[simp] theorem toNat_yangyin  : toNat yangyin  = 1 := rfl
@[simp] theorem toNat_yinyang  : toNat yinyang  = 2 := rfl
@[simp] theorem toNat_yinyin   : toNat yinyin   = 3 := rfl

/-- The 4 named Ben values are pairwise distinct. -/
theorem all_nodup : all.Nodup := by
  have : (all.map toNat).Nodup := by
    show ([0, 1, 2, 3] : List Nat).Nodup
    decide
  exact List.Nodup.of_map _ this

/-- Coverage: every `Ben` is one of the 4 named values. -/
theorem mem_all (b : Ben) : b ∈ all := by
  have ht : b = mk b.y1 b.y2 := by
    apply ext <;> rfl
  rw [ht]
  unfold all
  rcases b.y1 with _ | _ <;> rcases b.y2 with _ | _ <;>
    simp [yangyang, yangyin, yinyang, yinyin, Yao.yang, Yao.yin]

/-- Character label of a Ben (single-char Pauli-style identifiers). -/
def label (b : Ben) : String :=
  match b.y1, b.y2 with
  | false, false => "oo"
  | false, true  => "ox"
  | true,  false => "xo"
  | true,  true  => "xx"

@[simp] theorem label_yangyang : label yangyang = "oo" := rfl
@[simp] theorem label_yangyin  : label yangyin  = "ox" := rfl
@[simp] theorem label_yinyang  : label yinyang  = "xo" := rfl
@[simp] theorem label_yinyin   : label yinyin   = "xx" := rfl

end Ben

/-! ## § 2 Zheng (征) — R 4 = 后 4 爻 (directional mark) -/

/-- `Zheng := R 4` — the **征 (mark)** factor of a hexagram, i.e.
    the outer 4 yao (`y3`, `y4`, `y5`, `y6`). -/
abbrev Zheng : Type := R 4

namespace Zheng

/-- Read the 1st yao of a Zheng (= y3 of the parent hexagram). -/
def y1 (z : Zheng) : Yao := z ⟨0, by decide⟩

/-- Read the 2nd yao of a Zheng (= y4 of the parent hexagram). -/
def y2 (z : Zheng) : Yao := z ⟨1, by decide⟩

/-- Read the 3rd yao of a Zheng (= y5 of the parent hexagram). -/
def y3 (z : Zheng) : Yao := z ⟨2, by decide⟩

/-- Read the 4th yao of a Zheng (= y6 of the parent hexagram). -/
def y4 (z : Zheng) : Yao := z ⟨3, by decide⟩

/-- Build a Zheng from its four yao components. -/
def mk (a b c d : Yao) : Zheng := fun i =>
  match i with
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d

@[simp] theorem y1_mk (a b c d : Yao) : y1 (mk a b c d) = a := rfl
@[simp] theorem y2_mk (a b c d : Yao) : y2 (mk a b c d) = b := rfl
@[simp] theorem y3_mk (a b c d : Yao) : y3 (mk a b c d) = c := rfl
@[simp] theorem y4_mk (a b c d : Yao) : y4 (mk a b c d) = d := rfl

/-- Zheng extensionality through its 4 yao components. -/
theorem ext (z w : Zheng) (h1 : y1 z = y1 w) (h2 : y2 z = y2 w)
    (h3 : y3 z = y3 w) (h4 : y4 z = y4 w) : z = w := by
  funext i
  match i with
  | ⟨0, _⟩ => exact h1
  | ⟨1, _⟩ => exact h2
  | ⟨2, _⟩ => exact h3
  | ⟨3, _⟩ => exact h4

/-- |征| = 16. -/
theorem card : Fintype.card Zheng = 16 := R.R4_card

end Zheng

/-! ## § 3 Mian (面) — Ben × Zheng ≃ Hexagram -/

/-- `Mian := Ben × Zheng = R 2 × R 4 ≃ R 6 = Hexagram`.  This is the
    **R-Family product** that exhibits the 本/征 decomposition of a
    hexagram. -/
abbrev Mian : Type := Ben × Zheng

namespace Mian

/-- |面| = 64. -/
theorem card : Fintype.card Mian = 64 := by
  show Fintype.card (Ben × Zheng) = 64
  rw [Fintype.card_prod, Ben.card, Zheng.card]

end Mian

/-! ## § 4 The Hexagram ↔ Mian isomorphism -/

/-- Combine a Ben (`y1, y2`) and a Zheng (`y3, y4, y5, y6`) into a Hexagram. -/
def toHexagram (m : Mian) : Hexagram :=
  Hexagram.mk m.1.y1 m.1.y2 m.2.y1 m.2.y2 m.2.y3 m.2.y4

/-- Split a Hexagram into its (Ben, Zheng) components. -/
def fromHexagram (h : Hexagram) : Mian :=
  (Ben.mk h.y1 h.y2, Zheng.mk h.y3 h.y4 h.y5 h.y6)

/-! ### § 4.1 Round-trip isomorphism -/

/-- `toHexagram ∘ fromHexagram = id`. -/
theorem toHexagram_fromHexagram (h : Hexagram) :
    toHexagram (fromHexagram h) = h := by
  apply Hexagram.ext <;> rfl

/-- `fromHexagram ∘ toHexagram = id`. -/
theorem fromHexagram_toHexagram (m : Mian) :
    fromHexagram (toHexagram m) = m := by
  cases m with
  | mk b z =>
    show (Ben.mk (Ben.y1 b) (Ben.y2 b),
          Zheng.mk (Zheng.y1 z) (Zheng.y2 z) (Zheng.y3 z) (Zheng.y4 z)) = (b, z)
    congr 1
    · apply Ben.ext <;> rfl
    · apply Zheng.ext <;> rfl

/-! ### § 4.2 Coordinate-level lemmas -/

@[simp] theorem toHexagram_y1 (m : Mian) : (toHexagram m).y1 = m.1.y1 := rfl
@[simp] theorem toHexagram_y2 (m : Mian) : (toHexagram m).y2 = m.1.y2 := rfl
@[simp] theorem toHexagram_y3 (m : Mian) : (toHexagram m).y3 = m.2.y1 := rfl
@[simp] theorem toHexagram_y4 (m : Mian) : (toHexagram m).y4 = m.2.y2 := rfl
@[simp] theorem toHexagram_y5 (m : Mian) : (toHexagram m).y5 = m.2.y3 := rfl
@[simp] theorem toHexagram_y6 (m : Mian) : (toHexagram m).y6 = m.2.y4 := rfl

@[simp] theorem fromHexagram_fst_y1 (h : Hexagram) :
    (fromHexagram h).1.y1 = h.y1 := rfl

@[simp] theorem fromHexagram_fst_y2 (h : Hexagram) :
    (fromHexagram h).1.y2 = h.y2 := rfl

@[simp] theorem fromHexagram_snd_y1 (h : Hexagram) :
    (fromHexagram h).2.y1 = h.y3 := rfl

@[simp] theorem fromHexagram_snd_y2 (h : Hexagram) :
    (fromHexagram h).2.y2 = h.y4 := rfl

@[simp] theorem fromHexagram_snd_y3 (h : Hexagram) :
    (fromHexagram h).2.y3 = h.y5 := rfl

@[simp] theorem fromHexagram_snd_y4 (h : Hexagram) :
    (fromHexagram h).2.y4 = h.y6 := rfl

/-! ## § 5 Ben-of-Hexagram projection (quadrant assignment) -/

/-- The 本 (substrate) of a hexagram: its first 2 yao as a `Ben`. -/
def benOf (h : Hexagram) : Ben := (fromHexagram h).1

/-- The 征 (mark) of a hexagram: its remaining 4 yao as a `Zheng`. -/
def zhengOf (h : Hexagram) : Zheng := (fromHexagram h).2

@[simp] theorem benOf_y1 (h : Hexagram) : (benOf h).y1 = h.y1 := rfl
@[simp] theorem benOf_y2 (h : Hexagram) : (benOf h).y2 = h.y2 := rfl

@[simp] theorem zhengOf_y1 (h : Hexagram) : (zhengOf h).y1 = h.y3 := rfl
@[simp] theorem zhengOf_y2 (h : Hexagram) : (zhengOf h).y2 = h.y4 := rfl
@[simp] theorem zhengOf_y3 (h : Hexagram) : (zhengOf h).y3 = h.y5 := rfl
@[simp] theorem zhengOf_y4 (h : Hexagram) : (zhengOf h).y4 = h.y6 := rfl

/-- Reassembly: `toHexagram (benOf h, zhengOf h) = h`. -/
theorem toHexagram_benOf_zhengOf (h : Hexagram) :
    toHexagram (benOf h, zhengOf h) = h := by
  exact toHexagram_fromHexagram h

/-! ## § 6 Quadrant decomposition: 4 × 16 = 64

The 4 named Ben values `(yangyang, yangyin, yinyang, yinyin)` partition
the 64 hexagrams into 4 equal-size quadrants of 16 hexagrams each. -/

/-- Quadrant label of a hexagram: its 本-projection. -/
def quadrantOf (h : Hexagram) : Ben := benOf h

/-- The list of hexagrams in a given quadrant. -/
def quadrantList (b : Ben) : List Hexagram :=
  Hexagram.allHex.filter (fun h => decide (benOf h = b))

/-- Each named-Ben quadrant has exactly 16 hexagrams. -/
theorem yangyang_quadrant_count :
    (quadrantList Ben.yangyang).length = 16 := by native_decide

theorem yangyin_quadrant_count :
    (quadrantList Ben.yangyin).length = 16 := by native_decide

theorem yinyang_quadrant_count :
    (quadrantList Ben.yinyang).length = 16 := by native_decide

theorem yinyin_quadrant_count :
    (quadrantList Ben.yinyin).length = 16 := by native_decide

/-- The 4 quadrants total 64 hexagrams: complete partition of Hexagram. -/
theorem quadrant_partition_complete :
    (quadrantList Ben.yangyang).length
    + (quadrantList Ben.yangyin).length
    + (quadrantList Ben.yinyang).length
    + (quadrantList Ben.yinyin).length
    = 64 := by native_decide

/-! ## § 7 Sanity tests: distinguished hexagrams + their quadrants -/

/-- 乾為天 (☰☰): all-yang substrate ⇒ quadrant `yangyang`. -/
theorem qianqian_quadrant : quadrantOf Hexagram.qianqian = Ben.yangyang := rfl

/-- 坤為地 (☷☷): all-yin substrate ⇒ quadrant `yinyin`. -/
theorem kunkun_quadrant : quadrantOf Hexagram.kunkun = Ben.yinyin := rfl

/-- 既濟 (☵☲): `(y1, y2) = (yang, yin)` ⇒ quadrant `yangyin`. -/
theorem jiji_quadrant : quadrantOf Hexagram.jiji = Ben.yangyin := rfl

/-- 未濟 (☲☵): `(y1, y2) = (yin, yang)` ⇒ quadrant `yinyang`. -/
theorem weiji_quadrant : quadrantOf Hexagram.weiji = Ben.yinyang := rfl

/-- 4 anchor quadrant assignments bundled. -/
theorem anchor_quadrants :
    quadrantOf Hexagram.qianqian = Ben.yangyang
    ∧ quadrantOf Hexagram.kunkun = Ben.yinyin
    ∧ quadrantOf Hexagram.jiji   = Ben.yangyin
    ∧ quadrantOf Hexagram.weiji  = Ben.yinyang :=
  ⟨qianqian_quadrant, kunkun_quadrant, jiji_quadrant, weiji_quadrant⟩

/-! ## § 8 Operator invariants

The R-Family `cuo` (錯, complement) and `zong` (綜, reverse) operators
on `Hexagram` interact with the 本/征 decomposition in clean ways. -/

/-- `cuo` (complement) flips every yao of `Ben`. -/
theorem benOf_cuo (h : Hexagram) :
    benOf (Hexagram.cuo h) = Ben.mk (!h.y1) (!h.y2) := by
  apply Ben.ext <;> rfl

/-- `cuo` (complement) flips every yao of `Zheng`. -/
theorem zhengOf_cuo (h : Hexagram) :
    zhengOf (Hexagram.cuo h) = Zheng.mk (!h.y3) (!h.y4) (!h.y5) (!h.y6) := by
  apply Zheng.ext <;> rfl

/-- `zong` (reverse) sends the bottom 2 yao to the top 2 (reversed),
    so `benOf (zong h)` reads `(h.y6, h.y5)`. -/
theorem benOf_zong (h : Hexagram) :
    benOf (Hexagram.zong h) = Ben.mk h.y6 h.y5 := by
  apply Ben.ext <;> rfl

/-- `zong` (reverse): the new Zheng reads `(h.y4, h.y3, h.y2, h.y1)`. -/
theorem zhengOf_zong (h : Hexagram) :
    zhengOf (Hexagram.zong h) = Zheng.mk h.y4 h.y3 h.y2 h.y1 := by
  apply Zheng.ext <;> rfl

/-! ## § 9 Public summary -/

/-- **§ 1-8 总结**: the 本/征 decomposition is a clean R-Family product
    isomorphism `R 6 ≃ R 2 × R 4`, with the 4 named substrates
    partitioning Hexagram into 4 × 16 = 64 cells.

    All four anchor hexagrams (乾, 坤, 既濟, 未濟) sit in distinct
    quadrants, witnessing that the 本-projection is non-degenerate. -/
theorem benzheng_summary :
    -- § 4: round-trip isomorphism
    (∀ h : Hexagram, toHexagram (fromHexagram h) = h)
    ∧ (∀ m : Mian, fromHexagram (toHexagram m) = m)
    -- § 6: 4-quadrant partition
    ∧ (quadrantList Ben.yangyang).length = 16
    ∧ (quadrantList Ben.yangyin).length  = 16
    ∧ (quadrantList Ben.yinyang).length  = 16
    ∧ (quadrantList Ben.yinyin).length   = 16
    -- § 7: anchors in 4 distinct quadrants
    ∧ quadrantOf Hexagram.qianqian = Ben.yangyang
    ∧ quadrantOf Hexagram.kunkun   = Ben.yinyin
    ∧ quadrantOf Hexagram.jiji     = Ben.yangyin
    ∧ quadrantOf Hexagram.weiji    = Ben.yinyang :=
  ⟨toHexagram_fromHexagram, fromHexagram_toHexagram,
   yangyang_quadrant_count, yangyin_quadrant_count,
   yinyang_quadrant_count, yinyin_quadrant_count,
   qianqian_quadrant, kunkun_quadrant, jiji_quadrant, weiji_quadrant⟩

end SSBX.Foundation.Atlas.Yi.BenZheng
