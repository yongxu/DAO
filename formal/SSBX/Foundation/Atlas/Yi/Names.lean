/-
# Foundation.Atlas.Yi.Names — Yi naming bridge on R-Family carriers

Per `wen-algebra` v0.6 §9 (Atlas separation) and `v4-foundation` v0.5
§15 (external traditions):

    Yao        ≃  Bool          = R 1
    Trigram    ≃  Fin 3 → Bool  = R 3
    Hexagram   ≃  Fin 6 → Bool  = R 6
    Shi (V₄)   ≃  Fin 2 → Bool  = R 2

This module is an **application-layer overlay** on top of the
language-independent `R_N := Fin N → Bool` core (`Foundation/R/`).  No
Yi naming appears in `Foundation/R/`; everything Yi-flavoured lives
here in `Foundation/Atlas/Yi/`.

## Bit-pattern convention

Per the project convention used throughout `Foundation/R/Basic.lean`:

    o = false = yang (阳)
    x = true  = yin  (阴)

The 8 trigram names (Bagua) and the 64 hexagram names sit on top of
this single bit assignment; see `Bagua.lean` and `Hexagrams.lean` for
the concrete name → `R N` value tables.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9 (Atlas separation).
* `v4-foundation.md` v0.5 §15 (external-tradition bindings).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Atlas.Yi

open SSBX.Foundation.R

/-! ## § 1 Yao (爻) — the bit -/

/-- 爻 (yáo): the binary atom of 周易.  Per `wen-algebra` v0.6, Yao is
    just the language-independent bit `Bool = R 1`.  Yi naming comes in
    via the two `@[match_pattern]` defs `Yao.yang` and `Yao.yin`. -/
abbrev Yao : Type := Bool

namespace Yao

/-- `yang` (阳, ⚊) = `false`.  Per project convention `o = false = yang`. -/
@[match_pattern] def yang : Yao := false

/-- `yin` (阴, ⚋) = `true`.  Per project convention `x = true = yin`. -/
@[match_pattern] def yin : Yao := true

/-- 错 on a single yao (atomic negation): yang ↔ yin. -/
def neg : Yao → Yao
  | yang => yin
  | yin  => yang

@[simp] theorem neg_yang : neg yang = yin := rfl
@[simp] theorem neg_yin  : neg yin  = yang := rfl

/-- 错 is involutive on a single yao. -/
theorem neg_neg (y : Yao) : neg (neg y) = y := by
  cases y <;> rfl

end Yao

/-! ## § 2 Trigram (T₃ / 八卦) — R 3 -/

/-- 三爻卦 (trigram): `R 3 = Fin 3 → Bool`.  Per `wen-algebra` v0.6,
    the trigram type is exactly `R 3`; the 8 traditional names live in
    `Atlas/Yi/Bagua.lean`. -/
abbrev Trigram : Type := R 3

namespace Trigram

/-- Read the 1st yao (初爻, bottom). -/
def y1 (t : Trigram) : Yao := t ⟨0, by decide⟩

/-- Read the 2nd yao (中爻). -/
def y2 (t : Trigram) : Yao := t ⟨1, by decide⟩

/-- Read the 3rd yao (上爻, top). -/
def y3 (t : Trigram) : Yao := t ⟨2, by decide⟩

/-- Build a trigram from its three yao components.  `mk a b c` has
    `y1 = a, y2 = b, y3 = c`. -/
def mk (a b c : Yao) : Trigram := fun i =>
  match i with
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

@[simp] theorem y1_mk (a b c : Yao) : y1 (mk a b c) = a := rfl
@[simp] theorem y2_mk (a b c : Yao) : y2 (mk a b c) = b := rfl
@[simp] theorem y3_mk (a b c : Yao) : y3 (mk a b c) = c := rfl

/-- Trigram extensionality through its 3 yao components. -/
theorem ext (t u : Trigram) (h1 : y1 t = y1 u) (h2 : y2 t = y2 u)
    (h3 : y3 t = y3 u) : t = u := by
  funext i
  match i with
  | ⟨0, _⟩ => exact h1
  | ⟨1, _⟩ => exact h2
  | ⟨2, _⟩ => exact h3

/-- Legacy-compat positional read: `t.positions i = t i`. -/
def positions (t : Trigram) (i : Fin 3) : Yao := t i

/-- Function-form constructor: a `Trigram` is exactly a `Fin 3 → Yao`. -/
def ofFn (fn : Fin 3 → Yao) : Trigram := fn

end Trigram

/-! ## § 3 Hexagram (T₆ / 六十四卦) — R 6 -/

/-- 六爻卦 (hexagram): `R 6 = Fin 6 → Bool`.  Per `wen-algebra` v0.6,
    the hexagram type is exactly `R 6`; the 64 traditional names live
    in `Atlas/Yi/Hexagrams.lean`. -/
abbrev Hexagram : Type := R 6

namespace Hexagram

/-- 1st yao (初爻, bottom). -/
def y1 (h : Hexagram) : Yao := h ⟨0, by decide⟩
/-- 2nd yao. -/
def y2 (h : Hexagram) : Yao := h ⟨1, by decide⟩
/-- 3rd yao (top of 内卦, inner trigram). -/
def y3 (h : Hexagram) : Yao := h ⟨2, by decide⟩
/-- 4th yao (bottom of 外卦, outer trigram). -/
def y4 (h : Hexagram) : Yao := h ⟨3, by decide⟩
/-- 5th yao. -/
def y5 (h : Hexagram) : Yao := h ⟨4, by decide⟩
/-- 6th yao (上爻, top). -/
def y6 (h : Hexagram) : Yao := h ⟨5, by decide⟩

/-- Build a hexagram from its six yao components.  `mk a b c d e f`
    has `y1 = a, …, y6 = f`. -/
def mk (a b c d e f : Yao) : Hexagram := fun i =>
  match i with
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d
  | ⟨4, _⟩ => e
  | ⟨5, _⟩ => f

@[simp] theorem y1_mk (a b c d e f : Yao) : y1 (mk a b c d e f) = a := rfl
@[simp] theorem y2_mk (a b c d e f : Yao) : y2 (mk a b c d e f) = b := rfl
@[simp] theorem y3_mk (a b c d e f : Yao) : y3 (mk a b c d e f) = c := rfl
@[simp] theorem y4_mk (a b c d e f : Yao) : y4 (mk a b c d e f) = d := rfl
@[simp] theorem y5_mk (a b c d e f : Yao) : y5 (mk a b c d e f) = e := rfl
@[simp] theorem y6_mk (a b c d e f : Yao) : y6 (mk a b c d e f) = f := rfl

/-- Hexagram extensionality through its 6 yao components. -/
theorem ext (h k : Hexagram) (h1 : y1 h = y1 k) (h2 : y2 h = y2 k)
    (h3 : y3 h = y3 k) (h4 : y4 h = y4 k) (h5 : y5 h = y5 k)
    (h6 : y6 h = y6 k) : h = k := by
  funext i
  match i with
  | ⟨0, _⟩ => exact h1
  | ⟨1, _⟩ => exact h2
  | ⟨2, _⟩ => exact h3
  | ⟨3, _⟩ => exact h4
  | ⟨4, _⟩ => exact h5
  | ⟨5, _⟩ => exact h6

/-- 内卦 (inner trigram): the lower 3 yao = `y1 / y2 / y3`. -/
def innerTrigram (h : Hexagram) : Trigram := Trigram.mk h.y1 h.y2 h.y3

/-- 外卦 (outer trigram): the upper 3 yao = `y4 / y5 / y6`. -/
def outerTrigram (h : Hexagram) : Trigram := Trigram.mk h.y4 h.y5 h.y6

/-- Legacy-compat positional read: `h.positions i = h i`. -/
def positions (h : Hexagram) (i : Fin 6) : Yao := h i

/-- Function-form constructor: a `Hexagram` is exactly a `Fin 6 → Yao`. -/
def ofFn (fn : Fin 6 → Yao) : Hexagram := fn

/-- ⊕ : 内卦 → 外卦 → hexagram.
    inner is below (y1, y2, y3); outer is above (y4, y5, y6).
    Non-commutative in general. -/
def oplus (inner outer : Trigram) : Hexagram :=
  mk inner.y1 inner.y2 inner.y3 outer.y1 outer.y2 outer.y3

@[simp] theorem innerTrigram_oplus (a b : Trigram) :
    (oplus a b).innerTrigram = a := by
  apply Trigram.ext <;> rfl

@[simp] theorem outerTrigram_oplus (a b : Trigram) :
    (oplus a b).outerTrigram = b := by
  apply Trigram.ext <;> rfl

end Hexagram

/-! ## § 4 Shi (时态, V₄) — R 2 -/

/-- 时态 (Shí, "state"): the R 2 Klein-four group `R 2 = Fin 2 → Bool`.
    Per `wen-algebra` v0.6, Shi is exactly `R 2`; the 4 traditional
    names live in `Atlas/Yi/Shi.lean`. -/
abbrev Shi : Type := R 2

end SSBX.Foundation.Atlas.Yi
