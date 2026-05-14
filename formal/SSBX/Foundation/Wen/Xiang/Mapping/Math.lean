/-
# Wen.Xiang.Mapping.Math — V₄ Klein-group reading of `Image`

`wen-algebra` v0.4 §0.2 / §1.1: the atomic `Image` carrier is the Klein
four-group `V₄ = (Z/2)²`.  Standard mathematical notation uses
`{e, a, b, ab}` for the four atoms, which this module exposes as
abbreviations on top of the bit-pattern primary names.

| Lean       | bit       | F₂² coord | 文        |
|------------|-----------|-----------|-----------|
| `e`        | `Image.oo`| (0, 0)    | 道         |
| `a`        | `Image.xo`| (1, 0)    | 错         |
| `b`        | `Image.ox`| (0, 1)    | 综         |
| `ab`       | `Image.xx`| (1, 1)    | 错综       |

`abbrev`s keep the V₄-named view definitionally equal to its
bit-pattern source, so the V₄ multiplication table is `decide`-able and
all `Image` lemmas apply through the alias.
-/

import SSBX.Foundation.Wen.Xiang.Image

namespace SSBX.Foundation.Wen.Xiang.Mapping.Math

open SSBX.Foundation.Wen.Xiang

/-! ## § 1 V₄ atoms (Math notation) -/

/-- The V₄ identity (= 道, Identity, dao, Pauli I).  Bit pattern `oo`. -/
abbrev e : Image := .oo

/-- The α-axis V₄ generator (= 错, ContentFlip, cuo, Pauli X).
    Bit pattern `xo`. -/
abbrev a : Image := .xo

/-- The β-axis V₄ generator (= 综, FrameFlip, zong, Pauli Z).
    Bit pattern `ox`. -/
abbrev b : Image := .ox

/-- The diagonal `a · b` (= 错综, CompoundFlip, cuozong, Pauli Y).
    Bit pattern `xx`. -/
abbrev ab : Image := .xx

/-! ## § 2 V₄ multiplication table — verifiable by `decide` -/

example : e * a = a := by decide
example : a * e = a := by decide
example : a * a = e := by decide
example : b * b = e := by decide
example : ab * ab = e := by decide
example : a * b = ab := by decide
example : b * a = ab := by decide
example : a * ab = b := by decide
example : ab * a = b := by decide
example : b * ab = a := by decide
example : ab * b = a := by decide

/-! ## § 3 Listing -/

/-- All four V₄ atoms in canonical Math order: `e, a, b, ab`. -/
def all : List Image := [e, a, b, ab]

theorem all_length : all.length = 4 := rfl
theorem all_eq_image_all : all = Image.all := rfl

end SSBX.Foundation.Wen.Xiang.Mapping.Math
