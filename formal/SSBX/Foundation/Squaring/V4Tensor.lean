/-
# V₄ Tensor — R₈ ≅ V₄⁴

This module is the first Mathlib-facing bridge for the Cell256 carrier.
Foundation files keep Mathlib imports out; here we bind the already-proved
Cell256 XOR laws to `Fintype` and `AddCommGroup` instances, then expose the
four Klein-four axes of R₈.
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Basic
import SSBX.Foundation.Bagua.Cell256
import SSBX.Foundation.Hierarchy.LiftProject

namespace SSBX.Foundation.Squaring

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256

namespace V4Tensor

/-! ## Local Mathlib instances for existing carriers -/

instance instFintypeYao : Fintype Yao where
  elems := [Yao.yang, Yao.yin].toFinset
  complete := by
    intro y
    cases y <;> simp

instance instAddYao : Add Yao := ⟨Cell256.yaoXor⟩
instance instZeroYao : Zero Yao := ⟨Yao.yang⟩
instance instNegYao : Neg Yao := ⟨id⟩
instance instSubYao : Sub Yao := ⟨Cell256.yaoXor⟩

@[simp] theorem yao_add_eq_xor (a b : Yao) : a + b = Cell256.yaoXor a b := rfl

instance instAddCommGroupYao : AddCommGroup Yao where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  zero_add := by
    intro a
    cases a <;> rfl
  add_zero := by
    intro a
    cases a <;> rfl
  neg_add_cancel := by
    intro a
    cases a <;> rfl
  add_comm := by
    intro a b
    cases a <;> cases b <;> rfl

noncomputable instance instFintypeCell256 : Fintype Cell256 := by
  classical
  exact
    { elems := Cell256.all.toFinset
      complete := by
        intro c
        exact List.mem_toFinset.mpr (Cell256.mem_all c) }

instance instAddCommGroupCell256 : AddCommGroup Cell256 where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := Cell256.xor_assoc
  zero_add := Cell256.origin_xor
  add_zero := Cell256.xor_origin
  neg_add_cancel := by
    intro c
    simpa [Cell256.neg_def] using Cell256.xor_self c
  add_comm := Cell256.xor_comm

/-! ## Generic V₄ carrier and the third-axis alias -/

/-- Generic Klein-four carrier represented as two Yao bits. -/
abbrev V4 : Type := Yao × Yao

/-- Third V₄ axis from `(y₅,y₆)`. The doctrine-level name remains open. -/
abbrev OuterMian : Type := V4

def boolToYao : Bool → Yao
  | false => Yao.yang
  | true => Yao.yin

def yaoToBool : Yao → Bool
  | Yao.yang => false
  | Yao.yin => true

@[simp] theorem boolToYao_yaoToBool (y : Yao) : boolToYao (yaoToBool y) = y := by
  cases y <;> rfl

@[simp] theorem yaoToBool_boolToYao (b : Bool) : yaoToBool (boolToYao b) = b := by
  cases b <;> rfl

@[simp] theorem boolToYao_xor (a b : Bool) :
    boolToYao (Bool.xor a b) = boolToYao a + boolToYao b := by
  cases a <;> cases b <;> rfl

def shiToV4 (s : Shi) : V4 :=
  (boolToYao (Shi.toYinGuo s).1, boolToYao (Shi.toYinGuo s).2)

def v4ToShi (v : V4) : Shi :=
  Shi.ofYinGuo (yaoToBool v.1, yaoToBool v.2)

@[simp] theorem v4ToShi_shiToV4 (s : Shi) : v4ToShi (shiToV4 s) = s := by
  rcases s with ⟨yin, guo⟩
  cases yin <;> cases guo <;> rfl

@[simp] theorem shiToV4_v4ToShi (v : V4) : shiToV4 (v4ToShi v) = v := by
  rcases v with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-! ## Main equivalence: Cell256 ≃+ V₄⁴ -/

def toV4Quad (c : Cell256) : V4 × V4 × V4 × V4 :=
  ((c.1.y1, c.1.y2), (c.1.y3, c.1.y4), (c.1.y5, c.1.y6), shiToV4 c.2)

def ofV4Quad : V4 × V4 × V4 × V4 → Cell256
  | ((y1, y2), (y3, y4), (y5, y6), shi) =>
      (⟨y1, y2, y3, y4, y5, y6⟩, v4ToShi shi)

theorem to_of (q : V4 × V4 × V4 × V4) : toV4Quad (ofV4Quad q) = q := by
  rcases q with ⟨⟨y1, y2⟩, ⟨y3, y4⟩, ⟨y5, y6⟩, ⟨s1, s2⟩⟩
  cases s1 <;> cases s2 <;> rfl

theorem of_to (c : Cell256) : ofV4Quad (toV4Quad c) = c := by
  rcases c with ⟨h, s⟩
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  rcases s with ⟨yin, guo⟩
  cases yin <;> cases guo <;> rfl

def iso : Cell256 ≃+ (V4 × V4 × V4 × V4) where
  toFun := toV4Quad
  invFun := ofV4Quad
  left_inv := of_to
  right_inv := to_of
  map_add' := by
    intro a b
    rcases a with ⟨ha, sa⟩
    rcases b with ⟨hb, sb⟩
    rcases ha with ⟨a1, a2, a3, a4, a5, a6⟩
    rcases hb with ⟨b1, b2, b3, b4, b5, b6⟩
    rcases sa with ⟨ay, ag⟩
    rcases sb with ⟨byin, bg⟩
    simp [toV4Quad, Cell256.add_def, Cell256.xor, Cell256.hexXor,
      Cell256.shiXor, Shi.toYinGuo, Shi.ofYinGuo, shiToV4]

theorem origin_toV4Quad :
    toV4Quad Cell256.origin =
      ((Yao.yang, Yao.yang), (Yao.yang, Yao.yang),
       (Yao.yang, Yao.yang), (Yao.yang, Yao.yang)) := rfl

theorem v4_tensor_summary :
    (∀ c : Cell256, ofV4Quad (toV4Quad c) = c)
    ∧ (∀ q : V4 × V4 × V4 × V4, toV4Quad (ofV4Quad q) = q)
    ∧ toV4Quad Cell256.origin =
      ((Yao.yang, Yao.yang), (Yao.yang, Yao.yang),
       (Yao.yang, Yao.yang), (Yao.yang, Yao.yang)) :=
  ⟨of_to, to_of, origin_toV4Quad⟩

end V4Tensor

end SSBX.Foundation.Squaring
