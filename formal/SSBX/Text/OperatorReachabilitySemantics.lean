import SSBX.Foundation.Bagua.R8

/-!
# OperatorReachabilitySemantics — seven generators over `R8`

This file defines the conservative reachability generator family used by the
256-cell layer: six line flips plus one `shiNext` step.

## Phase F.2 migration note (Cell192 → R8)

Previously this module operated on `Cell192 = Hexagram × Shi(Z/3)` with the
`shiNext` generator implementing the Z/3 cycle 已→今→未→已 (`shiNext^[3] = id`).

After Phase F doctrine alignment, `Shi` is the V₄ Klein four-group
`{道, 已, 今, 未}` and `R8 = Hexagram × Shi(V₄)` (256 cells). V₄ has no
canonical cyclic order, so `shiNext` is now the V₄ `Shi.complement` involution
(因-axis toggle 道↔已, 今↔未). It is order-2 rather than order-3.

The inductive type names `Cell192Generator` and `Cell192TransitionOperator`
are intentionally retained as legacy stable identifiers (downstream
`OperatorCellMap` depends on `Cell192Generator.all_length` and friends).
The constructors and apply target now operate on `R8` and match the
post-migration semantics.
-/

namespace SSBX.Text.OperatorReachabilitySemantics

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaAlgebra

/-- The six line-flip generators as their own indexed family. -/
inductive LineFlipGenerator where
  | flip1
  | flip2
  | flip3
  | flip4
  | flip5
  | flip6
  deriving Repr, DecidableEq, BEq

namespace LineFlipGenerator

/-- Apply one line-flip generator to a `R8`. -/
def apply : LineFlipGenerator → R8 → R8
  | .flip1, c => R8.flip1 c
  | .flip2, c => R8.flip2 c
  | .flip3, c => R8.flip3 c
  | .flip4, c => R8.flip4 c
  | .flip5, c => R8.flip5 c
  | .flip6, c => R8.flip6 c

end LineFlipGenerator

/--
The seven elementary reachability generators on `R8`.

Legacy name kept stable for downstream `OperatorCellMap`. The generator
`shiNext` is now the V₄ `Shi.complement` involution (post-Phase F.2), not the
Z/3 cycle of the legacy 192-cell layer.
-/
inductive Cell192Generator where
  | flip1
  | flip2
  | flip3
  | flip4
  | flip5
  | flip6
  | shiNext
  deriving Repr, DecidableEq, BEq

namespace Cell192Generator

/-- Embed a line-flip generator into the full seven-generator family. -/
def lineFlip : LineFlipGenerator → Cell192Generator
  | .flip1 => .flip1
  | .flip2 => .flip2
  | .flip3 => .flip3
  | .flip4 => .flip4
  | .flip5 => .flip5
  | .flip6 => .flip6

/-- Compact generator key for the 256-cell transition index. -/
def key : Cell192Generator → String
  | .flip1 => "L1"
  | .flip2 => "L2"
  | .flip3 => "L3"
  | .flip4 => "L4"
  | .flip5 => "L5"
  | .flip6 => "L6"
  | .shiNext => "T+"

/-- Short Chinese name for the 256-cell transition index. -/
def zhName : Cell192Generator → String
  | .flip1 => "翻初爻"
  | .flip2 => "翻二爻"
  | .flip3 => "翻三爻"
  | .flip4 => "翻四爻"
  | .flip5 => "翻五爻"
  | .flip6 => "翻上爻"
  | .shiNext => "时态翻转"

/-- Lean operator reference used by generated documentation. -/
def operatorRef : Cell192Generator → String
  | .flip1 => "R8.flip1"
  | .flip2 => "R8.flip2"
  | .flip3 => "R8.flip3"
  | .flip4 => "R8.flip4"
  | .flip5 => "R8.flip5"
  | .flip6 => "R8.flip6"
  | .shiNext => "R8.shiCuo"

/-- Concrete one-step effect of a generator on a 256-cell position. -/
def effectSummary : Cell192Generator → String
  | .flip1 => "翻转初爻，保持时态。"
  | .flip2 => "翻转二爻，保持时态。"
  | .flip3 => "翻转三爻，保持时态。"
  | .flip4 => "翻转四爻，保持时态。"
  | .flip5 => "翻转五爻，保持时态。"
  | .flip6 => "翻转上爻，保持时态。"
  | .shiNext => "卦象不变，时态按 V₄ 因-轴翻转 (道↔已, 今↔未)。"

/-- The complete seven-generator list. -/
def all : List Cell192Generator :=
  [.flip1, .flip2, .flip3, .flip4, .flip5, .flip6, .shiNext]

/-- Apply one reachability generator to a `R8`. -/
def apply : Cell192Generator → R8 → R8
  | .flip1, c => R8.flip1 c
  | .flip2, c => R8.flip2 c
  | .flip3, c => R8.flip3 c
  | .flip4, c => R8.flip4 c
  | .flip5, c => R8.flip5 c
  | .flip6, c => R8.flip6 c
  | .shiNext, c => R8.shiCuo c

theorem all_length : all.length = 7 := by
  native_decide

theorem all_nodup : all.Nodup := by
  native_decide

theorem lineFlip_flip1 : lineFlip .flip1 = .flip1 := rfl
theorem lineFlip_flip2 : lineFlip .flip2 = .flip2 := rfl
theorem lineFlip_flip3 : lineFlip .flip3 = .flip3 := rfl
theorem lineFlip_flip4 : lineFlip .flip4 = .flip4 := rfl
theorem lineFlip_flip5 : lineFlip .flip5 = .flip5 := rfl
theorem lineFlip_flip6 : lineFlip .flip6 = .flip6 := rfl

theorem apply_flip1 (c : R8) : apply .flip1 c = R8.flip1 c := rfl
theorem apply_flip2 (c : R8) : apply .flip2 c = R8.flip2 c := rfl
theorem apply_flip3 (c : R8) : apply .flip3 c = R8.flip3 c := rfl
theorem apply_flip4 (c : R8) : apply .flip4 c = R8.flip4 c := rfl
theorem apply_flip5 (c : R8) : apply .flip5 c = R8.flip5 c := rfl
theorem apply_flip6 (c : R8) : apply .flip6 c = R8.flip6 c := rfl
theorem apply_shiNext (c : R8) : apply .shiNext c = R8.shiCuo c := rfl

theorem lineFlip_apply_preserves_shi (g : LineFlipGenerator) (c : R8) :
    (apply (lineFlip g) c).2 = c.2 := by
  cases g <;> rcases c with ⟨h, s⟩ <;> rfl

theorem flip1_preserves_shi (c : R8) : (apply .flip1 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip2_preserves_shi (c : R8) : (apply .flip2 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip3_preserves_shi (c : R8) : (apply .flip3 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip4_preserves_shi (c : R8) : (apply .flip4 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip5_preserves_shi (c : R8) : (apply .flip5 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip6_preserves_shi (c : R8) : (apply .flip6 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem shiNext_preserves_hexagram (c : R8) :
    (apply .shiNext c).1 = c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem shiNext_updates_shi (c : R8) :
    (apply .shiNext c).2 = c.2.complement := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip1_updates_hexagram (c : R8) :
    (apply .flip1 c).1 = dongInner c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip2_updates_hexagram (c : R8) :
    (apply .flip2 c).1 = middleFlipInner c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip3_updates_hexagram (c : R8) :
    (apply .flip3 c).1 = topFlipInner c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip4_updates_hexagram (c : R8) :
    (apply .flip4 c).1 = dongOuter c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip5_updates_hexagram (c : R8) :
    (apply .flip5 c).1 = middleFlipOuter c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip6_updates_hexagram (c : R8) :
    (apply .flip6 c).1 = topFlipOuter c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip1_involutive (c : R8) : apply .flip1 (apply .flip1 c) = c :=
  R8.flip1_flip1 c

theorem flip2_involutive (c : R8) : apply .flip2 (apply .flip2 c) = c :=
  R8.flip2_flip2 c

theorem flip3_involutive (c : R8) : apply .flip3 (apply .flip3 c) = c :=
  R8.flip3_flip3 c

theorem flip4_involutive (c : R8) : apply .flip4 (apply .flip4 c) = c :=
  R8.flip4_flip4 c

theorem flip5_involutive (c : R8) : apply .flip5 (apply .flip5 c) = c :=
  R8.flip5_flip5 c

theorem flip6_involutive (c : R8) : apply .flip6 (apply .flip6 c) = c :=
  R8.flip6_flip6 c

theorem lineFlip_involutive (g : LineFlipGenerator) (c : R8) :
    apply (lineFlip g) (apply (lineFlip g) c) = c := by
  cases g
  · exact flip1_involutive c
  · exact flip2_involutive c
  · exact flip3_involutive c
  · exact flip4_involutive c
  · exact flip5_involutive c
  · exact flip6_involutive c

/--
Post-migration: `shiNext` is the V₄ `Shi.complement` involution (order 2),
replacing the legacy Z/3 cycle (order 3) of `Cell192`. -/
theorem shiNext_involutive (c : R8) :
    apply .shiNext (apply .shiNext c) = c :=
  R8.shiCuo_shiCuo c

/--
Summary: the reachability layer has seven distinct generators; the six line
generators preserve `Shi` and are involutive, while `shiNext` preserves the
hexagram component and is now an involution (V₄ `Shi.complement`, order 2 — was
order 3 in the legacy Z/3 cycle).
-/
theorem cell256_generator_summary :
    all.length = 7
    ∧ all.Nodup
    ∧ (∀ g : LineFlipGenerator, ∀ c : R8, (apply (lineFlip g) c).2 = c.2)
    ∧ (∀ c : R8, (apply .shiNext c).1 = c.1)
    ∧ (∀ c : R8, (apply .shiNext c).2 = c.2.complement)
    ∧ (∀ g : LineFlipGenerator, ∀ c : R8,
        apply (lineFlip g) (apply (lineFlip g) c) = c)
    ∧ (∀ c : R8, apply .shiNext (apply .shiNext c) = c) := by
  exact
    ⟨ all_length
    , all_nodup
    , lineFlip_apply_preserves_shi
    , shiNext_preserves_hexagram
    , shiNext_updates_shi
    , lineFlip_involutive
    , shiNext_involutive
    ⟩

end Cell192Generator

/-! ## Named deterministic transition operators on R8 -/

/--
Named one-step transition operators on `R8`.

Legacy name kept stable for documentation/index purposes. Post Phase F.2:
`shiNext` and `shiPrev` both collapse to the V₄ `Shi.complement` involution
(any V₄ involution is its own inverse). They are retained as distinct
inhabitants of this enumeration to keep the transition-index documentation
schema stable.
-/
inductive Cell192TransitionOperator where
  | flip1
  | flip2
  | flip3
  | flip4
  | flip5
  | flip6
  | shiNext
  | shiPrev
  | hexCuo
  | hexZong
  | hexHu
  deriving Repr, DecidableEq, BEq

namespace Cell192TransitionOperator

/-- Compact operator key for the 256-cell transition index. -/
def key : Cell192TransitionOperator → String
  | .flip1 => "L1"
  | .flip2 => "L2"
  | .flip3 => "L3"
  | .flip4 => "L4"
  | .flip5 => "L5"
  | .flip6 => "L6"
  | .shiNext => "T+"
  | .shiPrev => "T-"
  | .hexCuo => "CUO"
  | .hexZong => "ZONG"
  | .hexHu => "HU"

/-- Short Chinese name for the 256-cell transition index. -/
def zhName : Cell192TransitionOperator → String
  | .flip1 => "翻初爻"
  | .flip2 => "翻二爻"
  | .flip3 => "翻三爻"
  | .flip4 => "翻四爻"
  | .flip5 => "翻五爻"
  | .flip6 => "翻上爻"
  | .shiNext => "时态翻转"
  | .shiPrev => "时态翻转"
  | .hexCuo => "错卦"
  | .hexZong => "综卦"
  | .hexHu => "互卦"

/-- Lean operator reference used by generated documentation. -/
def operatorRef : Cell192TransitionOperator → String
  | .flip1 => "R8.flip1"
  | .flip2 => "R8.flip2"
  | .flip3 => "R8.flip3"
  | .flip4 => "R8.flip4"
  | .flip5 => "R8.flip5"
  | .flip6 => "R8.flip6"
  | .shiNext => "R8.shiCuo"
  | .shiPrev => "R8.shiCuo"
  | .hexCuo => "R8.hexCuo"
  | .hexZong => "R8.hexZong"
  | .hexHu => "R8.hexHu"

/-- Concrete one-step effect of a named operator on a 256-cell position. -/
def effectSummary : Cell192TransitionOperator → String
  | .flip1 => "翻转初爻，保持时态。"
  | .flip2 => "翻转二爻，保持时态。"
  | .flip3 => "翻转三爻，保持时态。"
  | .flip4 => "翻转四爻，保持时态。"
  | .flip5 => "翻转五爻，保持时态。"
  | .flip6 => "翻转上爻，保持时态。"
  | .shiNext => "卦象不变，时态按 V₄ 因-轴翻转 (道↔已, 今↔未)。"
  | .shiPrev => "卦象不变，时态按 V₄ 因-轴翻转 (V₄ 涉自逆，与 shiNext 同操作)。"
  | .hexCuo => "六爻全反，保持时态。"
  | .hexZong => "六爻上下反序，保持时态。"
  | .hexHu => "取二三四、三四五成互卦，保持时态。"

/-- The named deterministic transition-operator list. -/
def all : List Cell192TransitionOperator :=
  [.flip1, .flip2, .flip3, .flip4, .flip5, .flip6,
   .shiNext, .shiPrev, .hexCuo, .hexZong, .hexHu]

/-- Apply one named transition operator to a `R8`. -/
def apply : Cell192TransitionOperator → R8 → R8
  | .flip1, c => R8.flip1 c
  | .flip2, c => R8.flip2 c
  | .flip3, c => R8.flip3 c
  | .flip4, c => R8.flip4 c
  | .flip5, c => R8.flip5 c
  | .flip6, c => R8.flip6 c
  | .shiNext, c => R8.shiCuo c
  | .shiPrev, c => R8.shiCuo c
  | .hexCuo, c => R8.hexCuo c
  | .hexZong, c => R8.hexZong c
  | .hexHu, c => R8.hexHu c

theorem all_length : all.length = 11 := by
  native_decide

theorem all_nodup : all.Nodup := by
  native_decide

end Cell192TransitionOperator

end SSBX.Text.OperatorReachabilitySemantics
