import SSBX.Foundation.Bagua.Cell192

/-!
# OperatorReachabilitySemantics — seven generators over `Cell192`

This file defines the conservative reachability generator family used by the
192-cell layer: six line flips plus one cyclic `shiNext` step.
-/

namespace SSBX.Text.OperatorReachabilitySemantics

open SSBX.Foundation.Bagua.Cell192
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

/-- Apply one line-flip generator to a `Cell192`. -/
def apply : LineFlipGenerator → Cell192 → Cell192
  | .flip1, c => Cell192.flip1 c
  | .flip2, c => Cell192.flip2 c
  | .flip3, c => Cell192.flip3 c
  | .flip4, c => Cell192.flip4 c
  | .flip5, c => Cell192.flip5 c
  | .flip6, c => Cell192.flip6 c

end LineFlipGenerator

/-- The seven elementary reachability generators on `Cell192`. -/
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

/-- Compact generator key for the 192-cell transition index. -/
def key : Cell192Generator → String
  | .flip1 => "L1"
  | .flip2 => "L2"
  | .flip3 => "L3"
  | .flip4 => "L4"
  | .flip5 => "L5"
  | .flip6 => "L6"
  | .shiNext => "T+"

/-- Short Chinese name for the 192-cell transition index. -/
def zhName : Cell192Generator → String
  | .flip1 => "翻初爻"
  | .flip2 => "翻二爻"
  | .flip3 => "翻三爻"
  | .flip4 => "翻四爻"
  | .flip5 => "翻五爻"
  | .flip6 => "翻上爻"
  | .shiNext => "时态前进"

/-- Lean operator reference used by generated documentation. -/
def operatorRef : Cell192Generator → String
  | .flip1 => "Cell192.flip1"
  | .flip2 => "Cell192.flip2"
  | .flip3 => "Cell192.flip3"
  | .flip4 => "Cell192.flip4"
  | .flip5 => "Cell192.flip5"
  | .flip6 => "Cell192.flip6"
  | .shiNext => "Cell192.shiNext"

/-- Concrete one-step effect of a generator on a 192-cell position. -/
def effectSummary : Cell192Generator → String
  | .flip1 => "翻转初爻，保持时态。"
  | .flip2 => "翻转二爻，保持时态。"
  | .flip3 => "翻转三爻，保持时态。"
  | .flip4 => "翻转四爻，保持时态。"
  | .flip5 => "翻转五爻，保持时态。"
  | .flip6 => "翻转上爻，保持时态。"
  | .shiNext => "卦象不变，时态按 已→今→未→已 前进。"

/-- The complete seven-generator list. -/
def all : List Cell192Generator :=
  [.flip1, .flip2, .flip3, .flip4, .flip5, .flip6, .shiNext]

/-- Apply one reachability generator to a `Cell192`. -/
def apply : Cell192Generator → Cell192 → Cell192
  | .flip1, c => Cell192.flip1 c
  | .flip2, c => Cell192.flip2 c
  | .flip3, c => Cell192.flip3 c
  | .flip4, c => Cell192.flip4 c
  | .flip5, c => Cell192.flip5 c
  | .flip6, c => Cell192.flip6 c
  | .shiNext, c => Cell192.shiNext c

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

theorem apply_flip1 (c : Cell192) : apply .flip1 c = Cell192.flip1 c := rfl
theorem apply_flip2 (c : Cell192) : apply .flip2 c = Cell192.flip2 c := rfl
theorem apply_flip3 (c : Cell192) : apply .flip3 c = Cell192.flip3 c := rfl
theorem apply_flip4 (c : Cell192) : apply .flip4 c = Cell192.flip4 c := rfl
theorem apply_flip5 (c : Cell192) : apply .flip5 c = Cell192.flip5 c := rfl
theorem apply_flip6 (c : Cell192) : apply .flip6 c = Cell192.flip6 c := rfl
theorem apply_shiNext (c : Cell192) : apply .shiNext c = Cell192.shiNext c := rfl

theorem lineFlip_apply_preserves_shi (g : LineFlipGenerator) (c : Cell192) :
    (apply (lineFlip g) c).2 = c.2 := by
  cases g <;> rcases c with ⟨h, s⟩ <;> rfl

theorem flip1_preserves_shi (c : Cell192) : (apply .flip1 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip2_preserves_shi (c : Cell192) : (apply .flip2 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip3_preserves_shi (c : Cell192) : (apply .flip3 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip4_preserves_shi (c : Cell192) : (apply .flip4 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip5_preserves_shi (c : Cell192) : (apply .flip5 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip6_preserves_shi (c : Cell192) : (apply .flip6 c).2 = c.2 := by
  rcases c with ⟨h, s⟩
  rfl

theorem shiNext_preserves_hexagram (c : Cell192) :
    (apply .shiNext c).1 = c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem shiNext_updates_shi (c : Cell192) :
    (apply .shiNext c).2 = c.2.next := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip1_updates_hexagram (c : Cell192) :
    (apply .flip1 c).1 = dongInner c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip2_updates_hexagram (c : Cell192) :
    (apply .flip2 c).1 = huaInner c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip3_updates_hexagram (c : Cell192) :
    (apply .flip3 c).1 = bianInner c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip4_updates_hexagram (c : Cell192) :
    (apply .flip4 c).1 = dongOuter c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip5_updates_hexagram (c : Cell192) :
    (apply .flip5 c).1 = huaOuter c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip6_updates_hexagram (c : Cell192) :
    (apply .flip6 c).1 = bianOuter c.1 := by
  rcases c with ⟨h, s⟩
  rfl

theorem flip1_involutive (c : Cell192) : apply .flip1 (apply .flip1 c) = c :=
  Cell192.flip1_flip1 c

theorem flip2_involutive (c : Cell192) : apply .flip2 (apply .flip2 c) = c :=
  Cell192.flip2_flip2 c

theorem flip3_involutive (c : Cell192) : apply .flip3 (apply .flip3 c) = c :=
  Cell192.flip3_flip3 c

theorem flip4_involutive (c : Cell192) : apply .flip4 (apply .flip4 c) = c :=
  Cell192.flip4_flip4 c

theorem flip5_involutive (c : Cell192) : apply .flip5 (apply .flip5 c) = c :=
  Cell192.flip5_flip5 c

theorem flip6_involutive (c : Cell192) : apply .flip6 (apply .flip6 c) = c :=
  Cell192.flip6_flip6 c

theorem lineFlip_involutive (g : LineFlipGenerator) (c : Cell192) :
    apply (lineFlip g) (apply (lineFlip g) c) = c := by
  cases g
  · exact flip1_involutive c
  · exact flip2_involutive c
  · exact flip3_involutive c
  · exact flip4_involutive c
  · exact flip5_involutive c
  · exact flip6_involutive c

theorem shiNext_order_three (c : Cell192) :
    apply .shiNext (apply .shiNext (apply .shiNext c)) = c :=
  Cell192.shiNext_three c

/--
Summary: the reachability layer has seven distinct generators; the six line
generators preserve `Shi` and are involutive, while `shiNext` preserves the
hexagram component and has order three.
-/
theorem cell192_generator_summary :
    all.length = 7
    ∧ all.Nodup
    ∧ (∀ g : LineFlipGenerator, ∀ c : Cell192, (apply (lineFlip g) c).2 = c.2)
    ∧ (∀ c : Cell192, (apply .shiNext c).1 = c.1)
    ∧ (∀ c : Cell192, (apply .shiNext c).2 = c.2.next)
    ∧ (∀ g : LineFlipGenerator, ∀ c : Cell192,
        apply (lineFlip g) (apply (lineFlip g) c) = c)
    ∧ (∀ c : Cell192, apply .shiNext (apply .shiNext (apply .shiNext c)) = c) := by
  exact
    ⟨ all_length
    , all_nodup
    , lineFlip_apply_preserves_shi
    , shiNext_preserves_hexagram
    , shiNext_updates_shi
    , lineFlip_involutive
    , shiNext_order_three
    ⟩

end Cell192Generator

/-! ## Named deterministic transition operators on Cell192 -/

/--
Named one-step transition operators on `Cell192`.

`Cell192Generator` above is the minimal reachability generator family used by
proofs.  This wider family is for transition-index documentation: it includes
the named lateral operators that already have total `Cell192 → Cell192`
definitions.
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

/-- Compact operator key for the 192-cell transition index. -/
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

/-- Short Chinese name for the 192-cell transition index. -/
def zhName : Cell192TransitionOperator → String
  | .flip1 => "翻初爻"
  | .flip2 => "翻二爻"
  | .flip3 => "翻三爻"
  | .flip4 => "翻四爻"
  | .flip5 => "翻五爻"
  | .flip6 => "翻上爻"
  | .shiNext => "时态前进"
  | .shiPrev => "时态后退"
  | .hexCuo => "错卦"
  | .hexZong => "综卦"
  | .hexHu => "互卦"

/-- Lean operator reference used by generated documentation. -/
def operatorRef : Cell192TransitionOperator → String
  | .flip1 => "Cell192.flip1"
  | .flip2 => "Cell192.flip2"
  | .flip3 => "Cell192.flip3"
  | .flip4 => "Cell192.flip4"
  | .flip5 => "Cell192.flip5"
  | .flip6 => "Cell192.flip6"
  | .shiNext => "Cell192.shiNext"
  | .shiPrev => "Cell192.shiPrev"
  | .hexCuo => "Cell192.hexCuo"
  | .hexZong => "Cell192.hexZong"
  | .hexHu => "Cell192.hexHu"

/-- Concrete one-step effect of a named operator on a 192-cell position. -/
def effectSummary : Cell192TransitionOperator → String
  | .flip1 => "翻转初爻，保持时态。"
  | .flip2 => "翻转二爻，保持时态。"
  | .flip3 => "翻转三爻，保持时态。"
  | .flip4 => "翻转四爻，保持时态。"
  | .flip5 => "翻转五爻，保持时态。"
  | .flip6 => "翻转上爻，保持时态。"
  | .shiNext => "卦象不变，时态按 已→今→未→已 前进。"
  | .shiPrev => "卦象不变，时态按 已←今←未←已 后退。"
  | .hexCuo => "六爻全反，保持时态。"
  | .hexZong => "六爻上下反序，保持时态。"
  | .hexHu => "取二三四、三四五成互卦，保持时态。"

/-- The named deterministic transition-operator list. -/
def all : List Cell192TransitionOperator :=
  [.flip1, .flip2, .flip3, .flip4, .flip5, .flip6,
   .shiNext, .shiPrev, .hexCuo, .hexZong, .hexHu]

/-- Apply one named transition operator to a `Cell192`. -/
def apply : Cell192TransitionOperator → Cell192 → Cell192
  | .flip1, c => Cell192.flip1 c
  | .flip2, c => Cell192.flip2 c
  | .flip3, c => Cell192.flip3 c
  | .flip4, c => Cell192.flip4 c
  | .flip5, c => Cell192.flip5 c
  | .flip6, c => Cell192.flip6 c
  | .shiNext, c => Cell192.shiNext c
  | .shiPrev, c => Cell192.shiPrev c
  | .hexCuo, c => Cell192.hexCuo c
  | .hexZong, c => Cell192.hexZong c
  | .hexHu, c => Cell192.hexHu c

theorem all_length : all.length = 11 := by
  native_decide

theorem all_nodup : all.Nodup := by
  native_decide

end Cell192TransitionOperator

end SSBX.Text.OperatorReachabilitySemantics
