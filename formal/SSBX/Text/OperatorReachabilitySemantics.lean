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

end SSBX.Text.OperatorReachabilitySemantics
