import SSBX.Foundation.Bagua.R8
import SSBX.Foundation.Yi.YiCore
import SSBX.Text.OperatorSignatures

/-!
# OperatorFamilySemantics — parametric family laws over R8

This file proves family-level semantics for a small set of catalogue operators
whose meaning is already represented by uniform `R8` transformations.  It
is intentionally parametric: one theorem ranges over all cells, instead of
generating pair-specific theorems for every operator-cell row.
-/

namespace SSBX.Text.OperatorFamilySemantics

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorSignatures

/-- Cell-uniform transformations with exact operator-family anchors. -/
inductive CellTransformKind where
  | id
  | next64
  | prev64
  | complement
  | reverse
  | interlace
  | complementReverse
  | flip1
  | flip2
  | flip3
  deriving Repr, DecidableEq, BEq

namespace CellTransformKind

def operatorId : CellTransformKind → OperatorId
  | .id => .R_6
  | .next64 => .T_10
  | .prev64 => .T_12
  | .complement => .Z_5
  | .reverse => .Z_6
  | .interlace => .Z_3
  | .complementReverse => .Z_33
  | .flip1 => .T_5
  | .flip2 => .T_1
  | .flip3 => .T_2

def apply : CellTransformKind → R8 → R8
  | .id, c => c
  | .next64, c => («生» c.1, c.2)
  | .prev64, c => («加» Hexagram.earth c.1, c.2)
  | .complement, c => R8.hexCuo c
  | .reverse, c => R8.hexZong c
  | .interlace, c => R8.hexHu c
  | .complementReverse, c => (c.1.complementReverse, c.2)
  | .flip1, c => R8.flip1 c
  | .flip2, c => R8.flip2 c
  | .flip3, c => R8.flip3 c

end CellTransformKind

def cellTransformKinds : List CellTransformKind :=
  [.id, .next64, .prev64, .complement, .reverse, .interlace, .complementReverse, .flip1, .flip2, .flip3]

def cellTransformOperatorIds : List OperatorId :=
  [ .R_6, .R_11, .T_1, .T_2, .T_4, .T_5, .T_6, .T_7, .T_8, .T_9, .T_10
  , .T_12, .T_13, .T_14, .T_15, .B_3, .B_4, .B_5, .B_6, .I_2, .I_6, .I_8
  , .P_9, .D_1, .L_9, .L_10, .Y_3, .Y_4, .Y_5, .Y_17, .Y_18, .Z_2, .Z_3
  , .Z_5, .Z_6, .Z_8, .Z_9, .Z_12, .Z_13, .Z_22, .Z_31, .Z_33, .ZA_2 ]

def cellTransformForOperator? : OperatorId → Option CellTransformKind
  | .R_6 | .R_11 | .T_7 | .T_8 | .B_4 | .B_5 | .B_6 | .I_2 | .P_9 | .D_1
  | .L_9 | .L_10 | .Y_17 | .Y_18 | .Z_12 | .Z_13 | .ZA_2 => some .id
  | .T_10 | .T_13 | .T_15 | .B_3 | .Y_3 | .Z_9 => some .next64
  | .T_12 | .T_14 | .Y_4 | .Y_5 | .Z_8 | .Z_22 => some .prev64
  | .T_4 | .T_6 | .Z_5 | .Z_31 => some .complement
  | .Z_6 => some .reverse
  | .T_9 => some .reverse
  | .I_6 | .Z_2 | .Z_3 => some .interlace
  | .I_8 | .Z_33 => some .complementReverse
  | .T_5 => some .flip1
  | .T_1 => some .flip2
  | .T_2 => some .flip3
  | _ => none

def applyCellTransformForOperator? (id : OperatorId) (c : R8) : Option R8 :=
  (cellTransformForOperator? id).map (fun k => k.apply c)

theorem cellTransformKinds_length :
    cellTransformKinds.length = 10 := by
  native_decide

theorem cellTransformOperatorIds_eq :
    cellTransformOperatorIds =
      [ .R_6, .R_11, .T_1, .T_2, .T_4, .T_5, .T_6, .T_7, .T_8, .T_9, .T_10
      , .T_12, .T_13, .T_14, .T_15, .B_3, .B_4, .B_5, .B_6, .I_2, .I_6, .I_8
      , .P_9, .D_1, .L_9, .L_10, .Y_3, .Y_4, .Y_5, .Y_17, .Y_18, .Z_2, .Z_3
      , .Z_5, .Z_6, .Z_8, .Z_9, .Z_12, .Z_13, .Z_22, .Z_31, .Z_33, .ZA_2 ] := by
  native_decide

theorem cellTransformOperatorIds_length :
    cellTransformOperatorIds.length = 43 := by
  native_decide

theorem cellTransformOperatorIds_nodup :
    cellTransformOperatorIds.Nodup := by
  native_decide

theorem cellTransformOperatorIds_catalogue_members :
    cellTransformOperatorIds.all (fun id => decide (id ∈ allOperatorIds)) = true := by
  native_decide

theorem cellTransformOperatorIds_have_catalogue_signature :
    cellTransformOperatorIds.all (fun id => decide ((fullSignatureFor id).id = id)) = true := by
  native_decide

theorem cellTransformForOperator?_id :
    cellTransformForOperator? .R_6 = some .id := rfl

theorem cellTransformForOperator?_next64 :
    cellTransformForOperator? .T_10 = some .next64 := rfl

theorem cellTransformForOperator?_prev64 :
    cellTransformForOperator? .T_12 = some .prev64 := rfl

theorem cellTransformForOperator?_cuo :
    cellTransformForOperator? .Z_5 = some .complement := rfl

theorem cellTransformForOperator?_zong :
    cellTransformForOperator? .Z_6 = some .reverse := rfl

theorem cellTransformForOperator?_hu :
    cellTransformForOperator? .Z_3 = some .interlace := rfl

theorem cellTransformForOperator?_fan :
    cellTransformForOperator? .T_6 = some .complement := rfl

theorem cellTransformForOperator?_fanOperator :
    cellTransformForOperator? .Z_31 = some .complement := rfl

theorem cellTransformForOperator?_cuoZong :
    cellTransformForOperator? .Z_33 = some .complementReverse := rfl

theorem cellTransformForOperator?_flip1 :
    cellTransformForOperator? .T_5 = some .flip1 := rfl

theorem cellTransformForOperator?_flip2 :
    cellTransformForOperator? .T_1 = some .flip2 := rfl

theorem cellTransformForOperator?_flip3 :
    cellTransformForOperator? .T_2 = some .flip3 := rfl

theorem applyCellTransformForOperator?_id (c : R8) :
    applyCellTransformForOperator? .R_6 c = some c := rfl

theorem applyCellTransformForOperator?_next64 (c : R8) :
    applyCellTransformForOperator? .T_10 c = some («生» c.1, c.2) := rfl

theorem applyCellTransformForOperator?_prev64 (c : R8) :
    applyCellTransformForOperator? .T_12 c = some («加» Hexagram.earth c.1, c.2) := rfl

theorem applyCellTransformForOperator?_cuo (c : R8) :
    applyCellTransformForOperator? .Z_5 c = some (R8.hexCuo c) := rfl

theorem applyCellTransformForOperator?_zong (c : R8) :
    applyCellTransformForOperator? .Z_6 c = some (R8.hexZong c) := rfl

theorem applyCellTransformForOperator?_hu (c : R8) :
    applyCellTransformForOperator? .Z_3 c = some (R8.hexHu c) := rfl

theorem applyCellTransformForOperator?_fan (c : R8) :
    applyCellTransformForOperator? .T_6 c = some (R8.hexCuo c) := rfl

theorem applyCellTransformForOperator?_fanOperator (c : R8) :
    applyCellTransformForOperator? .Z_31 c = some (R8.hexCuo c) := rfl

theorem applyCellTransformForOperator?_cuoZong (c : R8) :
    applyCellTransformForOperator? .Z_33 c = some (c.1.complementReverse, c.2) := rfl

theorem applyCellTransformForOperator?_flip1 (c : R8) :
    applyCellTransformForOperator? .T_5 c = some (R8.flip1 c) := rfl

theorem applyCellTransformForOperator?_flip2 (c : R8) :
    applyCellTransformForOperator? .T_1 c = some (R8.flip2 c) := rfl

theorem applyCellTransformForOperator?_flip3 (c : R8) :
    applyCellTransformForOperator? .T_2 c = some (R8.flip3 c) := rfl

theorem cellTransform_preserves_shi (k : CellTransformKind) (c : R8) :
    (k.apply c).2 = c.2 := by
  cases k <;> rcases c with ⟨h, s⟩ <;> rfl

theorem cuo_family_involutive (c : R8) :
    CellTransformKind.complement.apply (CellTransformKind.complement.apply c) = c :=
  R8.hexCuo_hexCuo c

theorem zong_family_involutive (c : R8) :
    CellTransformKind.reverse.apply (CellTransformKind.reverse.apply c) = c :=
  R8.hexZong_hexZong c

theorem cuo_zong_family_comm (c : R8) :
    CellTransformKind.complement.apply (CellTransformKind.reverse.apply c)
      = CellTransformKind.reverse.apply (CellTransformKind.complement.apply c) :=
  R8.hexCuo_hexZong_comm c

theorem cuo_zong_family_composite_involutive (c : R8) :
    CellTransformKind.complement.apply
      (CellTransformKind.reverse.apply
        (CellTransformKind.complement.apply
          (CellTransformKind.reverse.apply c))) = c :=
  R8.hexCuoZong_hexCuoZong c

/--
Summary: ten operator families currently have parameterized `R8`
semantics, with forty-three catalogue ids enabled where the surface row has a
conservative exact Hex transform anchor.  These laws range over all cells; they
do not introduce pair-specific theorem rows.
-/
theorem cell_transform_family_summary :
    cellTransformKinds.length = 10
    ∧ cellTransformOperatorIds.length = 43
    ∧ cellTransformOperatorIds =
      [ .R_6, .R_11, .T_1, .T_2, .T_4, .T_5, .T_6, .T_7, .T_8, .T_9, .T_10
      , .T_12, .T_13, .T_14, .T_15, .B_3, .B_4, .B_5, .B_6, .I_2, .I_6, .I_8
      , .P_9, .D_1, .L_9, .L_10, .Y_3, .Y_4, .Y_5, .Y_17, .Y_18, .Z_2, .Z_3
      , .Z_5, .Z_6, .Z_8, .Z_9, .Z_12, .Z_13, .Z_22, .Z_31, .Z_33, .ZA_2 ]
    ∧ cellTransformOperatorIds.Nodup
    ∧ cellTransformOperatorIds.all (fun id => decide (id ∈ allOperatorIds)) = true
    ∧ cellTransformOperatorIds.all (fun id => decide ((fullSignatureFor id).id = id)) = true
    ∧ (∀ k : CellTransformKind, ∀ c : R8, (k.apply c).2 = c.2)
    ∧ (∀ c : R8, CellTransformKind.complement.apply (CellTransformKind.complement.apply c) = c)
    ∧ (∀ c : R8, CellTransformKind.reverse.apply (CellTransformKind.reverse.apply c) = c)
    ∧ (∀ c : R8,
        CellTransformKind.complement.apply (CellTransformKind.reverse.apply c)
          = CellTransformKind.reverse.apply (CellTransformKind.complement.apply c)) := by
  exact
    ⟨ cellTransformKinds_length
    , cellTransformOperatorIds_length
    , cellTransformOperatorIds_eq
    , cellTransformOperatorIds_nodup
    , cellTransformOperatorIds_catalogue_members
    , cellTransformOperatorIds_have_catalogue_signature
    , cellTransform_preserves_shi
    , cuo_family_involutive
    , zong_family_involutive
    , cuo_zong_family_comm
    ⟩

end SSBX.Text.OperatorFamilySemantics
