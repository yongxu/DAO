import SSBX.Foundation.Bagua.Cell192
import SSBX.Text.OperatorSignatures

/-!
# OperatorFamilySemantics — parametric family laws over Cell192

This file proves family-level semantics for a small set of catalogue operators
whose meaning is already represented by uniform `Cell192` transformations.  It
is intentionally parametric: one theorem ranges over all cells, instead of
generating pair-specific theorems for every operator-cell row.
-/

namespace SSBX.Text.OperatorFamilySemantics

open SSBX.Foundation.Bagua.Cell192
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorSignatures

/-- Cell-uniform transformations with exact operator-family anchors. -/
inductive CellTransformKind where
  | cuo
  | zong
  | hu
  deriving Repr, DecidableEq, BEq

namespace CellTransformKind

def operatorId : CellTransformKind → OperatorId
  | .cuo => .Z_5
  | .zong => .Z_6
  | .hu => .Z_3

def apply : CellTransformKind → Cell192 → Cell192
  | .cuo, c => Cell192.hexCuo c
  | .zong, c => Cell192.hexZong c
  | .hu, c => Cell192.hexHu c

end CellTransformKind

def cellTransformKinds : List CellTransformKind :=
  [.cuo, .zong, .hu]

def cellTransformOperatorIds : List OperatorId :=
  cellTransformKinds.map CellTransformKind.operatorId

def cellTransformForOperator? : OperatorId → Option CellTransformKind
  | .Z_5 => some .cuo
  | .Z_6 => some .zong
  | .Z_3 => some .hu
  | _ => none

def applyCellTransformForOperator? (id : OperatorId) (c : Cell192) : Option Cell192 :=
  (cellTransformForOperator? id).map (fun k => k.apply c)

theorem cellTransformKinds_length :
    cellTransformKinds.length = 3 := by
  native_decide

theorem cellTransformOperatorIds_eq :
    cellTransformOperatorIds = [.Z_5, .Z_6, .Z_3] := by
  native_decide

theorem cellTransformOperatorIds_nodup :
    cellTransformOperatorIds.Nodup := by
  native_decide

theorem cellTransformOperatorIds_catalogue_members :
    cellTransformOperatorIds.all (fun id => decide (id ∈ allOperatorIds)) = true := by
  native_decide

theorem cellTransformOperatorIds_have_signature_seed :
    cellTransformOperatorIds.all (fun id => decide (id ∈ signedOperatorIds)) = true := by
  native_decide

theorem cellTransformForOperator?_cuo :
    cellTransformForOperator? .Z_5 = some .cuo := rfl

theorem cellTransformForOperator?_zong :
    cellTransformForOperator? .Z_6 = some .zong := rfl

theorem cellTransformForOperator?_hu :
    cellTransformForOperator? .Z_3 = some .hu := rfl

theorem applyCellTransformForOperator?_cuo (c : Cell192) :
    applyCellTransformForOperator? .Z_5 c = some (Cell192.hexCuo c) := rfl

theorem applyCellTransformForOperator?_zong (c : Cell192) :
    applyCellTransformForOperator? .Z_6 c = some (Cell192.hexZong c) := rfl

theorem applyCellTransformForOperator?_hu (c : Cell192) :
    applyCellTransformForOperator? .Z_3 c = some (Cell192.hexHu c) := rfl

theorem cellTransform_preserves_shi (k : CellTransformKind) (c : Cell192) :
    (k.apply c).2 = c.2 := by
  cases k <;> rcases c with ⟨h, s⟩ <;> rfl

theorem cuo_family_involutive (c : Cell192) :
    CellTransformKind.cuo.apply (CellTransformKind.cuo.apply c) = c :=
  Cell192.hexCuo_hexCuo c

theorem zong_family_involutive (c : Cell192) :
    CellTransformKind.zong.apply (CellTransformKind.zong.apply c) = c :=
  Cell192.hexZong_hexZong c

theorem cuo_zong_family_comm (c : Cell192) :
    CellTransformKind.cuo.apply (CellTransformKind.zong.apply c)
      = CellTransformKind.zong.apply (CellTransformKind.cuo.apply c) :=
  Cell192.hexCuo_hexZong_comm c

theorem cuo_zong_family_composite_involutive (c : Cell192) :
    CellTransformKind.cuo.apply
      (CellTransformKind.zong.apply
        (CellTransformKind.cuo.apply
          (CellTransformKind.zong.apply c))) = c :=
  Cell192.hexCuoZong_hexCuoZong c

/--
Summary: three operator families currently have parameterized `Cell192`
semantics.  These laws range over all cells; they do not introduce 3 × 192
pair-specific theorem rows.
-/
theorem cell_transform_family_summary :
    cellTransformKinds.length = 3
    ∧ cellTransformOperatorIds = [.Z_5, .Z_6, .Z_3]
    ∧ cellTransformOperatorIds.Nodup
    ∧ cellTransformOperatorIds.all (fun id => decide (id ∈ allOperatorIds)) = true
    ∧ cellTransformOperatorIds.all (fun id => decide (id ∈ signedOperatorIds)) = true
    ∧ (∀ k : CellTransformKind, ∀ c : Cell192, (k.apply c).2 = c.2)
    ∧ (∀ c : Cell192, CellTransformKind.cuo.apply (CellTransformKind.cuo.apply c) = c)
    ∧ (∀ c : Cell192, CellTransformKind.zong.apply (CellTransformKind.zong.apply c) = c)
    ∧ (∀ c : Cell192,
        CellTransformKind.cuo.apply (CellTransformKind.zong.apply c)
          = CellTransformKind.zong.apply (CellTransformKind.cuo.apply c)) := by
  exact
    ⟨ cellTransformKinds_length
    , cellTransformOperatorIds_eq
    , cellTransformOperatorIds_nodup
    , cellTransformOperatorIds_catalogue_members
    , cellTransformOperatorIds_have_signature_seed
    , cellTransform_preserves_shi
    , cuo_family_involutive
    , zong_family_involutive
    , cuo_zong_family_comm
    ⟩

end SSBX.Text.OperatorFamilySemantics
