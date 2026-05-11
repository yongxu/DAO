/-
# RootLanguageTree -- R0..R8 root interface counts and generated-rule spine

This module is a typed skeleton for the documentation group
`docs-next/10_formal_形式/root-language-tree/`.

It proves only the structural bookkeeping:

* the strict R0..R8 layer sizes sum to 511 root cells;
* the interface reading table has 1022 entries when every root is read as
  both `cell` and `operator`;
* the ontology reading has 1021 entries when R0 remains prior to the
  cell/operator split;
* the root rules are a fixed, exhaustive kernel for later Wen/Lisp work.

It does not choose the final Chinese glyphs for provisional layers.
-/

import SSBX.Foundation.Hierarchy.LiftProject

namespace SSBX.Foundation.Hierarchy.RootLanguageTree

/-! ## Root layers and roles -/

/-- Strict R-layers R0..R8. -/
inductive RootLayer : Type
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8
  deriving Repr, DecidableEq

namespace RootLayer

/-- Canonical layer enumeration. -/
def all : List RootLayer :=
  [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8]

theorem all_length : all.length = 9 := rfl

/-- R-index as a natural number. -/
def index : RootLayer -> Nat
  | .r0 => 0
  | .r1 => 1
  | .r2 => 2
  | .r3 => 3
  | .r4 => 4
  | .r5 => 5
  | .r6 => 6
  | .r7 => 7
  | .r8 => 8

/-- Strict uniform size: |Rn| = 2^n. -/
def size (l : RootLayer) : Nat :=
  2 ^ l.index

theorem size_r0 : size .r0 = 1 := rfl
theorem size_r1 : size .r1 = 2 := rfl
theorem size_r2 : size .r2 = 4 := rfl
theorem size_r3 : size .r3 = 8 := rfl
theorem size_r4 : size .r4 = 16 := rfl
theorem size_r5 : size .r5 = 32 := rfl
theorem size_r6 : size .r6 = 64 := rfl
theorem size_r7 : size .r7 = 128 := rfl
theorem size_r8 : size .r8 = 256 := rfl

/-- Concrete layer-size list used by the generated review package. -/
def sizeList : List Nat :=
  all.map size

theorem sizeList_eq :
    sizeList = [1, 2, 4, 8, 16, 32, 64, 128, 256] := rfl

theorem root_cell_count_eq_511 :
    sizeList.sum = 511 := by
  native_decide

theorem nonzero_root_cell_count_eq_510 :
    [2, 4, 8, 16, 32, 64, 128, 256].sum = 510 := by
  native_decide

/-- Every declared layer is in the canonical enumeration. -/
theorem mem_all (l : RootLayer) : l ∈ all := by
  cases l <;> simp [all]

end RootLayer

/-- The two interface readings of a root object. -/
inductive RootRole : Type
  | cell
  | operator
  deriving Repr, DecidableEq

namespace RootRole

def all : List RootRole := [.cell, .operator]

theorem all_length : all.length = 2 := rfl

theorem mem_all (r : RootRole) : r ∈ all := by
  cases r <;> simp [all]

end RootRole

/-! ## Counts for 511 / 1021 / 1022 -/

/-- Pure root-cell count across R0..R8. -/
def rootCellCount : Nat :=
  RootLayer.sizeList.sum

/-- Interface reading count: each root is read as `cell` and as `operator`. -/
def interfaceReadingCount : Nat :=
  rootCellCount * RootRole.all.length

/-- Ontology-root count: R0 is prior to the split; R1..R8 split into two roles. -/
def ontologyRootCount : Nat :=
  1 + 2 * [2, 4, 8, 16, 32, 64, 128, 256].sum

theorem rootCellCount_eq_511 :
    rootCellCount = 511 := by
  native_decide

theorem interfaceReadingCount_eq_1022 :
    interfaceReadingCount = 1022 := by
  native_decide

theorem ontologyRootCount_eq_1021 :
    ontologyRootCount = 1021 := by
  native_decide

/-- The 1022 interface table differs from the 1021 ontology tree by the extra
R0 operator reading. -/
theorem ontology_plus_r0_operator_eq_interface :
    ontologyRootCount + 1 = interfaceReadingCount := by
  native_decide

/-! ## Root cells and interface entries -/

/-- A root cell is a bounded code in the carrier of a layer.

This intentionally stores only the finite code and layer. The concrete
carrier interpretation lives in the existing R0..R8 modules. -/
structure RootCell where
  layer : RootLayer
  code : Fin layer.size
  deriving Repr

/-- Interface entry used by the generated 1022 review package. -/
structure RootInterfaceEntry where
  cell : RootCell
  role : RootRole
  deriving Repr

/-- The formal reading of a root interface entry. -/
inductive RootReadingKind : Type
  | carrierElement
  | xorMaskOperator
  deriving Repr, DecidableEq

/-- Read a root entry according to its interface role. -/
def readingKind (e : RootInterfaceEntry) : RootReadingKind :=
  match e.role with
  | .cell => .carrierElement
  | .operator => .xorMaskOperator

theorem cell_role_reads_as_carrier (c : RootCell) :
    readingKind ⟨c, .cell⟩ = .carrierElement := rfl

theorem operator_role_reads_as_xor_mask (c : RootCell) :
    readingKind ⟨c, .operator⟩ = .xorMaskOperator := rfl

/-! ## Root rules -/

/-- Minimal root-rule kernel for the later Wen/Lisp layer. -/
inductive RootRule : Type
  | quote
  | apply
  | compose
  | xor
  | neg
  | equal
  | ite
  | lookup
  | recurse
  | project
  | lift
  | returnDao
  deriving Repr, DecidableEq

namespace RootRule

/-- Canonical rule enumeration. -/
def all : List RootRule :=
  [.quote, .apply, .compose, .xor, .neg, .equal,
   .ite, .lookup, .recurse, .project, .lift, .returnDao]

theorem all_length : all.length = 12 := rfl

theorem mem_all (r : RootRule) : r ∈ all := by
  cases r <;> simp [all]

end RootRule

/-! ## Public summary -/

/-- Summary theorem for the root-language-tree typed skeleton. -/
theorem root_language_tree_summary :
    rootCellCount = 511
    ∧ interfaceReadingCount = 1022
    ∧ ontologyRootCount = 1021
    ∧ ontologyRootCount + 1 = interfaceReadingCount
    ∧ RootLayer.all.length = 9
    ∧ RootRole.all.length = 2
    ∧ RootRule.all.length = 12 := by
  exact
    ⟨ rootCellCount_eq_511
    , interfaceReadingCount_eq_1022
    , ontologyRootCount_eq_1021
    , ontology_plus_r0_operator_eq_interface
    , RootLayer.all_length
    , RootRole.all_length
    , RootRule.all_length
    ⟩

end SSBX.Foundation.Hierarchy.RootLanguageTree
