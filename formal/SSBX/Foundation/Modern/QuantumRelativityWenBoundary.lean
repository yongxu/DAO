/-
# QuantumRelativityWenBoundary — 文构造覆盖不受 tagged-language 边界否定

Companion: `义理/文构造完备与直相加边界.md`

本文件回应一个精确修正：

1. `QuantumRelativityNoGo` 只证明当前 tagged 量子/相对论物理语言并和不会
   自动坍缩为一个直接统一项；
2. 这不是文构造系统的不可能性结论；
3. 现有 WenSurface 层已经有 `371 × 192 = 71232` 覆盖网格、371 个可执行
   registry rows、以及 192 个 Cell 的全覆盖；
4. 因而 `192 × 371` 路线应被读作更强的构造基底候选，而不是被 tagged
   物理语言边界排除。
-/
import SSBX.Foundation.Modern.QuantumRelativityNoGo
import SSBX.Foundation.Wen.WenSurface.Coverage

namespace SSBX.Foundation.Modern.QuantumRelativityWenBoundary

open SSBX.Foundation.Modern.QuantumRelativityNoGo
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Wen.WenSurface
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorCellMap
open SSBX.Text.OperatorCellSemantics

/-! ## § 1 Wen constructive coverage -/

/-- 当前可机器检查的 `192 × 371` 文构造覆盖读法。 -/
def WenConstructiveCoverage : Prop :=
  allOperatorIds.length = 371
    ∧ Cell192.all.length = 192
    ∧ allOperatorCells.length = 71232
    ∧ executableRegistryEntries.length = 371
    ∧ allOperatorCellSemanticRows.length = 71232

/-- `371` 个文言算子与 `192` 个格位的覆盖网格已经机器检查。 -/
theorem wen_constructive_coverage_192_371 :
    WenConstructiveCoverage :=
  ⟨ allOperatorIds_length
  , Cell192.all_length
  , allOperatorCells_length
  , executableRegistryEntries_length
  , allOperatorCellSemanticRows_length
  ⟩

/-! ## § 2 Scope split -/

/-- 当前 tagged 物理语言的非坍缩边界。 -/
def TaggedPhysicalLanguageBoundary : Prop :=
  TaggedAdditionNoncollapse

/-- 边界适用的对象层。 -/
inductive BoundaryTarget : Type
  | currentTaggedPhysicalLanguage
  | wenConstructiveCoverage
  deriving Repr, DecidableEq

/-- tagged-language 直相加边界只适用于当前 tagged 物理语言，不适用于文构造覆盖层。 -/
def taggedBoundaryApplies : BoundaryTarget → Bool
  | .currentTaggedPhysicalLanguage => true
  | .wenConstructiveCoverage => false

/-- scope split：文构造覆盖不是 tagged physical-language noncollapse 的否定目标。 -/
theorem tagged_boundary_scope_split :
    taggedBoundaryApplies .currentTaggedPhysicalLanguage = true
    ∧ taggedBoundaryApplies .wenConstructiveCoverage = false :=
  ⟨rfl, rfl⟩

/-- tagged 物理语言非坍缩与 `192 × 371` 文构造覆盖可以同时成立。 -/
theorem tagged_boundary_compatible_with_wen_constructive_coverage :
    TaggedPhysicalLanguageBoundary
    ∧ WenConstructiveCoverage :=
  ⟨tagged_addition_noncollapse, wen_constructive_coverage_192_371⟩

/-! ## § 3 Public summary -/

/-- 公开摘要：
    (1) 当前 tagged 物理语言并和不自动坍缩；
    (2) `371 × 192` 文构造覆盖已机器检查；
    (3) 前者不否定后者；
    (4) 因此用户提出的 `192 × 371` 路线应作为构造基底方向继续推进。 -/
theorem wen_constructive_boundary_summary :
    TaggedPhysicalLanguageBoundary
    ∧ WenConstructiveCoverage
    ∧ taggedBoundaryApplies .currentTaggedPhysicalLanguage = true
    ∧ taggedBoundaryApplies .wenConstructiveCoverage = false :=
  ⟨ tagged_addition_noncollapse
  , wen_constructive_coverage_192_371
  , rfl
  , rfl
  ⟩

end SSBX.Foundation.Modern.QuantumRelativityWenBoundary
