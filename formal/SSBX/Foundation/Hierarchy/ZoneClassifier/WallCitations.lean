/-
# Foundation.Hierarchy.ZoneClassifier.WallCitations — 墙引用注册表

## 设计

每个 `WallTag` 对应一条**既存定理**。本文件 提供逐条 wrap 的 `cited_*` 定理，
其 RHS 直接 reduce 到原定理。若某引用断裂（namespace shift / rename），仅该
单行编译失败，定位即修。

## 证据流（Provenance Principle）

这里是显式可审计的 R_n 之外的真之入口：每条 `cited_*` 严格等于 codebase 中
已经证明过的某条定理。无新公理；无 sorry；无新真值断言。

逐条对应（按 WallTag 顺序）：

  | WallTag                        | 源定理                                                              |
  |--------------------------------|---------------------------------------------------------------------|
  | sheng_not_compilable           | WenDefCompile.sheng_not_cuo_equivariant                             |
  | kleene_inverter_dies           | CuoInvariance.unrestricted_kleene_inverter_inconsistent             |
  | godel_halts_internal           | GodelLi.halts_undecidable_internally                                |
  | godel_halts_kleene             | GodelLi.halts_undecidable_under_kleene                              |
  | rice .shao_yang                | Diagonal.halts_on_some_undecidable_under_kleene                     |
  | rice .tai_yin                  | Diagonal.halts_on_none_undecidable_under_kleene                     |
  | rice .tai_yang                 | Diagonal.halts_on_all_undecidable_under_kleene                      |
  | rice .shao_yin                 | Diagonal.halts_on_some_no_undecidable_under_kleene                  |
  | hu_fixed_only_qianqian_kunkun  | Hexagram.hu_fixed_point                                             |
  | cuo_not_truth_preserving       | V4.cuo_not_truth_preserving                                         |
  | zong_not_truth_preserving      | V4.zong_not_truth_preserving                                        |
  | li_cannot_encode_dao           | DaoLi.li_cannot_encode_dao                                          |
  | change_no_fixed_point          | Yuan.change_no_fixed_point                                          |
-/

import SSBX.Foundation.Hierarchy.ZoneClassifier.Types
import SSBX.Foundation.Wen.WenDefCompile
import SSBX.Foundation.Atlas.Yi.Classical.Algebra.CuoInvariance
import SSBX.Foundation.Atlas.Yi.Classical.Diagonal.GodelLi
import SSBX.Foundation.Atlas.Yi.Diagonal
import SSBX.Foundation.Atlas.Yi.Operators
import SSBX.Foundation.Hierarchy.Operators.V4.PreservationLogic
import SSBX.Foundation.Modern.DaoLi
import SSBX.Foundation.Core.Yuan

namespace SSBX.Foundation.Hierarchy.ZoneClassifier.WallCitations

/-! ## § 1  生 不可 ISA 编译 -/

def cited_sheng_not_compilable :=
  SSBX.Foundation.Wen.WenDefCompile.sheng_not_cuo_equivariant

/-! ## § 2  无限制 Kleene 反演不一致 -/

def cited_kleene_inverter_dies :=
  SSBX.Foundation.Bagua.CuoInvariance.unrestricted_kleene_inverter_inconsistent

/-! ## § 3  判停不可内部决 -/

def cited_godel_halts_internal :=
  SSBX.Foundation.Bagua.GodelLi.halts_undecidable_internally

def cited_godel_halts_kleene :=
  SSBX.Foundation.Bagua.GodelLi.halts_undecidable_under_kleene

/-! ## § 4  Rice 四象 -/

def cited_rice_shao_yang :=
  SSBX.Foundation.Atlas.Yi.Diagonal.halts_on_some_undecidable_under_kleene

def cited_rice_tai_yin :=
  SSBX.Foundation.Atlas.Yi.Diagonal.halts_on_none_undecidable_under_kleene

def cited_rice_tai_yang :=
  SSBX.Foundation.Atlas.Yi.Diagonal.halts_on_all_undecidable_under_kleene

def cited_rice_shao_yin :=
  SSBX.Foundation.Atlas.Yi.Diagonal.halts_on_some_no_undecidable_under_kleene

/-! ## § 5  互的不动点限于 qianqian、kunkun -/

def cited_hu_fixed_only_qianqian_kunkun :=
  SSBX.Foundation.Atlas.Yi.Hexagram.hu_fixed_point

/-! ## § 6  V₄ 错综 不保真 -/

def cited_cuo_not_truth_preserving :=
  SSBX.Foundation.Hierarchy.Operators.V4.ImplicationSlice.cuo_not_truth_preserving

def cited_zong_not_truth_preserving :=
  SSBX.Foundation.Hierarchy.Operators.V4.ImplicationSlice.zong_not_truth_preserving

/-! ## § 7  理 ⊭ 道 -/

def cited_li_cannot_encode_dao :=
  SSBX.Foundation.Modern.DaoLi.li_cannot_encode_dao

/-! ## § 8  易无不动点 -/

def cited_change_no_fixed_point :=
  SSBX.Foundation.Core.Yuan.change_no_fixed_point

/-! ## § 9  证据流全局见证

  以下定理 `all_citations_typecheck` 同时引用所有 `cited_*`，从而强制
  Lean 在编译本文件 时把所有 11 条引用一并 type-check。若任何引用断裂，
  本定理失败。 -/

theorem all_citations_typecheck : True := by
  let _ := @cited_sheng_not_compilable
  let _ := @cited_kleene_inverter_dies
  let _ := @cited_godel_halts_internal
  let _ := @cited_godel_halts_kleene
  let _ := @cited_rice_shao_yang
  let _ := @cited_rice_tai_yin
  let _ := @cited_rice_tai_yang
  let _ := @cited_rice_shao_yin
  let _ := @cited_hu_fixed_only_qianqian_kunkun
  let _ := @cited_cuo_not_truth_preserving
  let _ := @cited_zong_not_truth_preserving
  let _ := @cited_li_cannot_encode_dao
  let _ := @cited_change_no_fixed_point
  trivial

end SSBX.Foundation.Hierarchy.ZoneClassifier.WallCitations
