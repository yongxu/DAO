/-
# Foundation.Hierarchy.ZoneClassifier.Examples — #eval 演示

收紧后的烟雾测试，覆盖任意 n、dao_axiom 子集表、墙检测、交互。
Lift 已删除（见 Plan 第二轮）。
-/

import SSBX.Foundation.Hierarchy.ZoneClassifier.Classify
import SSBX.Foundation.Hierarchy.ZoneClassifier.Subsets
import SSBX.Foundation.Hierarchy.ZoneClassifier.Interaction

namespace SSBX.Foundation.Hierarchy.ZoneClassifier

open SSBX.Foundation.Wen.Layered

/-! ## § 1  零向量 + v4_compose → dao_axiom (任意 n) -/

#eval (classify (n := 8) BitSpace.zero OperatorTag.v4_compose).zone
#eval (classify (n := 100) BitSpace.zero OperatorTag.v4_compose).zone

/-! ## § 2  cuo_complement → wall（任意 cell；引用 cuo_not_truth_preserving） -/

#eval (classify (n := 8) BitSpace.zero OperatorTag.cuo_complement).zone

/-! ## § 3  6 位 yiCore_step → 全集即道 -/

#eval (daoSubset 6 OperatorTag.yiCore_step).card

/-! ## § 4  双 cell 交互演示 -/

#eval (interact (n := 8) BitSpace.zero BitSpace.zero OperatorTag.v4_compose).2.1

/-! ## § 5  无自然二元行动之 op 在交互上返回 none -/

#eval (interact (n := 6) BitSpace.zero BitSpace.zero OperatorTag.hu_interlace).1

end SSBX.Foundation.Hierarchy.ZoneClassifier
