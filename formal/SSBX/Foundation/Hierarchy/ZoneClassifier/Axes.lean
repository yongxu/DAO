/-
# Foundation.Hierarchy.ZoneClassifier.Axes — 诚实派生的轴

## 收紧 (第二轮)

仅保留 `extractShi`——其 `none` 路径是诚实的"在 n≠8 时无投影函数可调"。

删除的 extractor（第一轮版本均使用定义型默认，违规）：
- `extractBehavior` —— `if c'=c then stable else periodic` 错把"不动 ⟹ stable"
  扩展到"不不动 ⟹ periodic"。BehaviorClass 是 R-塔元层概念，BitSpace n 上无诚实派生
- `extractClaim` —— `if walls has pending then axiomBacked else proved` 默认 .proved 无根据
- `extractModality` —— `match z | .wall => .E | _ => .T` 之 .T 默认无根据
-/

import SSBX.Foundation.Hierarchy.ZoneClassifier.Types
import SSBX.Foundation.Atlas.Yi.DaoSource

namespace SSBX.Foundation.Hierarchy.ZoneClassifier

open SSBX.Foundation.Wen.Layered

/-! ## § 1  Shi 轴 (仅 n = 8 有意义) -/

/-- 从 `BitSpace n` 提取 Shi。仅 n = 8 时调用 `DaoSource.Shi.fromR8`；
    其他 n 返回 `none`（诚实的"无函数可调"，非定义型默认）。 -/
def extractShi : (n : Nat) → BitSpace n → Option SSBX.Foundation.Atlas.Yi.Shi
  | 8, c => some (SSBX.Foundation.Atlas.Yi.DaoSource.Shi.fromR8 c)
  | _, _ => none

end SSBX.Foundation.Hierarchy.ZoneClassifier
