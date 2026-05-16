/-
# Foundation.Hierarchy.ZoneClassifier.Interaction — 双 cell 交互

## 收紧 (第二轮)

`op.apply` 现返回 `Option (BitSpace n)`：无自然二元行动之 op 在交互上返回
`(none, wall, walls)`——诚实的"无 cell 落点 + 墙"，而非任意 fst fallback。
-/

import SSBX.Foundation.Hierarchy.ZoneClassifier.Classify

namespace SSBX.Foundation.Hierarchy.ZoneClassifier

open SSBX.Foundation.Wen.Layered

/-- 双 cell 交互：op 之二元行动若有则给出落点；否则 cell 部分为 none。
    Zone 由两边 zone 之 composeZone (max) 派生；walls 累加。 -/
def interact {n : Nat} (c₁ c₂ : BitSpace n) (op : OperatorTag) :
    Option (BitSpace n) × Zone × List WallWitness :=
  let c₃ := op.apply n c₁ c₂
  let z₁ := (classify c₁ op).zone
  let z₂ := (classify c₂ op).zone
  let z  := composeZone z₁ z₂
  let walls := (classify c₁ op).walls ++ (classify c₂ op).walls
  (c₃, z, walls)

/-- 墙吸收：任一边 zone = wall → 输出 zone = wall。
    由 `composeZone_wall_left` / `composeZone_wall_right` 直接派生。 -/
theorem interact_wall_absorb_left {n : Nat} (c₁ c₂ : BitSpace n) (op : OperatorTag)
    (h : (classify c₁ op).zone = .wall) :
    (interact c₁ c₂ op).2.1 = .wall := by
  simp [interact, h]

theorem interact_wall_absorb_right {n : Nat} (c₁ c₂ : BitSpace n) (op : OperatorTag)
    (h : (classify c₂ op).zone = .wall) :
    (interact c₁ c₂ op).2.1 = .wall := by
  simp [interact, h]

end SSBX.Foundation.Hierarchy.ZoneClassifier
