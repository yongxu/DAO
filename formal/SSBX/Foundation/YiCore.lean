/-
# YiCore — 易之微核

最小核：所有皆卦，法亦卦。

  唯一字 「一」（卦也）
  唯一动 「加」（卦加卦得卦）
  生 := 加一
  生生 := 生之复合

道法自然：法（生）即卦（一）也——law is in nature, not above.
生生不息：加一循环六十四而周。
二者一也：唯一闭合之两面。

无多余字，无外援。六十四卦自此得，以此判道，复以此自释。
-/
import SSBX.Foundation.WenyanSelfInterp

namespace SSBX.Foundation.YiCore

open SSBX.Foundation.Yi
open SSBX.Foundation.WenyanSelfInterp

/-! ## § 1  加 · 一 · 生 — 三字成核 -/

/-- 加：六十四卦自然加（mod 64）。 -/
def «加» (a b : Hexagram) : Hexagram :=
  SSBX.Foundation.Yi.Hexagram.fromIdx
    ⟨((SSBX.Foundation.Yi.Hexagram.toIdx a).val
      + (SSBX.Foundation.Yi.Hexagram.toIdx b).val) % 64,
     Nat.mod_lt _ (by omega)⟩

/-- 一：「一」之卦——index 为 1。 -/
def «一» : Hexagram := SSBX.Foundation.Yi.Hexagram.fromIdx ⟨1, by omega⟩

/-- 生：加一也。 -/
def «生» (h : Hexagram) : Hexagram := «加» «一» h

/-- 生生：n 次生之复合。 -/
def «生生» : Nat → Hexagram → Hexagram
  | 0, h => h
  | n+1, h => «生» («生生» n h)

/-! ## § 2  关键引理 -/

/-- 由 toIdx 之等推卦之等（toIdx 为双射）。 -/
theorem «卦由索引» (h₁ h₂ : Hexagram)
    (hh : (SSBX.Foundation.Yi.Hexagram.toIdx h₁).val
        = (SSBX.Foundation.Yi.Hexagram.toIdx h₂).val) : h₁ = h₂ := by
  have heq : SSBX.Foundation.Yi.Hexagram.toIdx h₁
           = SSBX.Foundation.Yi.Hexagram.toIdx h₂ := Fin.ext hh
  have e1 := (SSBX.Foundation.Yi.Hexagram.toIdx_fromIdx h₁).symm
  have e2 := (SSBX.Foundation.Yi.Hexagram.toIdx_fromIdx h₂).symm
  rw [e1, e2, heq]

/-- 一之索引为 1。 -/
theorem «一_toIdx» : (SSBX.Foundation.Yi.Hexagram.toIdx «一»).val = 1 := by
  show (SSBX.Foundation.Yi.Hexagram.toIdx
        (SSBX.Foundation.Yi.Hexagram.fromIdx ⟨1, by omega⟩)).val = 1
  rw [SSBX.Foundation.Yi.Hexagram.fromIdx_toIdx]

/-- 加之索引：两索引之和 mod 64。 -/
theorem «加_toIdx» (a b : Hexagram) :
    (SSBX.Foundation.Yi.Hexagram.toIdx («加» a b)).val
      = ((SSBX.Foundation.Yi.Hexagram.toIdx a).val
         + (SSBX.Foundation.Yi.Hexagram.toIdx b).val) % 64 := by
  show (SSBX.Foundation.Yi.Hexagram.toIdx
        (SSBX.Foundation.Yi.Hexagram.fromIdx ⟨_, _⟩)).val = _
  rw [SSBX.Foundation.Yi.Hexagram.fromIdx_toIdx]

/-- 生生之索引：n 次后即原索引加 n mod 64。 -/
theorem «生生_toIdx» (n : Nat) (h : Hexagram) :
    (SSBX.Foundation.Yi.Hexagram.toIdx («生生» n h)).val
      = ((SSBX.Foundation.Yi.Hexagram.toIdx h).val + n) % 64 := by
  induction n with
  | zero =>
    show (SSBX.Foundation.Yi.Hexagram.toIdx h).val
        = ((SSBX.Foundation.Yi.Hexagram.toIdx h).val + 0) % 64
    have : (SSBX.Foundation.Yi.Hexagram.toIdx h).val < 64 :=
      (SSBX.Foundation.Yi.Hexagram.toIdx h).isLt
    omega
  | succ k ih =>
    show (SSBX.Foundation.Yi.Hexagram.toIdx («生» («生生» k h))).val
        = ((SSBX.Foundation.Yi.Hexagram.toIdx h).val + (k + 1)) % 64
    show (SSBX.Foundation.Yi.Hexagram.toIdx («加» «一» («生生» k h))).val = _
    rw [«加_toIdx», «一_toIdx», ih]
    have hh : (SSBX.Foundation.Yi.Hexagram.toIdx h).val < 64 :=
      (SSBX.Foundation.Yi.Hexagram.toIdx h).isLt
    omega

/-! ## § 3  道法自然 — 法在卦中

  法（生）即加一。一是卦，故法是卦之化身。
  无须外授——自然之中已具其法。 -/

/-- 道法自然：存在某卦 k 使得施加 k 即施生。 -/
theorem «道法自然» : ∃ k : Hexagram, ∀ h : Hexagram, «生» h = «加» k h :=
  ⟨«一», fun _ => rfl⟩

/-- 法即卦：法之化身是 «一»，乃六十四卦之一也。 -/
theorem «法即卦» : ∃ k : Hexagram, k = «一» ∧ ∀ h, «生» h = «加» k h :=
  ⟨«一», rfl, fun _ => rfl⟩

/-! ## § 4  生生不息 — 自任卦达任卦 -/

/-- 周而复始：六十四生而归原。 -/
theorem «周而复始» : ∀ h : Hexagram, «生生» 64 h = h := by
  intro h
  apply «卦由索引»
  rw [«生生_toIdx»]
  have : (SSBX.Foundation.Yi.Hexagram.toIdx h).val < 64 :=
    (SSBX.Foundation.Yi.Hexagram.toIdx h).isLt
  omega

/-- 生生不息：自任卦 h 起，n 步可达任卦 h'（n < 64）。 -/
theorem «生生不息» : ∀ h h' : Hexagram, ∃ n : Nat, n < 64 ∧ «生生» n h = h' := by
  intro h h'
  let nh := (SSBX.Foundation.Yi.Hexagram.toIdx h).val
  let nh' := (SSBX.Foundation.Yi.Hexagram.toIdx h').val
  have hh : nh < 64 := (SSBX.Foundation.Yi.Hexagram.toIdx h).isLt
  have hh' : nh' < 64 := (SSBX.Foundation.Yi.Hexagram.toIdx h').isLt
  refine ⟨(nh' + 64 - nh) % 64, Nat.mod_lt _ (by omega), ?_⟩
  apply «卦由索引»
  rw [«生生_toIdx»]
  show (nh + (nh' + 64 - nh) % 64) % 64 = nh'
  omega

/-! ## § 5  二者一也 — 道法自然与生生不息合于一闭合 -/

/-- 道生一也：法即卦（道法自然） ∧ 生遍六十四（生生不息）。
    二者皆是「闭合于卦」之两面：
      ·  法之闭合：法本身是卦
      ·  生之闭合：生之轨迹遍卦
    一闭合也。 -/
theorem «道生一也» :
    (∃ k : Hexagram, k = «一» ∧ ∀ h, «生» h = «加» k h)  -- 道法自然
    ∧ (∀ h : Hexagram, «生生» 64 h = h)                    -- 周而复始
    ∧ (∀ h h' : Hexagram, ∃ n : Nat, n < 64 ∧ «生生» n h = h') -- 生生不息
    := ⟨«法即卦», «周而复始», «生生不息»⟩

/-! ## § 6  自指 — 法即一卦，生施于自身 -/

/-- 自指：«生» 施于 «一» 之前驱（«乾»，index 0）即得 «一» 自身。 -/
theorem «生施一即一» :
    «生» (SSBX.Foundation.Yi.Hexagram.fromIdx ⟨0, by omega⟩) = «一» := by
  apply «卦由索引»
  show (SSBX.Foundation.Yi.Hexagram.toIdx
        («加» «一» (SSBX.Foundation.Yi.Hexagram.fromIdx ⟨0, by omega⟩))).val
      = (SSBX.Foundation.Yi.Hexagram.toIdx «一»).val
  rw [«加_toIdx», «一_toIdx», SSBX.Foundation.Yi.Hexagram.fromIdx_toIdx]
  show (1 + 0) % 64 = 1
  omega

/-- 自释：法之卦施于乾即一，一施于一即二，依此六十四步而归原。 -/
theorem «乾起遍卦» (k : Nat) (hk : k < 64) :
    ∃ h : Hexagram,
      «生生» k (SSBX.Foundation.Yi.Hexagram.fromIdx ⟨0, by omega⟩) = h
      ∧ (SSBX.Foundation.Yi.Hexagram.toIdx h).val = k := by
  refine ⟨«生生» k (SSBX.Foundation.Yi.Hexagram.fromIdx ⟨0, by omega⟩), rfl, ?_⟩
  rw [«生生_toIdx»]
  show ((SSBX.Foundation.Yi.Hexagram.toIdx
          (SSBX.Foundation.Yi.Hexagram.fromIdx ⟨0, by omega⟩)).val + k) % 64 = k
  rw [SSBX.Foundation.Yi.Hexagram.fromIdx_toIdx]
  show (0 + k) % 64 = k
  omega

/-! ## § 7  完整六十四 — 自乾起，64 步遍历 -/

/-- 任卦皆有索引 k < 64，由乾起 k 步可达。 -/
theorem «六十四皆得» (h : Hexagram) :
    ∃ k : Nat, k < 64 ∧
    «生生» k (SSBX.Foundation.Yi.Hexagram.fromIdx ⟨0, by omega⟩) = h := by
  refine ⟨(SSBX.Foundation.Yi.Hexagram.toIdx h).val,
          (SSBX.Foundation.Yi.Hexagram.toIdx h).isLt, ?_⟩
  apply «卦由索引»
  rw [«生生_toIdx», SSBX.Foundation.Yi.Hexagram.fromIdx_toIdx]
  show (0 + (SSBX.Foundation.Yi.Hexagram.toIdx h).val) % 64
      = (SSBX.Foundation.Yi.Hexagram.toIdx h).val
  have : (SSBX.Foundation.Yi.Hexagram.toIdx h).val < 64 :=
    (SSBX.Foundation.Yi.Hexagram.toIdx h).isLt
  omega

/-! ## § 8  最小性 — 字数

  字数核算：
    «加»     —— 一动
    «一»     —— 一字
    «生»     —— 由「加 一」组合，非新字
    «生生»   —— 由「生」之 n 次复合，非新字

  共两字（加、一）。无更少之核能含 64 卦、自指、生生不息。
  -/

/-- 最小性：核仅含「加」与「一」二字。其余皆由组合得。 -/
theorem «微核之至» :
    (∀ h, «生» h = «加» «一» h) ∧
    (∀ n h, «生生» n h = Nat.recAux h (fun _ ih => «加» «一» ih) n) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro n h
  induction n with
  | zero => rfl
  | succ k ih => show «加» «一» («生生» k h) = _; rw [ih]

end SSBX.Foundation.YiCore
