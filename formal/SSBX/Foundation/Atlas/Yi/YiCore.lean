/-
# Foundation.Atlas.Yi.YiCore — 易之微核 on R-Family Hexagram

最小核：所有皆卦，法亦卦。

  唯一字 「一」（卦也）
  唯一动 「加」（卦加卦得卦）
  生 := 加一
  生生 := 生之复合

道法自然：法（生）即卦（一）也——law is in nature, not above.
生生不息：加一循环六十四而周。
二者一也：唯一闭合之两面。

无多余字，无外援。六十四卦自此得，以此判道，复以此自释。

This is the **R-Family port** of `Atlas/Yi/Classical/Core/YiCore.lean`.
The `Hexagram` carrier is now `R 6 = Fin 6 → Bool`; the index ↔
hexagram bijection is built locally via the bit-pattern encoding
`toBitNat : Hexagram → Fin 64` from `Atlas/Yi/Hexagrams.lean`.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9 (Atlas separation).
* `v4-foundation.md` v0.5 §15.6 (Hexagram = R 6).
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Hexagrams
import SSBX.Foundation.Atlas.Yi.Operators
import Mathlib.Tactic.IntervalCases

namespace SSBX.Foundation.Atlas.Yi.YiCore

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi
open SSBX.Foundation.Atlas.Yi.Hexagram (qianqian kunkun jiji weiji toBitNat toBitNat_lt mk y1 y2 y3 y4 y5 y6 ext)

/-! ## § 1 Local idx bijection (Hexagram ≃ Fin 64) via bit pattern

The R-Family `Hexagram = Fin 6 → Bool` has a natural bijection to
`Fin 64` via its bit pattern.  We use it here as the substrate of the
modular «加» (mod 64) without touching the King-Wen ordering in
`Hexagrams.lean`. -/

/-- `Hexagram → Fin 64`: pack the 6 yao into a 6-bit number. -/
def toIdx (h : Hexagram) : Fin 64 := ⟨toBitNat h, toBitNat_lt h⟩

/-- `Fin 64 → Hexagram`: unpack the 6 bits of `i.val` back to a hexagram.
    `y1` is the high bit (bit 5), `y6` is the low bit (bit 0). -/
def fromIdx (i : Fin 64) : Hexagram :=
  mk
    (decide (i.val / 32 % 2 = 1))
    (decide (i.val / 16 % 2 = 1))
    (decide (i.val / 8 % 2 = 1))
    (decide (i.val / 4 % 2 = 1))
    (decide (i.val / 2 % 2 = 1))
    (decide (i.val % 2 = 1))

/-! ### Round-trip lemmas (decide over a finite domain) -/

/-- `fromIdx (toIdx h) = h` (inverse direction 1). -/
theorem fromIdx_toIdx (h : Hexagram) : fromIdx (toIdx h) = h := by
  apply ext <;>
    (rcases h1 : h.y1 with _ | _ <;> rcases h2 : h.y2 with _ | _ <;>
     rcases h3 : h.y3 with _ | _ <;> rcases h4 : h.y4 with _ | _ <;>
     rcases h5 : h.y5 with _ | _ <;> rcases h6 : h.y6 with _ | _ <;>
     simp [fromIdx, toIdx, toBitNat, h1, h2, h3, h4, h5, h6])

/-- Auxiliary fromIdx defined on raw `Nat` (no `Fin` proof carried).
    Outside `n < 64` it is just `mk` of zero bits—harmless. -/
private def fromIdxNat (n : Nat) : Hexagram :=
  mk
    (decide (n / 32 % 2 = 1))
    (decide (n / 16 % 2 = 1))
    (decide (n / 8 % 2 = 1))
    (decide (n / 4 % 2 = 1))
    (decide (n / 2 % 2 = 1))
    (decide (n % 2 = 1))

private theorem fromIdx_eq (i : Fin 64) : fromIdx i = fromIdxNat i.val := rfl

/-- Helper: `toBitNat (fromIdxNat n) = n` for `n < 64`, exhaustive. -/
private theorem toBitNat_fromIdxNat (n : Nat) (hn : n < 64) :
    toBitNat (fromIdxNat n) = n := by
  interval_cases n <;> decide

/-- `toIdx (fromIdx i) = i` (inverse direction 2). -/
theorem toIdx_fromIdx (i : Fin 64) : toIdx (fromIdx i) = i := by
  apply Fin.ext
  show toBitNat (fromIdx i) = i.val
  rw [fromIdx_eq]
  exact toBitNat_fromIdxNat i.val i.isLt

/-! ## § 2  加 · 一 · 生 — 三字成核 -/

/-- 加：六十四卦自然加（mod 64）。 -/
def «加» (a b : Hexagram) : Hexagram :=
  fromIdx ⟨((toIdx a).val + (toIdx b).val) % 64, Nat.mod_lt _ (by omega)⟩

/-- 一：「一」之卦——bit index 为 1 (即 mk yang yang yang yang yang yin)。 -/
def «一» : Hexagram := fromIdx ⟨1, by omega⟩

/-- 生：加一也。 -/
def «生» (h : Hexagram) : Hexagram := «加» «一» h

/-- 生生：n 次生之复合。 -/
def «生生» : Nat → Hexagram → Hexagram
  | 0, h => h
  | n+1, h => «生» («生生» n h)

/-! ## § 3  关键引理 -/

/-- 由 toIdx 之等推卦之等（toIdx 为双射）。 -/
theorem «卦由索引» (h₁ h₂ : Hexagram)
    (hh : (toIdx h₁).val = (toIdx h₂).val) : h₁ = h₂ := by
  have heq : toIdx h₁ = toIdx h₂ := Fin.ext hh
  have e1 := (fromIdx_toIdx h₁).symm
  have e2 := (fromIdx_toIdx h₂).symm
  rw [e1, e2, heq]

/-- 一之索引为 1。 -/
theorem «一_toIdx» : (toIdx «一»).val = 1 := by
  show (toIdx (fromIdx ⟨1, by omega⟩)).val = 1
  rw [toIdx_fromIdx]

/-- 加之索引：两索引之和 mod 64。 -/
theorem «加_toIdx» (a b : Hexagram) :
    (toIdx («加» a b)).val
      = ((toIdx a).val + (toIdx b).val) % 64 := by
  show (toIdx (fromIdx ⟨_, _⟩)).val = _
  rw [toIdx_fromIdx]

/-- 生生之索引：n 次后即原索引加 n mod 64。 -/
theorem «生生_toIdx» (n : Nat) (h : Hexagram) :
    (toIdx («生生» n h)).val
      = ((toIdx h).val + n) % 64 := by
  induction n with
  | zero =>
    show (toIdx h).val = ((toIdx h).val + 0) % 64
    have : (toIdx h).val < 64 := (toIdx h).isLt
    omega
  | succ k ih =>
    show (toIdx («生» («生生» k h))).val
        = ((toIdx h).val + (k + 1)) % 64
    show (toIdx («加» «一» («生生» k h))).val = _
    rw [«加_toIdx», «一_toIdx», ih]
    have hh : (toIdx h).val < 64 := (toIdx h).isLt
    omega

/-! ## § 4  道法自然 — 法在卦中

  法（生）即加一。一是卦，故法是卦之化身。
  无须外授——自然之中已具其法。 -/

/-- 道法自然：存在某卦 k 使得施加 k 即施生。 -/
theorem «道法自然» : ∃ k : Hexagram, ∀ h : Hexagram, «生» h = «加» k h :=
  ⟨«一», fun _ => rfl⟩

/-- 法即卦：法之化身是 «一»，乃六十四卦之一也。 -/
theorem «法即卦» : ∃ k : Hexagram, k = «一» ∧ ∀ h, «生» h = «加» k h :=
  ⟨«一», rfl, fun _ => rfl⟩

/-! ## § 5  生生不息 — 自任卦达任卦 -/

/-- 周而复始：六十四生而归原。 -/
theorem «周而复始» : ∀ h : Hexagram, «生生» 64 h = h := by
  intro h
  apply «卦由索引»
  rw [«生生_toIdx»]
  have : (toIdx h).val < 64 := (toIdx h).isLt
  omega

/-- 生生不息：自任卦 h 起，n 步可达任卦 h'（n < 64）。 -/
theorem «生生不息» : ∀ h h' : Hexagram, ∃ n : Nat, n < 64 ∧ «生生» n h = h' := by
  intro h h'
  let nh := (toIdx h).val
  let nh' := (toIdx h').val
  have hh : nh < 64 := (toIdx h).isLt
  have hh' : nh' < 64 := (toIdx h').isLt
  refine ⟨(nh' + 64 - nh) % 64, Nat.mod_lt _ (by omega), ?_⟩
  apply «卦由索引»
  rw [«生生_toIdx»]
  show (nh + (nh' + 64 - nh) % 64) % 64 = nh'
  omega

/-! ## § 6  二者一也 — 道法自然与生生不息合于一闭合 -/

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

/-! ## § 7  自指 — 法即一卦，生施于自身 -/

/-- 自指：«生» 施于 «一» 之前驱（«乾» = 全 yang，bit-pattern 0）即得 «一» 自身。 -/
theorem «生施一即一» :
    «生» (fromIdx ⟨0, by omega⟩) = «一» := by
  apply «卦由索引»
  show (toIdx («加» «一» (fromIdx ⟨0, by omega⟩))).val
      = (toIdx «一»).val
  rw [«加_toIdx», «一_toIdx», toIdx_fromIdx]
  show (1 + 0) % 64 = 1
  omega

/-- «乾» (qianqian) 即 bit-pattern 0 之卦。 -/
theorem «乾_eq_fromIdx_0» : qianqian = fromIdx ⟨0, by omega⟩ := by
  apply ext <;> rfl

/-- 自释：法之卦施于乾即一，一施于一即二，依此六十四步而归原。 -/
theorem «乾起遍卦» (k : Nat) (hk : k < 64) :
    ∃ h : Hexagram,
      «生生» k (fromIdx ⟨0, by omega⟩) = h
      ∧ (toIdx h).val = k := by
  refine ⟨«生生» k (fromIdx ⟨0, by omega⟩), rfl, ?_⟩
  rw [«生生_toIdx»]
  show ((toIdx (fromIdx ⟨0, by omega⟩)).val + k) % 64 = k
  rw [toIdx_fromIdx]
  show (0 + k) % 64 = k
  omega

/-! ## § 8  完整六十四 — 自乾起，64 步遍历 -/

/-- 任卦皆有索引 k < 64，由乾起 k 步可达。 -/
theorem «六十四皆得» (h : Hexagram) :
    ∃ k : Nat, k < 64 ∧
    «生生» k (fromIdx ⟨0, by omega⟩) = h := by
  refine ⟨(toIdx h).val, (toIdx h).isLt, ?_⟩
  apply «卦由索引»
  rw [«生生_toIdx», toIdx_fromIdx]
  show (0 + (toIdx h).val) % 64 = (toIdx h).val
  have : (toIdx h).val < 64 := (toIdx h).isLt
  omega

/-! ## § 9  Named-hexagram accessors -/

/-- 生 施于 qianqian = «一» (since toBitNat qianqian = 0). -/
theorem «生_qianqian» : «生» qianqian = «一» := by
  apply «卦由索引»
  show (toIdx («加» «一» qianqian)).val = (toIdx «一»).val
  rw [«加_toIdx», «一_toIdx»]
  show (1 + (toIdx qianqian).val) % 64 = 1
  have hq : (toIdx qianqian).val = 0 := rfl
  rw [hq]

/-- toIdx of qianqian is 0. -/
theorem «toIdx_qianqian» : (toIdx qianqian).val = 0 := rfl

/-- toIdx of kunkun is 63 (all-yin bit pattern). -/
theorem «toIdx_kunkun» : (toIdx kunkun).val = 63 := rfl

/-! ## § 10  最小性 — 字数

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

end SSBX.Foundation.Atlas.Yi.YiCore
