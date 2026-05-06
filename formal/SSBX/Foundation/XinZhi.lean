/-
# XinZhi — 心智 · 唯识四分 / 心学四端 / 注意力函子之最薄骨架

Companion document: `四级生成_太极两翼四象八卦/心智 · 从元到识.md`

This file gives the **finite, no-Mathlib** core of the **心智** 衍 file:
  § 1   唯识四分 FenSi (相 / 见 / 自证 / 证自证) inductive
  § 2   FenSi ≅ SiXiang （Bool² 笛卡尔积之严格同构）
  § 3   心学四端 SiDuan (恻隐 / 羞恶 / 辞让 / 是非) inductive
  § 4   SiDuan ≅ 四正卦 （Trigram 之 li / kan / zhen / dui 之具体映射）
  § 5   注意力函子 Att （Trigram → Trigram）
  § 6   三值悬置 之心智 instance（接 LuoJi）
  § 7   公开摘要

## 道理二分立场
本文件仅依 Lean stdlib + Yi.lean + BaguaAlgebra + LuoJi，不引入 Mathlib。
神经科学 / 现象学时间意识 / 八识 等 future work（需 Husserl 严格化或大脑模型）。
-/
import SSBX.Foundation.Yi
import SSBX.Foundation.BaguaAlgebra
import SSBX.Foundation.LuoJi

set_option linter.unusedSimpArgs false

namespace SSBX.Foundation.XinZhi

open SSBX.Foundation.Yi
open SSBX.Foundation.BaguaAlgebra
open SSBX.Foundation.LuoJi

/-! ## § 1 唯识四分 -/

/-- **唯识四分**（陈那 / 护法之识之四分）：
    - 相分 (相) - 所观对象（境）
    - 见分 (见) - 能观主体（直接知）
    - 自证 - 知"我在见"
    - 证自证 - 知"我知我在见" -/
inductive FenSi : Type
  | xiang     -- 相分（所对）
  | jian      -- 见分（能观）
  | ziZheng   -- 自证（知我知）
  | zhengZi   -- 证自证（知我知我知）
  deriving DecidableEq, Repr

/-- 四分穷尽。 -/
def FenSi.all : List FenSi :=
  [.xiang, .jian, .ziZheng, .zhengZi]

theorem fensi_all_length : FenSi.all.length = 4 := rfl

/-! ## § 2 唯识四分 ≅ 四象之 Bool² 同构 -/

/-- 四分 → 四象 之映射。
    主体性轴 (主 = T / 客 = F) × 知性轴 (知 = T / 被知 = F)：
    - 见 = (T, T) = 太阳（主纯活）
    - 相 = (T, F) = 少阴（主对客）
    - 自证 = (F, T) = 少阳（客对主，反观）
    - 证自证 = (F, F) = 太阴（客纯静）-/
def FenSi.toSiXiang : FenSi → SiXiang
  | .jian     => SiXiang.taiYang   -- ⟨阳, 阳⟩
  | .xiang    => SiXiang.shaoYin   -- ⟨阳, 阴⟩
  | .ziZheng  => SiXiang.shaoYang  -- ⟨阴, 阳⟩
  | .zhengZi  => SiXiang.taiYin    -- ⟨阴, 阴⟩

/-- 四象 → 四分 之逆映射。 -/
def SiXiang.toFenSi (s : SiXiang) : FenSi :=
  match s.y1, s.y2 with
  | .yang, .yang => .jian
  | .yang, .yin  => .xiang
  | .yin,  .yang => .ziZheng
  | .yin,  .yin  => .zhengZi

/-- **四分 → 四象 → 四分 = id**（左可逆）。 -/
theorem fensi_sixiang_roundtrip (f : FenSi) :
    SiXiang.toFenSi (FenSi.toSiXiang f) = f := by
  cases f <;> rfl

/-- **四象 → 四分 → 四象 = id**（右可逆）。 -/
theorem sixiang_fensi_roundtrip (s : SiXiang) :
    FenSi.toSiXiang (SiXiang.toFenSi s) = s := by
  cases s with
  | mk y1 y2 =>
    cases y1 <;> cases y2 <;>
      simp [SiXiang.toFenSi, FenSi.toSiXiang,
            SiXiang.taiYang, SiXiang.shaoYin,
            SiXiang.shaoYang, SiXiang.taiYin]

/-! ## § 3 心学四端 -/

/-- **心学四端**（孟子《公孙丑上》）：
    - 恻隐之心（仁之端）
    - 羞恶之心（义之端）
    - 辞让之心（礼之端）
    - 是非之心（智之端）-/
inductive SiDuan : Type
  | ceYin   -- 恻隐（仁）
  | xiuWu   -- 羞恶（义）
  | ciRang  -- 辞让（礼）
  | shiFei  -- 是非（智）
  deriving DecidableEq, Repr

/-- 四端穷尽。 -/
def SiDuan.all : List SiDuan :=
  [.ceYin, .xiuWu, .ciRang, .shiFei]

theorem siduan_all_length : SiDuan.all.length = 4 := rfl

/-! ## § 4 心学四端 ≅ 四正卦 之意象 + 阴阳映射

四正卦：离 (li) / 坎 (kan) / 震 (zhen) / 兑 (dui)
- 恻隐 → 仁 → 离 (火，向外照人)
- 羞恶 → 义 → 坎 (水，自止其溺)
- 辞让 → 礼 → 震 (雷，仰让于序)
- 是非 → 智 → 兑 (泽，析判有无) -/

/-- 四端 → 四正卦 之映射。 -/
def SiDuan.toTrigram : SiDuan → Trigram
  | .ceYin   => Trigram.li
  | .xiuWu   => Trigram.kan
  | .ciRang  => Trigram.zhen
  | .shiFei  => Trigram.dui

/-- 6 对不等式由 `siduan_toTrigram_injective` 之 contrapositive 立得；此处记 SiDuan 之 inductive 不等。 -/
theorem ceYin_ne_xiuWu : SiDuan.ceYin ≠ SiDuan.xiuWu := by decide

/-- **四端各自之具体 Trigram 值**（用于注入性论证）。 -/
theorem siduan_to_li : SiDuan.toTrigram .ceYin = Trigram.li := rfl
theorem siduan_to_kan : SiDuan.toTrigram .xiuWu = Trigram.kan := rfl
theorem siduan_to_zhen : SiDuan.toTrigram .ciRang = Trigram.zhen := rfl
theorem siduan_to_dui : SiDuan.toTrigram .shiFei = Trigram.dui := rfl

/-- **四端 → 四正卦 是单射**：四个不同卦对应四个不同端（通过 16 case 检验）。 -/
theorem siduan_toTrigram_injective :
    ∀ a b : SiDuan, SiDuan.toTrigram a = SiDuan.toTrigram b → a = b := by
  intro a b h
  cases a <;> cases b <;>
    first
      | rfl
      | (exfalso; exact absurd h (by
          simp only [SiDuan.toTrigram, Trigram.li, Trigram.kan, Trigram.zhen, Trigram.dui]
          intro heq
          injection heq with h1 h2 h3
          first | exact Yao.noConfusion h1 | exact Yao.noConfusion h2 | exact Yao.noConfusion h3))

/-! ## § 5 注意力函子 -/

/-- **注意力转移**：从一卦到另一卦。借 BaguaAlgebra `transform`。 -/
def Att (a b : Trigram) : Trigram → Trigram := transform a b

/-- **注意力之单位**：起点 = 终点 时 注意力 = id（在起点上）。 -/
theorem att_id (a : Trigram) : Att a a a = a := by
  unfold Att
  exact transform_correct a a

/-- **注意力之 transform_correct**：在起点上之 attention 给终点。 -/
theorem att_correct (a b : Trigram) : Att a b a = b :=
  transform_correct a b

/-- **错卦作 全域注意力**：从乾到坤之注意力 = cuo。 -/
theorem att_qian_kun_via_cuo : Att qian kun qian = kun := by
  exact transform_correct qian kun

/-! ## § 6 心智 K3 三值之 inductive 重述 -/

/-- **心智之三值认同状态**：信 / 不信 / 悬置。 -/
inductive XinZ : Type
  | ren    -- 认同 (truthful conviction, ⊤)
  | bu     -- 否认 (denial, ⊥)
  | xuan   -- 悬置 (suspended, U)
  deriving DecidableEq, Repr

/-- 三态穷尽。 -/
def XinZ.all : List XinZ := [.ren, .bu, .xuan]

theorem xinz_all_length : XinZ.all.length = 3 := rfl

/-- **心智三值 ≅ K3 三值**（同构）。 -/
def XinZ.toTriV : XinZ → TriV
  | .ren  => .T
  | .bu   => .F
  | .xuan => .U

def TriV.toXinZ : TriV → XinZ
  | .T => .ren
  | .F => .bu
  | .U => .xuan

theorem xinz_triv_roundtrip (x : XinZ) : TriV.toXinZ (XinZ.toTriV x) = x := by
  cases x <;> rfl

theorem triv_xinz_roundtrip (t : TriV) : XinZ.toTriV (TriV.toXinZ t) = t := by
  cases t <;> rfl

/-- **悬置 ≠ 认同**（U⇏⊤ 在心智）。 -/
theorem xuan_ne_ren : XinZ.xuan ≠ XinZ.ren := by decide

/-- **悬置 ≠ 否认**。 -/
theorem xuan_ne_bu : XinZ.xuan ≠ XinZ.bu := by decide

/-! ## § 7 自证分 = 不动点 -/

/-- **自证算子**：心智在自证分上 = identity（自见自身）。 -/
def AttZiZheng (m : FenSi) : FenSi := m

/-- **自证算子任意输入皆不动点**。 -/
theorem ziZheng_fixed (m : FenSi) : AttZiZheng m = m := rfl

/-! ## § 8 公开摘要 -/

/-- **心智总摘要**：
    (1) 四分穷尽 4 元
    (2) 四端穷尽 4 元
    (3) 四分 ≅ Bool² 四象（双向 roundtrip）
    (4) 四端 → 四正卦 单射
    (5) 注意力函子 transform_correct
    (6) 三值认同 ≅ K3 TriV
    (7) 悬置 ≠ 认同（U ⇏ ⊤ 在心智）
    (8) 自证 = identity（必有不动点）-/
theorem xinzhi_summary :
    (FenSi.all.length = 4)
    ∧ (SiDuan.all.length = 4)
    ∧ (∀ f : FenSi, SiXiang.toFenSi (FenSi.toSiXiang f) = f)
    ∧ (∀ s : SiXiang, FenSi.toSiXiang (SiXiang.toFenSi s) = s)
    ∧ (∀ a b : SiDuan, SiDuan.toTrigram a = SiDuan.toTrigram b → a = b)
    ∧ (∀ a b : Trigram, Att a b a = b)
    ∧ (∀ x : XinZ, TriV.toXinZ (XinZ.toTriV x) = x)
    ∧ (XinZ.xuan ≠ XinZ.ren)
    ∧ (∀ m : FenSi, AttZiZheng m = m) :=
  ⟨fensi_all_length, siduan_all_length,
   fensi_sixiang_roundtrip, sixiang_fensi_roundtrip,
   siduan_toTrigram_injective, att_correct,
   xinz_triv_roundtrip, xuan_ne_ren, ziZheng_fixed⟩

end SSBX.Foundation.XinZhi
