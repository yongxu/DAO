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
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.BaguaAlgebra
import SSBX.Foundation.Eight.LuoJi

set_option linter.unusedSimpArgs false

namespace SSBX.Foundation.Eight.XinZhi

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Eight.LuoJi

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

/-! ## § 8 神经科学接口 · Hopfield-like + Hebbian (Phase 4 先行)

神经元 ≅ Yao（fire / rest）；3 神经元同步 pattern ≅ Trigram；
8 卦 ≅ 8 Hopfield-like attractor states（finite 离散版 Hopfield）。
Hebbian "neurons that fire together wire together"：在 (Z/2)³ flip 群上即"两 pattern 同步 → 加强连接"。
此处以 finite 框架陈述；连续动力（Hopfield 之 Lyapunov ODE）属 Phase 4 之 Mathlib 工作。 -/

/-- **神经元**：fire（激发）= yang，rest（静息）= yin。 -/
abbrev Neuron : Type := Yao

/-- **3 神经元同步 pattern**：三神经元之同时状态。 -/
abbrev Pattern3 : Type := Trigram

/-- **Hopfield-like attractor 总数 = 8**：八卦正好枚举所有 3-神经元 pattern。 -/
theorem hopfield_attractor_count : Trigram.all.length = 8 := by decide

/-- **Hebbian-like 转移**：从 current pattern 到 target，即应用 (Z/2)³ 中 (current → target) flip 于 current。
    "Pattern 同步" 即两 pattern 之差，"加强" 即此 flip 之 commit 至记忆。 -/
def hebbianTransition (current target : Pattern3) : Pattern3 :=
  transform current target current

/-- **Hebbian 之 transform_correct**：从 current 出发 + Hebbian flip → target。 -/
theorem hebbian_reaches_target (current target : Pattern3) :
    hebbianTransition current target = target :=
  transform_correct current target

/-- **firing rate（阴爻数）= 静神经元数**。 -/
def Pattern3.restCount (p : Pattern3) : Nat := Trigram.yinCount_helper p
where
  Trigram.yinCount_helper (t : Trigram) : Nat :=
    (if t.y1 = .yin then 1 else 0)
    + (if t.y2 = .yin then 1 else 0)
    + (if t.y3 = .yin then 1 else 0)

/-- **乾 pattern 之 restCount = 0**（全 fire）。 -/
theorem restCount_qian : Pattern3.restCount Trigram.qian = 0 := by decide

/-- **坤 pattern 之 restCount = 3**（全 rest）。 -/
theorem restCount_kun : Pattern3.restCount Trigram.kun = 3 := by decide

/-! ## § 9 现象学时间意识三相 · Husserl (Phase 4 先行)

Husserl 之内时间意识三相：
- retention（保持 / 刚过去）= 初爻 y₁
- primal impression（原印象 / 当下）= 中爻 y₂
- protention（前摄 / 即将）= 上爻 y₃

三爻 ≅ 三相 是 finite 离散骨架；连续 modulation 属 Phase 4 之 Mathlib 工作。 -/

/-- **时间意识三相**。 -/
inductive TimePhase : Type
  | retention      -- 保持（刚过去）
  | primalImpr     -- 原印象（当下）
  | protention     -- 前摄（即将）
  deriving DecidableEq, Repr

/-- 三相穷尽。 -/
def TimePhase.all : List TimePhase :=
  [.retention, .primalImpr, .protention]

theorem timephase_all_length : TimePhase.all.length = 3 := rfl

/-- **三相 → 三爻位置**：retention → 初爻，primalImpr → 中爻，protention → 上爻。 -/
def TimePhase.toFin3 : TimePhase → Fin 3
  | .retention   => 0
  | .primalImpr  => 1
  | .protention  => 2

/-- **三相投影到 Trigram**：从 Trigram 取对应爻之 yin/yang。 -/
def TimePhase.proj (t : Trigram) : TimePhase → Yao
  | .retention   => t.y1
  | .primalImpr  => t.y2
  | .protention  => t.y3

/-- **乾 之三相皆 yang**。 -/
theorem qian_all_yang (p : TimePhase) : TimePhase.proj Trigram.qian p = .yang := by
  cases p <;> rfl

/-- **坤 之三相皆 yin**。 -/
theorem kun_all_yin (p : TimePhase) : TimePhase.proj Trigram.kun p = .yin := by
  cases p <;> rfl

/-- **时间流之离散一步**：cyclic shift（retention ← primalImpr ← protention ← new）。
    Finite 版本：retention 出，protention 入新值。 -/
def timeFlow (newProtention : Yao) (t : Trigram) : Trigram :=
  ⟨t.y2, t.y3, newProtention⟩

/-- **时间流保 protention 之新输入**。 -/
theorem timeFlow_protention (newP : Yao) (t : Trigram) :
    (timeFlow newP t).y3 = newP := rfl

/-- **时间流之 primalImpr 由前一刻 protention 接续**。 -/
theorem timeFlow_continuity (newP : Yao) (t : Trigram) :
    (timeFlow newP t).y2 = t.y3 := rfl

/-- **时间流之 retention 由前一刻 primalImpr 接续**。 -/
theorem timeFlow_retention (newP : Yao) (t : Trigram) :
    (timeFlow newP t).y1 = t.y2 := rfl

/-- **三相互不相等**。 -/
theorem retention_ne_primalImpr : TimePhase.retention ≠ TimePhase.primalImpr := by decide
theorem primalImpr_ne_protention : TimePhase.primalImpr ≠ TimePhase.protention := by decide
theorem retention_ne_protention : TimePhase.retention ≠ TimePhase.protention := by decide

/-! ## § 10 公开摘要 -/

/-- **心智总摘要**（含 Phase 4 先行：神经 + 时间）：
    (1) 四分穷尽 4 元
    (2) 四端穷尽 4 元
    (3) 四分 ≅ Bool² 四象（双向 roundtrip）
    (4) 四端 → 四正卦 单射
    (5) 注意力函子 transform_correct
    (6) 三值认同 ≅ K3 TriV
    (7) 悬置 ≠ 认同（U ⇏ ⊤ 在心智）
    (8) 自证 = identity（必有不动点）
    (9) Hopfield-like attractor count = 8
    (10) Hebbian transition reaches target
    (11) 时间三相穷尽 3 元
    (12) 时间流保 continuity（primalImpr ← 上一刻 protention）-/
theorem xinzhi_summary :
    (FenSi.all.length = 4)
    ∧ (SiDuan.all.length = 4)
    ∧ (∀ f : FenSi, SiXiang.toFenSi (FenSi.toSiXiang f) = f)
    ∧ (∀ s : SiXiang, FenSi.toSiXiang (SiXiang.toFenSi s) = s)
    ∧ (∀ a b : SiDuan, SiDuan.toTrigram a = SiDuan.toTrigram b → a = b)
    ∧ (∀ a b : Trigram, Att a b a = b)
    ∧ (∀ x : XinZ, TriV.toXinZ (XinZ.toTriV x) = x)
    ∧ (XinZ.xuan ≠ XinZ.ren)
    ∧ (∀ m : FenSi, AttZiZheng m = m)
    ∧ (Trigram.all.length = 8)
    ∧ (∀ c t : Pattern3, hebbianTransition c t = t)
    ∧ (TimePhase.all.length = 3)
    ∧ (∀ newP : Yao, ∀ t : Trigram, (timeFlow newP t).y2 = t.y3) :=
  ⟨fensi_all_length, siduan_all_length,
   fensi_sixiang_roundtrip, sixiang_fensi_roundtrip,
   siduan_toTrigram_injective, att_correct,
   xinz_triv_roundtrip, xuan_ne_ren, ziZheng_fixed,
   hopfield_attractor_count, hebbian_reaches_target,
   timephase_all_length, timeFlow_continuity⟩

end SSBX.Foundation.Eight.XinZhi
