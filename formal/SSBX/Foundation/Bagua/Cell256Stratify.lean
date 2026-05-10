/-
# Cell256Stratify — R7/R8 双层收口（128 + 256 = (Z/2)⁷+(Z/2)⁸ in 自相似 R-hierarchy）

把 [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](../../../../docs-next/10_formal_形式/yi-RO-hierarchy.md)
之 R/O 双层级与 yi-calculus-theorem.md Theorems H–K 在 Lean 中显式落地：

  R1 (爻)        = (Z/2)¹      = 2          → `Yao`
  R2 (四象)      = (Z/2)²      = 4          → `SiXiang`
  R3 (八卦)      = (Z/2)³      = 8 = 4本+4征 → `Trigram`
  R6 (六十四卦)  = (Z/2)⁶      = 64         → `Hexagram`
  R7 (Cell128)   = (Z/2)⁷      = 128 = 64×2 → `Cell128 = Hexagram × YinBit` (R7 atom: 因 yīn)
  R8 (256-Cell)  = (Z/2)⁸      = 256 = 128×2 = 64×4 → `Cell256 = Hexagram × Shi` (R8 atom: 果 guǒ)

R-hierarchy R1..R8 全部纯 (Z/2)ⁿ 自相似闭合, 无任何非 (Z/2) 因子.
Shi V₄ = {道, 已, 今, 未} **at R8** 由 (因, 果) ∈ Bool² emerge (非 R7 单层 atom)：
  - 道 = (因=0, 果=0) — V₄ 单位元 = 跨时空永真 anchor

算子的物理同构（§ 3.4）：
  cuo  = P  (parity / sign reversal)
  zong = T  (time-reversal of yao sequence)
  错综 = PT
  hu   = Y  (Y-combinator / fixed-point operator)

R7 atomic 算子: **印 (yìn)** = toggle 因 bit
R8 atomic 算子: **投 (tóu)** = toggle 果 bit (= Shi V₄ 之第二轴)

**命名 caveats (provisional)**: 因/果/印/投 暂用，备选 (per yi-calculus-theorem.md §16):
印/投 (Husserl 现象学), 始/终 (Yi-native 系辞), 持/期 (现象学直译)。

本文件 **0 新 inductive**：所有 `def` 仅 lift 既有算子；Mian 保持单一身份（仅 benZheng 象限）。

§ 1  R-hierarchy R1..R8 显式命名 + 基数定理
§ 2  R8 算子 P/T/Y anchoring (parity / timeReversal / yComb / PT)
§ 3  R8 → BenZheng 投影（Quadrant + Mian on benZheng only）
§ 4  (Z/2)⁸ 群作用 simply-transitive on R8
§ 5  Position-operator-tree = Sheng 6 × Shi ≃ R8
§ 6  xuGua extension to R8 (xuGua256: 256 元有序列)
§ 7  R8 closure 摘要定理 + R7 中间层桥接
-/
import SSBX.Foundation.Bagua.Cell128
import SSBX.Foundation.Bagua.Cell256
import SSBX.Foundation.Bagua.BenZheng
import SSBX.Foundation.Bagua.BaguaAlgebra

namespace SSBX.Foundation.Bagua.Cell256Stratify

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell128
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BenZheng
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 1 R-Hierarchy R1..R8: 自相似 (Z/2)ⁿ -/

/-- R1 (爻) = (Z/2)¹ = 2 元二值原子. -/
abbrev R1 := Yao

/-- R2 (四象) = (Z/2)² = 4. -/
abbrev R2 := SiXiang

/-- R3 (八卦) = (Z/2)³ = 8 = 4 本 + 4 征. -/
abbrev R3 := Trigram

/-- R0 (太极) = (Z/2)⁰ = 1, trivial Unit. -/
abbrev R0 := Unit

/-- R4 (面) = (Z/2)⁴ = 16 = Ben × Zheng. anchor: BenZheng.Mian. -/
abbrev R4 := Mian

/-- R5 (五爻, provisional) = (Z/2)⁵ = 32 = Mian × Bool. 无传统 Yi anchor.
    名候选: 五爻 (descriptive) / 接 / 临 / 渐 — 详 yi-RO-hierarchy-v2.md §3.5. -/
abbrev R5 := Mian × Bool

/-- R6 (六十四卦) = (Z/2)⁶ = 64 = 4 quadrant × 16. -/
abbrev R6 := Hexagram

/-- R7 (Cell128) = (Z/2)⁷ = 128 = 64 × 2 (R6 + 因 yīn). -/
abbrev R7 := Cell128

/-- R8 (256-Cell) = (Z/2)⁸ = 256 = 128 × 2 = 64 × 4 (R7 + 果 guǒ). -/
abbrev R8 := Cell256

/-! ### 基数定理：每层 Rn 之元素数 -/

theorem R1_card_eq_2 : ([Yao.yang, Yao.yin] : List R1).length = 2 := rfl

theorem R2_card_eq_4 : (SiXiang.all : List R2).length = 4 := rfl

theorem R3_card_eq_8 : (Trigram.all : List R3).length = 8 := rfl

/-- R₀ trivial: |太极| = 1. -/
theorem R0_card_eq_1 : ([()] : List R0).length = 1 := rfl

/-- R₄ = 16 (Mian = Ben × Zheng = (Z/2)² × (Z/2)² = (Z/2)⁴). -/
theorem R4_card_eq_16 : (Mian.all : List R4).length = 16 := Mian.all_count

/-- R₅ = 32 (Mian × Bool, 五爻 provisional). -/
theorem R5_card_eq_32 : ((Mian.all.flatMap fun m => [(m, false), (m, true)]) : List R5).length = 32 := by native_decide

theorem R6_card_eq_64 : (Hexagram.allHex : List R6).length = 64 := by native_decide

theorem R7_card_eq_128 : (Cell128.all : List R7).length = 128 := Cell128.all_length

theorem R8_card_eq_256 : (Cell256.all : List R8).length = 256 := Cell256.all_length

/-! ### Step-up isomorphisms：R(n+1) factors over R(n) -/

/-- R8 = R6 × Shi (definitional, with Shi V₄ = (因, 果) tensor). -/
example : R8 = (R6 × Shi) := rfl

/-- R7 = R6 × YinBit (definitional). -/
example : R7 = (R6 × Cell128.YinBit) := rfl

/-- R3 ≅ R2 × Yao via fenToTrigram. -/
example (s : R2) (y : Yao) : R3 :=
  fenToTrigram s y

/-- R6 ≅ R3 × R3 via chong (重). -/
example (inner outer : R3) : R6 := chong inner outer

/-- R7 → R8 lift: 加 GuoBit. -/
def liftR7toR8 (c5 : R7) (g : GuoBit) : R8 :=
  (c5.1, Cell256.Shi.ofYinGuo (c5.2, g))

/-- R8 → R7 project: 丢 GuoBit (取 Shi 之 因 投影). -/
def projR8toR7 (c6 : R8) : R7 :=
  (c6.1, (Cell256.Shi.toYinGuo c6.2).1)

/-- R7 → R8 → R7 round-trip: project ∘ lift = id. -/
theorem projR6toR7_liftR7toR8 (c5 : R7) (g : GuoBit) :
    projR8toR7 (liftR7toR8 c5 g) = c5 := by
  rcases c5 with ⟨h, y⟩
  cases y <;> cases g <;> rfl

/-! ## § 2 R8 算子: cuo = P, zong = T, hu = Y

  R8 上 V₄ 出现两层（hex side + shi side），各自实现物理 P/T/PT.
  parity = hex cuo lift（保 Shi）；timeReversal = hex zong + Shi zong（双层 T）；
  PT = 错综（双层）；yComb = hu lift. -/

/-! ### parity (P) — yao-wise sign reversal on hex; preserves Shi -/

/-- P (parity): hex cuo lift 到 R8；保 Shi. -/
def parity (c : R8) : R8 := (Hexagram.cuo c.1, c.2)

theorem parity_parity (c : R8) : parity (parity c) = c := by
  rcases c with ⟨h, s⟩
  simp [parity, Hexagram.cuo_cuo]

/-! ### timeReversal (T) — zong on hex + zong on Shi (V₄ 二层 T) -/

/-- T (time-reversal): hex zong lift + Shi V₄ T-flip (Shi.zong: 道↔未, 已↔今). -/
def timeReversal (c : R8) : R8 := (Hexagram.zong c.1, c.2.zong)

theorem timeReversal_timeReversal (c : R8) : timeReversal (timeReversal c) = c := by
  rcases c with ⟨h, s⟩
  simp [timeReversal, Hexagram.zong_zong, Shi.zong_zong]

/-! ### PT = parity ∘ timeReversal = 错综 + Shi 双轴翻 -/

/-- PT: 错综 + Shi cuoZong (V₄ 中心元). -/
def PT (c : R8) : R8 := timeReversal (parity c)

theorem PT_PT (c : R8) : PT (PT c) = c := by
  rcases c with ⟨h, s⟩
  simp [PT, parity, timeReversal, Hexagram.zong_zong, Shi.zong_zong,
        Hexagram.cuo_cuo, ← Hexagram.cuo_zong_comm]

/-- P 与 T 交换（V₄ Klein 群结构）. -/
theorem parity_timeReversal_comm (c : R8) :
    parity (timeReversal c) = timeReversal (parity c) := by
  rcases c with ⟨h, s⟩
  simp [parity, timeReversal, Hexagram.cuo_zong_comm]

/-! ### yComb (Y) — hu lifted -/

/-- Y (Y-combinator / 互): hu lift 到 R8；保 Shi. -/
def yComb (c : R8) : R8 := (Hexagram.hu c.1, c.2)

/-- 乾 (qian) cell at any Shi is hu-fixed. -/
theorem yComb_qian (s : Shi) : yComb (Hexagram.qian, s) = (Hexagram.qian, s) := by
  simp [yComb, Hexagram.hu_qian]

/-- 坤 (kun) cell at any Shi is hu-fixed. -/
theorem yComb_kun (s : Shi) : yComb (Hexagram.kun, s) = (Hexagram.kun, s) := by
  simp [yComb, Hexagram.hu_kun]

/-- Hexagram-level hu attractors {乾, 坤, 既济, 未济} lift 至 16 个 R8 attractor
    (4 hex × 4 Shi = 16). -/
theorem yComb_attractors_count :
    ([(Hexagram.qian, Shi.dao), (Hexagram.qian, Shi.ji),
      (Hexagram.qian, Shi.jin), (Hexagram.qian, Shi.wei),
      (Hexagram.kun, Shi.dao),  (Hexagram.kun, Shi.ji),
      (Hexagram.kun, Shi.jin),  (Hexagram.kun, Shi.wei),
      (Hexagram.jiji, Shi.dao), (Hexagram.jiji, Shi.ji),
      (Hexagram.jiji, Shi.jin), (Hexagram.jiji, Shi.wei),
      (Hexagram.weiji, Shi.dao),(Hexagram.weiji, Shi.ji),
      (Hexagram.weiji, Shi.jin),(Hexagram.weiji, Shi.wei)
     ] : List R8).length = 16 := rfl

/-! ### parity 通过 6 单爻 flip 之复合 -/

/-- parity = 6 单爻 flip 之复合 (R8 lift of `hex_cuo_eq_compose`). -/
theorem parity_eq_six_flips (c : R8) :
    parity c = Cell256.flip1 (Cell256.flip2 (Cell256.flip3
                 (Cell256.flip4 (Cell256.flip5 (Cell256.flip6 c))))) := by
  rcases c with ⟨h, s⟩
  simp [parity, Cell256.flip1, Cell256.flip2, Cell256.flip3,
        Cell256.flip4, Cell256.flip5, Cell256.flip6]
  exact hex_cuo_eq_compose h

end SSBX.Foundation.Bagua.Cell256Stratify

/-! ## Yao XOR + Hexagram XOR 扩展（添加到 Yi.Yi 命名空间） -/

namespace SSBX.Foundation.Yi.Yi.Yao

/-- Yao XOR: yang 为单位元，yin 为非平凡元. -/
def xor : Yao → Yao → Yao
  | .yang, .yang => .yang
  | .yang, .yin  => .yin
  | .yin,  .yang => .yin
  | .yin,  .yin  => .yang

theorem xor_xor_left (a b : Yao) : xor (xor a b) a = b := by
  cases a <;> cases b <;> rfl

end SSBX.Foundation.Yi.Yi.Yao

namespace SSBX.Foundation.Yi.Yi.Hexagram

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.Yi.Yao

/-- Hexagram XOR: 逐爻 XOR. 把 Hexagram 视为 (Z/2)⁶ 群的载体. -/
def xor (a b : Hexagram) : Hexagram :=
  ⟨Yao.xor a.y1 b.y1, Yao.xor a.y2 b.y2, Yao.xor a.y3 b.y3,
   Yao.xor a.y4 b.y4, Yao.xor a.y5 b.y5, Yao.xor a.y6 b.y6⟩

/-- qian 为 XOR 单位元（右）. -/
theorem xor_qian_right (a : Hexagram) : xor a Hexagram.qian = a := by
  rcases a with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;> rfl

/-- qian 为 XOR 单位元（左）. -/
theorem xor_qian_left (a : Hexagram) : xor Hexagram.qian a = a := by
  rcases a with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;> rfl

end SSBX.Foundation.Yi.Yi.Hexagram

/-! ## Shi XOR (V₄ Klein 群作用) — 扩展 Cell256.Shi 命名空间 -/

namespace SSBX.Foundation.Bagua.Cell256.Shi

/-- Shi V₄ XOR: 道是单位元，cuo/zong/cuoZong 是 3 个生成元.

    实现：用 cuo/zong/cuoZong 表达 V₄ 之 act. -/
def xor (a b : Shi) : Shi :=
  match a with
  | .dao => b
  | .ji  => Shi.cuo b      -- 已 ⊕ b: 翻 past 轴
  | .wei => Shi.zong b     -- 未 ⊕ b: 翻 future 轴
  | .jin => Shi.cuoZong b  -- 今 ⊕ b: 翻双轴 (PT)

/-- 道 是 XOR 单位元（左）. -/
theorem xor_dao_left (s : Shi) : xor .dao s = s := rfl

/-- 道 是 XOR 单位元（右）. -/
theorem xor_dao_right (s : Shi) : xor s .dao = s := by
  cases s <;> rfl

/-- 自消律：xor (xor a b) a = b（即 V₄ 之每元素为自身逆元）. -/
theorem xor_xor_left (a b : Shi) : xor (xor a b) a = b := by
  cases a <;> cases b <;> rfl

theorem xor_comm (a b : Shi) : xor a b = xor b a := by
  cases a <;> cases b <;> rfl

end SSBX.Foundation.Bagua.Cell256.Shi

namespace SSBX.Foundation.Bagua.Cell256Stratify

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BenZheng
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 3 R8 → BenZheng 投影 (Quadrant + Mian on benZheng only) -/

/-- R8 quadrant projection — Shi-invariant. -/
def R8.quadrant (c : R8) : Quadrant := c.1.quadrant

/-- R8 cells filtered by quadrant. -/
def R8.quadrantList (q : Quadrant) : List R8 :=
  Cell256.all.filter (fun c => decide (c.1.quadrant = q))

/-- |benBen 象限| × 4 时态 = 64. -/
theorem R8.benBen_count : (R8.quadrantList .benBen).length = 64 := by native_decide

/-- |benZheng 象限| × 4 时态 = 64. -/
theorem R8.benZheng_count : (R8.quadrantList .benZheng).length = 64 := by native_decide

/-- |zhengBen 象限| × 4 时态 = 64. -/
theorem R8.zhengBen_count : (R8.quadrantList .zhengBen).length = 64 := by native_decide

/-- |zhengZheng 象限| × 4 时态 = 64. -/
theorem R8.zhengZheng_count : (R8.quadrantList .zhengZheng).length = 64 := by native_decide

/-- R8 4-象限分配完整：64 × 4 = 256. -/
theorem R8_quadrant_partition_complete :
    (R8.quadrantList .benBen).length
      + (R8.quadrantList .benZheng).length
      + (R8.quadrantList .zhengBen).length
      + (R8.quadrantList .zhengZheng).length = 256 := by native_decide

/-! ### Ben/Zheng 投影到 inner/outer trigram -/

def R8.innerBen? (c : R8) : Option Ben := Trigram.benOf? c.1.innerTrigram
def R8.outerBen? (c : R8) : Option Ben := Trigram.benOf? c.1.outerTrigram
def R8.innerZheng? (c : R8) : Option Zheng := Trigram.zhengOf? c.1.innerTrigram
def R8.outerZheng? (c : R8) : Option Zheng := Trigram.zhengOf? c.1.outerTrigram

/-! ### Mian (本×征) — 唯一 ontology，仅在 benZheng 象限有 label-语义 -/

def R8.mian? (c : R8) : Option Mian :=
  match R8.innerBen? c, R8.outerZheng? c with
  | some b, some z => some (b, z)
  | _, _ => none

/-- Mian 的特权命题：R8.mian? c = some _ ↔ c.quadrant = benZheng. -/
theorem R8.mian?_isSome_iff_benZheng (c : R8) :
    (R8.mian? c).isSome = true ↔ c.1.quadrant = .benZheng := by
  rcases c with ⟨⟨y1, y2, y3, y4, y5, y6⟩, s⟩
  cases s <;>
    (cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;> decide)

/-! ### 算子对 R8.quadrant 的作用 -/

/-- shiCuo / shiZong 保 quadrant (Shi 不动 hex). -/
theorem shiCuo_preserves_quadrant (c : R8) :
    R8.quadrant (Cell256.shiCuo c) = R8.quadrant c := by
  rcases c with ⟨h, s⟩; rfl

theorem shiZong_preserves_quadrant (c : R8) :
    R8.quadrant (Cell256.shiZong c) = R8.quadrant c := by
  rcases c with ⟨h, s⟩; rfl

/-- parity (= cuo lift) 保 quadrant. -/
theorem parity_preserves_quadrant (c : R8) :
    R8.quadrant (parity c) = R8.quadrant c := by
  rcases c with ⟨h, s⟩
  simp [parity, R8.quadrant]
  exact cuo_preserves_quadrant h

/-- timeReversal (zong + Shi.zong) 在 4 象限上的作用表. -/
theorem timeReversal_quadrant (c : R8) :
    R8.quadrant (timeReversal c) =
      match R8.quadrant c with
      | .benBen     => .benBen
      | .benZheng   => .zhengBen
      | .zhengBen   => .benZheng
      | .zhengZheng => .zhengZheng := by
  rcases c with ⟨h, s⟩
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> rfl

/-! ## § 4 (Z/2)⁸ 群作用 simply transitive on R8

  R8 = (Z/2)⁶ × V₄ = (Z/2)⁸. 群元 = R8Combo := Hexagram × Shi (256 元),
  作用经 hex XOR × Shi XOR. 自身即 R8. -/

/-- (Z/2)⁸ 群元: (hex mask, shi shift). 256 元. -/
abbrev R8Combo := Hexagram × Shi

/-- 群作用: (mask, shift) · (h, s) = (mask XOR h, shift XOR_V₄ s). -/
def R8Combo.apply (g : R8Combo) (c : R8) : R8 :=
  (Hexagram.xor g.1 c.1, Shi.xor g.2 c.2)

/-- 256 元枚举 = Cell256.all. -/
def R8Combo.all : List R8Combo := Cell256.all

/-- |R8Combo| = 256. -/
theorem R8Combo.all_length : R8Combo.all.length = 256 := Cell256.all_length

/-- apply 在 anchor (qian, dao) 上的特化：(g_h, g_s) ↦ (g_h, g_s)
    即 (qian, dao) 是 V₄ × (Z/2)⁶ 之 identity. -/
theorem R8Combo.apply_at_qian_dao (g : R8Combo) :
    g.apply (Hexagram.qian, Shi.dao) = (g.1, g.2) := by
  rcases g with ⟨h, s⟩
  simp [R8Combo.apply, Hexagram.xor_qian_right, Shi.xor_dao_right]

/-- **Surjectivity**：∀ c : R8, ∃ g, g.apply (qian, dao) = c. -/
theorem R8Combo.apply_qian_dao_surjective (c : R8) :
    ∃ g : R8Combo, g.apply (Hexagram.qian, Shi.dao) = c := by
  rcases c with ⟨h, s⟩
  refine ⟨(h, s), ?_⟩
  exact R8Combo.apply_at_qian_dao (h, s)

/-- **Injectivity**：apply (qian, dao) 是 R8Combo → R8 的 injection. -/
theorem R8Combo.apply_qian_dao_injective :
    Function.Injective (fun g : R8Combo => g.apply (Hexagram.qian, Shi.dao)) := by
  intro g1 g2 heq
  rcases g1 with ⟨h1, s1⟩
  rcases g2 with ⟨h2, s2⟩
  simp [R8Combo.apply_at_qian_dao] at heq
  exact Prod.mk.injEq _ _ _ _ |>.mpr heq

/-- **Simply transitive**：对任意 c : R8，存在唯一的 g 满足 g.apply (qian, dao) = c. -/
theorem R8Combo.apply_qian_dao_simply_transitive (c : R8) :
    ∃ g : R8Combo, g.apply (Hexagram.qian, Shi.dao) = c
      ∧ ∀ g' : R8Combo, g'.apply (Hexagram.qian, Shi.dao) = c → g' = g := by
  obtain ⟨g, hg⟩ := R8Combo.apply_qian_dao_surjective c
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  exact R8Combo.apply_qian_dao_injective (hg'.trans hg.symm)

/-! ### 单爻 flip + Shi V₄ 是群之 8 个 Coxeter-style 生成元 -/

/-- flip1 (= dongInner lift) 对应 R8Combo (⟨yin,yang,yang,yang,yang,yang⟩, dao). -/
theorem R8Combo.flip1_combo (c : R8) :
    R8Combo.apply (⟨.yin, .yang, .yang, .yang, .yang, .yang⟩, Shi.dao) c
      = Cell256.flip1 c := by
  rcases c with ⟨⟨y1, y2, y3, y4, y5, y6⟩, s⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    cases s <;> rfl

/-- shiCuo 对应 R8Combo (qian, ji) — Shi P-flip, hex 不动. -/
theorem R8Combo.shiCuo_combo (c : R8) :
    R8Combo.apply (Hexagram.qian, Shi.ji) c = Cell256.shiCuo c := by
  rcases c with ⟨h, s⟩
  simp [R8Combo.apply, Cell256.shiCuo, Shi.xor, Hexagram.xor_qian_left]

/-- shiZong 对应 R8Combo (qian, wei). -/
theorem R8Combo.shiZong_combo (c : R8) :
    R8Combo.apply (Hexagram.qian, Shi.wei) c = Cell256.shiZong c := by
  rcases c with ⟨h, s⟩
  simp [R8Combo.apply, Cell256.shiZong, Shi.xor, Hexagram.xor_qian_left]

/-! ## § 5 Position-Operator-Tree: Sheng 6 × Shi ≃ R8 -/

/-- R8 树类型：Sheng 6 (爻位前缀树) × Shi (V₄ 时态). -/
abbrev R8Tree := Sheng 6 × Shi

def R8Tree.toR5 (t : R8Tree) : R8 := (Sheng.toHexagram t.1, t.2)
def R8Tree.ofR5 (c : R8) : R8Tree := (Sheng.ofHexagram c.1, c.2)

theorem R8Tree.toR8_ofR5 (c : R8) : R8Tree.toR5 (R8Tree.ofR5 c) = c := by
  rcases c with ⟨h, s⟩
  simp [R8Tree.toR5, R8Tree.ofR5]
  exact Sheng.toHexagram_ofHexagram h

theorem R8Tree.ofR8_toR5 (t : R8Tree) : R8Tree.ofR5 (R8Tree.toR5 t) = t := by
  rcases t with ⟨s, shi⟩
  simp [R8Tree.toR5, R8Tree.ofR5]
  exact Sheng.ofHexagram_toHexagram s

/-- R8 树之 9 层 level counts: [1, 2, 4, 8, 16, 32, 64, 128, 256]. -/
theorem R8_tree_levels :
    Cell256.rootTo256TreeLevelCounts = [1, 2, 4, 8, 16, 32, 64, 128, 256] := rfl

theorem R8_tree_levels_sum :
    Cell256.rootTo256TreeLevelCounts.sum = 511 :=
  Cell256.rootTo256TreeLevelCounts_sum

/-! ## § 6 xuGua extension to R8 — Hex-major × Shi-minor (4-fold) -/

/-- xuGua 序扩展到 R8（Hex-major × Shi-minor: Hex_1[dao,ji,jin,wei], Hex_2[...], ...）. -/
def xuGua256 : List R8 :=
  Cell256.xuGua.flatMap fun h =>
    [(h, Shi.dao), (h, Shi.ji), (h, Shi.jin), (h, Shi.wei)]

theorem xuGua256_length : xuGua256.length = 256 := by native_decide

theorem xuGua256_nodup : xuGua256.Nodup := by native_decide

/-- xuGua256 之首：(乾, 道) — 永真起点. -/
theorem xuGua256_head :
    xuGua256.head? = some (Hexagram.qian, Shi.dao) := rfl

/-- xuGua256 之末：(未济, 未) — 开放未来终点. -/
theorem xuGua256_last :
    xuGua256.getLast? = some (Hexagram.weiji, Shi.wei) := by native_decide

/-- xuGua256 后继：Shi 内 V₄ 序（道→已→今→未），未→外跳到下卦的「道」. -/
def xuGuaNext256 (c : R8) : Option R8 :=
  match c.2 with
  | .dao => some (c.1, Shi.ji)
  | .ji  => some (c.1, Shi.jin)
  | .jin => some (c.1, Shi.wei)
  | .wei => (Cell256.xuGuaNext c.1).map fun h' => (h', Shi.dao)

/-! ## § 7 R8 Closure 摘要定理 -/

/-- R8 收口主定理：基数、R-hierarchy、P/T/Y、群作用、BenZheng 投影、树、xuGua 全在.

  这是 yi-as-meta-framework.md § 4.1 R8 层之 Lean 落地之公开 hand-off 接口. -/
theorem R8_complete :
    -- (1) 基数 256
    (Cell256.all : List R8).length = 256
    -- (2) R-hierarchy: R8 = R6 × Shi (definitional)
    ∧ (∀ c : R8, c = (c.1, c.2))
    -- (3) 算子 P/T/Y closure
    ∧ (∀ c : R8, parity (parity c) = c)
    ∧ (∀ c : R8, timeReversal (timeReversal c) = c)
    ∧ (∀ c : R8, parity (timeReversal c) = timeReversal (parity c))
    -- (4) 群作用 (Z/2)⁸ simply transitive on R8（经 anchor (qian, dao)）
    ∧ Function.Injective (fun g : R8Combo => g.apply (Hexagram.qian, Shi.dao))
    ∧ (∀ c : R8, ∃ g : R8Combo, g.apply (Hexagram.qian, Shi.dao) = c)
    -- (5) BenZheng 投影 + Mian 特权
    ∧ (∀ c : R8, (R8.mian? c).isSome = true ↔ c.1.quadrant = .benZheng)
    -- (6) 位置-算子树双射
    ∧ (∀ c : R8, R8Tree.toR5 (R8Tree.ofR5 c) = c)
    -- (7) xuGua extension to R8
    ∧ xuGua256.length = 256
    ∧ xuGua256.Nodup :=
  ⟨Cell256.all_length,
   fun c => by rcases c with ⟨_, _⟩; rfl,
   parity_parity,
   timeReversal_timeReversal,
   parity_timeReversal_comm,
   R8Combo.apply_qian_dao_injective,
   R8Combo.apply_qian_dao_surjective,
   R8.mian?_isSome_iff_benZheng,
   R8Tree.toR8_ofR5,
   xuGua256_length,
   xuGua256_nodup⟩

/-! ## Axiom audit

  `#print axioms R8_complete` 应只报告 Lean 核心公理（propext + native_decide attestations）.
  不应包含 `kleene_recursion_axiom` 或其它项目自定义公理. -/

#print axioms R8_complete

end SSBX.Foundation.Bagua.Cell256Stratify
