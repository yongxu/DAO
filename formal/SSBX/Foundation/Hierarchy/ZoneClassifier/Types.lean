/-
# Foundation.Hierarchy.ZoneClassifier.Types — 区域分类基础类型

## 设计

本文件**只声明枚举与记录**，不涉及任何外部 namespace 的 Prop。所有
"R_n 之外的真" 的引用（证据流）落在配套文件 `WallCitations.lean` 里，
那里每条引用是一行 `theorem cited_X := <existing theorem>` —— 单点失败即可
定位 stale citation，无需重写主类型层。

## 五区与十一墙

  * `Zone` (5)            — 道axiom / 道dynamic / 理 / 可理 / 墙
  * `WallTag` (11)        — 引用的不可能定理的标签
  * `RiceQuadrant` (4)    — Halts 四象（少阳/太阴/太阳/少阴）
  * `PendingInterfaceName` (6) — Pending 接口名
  * `OperatorTag` (10)    — 固定算子目录
  * `Classification`      — classify 返回的多轴 record

## 证据流原则 (Provenance Principle)

R_n 之外没有显式真。`WallTag` 是纯标签 enum；其证据来自 `WallCitations.lean`
里的引用定理——每个标签对应一条**既存定理**的一行包装。若某引用断裂，该单行
即编译失败，无需触动主类型层。
-/

import SSBX.Foundation.Wen.Layered.BitSpace
import SSBX.Foundation.Atlas.Yi.Shi

namespace SSBX.Foundation.Hierarchy.ZoneClassifier

open SSBX.Foundation.Wen.Layered

/-! ## § 1  Zone — 5 路分区 -/

inductive Zone
  | dao_axiom        -- 结构性道：V₄ identity / Cayley fixed point
  | dao_dynamic      -- 动力学道：op-轨道下可达 dao_axiom
  | li_conditional   -- 理：需前提才可定其轨道
  | ke_li            -- 可理：升档可决，本档不可决
  | wall             -- 墙：结构性不可达 / 不可判
  deriving DecidableEq, Repr, Inhabited

/-! ## § 2  RiceQuadrant — Halts 四象 -/

inductive RiceQuadrant
  | shao_yang  -- ∃ inp, Halts        (少阳)
  | tai_yin    -- ∀ inp, ¬ Halts      (太阴)
  | tai_yang   -- ∀ inp, Halts        (太阳)
  | shao_yin   -- ∃ inp, ¬ Halts      (少阴)
  deriving DecidableEq, Repr, Inhabited

/-! ## § 3  PendingInterfaceName — 6 经验接口 -/

inductive PendingInterfaceName
  | evilContinuation
  | openProjection
  | auditData
  | threshold
  | degreePeriod
  | calibration
  deriving DecidableEq, Repr, Inhabited

/-! ## § 4  OperatorTag — 固定算子目录

  具体 `apply` / `applicable` 在 `Operators.lean` 中。 -/

inductive OperatorTag
  | yiCore_step       -- «生生» on Hexagram (R₆ only)
  | v4_compose        -- V₄ XOR (任意偶 n)
  | cayley_mul        -- Cayley multiplication (R₈)
  | yin_mask          -- 印 mask (R₈)
  | tou_mask          -- 投 mask (R₈)
  | isa_12            -- 12-instr ISA (R₈)
  | hu_interlace      -- 互 (R₆)
  | zong_reverse      -- 综 (R₆)
  | cuo_complement    -- 错 (任意 n)
  | identity_op       -- 恒等 fallback
  deriving DecidableEq, Repr, Inhabited

/-! ## § 5  WallTag — 11 类墙的纯标签

  每条标签对应一条**既存定理**。证据见 `WallCitations.lean` 里逐条 wrap
  的 `cited_*` 定理。每条 docstring 记录了引用源以便审计。 -/

inductive WallTag
  /-- WenDefCompile.sheng_not_cuo_equivariant：«生» 不可由任何错-通约 ISA 程序计算 -/
  | sheng_not_compilable
  /-- CuoInvariance.unrestricted_kleene_inverter_inconsistent：无限制 Kleene 反演不一致 -/
  | kleene_inverter_dies
  /-- GodelLi.halts_undecidable_internally：判停不可内部决 -/
  | godel_halts_internal
  /-- GodelLi.halts_undecidable_under_kleene：判停在 Kleene 假设下不可决 -/
  | godel_halts_kleene
  /-- Diagonal.halts_on_{some,none,all,some_no}_undecidable_under_kleene：Rice 四象 -/
  | rice (q : RiceQuadrant)
  /-- Hexagram.hu_fixed_point：互的不动点仅有 qianqian、kunkun -/
  | hu_fixed_only_qianqian_kunkun
  /-- V4.cuo_not_truth_preserving：错不保真 -/
  | cuo_not_truth_preserving
  /-- V4.zong_not_truth_preserving：综不保真 -/
  | zong_not_truth_preserving
  /-- Modern.DaoLi.li_cannot_encode_dao：理不可编码道（ω-塔） -/
  | li_cannot_encode_dao
  /-- Core.Yuan.change_no_fixed_point：易无不动点 -/
  | change_no_fixed_point
  /-- 经验墙：6 个 Pending 接口等待校准 -/
  | pending (interface : PendingInterfaceName)
  deriving DecidableEq, Repr, Inhabited

/-! ## § 6  WallWitness — 墙见证

  当前版：仅持标签。证据流由 `WallCitations.lean` 中的 `cited_*` 定理
  集中提供（每条引用一条既存定理）。下游可通过 `WallWitness.tag` 索取
  对应的引用定理。 -/

structure WallWitness where
  tag : WallTag
  deriving DecidableEq, Repr, Inhabited

namespace WallWitness

@[inline] def sheng : WallWitness := ⟨.sheng_not_compilable⟩
@[inline] def kleene : WallWitness := ⟨.kleene_inverter_dies⟩
@[inline] def godelInternal : WallWitness := ⟨.godel_halts_internal⟩
@[inline] def godelKleene : WallWitness := ⟨.godel_halts_kleene⟩
@[inline] def rice (q : RiceQuadrant) : WallWitness := ⟨.rice q⟩
@[inline] def huFixed : WallWitness := ⟨.hu_fixed_only_qianqian_kunkun⟩
@[inline] def cuoFail : WallWitness := ⟨.cuo_not_truth_preserving⟩
@[inline] def zongFail : WallWitness := ⟨.zong_not_truth_preserving⟩
@[inline] def liNoDao : WallWitness := ⟨.li_cannot_encode_dao⟩
@[inline] def changeNoFixed : WallWitness := ⟨.change_no_fixed_point⟩
@[inline] def pending (i : PendingInterfaceName) : WallWitness := ⟨.pending i⟩

end WallWitness

/-! ## § 7  Classification — 收紧后的多轴 record (第二轮)

  仅保留**可诚实派生**的轴：
  - `zone` —— 由 classify 之有限计算给出（R_n 内禀）
  - `shi` —— `Option`，n=8 时由 `DaoSource.Shi.fromR8` 投影；其他 n 为 none（诚实的"无函数可调"）
  - `walls` —— 由 detectWalls (op, n) 派生，每条引用既证墙定理

  删除的字段（无诚实派生）：
  - `behavior` —— BehaviorClass 是 R-塔元层概念，BitSpace n 上无直接派生
  - `claim` —— ClaimKind 是 Truth ledger 之元数据，与 classify 无直接对应
  - `modality` —— Modality 由模态语境决定，与 zone 无结构对应 -/

structure Classification (n : Nat) where
  cell  : BitSpace n
  opTag : OperatorTag
  zone  : Zone
  shi   : Option SSBX.Foundation.Atlas.Yi.Shi
  walls : List WallWitness

end SSBX.Foundation.Hierarchy.ZoneClassifier
