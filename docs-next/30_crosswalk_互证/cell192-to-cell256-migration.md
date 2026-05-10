> 状态：v3 (2026-05-11) — Cell192 → Cell256 迁移操作指引。本页是带代码 diff 之 porting guide：把 v2 期 Cell192 + Z/3 Shi 之代码 / 文档 / 笔记，机械地映射到 v3 之 Cell256 + V₄ Klein Shi + R₀..R₈ strict-uniform。配套 [`old-to-new.md`](old-to-new.md) 之术语表。

# Cell192 → Cell256 迁移操作指引

> 配套阅读：[`old-to-new.md`](old-to-new.md)（术语层迁移表，22 行），[`../40_reference_参考/glossary.md`](../40_reference_参考/glossary.md)（v3 术语短释），[`../10_formal_形式/yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md)（v3 doctrine 主干）。

本页是**操作层**手册：如果你手上的 Lean 代码、docs 笔记或脚本仍引用 v2 期之 Cell192、Z/3 Shi 或旧 R₁..R₆ chong-jump 编号，本页给一步步映射到 v3 之具体方案。结构层错误（v2 把 Shi 编为 Z/3 cyclic）已在 v3 修正为 V₄ Klein 群（详 [`cell256-grid.md`](../10_formal_形式/cell256-grid.md) sibling 文档），R-hierarchy 重号为 R₀..R₈ strict (Z/2)ⁿ uniform（详 [`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md)）。

> **Phase C addendum (commit 90c34f0, 2026-05-11)**：Shi 本身在 v3 内又做了一次精化 —— 从 `inductive Shi { dao, ji, jin, wei }` 改写为 **`abbrev Shi := YinBit × GuoBit`**（4 名字下放为 `@[match_pattern] def`s）。此变更在 v3 内部完成，**不影响下述 v2 → v3 迁移指引**：本页之 `inductive Shi : Type | dao | ji | jin | wei` 描述仍正确读为 v3 起点之 Shi 4-ctor 形态；Phase C 之后只是把这 4 个名字下放为 `Bool × Bool` 的 `@[match_pattern] def`，pattern 语法 `match s with | Shi.dao => ...` 与本页迁移指引中 Shi 用法 100% 兼容。详 [`../10_formal_形式/shi-v4.md`](../10_formal_形式/shi-v4.md) Phase C 注。

## 0. 迁移大要（一句话）

> v2 Cell192 = `Hexagram × ShiZ3`（64 × 3，Shi 是 Z/3 cyclic）→ v3 Cell256 = `Hexagram × Shi`（64 × 4，Shi 是 V₄ Klein 四群 `{道, 已, 今, 未}`）；R-hierarchy 旧编号 R₁..R₆（含 R₃→R₄ chong jump）→ 新编号 R₀..R₈ strict (Z/2)ⁿ uniform；印 / 投 由 Shi-only V₃ 内算子升为 Cell256 之 first-class XOR-mask atomic 算子；新增 first-class 道 = R₈ origin = V₄ identity = no-op = 永真 cell；旧 `R6_complete` 收口定理 → 新 `R8_complete` 收口定理（依赖只 propext + native_decide）。

## 1. Datatype 层迁移

### 1.1 Carrier 重定义

| v2（旧） | v3（新） | 备注 |
|---|---|---|
| `Cell192 := Hexagram × ShiZ3`（192 = 64 × 3） | `Cell256 := Hexagram × Shi`（256 = 64 × 4） | 总格数 192 → 256；增 1 个 Shi 元 |
| `inductive ShiZ3 : Type`<br/>` \| dao` (V₃ identity)<br/>` \| cur` (中态)<br/>` \| fin` (终态) | `inductive Shi : Type`<br/>` \| dao` (V₄ identity, 道)<br/>` \| ji` (P, 已)<br/>` \| jin` (PT, 今)<br/>` \| wei` (T, 未) | Z/3 cyclic → V₄ Klein；4 ctor；中点 `cur` 改为 V₄ central 元 `今` (= PT)；旧 `fin` 拆为独立 axis 之 `已` 与 `未` |
| `Cell128`（v2 中已存在但偶尔与 Cell192 混淆） | `Cell128 := Hexagram × YinBit`（128 = 64 × 2） | 中间层 R₇；`YinBit : Bool` |
| 无显式 R₀ | `R₀ := Unit`（太极） | 显式纳入 R-hierarchy |

代码迁移示例：

```diff
- abbrev Cell192 : Type := Hexagram × ShiZ3
+ abbrev Cell256 : Type := Hexagram × Shi
+ -- 中间层：Cell128 = Hexagram × YinBit (R₇)
+ abbrev Cell128 : Type := Hexagram × YinBit
```

### 1.2 Shi inductive 重写

```diff
- inductive ShiZ3 : Type
-   | dao    -- 道 (V₃ identity, 永真)
-   | cur    -- 中态
-   | fin    -- 终态
-   deriving Repr, DecidableEq, BEq

+ inductive Shi : Type
+   | dao   -- 道 (eternal / V₄ identity, 跨时空 anchor)
+   | ji    -- 已 (past, P-like): (因=1, 果=0)
+   | jin   -- 今 (present, PT, V₄ central): (因=1, 果=1)
+   | wei   -- 未 (future, T-like): (因=0, 果=1)
+   deriving Repr, DecidableEq, BEq
```

### 1.3 道之地位升级

```diff
-- v2: 道是 ShiZ3 之 ctor，但无形式 first-class 地位
-- v3: 道获得 5 重身份
+ /-- 道 cell at R₈ = (qian, dao) = (Z/2)⁸ identity = R₈ origin
+     = no-op operator = 永真 cell. -/
+ def origin : Cell256 := (Hexagram.qian, Shi.dao)
+ -- OXNotation: OX["oooooooo"] = (Hexagram.qian, Shi.dao) = origin
```

## 2. 算子层迁移

### 2.1 印 / 投 升 first-class XOR-mask 算子

v2 期之印 / 投 仅作 ShiZ3 上之 V₃ 算子（隐含「中态轮转」）。v3 把它们升为 **Cell256 之 first-class XOR-with-fixed-mask 算子**。

```diff
-- v2: 印 / 投 = ShiZ3 上之 V₃ generator
- def yin (s : ShiZ3) : ShiZ3 := match s with
-   | .dao => .cur | .cur => .fin | .fin => .dao
- def tou (s : ShiZ3) : ShiZ3 := ...

-- v3: 印 = XOR with yin_mask = (qian, ji)
+ def yin_mask : Cell256 := (Hexagram.qian, Shi.ji)   -- OX["ooooooxo"]
+ def tou_mask : Cell256 := (Hexagram.qian, Shi.wei)  -- OX["ooooooox"]
+ def yin (c : Cell256) : Cell256 := xor c yin_mask
+ def tou (c : Cell256) : Cell256 := xor c tou_mask

-- 新性质：
+ theorem yin_yin (c : Cell256) : yin (yin c) = c          -- involution
+ theorem tou_tou (c : Cell256) : tou (tou c) = c
+ theorem yin_tou_comm (c : Cell256) : yin (tou c) = tou (yin c)   -- commute
+ theorem yin_mask_xor_tou_mask : xor yin_mask tou_mask = (Hexagram.qian, Shi.jin)
+   -- 印 ⊘ 投 = V₄ central element (今)
```

### 2.2 cuo / zong / cuoZong on Shi（V₄ generators）

```diff
-- v2: 旧 ShiZ3 之 cuo / zong 是 Z/3 cyclic shift（结构错误）

-- v3: V₄ Klein 群 generators
+ namespace Shi
+ def cuo : Shi → Shi
+   | .dao => .ji  | .ji => .dao | .jin => .wei | .wei => .jin
+ def zong : Shi → Shi
+   | .dao => .wei | .ji => .jin | .jin => .ji  | .wei => .dao
+ def cuoZong : Shi → Shi    -- = cuo ∘ zong
+   | .dao => .jin | .ji => .wei | .jin => .dao | .wei => .ji
+ -- V₄ relations:
+ theorem cuo_cuo (s : Shi) : cuo (cuo s) = s        -- involution
+ theorem zong_zong (s : Shi) : zong (zong s) = s
+ theorem cuoZong_cuoZong (s : Shi) : cuoZong (cuoZong s) = s
+ theorem cuo_zong_comm (s : Shi) : cuo (zong s) = zong (cuo s)   -- abelian
+ theorem cuoZong_eq_compose (s : Shi) : cuoZong s = cuo (zong s)
+ end Shi
```

### 2.3 hexZong / hexHu lifted to Cell128 + Cell256

```diff
-- v2: 旧 Cell192 上之 hex 算子 lift
- def cell192_hexZong (c : Cell192) : Cell192 := (Hexagram.zong c.1, c.2)

-- v3: 同样语义，载体是 V₄-extended Cell256（保 Shi V₄ 部分）
+ namespace Cell256
+ def hexZong (c : Cell256) : Cell256 := (Hexagram.zong c.1, c.2)
+ def hexHu (c : Cell256) : Cell256 := (Hexagram.hu c.1, c.2)
+ -- 同样在 Cell128 上：
+ -- (hexZong c : Cell128) := (Hexagram.zong c.1, c.2)
+ end Cell256
```

## 3. API 层迁移（双射 / 结构）

### 3.1 Shi ↔ (YinBit × GuoBit) 双射

v3 之关键发现：Shi V₄ ≅ Bool²（按 (因, 果) 编码）。v2 期无此双射。

```lean
-- v3 新 API
def Shi.toYinGuo : Shi → YinBit × GuoBit
  | .dao => (false, false)
  | .ji  => (true,  false)
  | .wei => (false, true)
  | .jin => (true,  true)
def Shi.ofYinGuo : YinBit × GuoBit → Shi
  | (false, false) => .dao  | (true,  false) => .ji
  | (false, true)  => .wei  | (true,  true)  => .jin
theorem ofYinGuo_toYinGuo (s : Shi) : ofYinGuo (toYinGuo s) = s
theorem toYinGuo_ofYinGuo (yg : YinBit × GuoBit) : toYinGuo (ofYinGuo yg) = yg
```

任何 v2 中按 ShiZ3 三分支匹配的代码，v3 应改为按 V₄ 四分支匹配，或先用 `Shi.toYinGuo` 投 Bool² 再处理。

### 3.2 AddCommGroup Cell256 instance（Phase A 新加）

```diff
+ /-! v3 Phase A: Cell256 是 (Z/2)⁸ Abelian 群 -/
+ instance : Add Cell256 := ⟨Cell256.xor⟩
+ instance : Zero Cell256 := ⟨Cell256.origin⟩
+ instance : Neg Cell256 := ⟨id⟩          -- (Z/2)ⁿ 中 -c = c
+ instance : Sub Cell256 := ⟨Cell256.xor⟩
+ -- 同等 instance 在 Cell128 上
+ -- Cayley fusion:
+ instance : SMul Cell256 Cell256 := ⟨Cell256.xor⟩
+ def cayley (c : Cell256) : Cell256 → Cell256 := fun s => xor c s
+ def epsAtOrigin (f : Cell256 → Cell256) : Cell256 := f origin
+ theorem epsAtOrigin_cayley (c : Cell256) : epsAtOrigin (cayley c) = c
+ theorem cayley_inj : Function.Injective cayley
```

## 4. R-hierarchy 重号（v1 R₁..R₆ → v3 R₀..R₈）

| v1 名 | v3 名 | size | 类型 |
|---|---|---|---|
| (隐含) | **R₀** | 1 | `Unit` (太极) — 显式纳入 |
| R₁ | R₁ | 2 | `Yao` |
| R₂ | R₂ | 4 | `SiXiang` |
| R₃ | R₃ | 8 | `Trigram` |
| (跳过) | **R₄** | 16 | `Mian = Ben × Zheng`（显式补） |
| (跳过) | **R₅** | 32 | `Wuyao = Mian × Bool`（provisional 五爻） |
| R₄ | **R₆** | 64 | `Hexagram` (重号 +2) |
| R₅ | **R₇** | 128 | `Cell128 = Hexagram × YinBit` (重号 +2) |
| R₆ | **R₈** | 256 | `Cell256 = Hexagram × Shi` (重号 +2，且 192 → 256) |

任何引用 v1 R-index 之代码 / 文档须按上表 +2 重号（R₄→R₆，R₅→R₇，R₆→R₈），并显式接纳 R₀ / R₄ / R₅ 三件新层。

```diff
-- v1: 旧编号
- abbrev R6 := Cell192        -- 旧顶层
- theorem R6_complete : ...   -- 旧收口

-- v3: 新编号
+ abbrev R8 := Cell256         -- 新顶层
+ theorem R8_complete : ...    -- 新收口（增 P/T/Y closure + V₄ + xuGua256）
```

完整 v3 R-hierarchy 别名见 [`Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)（umbrella）+ 各 `R{n}_*.lean` shim。

## 5. Lift / Project 重新统一

v2 没有跨层 lift / project 之 uniform API。v3 给出 8 对统一 API + 8 件 retract 引理：

```lean
-- v3 新 API（in Foundation/Hierarchy/LiftProject.lean）
def liftR0toR1 (_ : R0) (y : Yao) : R1 := y
def projR1toR0 (_ : R1) : R0 := ()
theorem proj_lift_id_R0 (r0 : R0) (y : Yao) : projR1toR0 (liftR0toR1 r0 y) = r0
-- ... 同样 R1↔R2, R2↔R3, R3↔R4, R4↔R5, R5↔R6, R6↔R7, R7↔R8

theorem liftProject_summary :
    -- 8 件 proj_lift_id_R{n} 之合订
    ... := ⟨..., proj_lift_id_R7⟩
```

旧 chong（重）= `R₃ × R₃ → R₆` 在 v3 下被显式认知为 **3 步 +1 bit lift composite**：`R₃ → R₄ → R₅ → R₆`（见 `yi-RO-hierarchy.md § 3.9`）。

## 6. 文件路径变更

| v2 路径（已删 / 已迁） | v3 路径 |
|---|---|
| `formal/SSBX/Foundation/Bagua/Cell192.lean`（已删） | [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| `formal/SSBX/Foundation/Bagua/Cell192Stratify.lean`（已删） | [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) |
| (Cell128 旧零碎) | [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)（独立 R₇ 层） |
| (无 R-hierarchy umbrella) | [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) |
| (无 lift/project 模块) | [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) |
| (无 R-index 别名 shim) | `formal/SSBX/Foundation/Hierarchy/R{0..8}_*.lean` |
| (无 atomic / V4Outer 分类) | [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) + [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) |
| (无 OX literal) | [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) |

## 7. WenyanSelfInterp.lean: base-192 → base-256（部分 pending）

`Foundation/Wen/WenyanSelfInterp.lean` 是项目之 self-interpreter / quine 路线核心。v2 期使用 base-192 dispatch program。v3 之状态：

- **完成（commit `7de5064` Phase F.1）**：atomic encoding 已迁 `Cell256.Shi`（V₄ Klein 4-group），下游 encInstr / ProgEnc / StateEnc / metaStep 全在 Cell256 上操作。
- **完成**：`metaInterpStepPc_branchShiEq_notTaken_*` 之新 `Shi.dao` ctor "not-taken" 覆盖。
- **PENDING**：12-tag base-256 dispatch program 之完整 re-derivation（hex 0..2 × 4 shi states 之具体 routing 表）。详 `WenyanSelfInterp.lean` 头部 Phase F.1 注释。

任何接触 self-interp / dispatch / quine 之 v2 代码，应先确认是否在 Phase F.1 已完成之 atomic-encoding 范围内；超出范围（如 dispatch program 重导）属 pending 工作。

## 8. Tests / 收口定理重号

| v2 名 | v3 名 | 内容增量 |
|---|---|---|
| `cell192_summary` | `cell256_summary` (legacy) + `cell256_phaseA_summary` | + AddCommGroup laws + Cayley fusion + 印/投 mask involutivity |
| `cell192_complete` / `R6_complete` | `R8_complete` bundle | + V₄ outer + P/T/Y closure + 群作用 simply-transitive on (qian, dao) + BenZheng 投影 + 位置-算子树双射 + xuGua256 |
| (无) | `liftProject_summary` | 8 对 lift/project retract |
| (无) | `atomic_all_involutive` | 10 件 XOR atomic 算子 involutivity |
| (无) | `v4_outer_summary` | V₄ Klein 关系 + cell128/256 lift involutivity + hu 不动点 |
| (无) | `cell128_phaseA_summary` | Cell128 (Z/2)⁷ Abelian + Cayley + 印 mask form |

## 9. 文档迁移

| 类别 | 处理 |
|---|---|
| 已被 v3 严格取代之 docs-next / 义理 .md | 移入 [`史/`](../../史/README.md) 子目录；不再被 docs-next 索引 |
| 仍可援引之研究档案（v9–v14, daoli-v11/v12 等） | 留在 `史料/`，仍作研究指针 |
| docs-next / 义理 / 表六之 v3 改写 | 在新版规范文档中生效（见 sibling docs：[`cell256-grid.md`](../10_formal_形式/cell256-grid.md), [`v4-shi.md`](../10_formal_形式/v4-shi.md), [`cell256-algebra.md`](../10_formal_形式/cell256-algebra.md), [`yin-tou-operators.md`](../10_formal_形式/yin-tou-operators.md), [`ox-notation.md`](../10_formal_形式/ox-notation.md), [`operator-split.md`](../10_formal_形式/operator-split.md), [`lift-project.md`](../10_formal_形式/lift-project.md)） |
| 表六 192 → 256 | 旧 `表六_192格全表_旧Z3版.md` 在 `史/义理-pre-v3/`；新 `表六_256格全表.md` 由并行 agent 在 `六表_实虚史真/` 中产出 |

## 10. 已迁案例（可作样板）

| 文件 | 提交 | 性质 |
|---|---|---|
| [`formal/SSBX/Text/OperatorAnchors.lean`](../../formal/SSBX/Text/OperatorAnchors.lean) | `7de5064` (Phase A-F) | 文言算子到八卦系统的锚点 — 编码层不变；cell-anchor 重 map 到 256 网格 |
| [`formal/SSBX/Text/OperatorCellMap.lean`](../../formal/SSBX/Text/OperatorCellMap.lean) | `7de5064`, `0003224` | 单元映射 — V₄-extended |
| `Foundation/Bagua/BaguaTuring.lean` / `GodelLi.lean` | `7de5064`, `0003224` | 不完备路线 — 全迁 Cell256 |
| `Foundation/Modern/*` cascades | `0003224` (Phase F.x.5) | Modern 接口 — Cell192 → Cell256 完成 |
| YinBit dedup | `8e4406e` (Phase F.6) | 清理 + Phase G 文档同步 + B.1 |

参考这些 commit 之 diff 是最直观的迁移样板。

## 11. Sample diff snippet（前后对照）

### Lean 代码

```diff
- -- v2 期 (Cell192)
- import SSBX.Foundation.Bagua.Cell192
- open SSBX.Foundation.Bagua.Cell192
-
- def myOp (c : Cell192) : Cell192 :=
-   match c.2 with
-   | .dao => (Hexagram.zong c.1, .cur)
-   | .cur => (c.1, .fin)
-   | .fin => (Hexagram.hu c.1, .dao)

+ -- v3 (Cell256)
+ import SSBX.Foundation.Bagua.Cell256
+ open SSBX.Foundation.Bagua.Cell256
+
+ def myOp (c : Cell256) : Cell256 :=
+   match c.2 with
+   | .dao => (Hexagram.zong c.1, .ji)    -- 中态：v₃ cur → v₄ 已 / 今 / 未 之一
+   | .ji  => (c.1, .jin)
+   | .jin => (Hexagram.hu c.1, .wei)
+   | .wei => (c.1, .dao)                 -- 新增：v₄ 之第 4 态
```

### 文档表述

```diff
- v2 表述: 「Cell192 上之 印 / 投 算子是 ShiZ3 之 V₃ generator,
-   印 之复合 3 次回到 dao（cyclic）。」
+ v3 表述: 「Cell256 上之 印 / 投 算子是 V₄ Klein 群之 atomic
+   XOR-mask（at Cell256 by mask），二者皆 involution 且交换；
+   印 ⊘ 投 = V₄ 中心元 (qian, jin)。」
```

### Doctrine 表述

```diff
- v2 表述: 「R₆ 之 192 格全表是项目顶层 closure。」
+ v3 表述: 「R₈ 之 256 格全表（V₄ Shi）是 (Z/2)ⁿ self-describing 之
+   自然闭合（无第 9 个独立 binary axis）。256 = (Z/2)⁸ Abelian
+   Cayley 自作用 + V₄ 外对称 + 道作为 origin。」
```

## 12. Checklist（迁移完成判据）

- [ ] 所有 `Cell192` 引用改为 `Cell256` 或 `Cell128`（若是 R₇ 中间层）。
- [ ] 所有 `ShiZ3` / `ShiZ3.dao/cur/fin` 改为 `Shi` / `Shi.dao/ji/jin/wei`。
- [ ] 所有按 ShiZ3 三分支之 match 改为按 Shi 四分支，或先用 `Shi.toYinGuo` 投 Bool²。
- [ ] R-index 编号 +2（旧 R₁..R₆ → 新 R₃..R₈）；显式接纳 R₀ / R₄ / R₅。
- [ ] `R6_complete` 之引用改为 `R8_complete`。
- [ ] 文件路径 `formal/SSBX/Foundation/Bagua/Cell192*.lean` → `Cell256*.lean` / `Cell128.lean`。
- [ ] 文档表述「192 格」「Z/3 Shi」「Mian 是顶」「印/投 是 Shi 算子」全按 v3 重写。
- [ ] WenyanSelfInterp.lean 接触者：确认在 Phase F.1 已完成范围内，否则标 pending。
- [ ] 已被取代之 docs / 义理 .md 移入 `史/` 子目录。

## 13. 不变量（v2 → v3 仍成立）

下列属性 **v2 与 v3 都成立**（迁移时无须重证）：

- 64 卦本体（Hexagram = Yao⁶ = (Z/2)⁶）；64 个具名卦（乾、坤、屯、蒙、…）。
- BenZheng 之 4 本（物 / 动 / 间 / 事）+ 4 征（几 / 势 / 机 / 时）+ 16 命（Mian）+ 4 quadrant（本本 / 本征 / 征本 / 征征）。
- `dong` / `hua` / `bian`（R₃ atomic flips）+ `cuo` / `zong` / `hu`（R₃/R₆ outer）之结构性质。
- 序卦（King Wen order）之 64 卦序列。
- 「文道一也」「自释」「quine」之总目标（实现细节按 § 7 调整）。

## 形式锚

- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — Cell256 / Shi V₄ / 印 / 投 mask / Cayley
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — Cell128 (R₇ 中间层) / YinBit / 印 / flip1..flip6
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — `R8_complete` 收口；axiom audit 仅 propext + native_decide
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ umbrella
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — 8 对 lift/project + retract 引理
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — XOR atomic 算子分类
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — V₄ Klein outer permutation 算子分类
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["o/x×8"]` Cell256 字面量
- [`formal/SSBX/Foundation/Wen/WenyanSelfInterp.lean`](../../formal/SSBX/Foundation/Wen/WenyanSelfInterp.lean) — Phase F.1 atomic encoding 已迁；base-256 dispatch re-derivation pending
- [`formal/SSBX/Text/OperatorAnchors.lean`](../../formal/SSBX/Text/OperatorAnchors.lean) — 文言算子到八卦系统的锚点（已迁 Cell256，commit `7de5064`）
- [`formal/SSBX/Text/OperatorCellMap.lean`](../../formal/SSBX/Text/OperatorCellMap.lean) — 单元映射（已迁，commit `7de5064` / `0003224`）
- [`docs-next/30_crosswalk_互证/old-to-new.md`](old-to-new.md) — v2 → v3 术语迁移表
- [`docs-next/30_crosswalk_互证/claim-status.md`](claim-status.md) — v3 当前 live claim
- [`docs-next/40_reference_参考/glossary.md`](../40_reference_参考/glossary.md) — v3 术语短释
- [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) — v3 doctrine 主干
- [`史/README.md`](../../史/README.md) — v3 取代档总入口
