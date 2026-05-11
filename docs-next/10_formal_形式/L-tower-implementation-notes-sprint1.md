# L-tower Sprint 1+2 Implementation Notes

> 状态：2026-05-11
> 范围：[L-tower-plan-v0.2.md](L-tower-plan-v0.2.md) Sprint 1 (M1–M3) + Sprint 2 (M4–M5) 之实施记录
> 结果：**0 axiom**, 1 documented `sorry` (`L1.octant_card` per v0.2 §7.2 fallback)
> 文件：5 个，位于 `formal/SSBX/Foundation/Squaring/`
> Build：`lake build SSBX.Foundation.Squaring.ProfiniteLimit` 成功，3317 jobs

---

## 1. 实施结果总览

| Milestone | 文件 | 估 LOC | 实 LOC | 比例 | 状态 |
|---|---|---|---|---|---|
| M1 V4Tensor | [V4Tensor.lean](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean) | 250 | 164 | 66% | ✅ 全证 |
| M2 L1 | [L1.lean](../../formal/SSBX/Foundation/Squaring/L1.lean) | 500 | 122 | 24% | ⚠️ `octant_card` sorry |
| M3 RetractTower | [RetractTower.lean](../../formal/SSBX/Foundation/Squaring/RetractTower.lean) | 400 | 120 | 30% | ✅ 全证 |
| M4 StreamCarrier | [StreamCarrier.lean](../../formal/SSBX/Foundation/Squaring/StreamCarrier.lean) | 200 | 74 | 37% | ✅ 全证 |
| M5.0 Coalgebra | (skipped) | 200 | 0 | 0% | ✅ 不必要（见 §2） |
| M5 ProfiniteLimit | [ProfiniteLimit.lean](../../formal/SSBX/Foundation/Squaring/ProfiniteLimit.lean) | 350 | 411 | 117% | ✅ 全证 |
| **合计** | | **1900** | **891** | **47%** | |

总 LOC 显著低于估计；主要原因见 §2。

---

## 2. 关键修正：M5.0 Coalgebra.lean 不需要

v0.2 §3.2「缺口清单」基于我（错误的）初步审计，列 `Endofunctor.Coalgebra` 为 Mathlib 缺失项，要求写 ~200 LOC 镜像。**这个判断是错的**。

实际：

```
$ grep -n "structure Coalgebra" \
    .lake/packages/mathlib/Mathlib/CategoryTheory/Endofunctor/Algebra.lean
227:structure Coalgebra (F : C ⥤ C) where
```

Mathlib 把 `Algebra` 和 `Coalgebra` **bundled 在同一文件 `Endofunctor/Algebra.lean`** 里（Coalgebra 从 line 227 起）。我之前 grep `Coalgebra*` 只找到 `Analysis/InnerProductSpace/Coalgebra.lean`（无关），漏掉了 Endofunctor 内的 Coalgebra。

**Agent 正确识别这点并跳过了 M5.0**。`ProfiniteLimit.lean` 直接用 `CategoryTheory.Endofunctor.Coalgebra` 现成 API。

### v0.2 plan 应更新

- §3.2 删 `Endofunctor.Coalgebra` 缺口项
- §4 删 M5.0 milestone
- §11 加 `Coalgebra` 到 Mathlib API cheatsheet
- 实际工作量 6 → 5 milestones

（本笔记仅记录修正，不直接改 v0.2 文档；后续如做 v0.3 应吸收。）

---

## 3. 已知 follow-up：L1.octant_card 之 sorry

`L1.lean` 含 `octantIndex`、`octant`、`octant_partition`，但 `octant_card`（每 octant 有 8192 元素）**留 documented `sorry`** 按 v0.2 §7.2 fallback。这是整个 Sprint 中**唯一**未证项。

### 证明 sketch

`octantIndex : L1 → Fin 8` 是两个 surjective additive group homomorphism 之复合：
1. `L₁ → Cell256`: `(a, b) ↦ a + b`（群同态，满射）
2. `Cell256 → (Z/2)³`: 投到前 3 个 hexagram bits（群同态，满射）

复合 `L₁ → (Z/2)³` 再 reindex 为 `Fin 8`，是 surjective group homomorphism。kernel 在 L₁ 内 index = 8，故每个 coset (= 每个 octant) 大小 `|L₁| / 8 = 65536 / 8 = 8192`（Lagrange）。

### 三条 closure path

| 路径 | 思路 | 估 LOC | 风险 |
|---|---|---|---|
| (a) 群论 via Lagrange | 形式化 composite 为 `AddMonoidHom`，应用 `Subgroup.card_eq_card_quotient_mul_card_subgroup` 类引理 | ~80 | 低；标准 Mathlib 用法 |
| (b) Cardinality 操作 | 双射 `octant i ≃ Cell256 × (32-element subset)`，分别 256 × 32 = 8192 | ~120 | 中；bijection 构造繁琐 |
| (c) `native_decide` | 直接对 65536 元 domain `by native_decide` | 1 | 高；性能未测，可能超时 |

**建议**：path (a) 是最 idiomatic、最易维护的。但**当前 sprint 不阻塞**——`octant_card` 是孤立定理，下游 (M3-M5) 不依赖它。可作为 followup task 独立完成。

### 已落地的 sorry stub

[L1.lean](../../formal/SSBX/Foundation/Squaring/L1.lean) 内 `octant_card` theorem 已显式声明：

```lean
/-- Each octant has size 8192 = |L₁|/8.
    [proof sketch + v0.2 §7.2 reference + this notes file link] -/
theorem octant_card (i : Fin 8) : (octant i).ncard = 8192 := by
  sorry
```

并已加入 `l1_summary` 汇总定理之合取列表，使其在 lake build 时可见 sorry warning（不会被 silent dropped）。

---

## 4. Sprint 边界注记

[Chip](#) 原本只 scope Sprint 1 (M1+M2+M3)；agent 直接做完 Sprint 2 (M4+M5) 一并交付。净效应：

- 节省 1 周 calendar
- 5 个文件单 pass 完成，无 Sprint 间 refactor
- 一致性：ProfiniteLimit 依赖 V4Tensor + StreamCarrier，一气呵成更自然

风险：Sprint 间 review checkpoint 被压缩到一次 —— 这份 notes 就是 retroactive review。

---

## 5. v0.2 §9 Decision log 之 agent 实际选择对照

| D# | v0.2 决策 | Agent 落地 | 一致？ |
|---|---|---|---|
| D1 | squaring projection π = Prod.fst | `def pi : L (n+1) → L n := Prod.fst` ([ProfiniteLimit.lean:52](../../formal/SSBX/Foundation/Squaring/ProfiniteLimit.lean:52)) | ✅ |
| D2 | 8-octant 沿 atomic flips | 实际用 `(a+b)` 之前 3 hex bits ≅ atomic flips 之 XOR-mask quotient | ⚠️ 语义等价；命名偏 abstract bit-projection |
| D3 | Coalgebra.lean 自给 200 LOC | 跳过（Mathlib 已有） | ❌ **正确偏离**——v0.2 错了 |
| D4 | 不引 Smyth–Plotkin | 全程无 SP；用 `IsTerminal` 直接表达 final coalgebra | ✅ |
| D5 | L₁ 子层用 `L1.subR8` 等 L-prefix | RetractTower 内 `projL1toR0..R7` + `liftR0..R7toL1`，命名风格符合 | ✅ |
| D6 | Profinite category 桥接 optional | 用 `CategoryTheory.Endofunctor.Coalgebra` 直接 instantiate；未走 `Profinite.asLimit` | ✅ Light-weight 路径 |

D3 是 v0.2 之 audit error；D2 是无害的命名偏差。其余完美对齐。

---

## 6. Build 验证

```
$ cd /Users/ren/repos/生生不息
$ lake build SSBX.Foundation.Squaring.ProfiniteLimit
⚠ [3317/3317] Built SSBX.Foundation.Squaring.L1 (9.2s)
warning: formal/SSBX/Foundation/Squaring/L1.lean:110:8: declaration uses `sorry`
Build completed successfully (3317 jobs).
```

唯一 warning 是 `L1.octant_card` 之 documented sorry —— 符合 v0.2 §8.1 验收"sorry ≤ 1（仅 §7 已识别且文档化的）"。

### Axiom 计数

```
$ grep -rn "axiom" formal/SSBX/Foundation/Squaring/
(no output)
```

**0 axiom 目标达成**。

---

## 7. 下一步 (v0.2 §10 future work)

完成本 Sprint 后，自然 followup（未排期）：

| Milestone | 内容 | 依赖 |
|---|---|---|
| **M2.5** `octant_card` 补全 | 实现上述三路径之一，消去唯一 sorry | 当前 L1 |
| **M7** Profinite topological group | Cantor 拓扑 + topological group instance | M5 + Mathlib `Profinite` |
| **M8** 2-adic interpretation | L_∞ ↔ F₂[[t]] formal power series | M5 + Mathlib `WittVector` |
| **M9** counted-loop ↔ coalgebra | MetaInterp Phase A 桥接 | M4 |
| **M10** DaoSource on TrajCell | 16-命 之 generative semantics demo | M4 |
| **M11** YiInstr ceiling formal | «生», «一» 不可达性 categorical 证 | M5 |
| **M12** PR Coalgebra 回 Mathlib | **N/A** —— Mathlib 已有 | — |

注意 M12 也可勾掉了。

---

## 8. 数字快照

| 维度 | v0.1 估 | v0.2 估 | 实际 |
|---|---|---|---|
| Axiom | 4 + 1 (CT) | 0 | 0 ✅ |
| Sorry | — | ≤ 1 documented | 1 ✅ |
| LOC | ~5000 | ~1700 | 891 |
| Calendar | 4–6 周 | ~2 周 | < 1 周（agent 一次性 deliver） |
| Files | 6 | 6 | 5（M5.0 跳） |
| Mathlib 重度依赖 | 否 | 是 | 是 ✅ |

最终交付 LOC 是 v0.2 估计的 52%、v0.1 估计的 17.8%。主因：(a) Mathlib `Coalgebra` 已存在省 200 LOC，(b) Stream'.IsBisimulation 直用省 ~150 LOC，(c) RetractTower 用 simp-chain 替代显式 case enumeration 省 ~280 LOC，(d) L1.octant_card 延迟省 ~100 LOC。

**核心命题（profinite limit ≅ Stream Cell256 + final coalgebra universal property）已 0-axiom 形式证完**——这是 v0.1 最初目标的完整达成。

---

*End of Sprint 1+2 implementation notes.*
