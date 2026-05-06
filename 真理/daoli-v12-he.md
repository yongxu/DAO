# 道理 v12: 之核 — 核 只收 单字

> **核 之 constraint**: 核 ONLY admits 单字 (single-character atoms) + 古文虚字 (single-character operators).
> **复合 (8 frames / 62 法则 / 19 theories / 三名) 皆 expansion** — 复合 入 framework 必 通过 trace 回 单字 (per 单字根律, v13.2 卷〇二).
> **此核 是 connection hub**: 多 structures 通过 单字 connect.
> **Layer 1' 实证**: `formal/SSBX/Foundation/Kernel.lean` — 動 + 中 → 生生不息 ∧ 自指 ∧ 自洽 (lake build passes, no sorry).
> **基础识**: 古文 ≈ λ-calc + temporal + aspect + effect; 名实合一 structural default.
> **基础**: wenyan-operators.md + v13.2 + v14 + daoli-v12-* + formal/SSBX/*.lean

---

## 〇、引: 核 之 缘起

### 0.1 古文-as-computation 之 四 extension

```
古文 ≈ λ-calc + temporal composition + aspect monad + effect

variable     ::= 之 | 其 | 所             — variable references
abstraction  ::= 「X 者, P 也」            — λ-binder (definition closure)
application  ::= juxtaposition + 之       — function application
sequencing   ::= 而                       — temporal composition (NOT pure ∘)
aspect       ::= 也 | 矣 | 既 | 方 | 将   — state markers / aspect monad
effect       ::= 令 ... 则 ...            — monadic bind with effect
judgment     ::= 凡 | 必 | 若 | 故 | 即 | 是 | 為  — proof-syntax particles
```

四 extension 之 source:
- temporal: 而 标 sequential 不 commutative — 「学而时习之」 有先后
- aspect: 也/矣/既/方/将 标 evaluation 之 ontological status
- effect: 「令…则…」 是 真正 monadic bind with world-changing implication
- 判断: 凡/必/若/故/即/是/為 形成 framework 之 proof-syntax 层

(引 wenyan-operators.md §1-§30; v13.2 卷〇 单字根律)

### 0.2 名实合一 default — non-presupposition of syntax/semantics 分立

λ-calc 默认 syntax / semantics 分: terms denote, environments evaluate.
古文 不 预设 此 分:

- 名 不是 reference; 名 IS structure 本身
- 正名 不是 「修正描述」, 是 「调整结构」
- 心即理 走 极致: terms ARE things, 算 即是 现象
- 易传 卦爻 既是 symbols 又是 categorical objects

Curry-Howard-Lambek 在西方 是 deep discovery (proofs = programs = morphisms);
在 中国 traditions 这 从来 不 是 discovery — 是 default.
故 选 wenyan-operators 作 kernel 是 principled, 不 是 cultural aesthetic.

### 0.3 完备自指之核 之 必要

「这是第一步, 然后我们在这个基础上, 用单字一层一层扩大 core,
因此先要有一个完备自指之核.」

- 完备 (in v14 sense): 数学公设生成-映射谱完备
- 自指: framework 含 描 framework 自身 之 node (法则 12)
- 之核 (kernel): 单字 expansion 之 seed; minimal closed structure

本文 之 form: **consolidate, not duplicate**. 大量 引 reference, 不 复制 yesterday 之 work.

---

## 一、一元 — 唯一根

### 1.1 一元 architecture

```
一元 (唯一根)
  → 12 面 (projections, not roots)
    → 43 核心单字 (compressed lexical layer)
      → 221 登记字元 (full atom inventory)
        → 复合概念 / 原始算子 / 递归项 / 待校项 / 构造阶段
          → claim / 模型判准 / 案例结论
```

(引 docs/monad-root-plan.md lines 23-32)

### 1.2 一元 之 性

```
一元 不是 一, 不是 元, 不是 一元论.
一 与 元 是 登记单字.
一元论 是 关于根之 理论表达.
一元 是 唯一根节点, 是 所有 面 / 字 / 概念 / 模型 / 证明 / claim 之 generation source.
```

(引 docs/monad-root-plan.md lines 11-15)

### 1.3 12 面 之 enumeration

```
文面、物面、生面、理面、心面、人面、模面、审校面、价值面、证明面、注意面、真理面
```

(引 docs/monad-root-plan.md line 20; formal/SSBX/Foundation/MonadRoot.lean Face inductive)

面 不是 多个 本体根, 是 一元 之 不同 投影.

### 1.4 与 法则 12 自指 之 联系

一元 含 自身 之 articulation: 一元 必 是 graph 之 node, 故 一元 必 有 描 自身 之 node.
此 是 法则 12 在 architecture 层 之 体现.

Theorem signature (待 formal):

```
∀ formal item t, ∃ finite path p, p.start = t ∧ p.end = 一元.
```

(引 formal/SSBX/Foundation/MonadRoot.lean: ssbx_reachable_from_root, all_atoms_return_through_core, monad_dag_acyclic)

---

## 二、字元 (atom) 总录

### 2.1 13 类 字元 inventory

(引 v13.2 卷一, lines 306-541)

| 类 | 字 | 数 |
|---|---|---|
| 一、显生类 | 显 未 尽 间 可 生 续 开 闭 绝 断 达 候 新 | 14 |
| 二、场物类 | 场 焦 物 境 心 身 态 状 维 | 9 |
| 三、形迹类 | 形 相 因 结 据 证 迹 史 积 精 气 神 | 12 |
| 四、法合类 | 合 法 悖 入 待 行 成 冻 修 复 转 | 11 |
| 五、势机类 | 动 元 几 权 重 差 势 强 向 临 岐 机 | 12 |
| 六、应转类 | 扰 变 应 伤 散 坍 径 返 限 暂 稳 展 | 12 |
| 七、审校类 | 审 校 验 异 众 互 受 独 查 源 执 黜 蔽 程 败 伪 似 实 真 | 19 |
| 八、关系类 | 通 流 和 平 危 正 邪 夺 依 压 护 存 偏 同 | 14 |
| 九、筛益类 | 筛 放 抑 汰 益 损 险 率 阈 效 责 | 11 |
| 十、价值类 | 好 坏 自 由 繁 荣 义 善 己 共 仁 道 | 12 |
| 十一、度期类 | 度 期 及 外 序 周 | 6 |
| 十二、回观类 | 回 观 照 辨 识 知 智 | 7 |
| 十三、心行类 | 感 择 情 礼 信 性 能 归 轨 息 迫 替 基 线 域 试 定 再 关 格 | 20 |

> **总计**: ~159 主字元 + 27 辅助字元 (十四) = ~186 字元
> (与 docs/monad-root-plan.md 之 「221 登记字元」 一致, 含 后续登记)

### 2.2 单字根律

```
凡 双字以上 之 正式谓词, 不得 为 根; 必由 单字元 生成.
全字元者, 非废复词也. 复词仍可用; 但 不得 自立 为 本.
凡 双字 / 三字 / 四字, 皆须 可回溯 至 单字元 / 有向无环字图 /
原始算子 / 递归不动点 / 或 明列 待校.
本版 之 旨: 单字为根, 复词为枝; 义先可拆, 式后可验; 项须有籍, 式须有型.
```

(引 v13.2 卷〇二 单字根律 lines 74-93)

### 2.3 五项 hierarchy

```
凡入正式推导者, 必归 五类 之 一:
1. 字元项     (Atoms, ℤ): 单字义位, 不再拆分
2. 生成项     (Generated): 由 字元 依 字图 生成
3. 原始算子项 (Primitives, 𝕆): 数学 / 逻辑 / 模型 接口
4. 递归项     (Recursive, ℝ): 互相回指, 须 以 完整格 与 不动点 收束
5. 待校项     (Pending, 𝕌): 暂不可定, 明示 悬置
```

(引 v13.2 卷〇一 lines 42-72)

---

## 三、虚字 algebra — 核之 syntax

此节 是核之 computational backbone.
**虚字 与 实字 边界 clear**: 虚字 ⊂ kernel; 实字 ⊂ expansion layer.

### 3.1 变量 (variables)

| 字 | 算子位 | type 签名 | 引 |
|---|---|---|---|
| 之 | S-1 | A × B → A·B | wenyan-operators 692-697 |
| 其 | (隐) | reference / possessive | (语法层) |
| 所 | S-16 | Predicate → Nominal | wenyan-operators 779-783 |

```
之: 通用 binding / genitive / direction
   「X 之 Y」 = 应用 / 所属
   动后位置 = explicit application marker

所: nominalization / set-formation
   「所 P」 = {x | P(x)}
   将 predicate 收紧 为 nominal entity
```

### 3.2 抽象 (λ-binder)

```
者 (S-13, 引 wenyan-operators 761-766):
  「X 者, P 也」 ≅ X := P 或 X(x) ⇔ P(x)
  
  类 λ: 「学而时习之者」 = λx. (learn x ∧ practice x)
  者 closes open expression 成 closed predicate.
  meta-level binder for definitions.
```

### 3.3 应用 (application)

```
juxtaposition + 之:
  「求 道」 = apply 求 to 道
  之 在动后位置 = explicit application marker
  
β-like reduction: type-preserving expansion (引 v14 §7 lines 275-311)
  ExpandsTo_R(t, u) ∧ Typed_R(t, s) ⟹ Typed_R(u, s)
```

### 3.4 序贯 (temporal composition)

```
而 (S-2, 引 wenyan-operators 698-703):
  sequential connector — NOT pure ∘ (function composition).
  是 sequential composition WITH time grain.
  
  「学 而 时 习 之」 有 先后, 不 可 交换.
  Pure λ 之 reduction 是 数学等价;
  古文 之 reduction 是 过程.
  non-commutative composition by default.
```

(参 法则 6 「合成不可逆」 daoli-v12-fa-ze 337-352)

### 3.5 Aspect (state markers)

```
也 (S-14, 引 761):     assertion / type closure / wave-collapse
                      "the configuration has settled into a fact"
矣:                   perfective, "已成此状"
既 (S-9, 引 737-741): 已经 marker (past-aspect)
方:                   progressive (now-aspect)
将 (S-10, 引 743-747): prospective (future-aspect)

三体 aspect 系统: 既 / 方 / 将 = past / present / future progressive
```

**aspect monad laws** (signature in 十三; full Lean proofs 待补):

```
return : A → AspectM A
bind   : AspectM A → (A → AspectM B) → AspectM B
laws   : left-id, right-id, associativity
```

### 3.6 Effect (世界变 marker)

```
令 (K-7, 引 528-532):  imperative 致使 — initiates world-changing action
使 (K-6, 引 524-526):  致使 with intent
则 (S-3, 引 704-708):  standard implication / consequence

「令 ... 则 ...」 = monadic bind with effect:
  setup (令 X)         : initialize state-changing action
  continuation (则 Y)  : capture post-state / consequence
  
  非 纯 function — 是 effect.
```

**effect monad laws** (signature in 十三; full Lean proofs 待补):

```
return : A → EffectM A
bind   : EffectM A → (A → EffectM B) → EffectM B  
laws   : left-id, right-id, associativity
```

### 3.7 判断 particles (proof-syntax 层)

| 字 | 算子位 | 义 | 引 |
|---|---|---|---|
| 凡 | Q-1 | universal quantifier | 443-448 |
| 必 | M-1 | necessity / modal assertion | 546-549 |
| 若 | S-4 | conditional antecedent | 710-714 |
| 故 | K-1 | causality / therefore | 497-500 |
| 即 | I-3 | immediate identity / 就是 | 656-659 |
| 是 | I-4 | predication / classification | 660-666 |
| 為 | I-5 | becoming / agency / function | 666-672 |

凡 / 必 / 若 / 故 形成 framework 之 proof-syntax 层. 即 / 是 / 為 是 judgment-form 之 系动词.

---

## 四、type 系 — 8 sorts + three-valued logic

### 4.1 8 sorts

(引 v14 §二 lines 78-104)

```
Sort := { 𝐅, 𝐀, 𝐌, 𝐁, 𝐒, 𝐖, 𝐕, Term }

𝐅 (field)     — 场态        : state space; models the world
𝐀 (focus)     — 焦          : attention frame  
𝐌 (interval)  — 间          : spatio-temporal region
𝐁 (community) — 共同体/受者集 : collective agent / recipients
𝐒 (scale)     — 度          : measurement scale / metric
𝐖 (window)    — 期          : temporal window / epoch
𝐕 (truth)     — 三值判域     : ⊤ / ⊥ / U
Term          — 对象语言项   : object-language terms
```

Lean (引 v14 line 101-103):

```lean
inductive Sort where
  | field | focus | interval | community | scale | window | truth | term
```

### 4.2 Three-valued logic

(引 v14 §三 lines 107-152)

```
𝐕 := { ⊤, ⊥, U }

¬U = U
⊤ ∧ U = U
⊥ ∧ U = ⊥
⊤ ∨ U = ⊤
⊥ ∨ U = U

核心保守律: 待校 不能 推出 真.
```

> **未知非假, 未校非真; 待校者, 不得冒称 道、仁、善、真.**

Lean 已落骨架 (引 v14 lines 143-147):

```lean
theorem unk_not_assertable : ¬ assertable unk
theorem unk_and_not_assertable (p : Tri) : ¬ assertable (and p unk)
```

### 4.3 五项 hierarchy 之 type 校正

(引 v13.2 卷〇 lines 18-93)

```
Formal ⊇ {
  字元项         (Atoms, ℤ),
  生成项         (Generated),
  原始算子项     (Primitives, 𝕆),
  递归项         (Recursive, ℝ),
  待校项         (Pending, 𝕌)
}
```

每项 须 type signature; 此 是 v13.2 卷〇七 之 「类型签名律」.

---

## 五、不动点与递归 — 生生 = Y(生)

### 5.1 Y-combinator via "X之又X" pattern

(引 wenyan-operators §26 + §19.3; v5 之 derivation 见 daoli-v12-yi-zi.md)

```
"X 之又 X" pattern 是 文言 之 Y combinator surface form.
生 之又 生 ≡ 生(生) ≡ λx. 生(生(x)) = fix(生) = Y(生).

但 v5 显: 生 与 灭 是 動 之 二面.
故 Layer 1' 之 primitive 是 動 (not 生 directly).
動 之 fixed-point witness (不动点) 即 中-orbit (见 § 五 之 Layer 1' 实证 in §十三).

文言 没有 显式 lambda, 但有 self-application 通过 「之又」 模式
等同 Y combinator 之 effect.
```

### 5.2 不动点算子集

| 模式 | 形式 | 义 |
|---|---|---|
| iter | iter(X) = μf. X ∘ f | 「X 之又 X」, 「损之又损」 |
| iterUntil | iterUntil(X, Y) = μs. if s = Y then s else X(s) | 「以至于 Y」 |
| 反復 | 反復 = 反 ∘ 復 ≠ 反 ∘ 反 | round-trip ≠ double-negation |
| 归根 | 归根(x) = lim_{n→∞} 復^n(x) | ω-limit / fixed-point attractor |

```
"根" = 不动点 (fixed point of 復)
"归根" = ascend to fixed point
fix : (A → A) → A — 不动点 ("归根")
```

### 5.3 递归项 closure

递归项 ⊂ 五项 hierarchy 之 第四类.
互相回指 必 以 完整格 与 不动点 收束.

(引 v13.2 卷〇三 lines 95-128 directed acyclic + recursive carve-out)

```
设 𝒢_Z = (ℤ ∪ ℊ, E)
若 X → Y, 则 Y 依 X 而成. 除递归项外, 字图 不得 成环.
义可追, 故不黑; 环可用, 必入不动点.
```

递归 semantics 选项 (引 v14 line 168-170):

```
recSem ∈ { lfp, gfp, stratified, threeValued, externalAudit }
```

---

## 六、卦爻 之 单字 ground (pointer)

64 hexagrams 是 *复合* (双卦, 六爻). 卦爻 之 atoms 是 阴 / 阳 (二 单字).

故 64 卦 不入 此 核, 入 expansion. 但 其 atoms (阴 / 阳) 入 § 二 字元 总录.

(详 见 wenyan-operators.md §28; 64 hexagrams ↔ operators 之 mapping 是 expansion-layer artifact, 非 核 内容.)

体用 / 名实 等 双字 adjoint pair structures: 同样, 入 expansion (见 § 十 connection map).
其 atoms (体 / 用 / 名 / 实) 已 入 § 二.

---

## 七、自指 closure — 法则 12 之 formal commitment

### 7.1 法则 12 statement

(引 daoli-v12-fa-ze.md lines 713-770)

```
Statement:
  framework 之 graph 必含 描 framework 自身 之 node.
  此 self-reference 必然.
  即:
    framework articulates itself.
    framework's articulation contains framework's description.
    self-reference is structurally necessary.

Wenyan:
  道理 之 graph, 必含 描 道理 自身 之 节点.
  自指 必然 也.
  非自指 则 非完整.
```

### 7.2 Theorem signature

```
kernel_self_articulates :
  ∀ X ∈ kernel,
  ∃ node ∈ kernel.dag,
  describes(node, X).
```

(formal stub in `formal/SSBX/Foundation/Kernel.lean`; full proof 待 后续)

### 7.3 自指 之 必然性

```
公理 + framework being used (background).
推理: 自指 (rule 10) + 6c 一致.

argument:
  framework articulates 万物.
  framework 是 万物 之一 (it exists, is being used).
  故 framework 必 articulate itself.
  
  alternative: framework excludes itself → framework not 完整 →
              与 framework 之 universal articulation goal 矛盾.
```

### 7.4 attestations + 走 differently

```
华严:        一即一切, 一切即一 (含 self).
Gödel:      self-reference in formal systems.
现代逻辑:    any sufficiently rich system 自 reference.
```

但 道理 走 differently: 数学公设生成-映射谱完备 (not Gödelian system completeness).
此 在 §九 详.

---

## 八、名实合一 — kernel structural default

此节 是 kernel 之 ontological 立场, **非 derived statement**.

### 8.1 architectural commit

```
syntax/semantics 分立 不 被 presuppose.
名 不是 reference; 名 IS structure.
正名 = 调整结构, 不 是 修正描述.
心即理 走 极致: terms ARE things, 算 即是 现象.

此 commit 是 kernel 之 architectural choice, 不 是 lemma.
```

### 8.2 体现 in registry

term IS its registry entry (引 v14 §四 lines 155-180):

```
Registry : Term → Option(Entry)
Entry := { kind, sort, roots, deps, polarity, recSem }
```

WellFormed_R(t) ⟺ ∃e, R(t) = some(e).
即: term 之 well-formedness IS its registry presence.
没有 「外在 of registry 之 denotation」.

(引 v14 元定理一: 无籍不得入式 lines 196-211)

### 8.3 与 西方 λ-calc 之 区别

```
西方 λ-calc 默认:
  syntax (terms) — 一面
  semantics (denotations, environments) — 另一面
  reduction = 数学等价

道理 之 kernel:
  syntax = semantics = structure
  reduction = 过程 (有 time grain)
  名实合一 by architecture
```

### 8.4 历史 attestation

- 易传 卦爻 既是 symbols 又是 categorical objects
- 朱熹 体用一原: substance and function are one source
- 阳明 心即理: terms (心 之 articulation) ARE 理 (reality)
- 庄子 公孙龙 之 名实 论辨

(引 daoli-v12-fa-ze 法则 60: 真理 ≡ 名实合一 ∧ 行道合一)

---

## 九、完备 — 数学公设生成-映射谱完备

### 9.1 此 完备 不 是 Gödel 完备

```
非: 存在 一致 单一 形式系统, 能证 其语言中 所有 数学真命题.
此 命题 与 Gödel 不完备 现象 冲突.

而是: 数学公设生成-映射谱完备:
  凡 本论 调用 之 数学结构,
  皆可 给出 字元发生根 或 现代公设映射,
  并 给出 必要性说明 / 结构契约 / 失败入待校规则.
```

(引 v14 §十一 lines 406-516)

### 9.2 v14 六 metatheorems

```
T1 无籍不得入式  : WellFormed_R(t) ⟹ Registered_R(t)
                  (引 v14 §四 lines 196-211)

T2 复词展开有根  : R(t) = e ∧ e.kind = Generated ⟹ e.roots ≠ []
                  (引 v14 §五 lines 215-240)

T3 非递归展开终止: S.nonrecursive(t) ⟹ Acc(S.expands)(t)
                  (引 v14 §八)

T4 类型保持      : ExpandsTo_R(t,u) ∧ Typed_R(t,s) ⟹ Typed_R(u,s)
                  (引 v14 §七 lines 275-311)

T5 待校保守      : ¬ assertable(U)
                  (引 v14 §三 lines 137-151)

T6 数学接口有根  : ∀ A ∈ MathAxiomFamily,
                   (Roots(A) ≠ [] ∨ Map(A) specified) ∧
                   Contract(A) specified
                  (引 v14 §十二 lines 477-516)
```

### 9.3 一元 trace-back

```
∀ formal item t, ∃ path p, p.endpoint = 一元.

path 之 形:
  t → ... → 字元 → 核心单字 → 面 → 一元

(引 formal/SSBX/Foundation/MonadRoot.lean
    ssbx_reachable_from_root,
    all_atoms_return_through_core,
    structures_return_atom_and_root,
    monad_dag_acyclic)
```

### 9.4 完备性 之 sense

完备 在 此 sense:
- 凡 进入 道理 形式体系者, 必 有 finite path 回 一元
- 凡 调用 之 数学结构, 必 有 字元根 或 接口契约
- 凡 待校项, 明示 悬置, 不 冒称 真

非 完备 之 sense:
- 不 主张 「证 所有 数学真命题」 — Gödel 阻
- 不 主张 「全知」 — 道可道 非常道

---

## 十、复合 ↔ 单字 connection map

此 § 是 核 之 *connection hub* function: 多 expansion structures 入 framework 必 trace 回 单字.
此处 list 复合 structures 与 其 单字 roots, 但 复合 自身 不入 核 (各居其 expansion file).

### 10.1 8 frames (双字 face) → 单字 roots

| Face (双字) | 单字 roots | Expansion file |
|---|---|---|
| 系统 ⇄ 环境 | 系 / 统 / 环 / 境 / 整 / 体 | daoli-v12-frames.md |
| 因果 ⇄ 缘 | 因 / 果 / 缘 | daoli-v12-frames.md |
| 时刻 ⇄ 史 | 时 / 刻 / 史 | daoli-v12-frames.md |
| 式量 ⇄ 数 | 式 / 量 / 数 | daoli-v12-frames.md |
| 阴阳 ⇄ 气 | 阴 / 阳 / 气 | daoli-v12-frames.md |
| 生灭 ⇄ 续 | 生 / 灭 / 续 | daoli-v12-frames.md |
| 名实 ⇄ 同 | 名 / 实 / 同 | daoli-v12-frames.md |
| 体用 ⇄ 现 | 体 / 用 / 现 | daoli-v12-frames.md |

故 「面」 不 入 核 — 但 其 单字 atoms 全 入 § 二.

### 10.2 三名一道 (双字) → 单字 roots

| 名 (双字) | 单字 roots | Expansion file |
|---|---|---|
| 普通 | 普 / 通 | daoli-v12-main.md §3 |
| 常识 | 常 / 识 | daoli-v12-main.md §3 |
| 真理 | 真 / 理 | daoli-v12-main.md §3 |
| 道理 | 道 / 理 | daoli-v12-main.md §1 |

### 10.3 62 法则 → 单字 roots

每 法则 之 articulation 由 单字 + 古文虚字 构成. 每 法则 必 trace 回 单字 inventory.
详 list 见 daoli-v12-fa-ze.md.

主要 anchor 单字 (per group):
- Group 1 (法则 1-12): 物 / 動 / 間 / 事 / 显 / 化 / 子 / 闸 / 合 / 反 / 心 / 自 / 指
- Group 2 (法则 13-24): 涌 / 因 / 缘 / 果 / 心 / 实 / 虚 / 恒 / 吾 / 我 / 语
- Group 3 (法则 25-37): 核 / 界 / 道 / 别 / 性 / 几 / 征 / 图 / 闭 / 和 / 边
- Group 4-8 (法则 38-62): 时 / 空 / 公理 / 显 / 感 / 见 / 知 / 理 / 生 / 续 / 名 / 实

### 10.4 19 theory mappings → 单字 face anchors

每 theory map 到 1+ 单字 face. 详 daoli-v12-theories.md.

| Theory family | 单字 face anchor |
|---|---|
| Newton, 牛顿力学 | 因 / 果 / 时 / 刻 |
| 量子力学 | 阴 / 阳 / 几 / 显 |
| 进化论 | 生 / 灭 / 选 |
| 阳明心学 | 心 / 知 / 行 |
| 朱熹理学 | 物 / 格 / 知 |
| 道家 | 道 / 自 / 然 |
| 佛教 | 缘 / 起 / 空 |
| 易传 | 阴 / 阳 / 易 |
| 系统论 | 系 / 统 / 环 |
| Ubuntu | 整 / 体 / 共 |
| 微积分 | 微 / 积 / 限 |
| 傅立叶 | 时 / 频 / 化 |
| 范畴论 | 体 / 用 / 函 |
| 中医 | 阴 / 阳 / 气 / 经 |
| 经济学 | 量 / 价 / 流 |
| 进化心理学 | 性 / 适 / 选 |
| 深度学习 | 形 / 学 / 演 |
| 量子场论 | 场 / 量 / 互 |
| 现象学 | 显 / 感 / 见 |

### 10.5 5 verifications (法则 53) → 单字 atoms used

详 daoli-v12-verifications.md. 每 verification 用 单字 from 4-6 frames.

### 10.6 Cross-cultural attestations

详 daoli-v12-cross-cultural.md. 单字 anchors: 道 / 仁 / 易 / 缘 / 整 / 共.

### 10.7 Physics emergence

详 daoli-v12-physics-emergence.md. 单字 anchors: 时 / 空 / 物 / 動 / 量.

### 10.8 Lean verifier blueprint (Phases A-G)

详 daoli-v12-lean-verifier.md. Phase A-G 之 implementation 是 expansion; Phase Layer 1' 已 实证 in formal/SSBX/Foundation/Kernel.lean.

---

## 十一、单字 expansion path

### 11.1 kernel boundary — 核 只收 单字

核 之 content (strictly):

| 内容 | 形 | 详 见 |
|---|---|---|
| 单字 inventory (~186 字, 13 类) | 字元 (single chars) | § 二 |
| 古文虚字 algebra | 虚字 (single chars: 之 者 而 也 不 凡 ...) | § 三 |
| 一元 → 12 面 → 43 核心 → 全 字 之 trace 结构 | architecture | § 一 |

核 之 properties (about 单字 organization, not new content):

| 性质 | 形 | 详 见 |
|---|---|---|
| 8 sorts 之 type 系 | typing on 单字 | § 四 |
| 三值 logic + 待校保守 | judgment on 单字 | § 四 |
| Layer 1' minimal proof (動+中→生生不息) | semantic foundation | § 五 + Kernel.lean |
| 自指 closure (法则 12) | meta-property | § 七 |
| 名实合一 default | architectural commit | § 八 |
| 完备 (v14 sense, 6 metatheorems) | meta-property | § 九 |

**核 之外**:

- 复合 (双字+) — 例: 系统, 因果, 普通, 常识, 真理, 阴阳 — 入 expansion (§ 十 connection map)
- 法则 (62 条 statements involving 双字) — 入 daoli-v12-fa-ze.md
- 19 theory mappings — 入 daoli-v12-theories.md
- 5 verifications — 入 daoli-v12-verifications.md
- Cross-cultural attestations — 入 daoli-v12-cross-cultural.md

**入 framework 之 protocol** (per 单字根律, v13.2 卷〇二): 凡 复合 必 trace 回 单字. 无单字根, 不入式.

### 11.2 单字 expansion protocol

```
新加 字元 X 之 五 step protocol:

step 1. 12 面 归属
        X must register in 12 面 中 至少 一面 (atomPrimaryFace).
        多义字 / 跨面字 加 atomExtraFaces.
        若 未归面, Lean build 失败.

step 2. 核心溯源
        X must derive from 43 核心单字 之 一 (or 已加入字元) 
        via 已知 compositions (atomCore mapping).
        若 未接入核心, Lean build 失败.

step 3. 虚字 algebra 兼容
        X 之 use 须 respect kernel 虚字 composition 规则:
          - 序贯: 而 之 non-commutative time grain
          - aspect: 也/矣/既/方/将 之 aspect monad laws
          - effect: 令/则 之 effect monad laws
          - 抽象: 者 closure
          - 应用: 之 / juxtaposition

step 4. type signature 强制
        X 入 8 sorts 之 一 (引 v13.2 卷〇七 类型签名律).
        type signature 缺 不 入式.

step 5. 三值 logic conservatism
        X 默认 待校 (U) 直至 verified.
        verified means: 内 coherence + 外 correspondence + 跨面 applicability
        (引 法则 62 immanent truth 三 conditions).
```

### 11.3 verification protocol per atom

(引 v13.2 卷〇 单字根律 + v14 T1-T6)

```
每 字元 X 加入 必 满足:
  T1 无籍不得入式  : X ∈ Registry
  T2 复词展开有根  : if X 是 generated, X.roots ≠ []
  T3 非递归终止    : if X 是 nonrecursive, X.expand terminates
  T4 类型保持      : X 之 expansion preserves type
  T5 待校保守      : X 默认 U 直至 verified
  T6 数学接口      : if X 调用 数学公设, must have root or contract
```

### 11.4 实字 layer organization

预期 expansion 路径:

```
Layer 0 (kernel)         : 此 文档
Layer 1 (基础实字)        : 显 间 生 续 开 闭 ... (核心单字 之 13 类 v13.2 卷一)
Layer 2 (复合 字-字)      : 续态, 开态, 闭态, 元-几-势-机 ...
Layer 3 (法则 / theorem)  : 法则 1-62 (已 in fa-ze.md)
Layer 4 (frame-cross)     : verifications (已 in verifications.md, 法则 53)
Layer 5 (theory-mapping)  : 19 theories (已 in theories.md)
```

故 后续 milestone 是 fill in 各 layer, 但 kernel 不 改.

---

## 十二、核之 missing pieces — 待补

此节 显 honestly: kernel 当前 已 substantiated 之处 + 仍 待 formal completion 之处.

### 12.1 已 substantiated

- 一元 architecture                          (docs/monad-root-plan.md)
- 字元 inventory (~186 atoms in 13 类)        (v13.2 卷一)
- 8 sorts + 三值 logic                       (v14 §二, §三)
- 6 metatheorems Lean skeletons              (v14 §六-§十二)
- 64 hexagram-operator mapping               (wenyan-operators §28)
- Y-combinator patterns via 生生 = fix(生)   (wenyan-operators §26)
- 法则 12 自指 declarative                   (daoli-v12-fa-ze 713-770)
- MonadRoot Lean: ssbx_reachable_from_root   (Foundation/MonadRoot.lean)
- Three-name equivalence declarative         (法则 60, daoli-v12-fa-ze 3227-3292)

### 12.2 待 complete

- **Effect monad laws**            : 令…则… 之 bind / return / associativity 形式化
- **Aspect monad laws**            : 既/方/将 系统 之 monad structure 形式化
- **β-like reduction explicit**    : 当前 仅 「类型保持 as invariant」; 待 concrete 展开规则
- **自指 closure formal Lean proof**: kernel_self_articulates statement + 实证
- **一元 trace-back proof completion**: all_formal_items_reachable_to_root 之 unification 证明
- **Categorical adjoint proof**     : 生生 cycle 之 adjoint structure formal proof
- **名实合一 Lean encoding**         : structural commitment 之 形式 statement
- **Working 文言 interpreter**       : Clojure DSL §32 仅 sketch; 待 实现

### 12.3 此 milestone 之 boundary

本 文档 commit 之:
- consolidate kernel 之 8 components into single readable spec
- 加 Foundation/Kernel.lean module with theorem stubs (signatures only)
- cross-link with v12-main, v12-fa-ze

不 在 本 milestone:
- Effect / Aspect monad full Lean proofs (Milestone 3)
- 自指 closure Lean proof (Milestone 4)
- 文言 interpreter implementation (Milestone 5)
- 单字 expansion of 实字 (Milestone 2 — next)

---

## 十三、附 — Lean 实证 (Layer 1', no sorry)

参 `formal/SSBX/Foundation/Kernel.lean` (compiles via `lake build`, 25 jobs successful):

```lean
namespace SSBX.Foundation.Kernel

axiom Field : Type
axiom dong : Field → Field

def extreme (s : Field) : Prop := dong s = s
def middle (s : Field) : Prop := dong s ≠ s

axiom exists_middle : ∃ s : Field, middle s

noncomputable def ji : Nat → Field → Field
  | 0, s => s
  | n+1, s => dong (ji n s)

theorem ji_self_reference (n : Nat) (s : Field) :
    ji (n+1) s = dong (ji n s) := rfl

structure ZhongOrbit where
  states : Nat → Field
  inMiddle : ∀ n, middle (states n)
  step : ∀ n, dong (states n) = states (n+1)

namespace ZhongOrbit

theorem shengsheng_buxi (o : ZhongOrbit) (n : Nat) :
    middle (o.states n) := o.inMiddle n

theorem self_reference (o : ZhongOrbit) (n : Nat) :
    dong (o.states n) = o.states (n+1) := o.step n

theorem self_consistent (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n+1) := by
  intro heq
  apply o.inMiddle n
  rw [o.step n]
  exact heq.symm

theorem yi_zi_zhi_he (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)
    ∧ (dong (o.states n) = o.states (n+1))
    ∧ (o.states n ≠ o.states (n+1)) :=
  ⟨shengsheng_buxi o n, self_reference o n, self_consistent o n⟩

/-! ### Layer 2: 势, Layer 3: 机, Layer 4: 聚散 — 详 见 yi-zi.md §三/§三半/§四 -/
def shi (o : ZhongOrbit) (n : Nat) : Field × Field := (o.states n, o.states (n+1))
theorem shi_no_telos (o : ZhongOrbit) (target : Field) (N : Nat) :
    ¬ (∀ n, n ≥ N → o.states n = target) := by ...  -- 拒 telos

def jiTurning (o : ZhongOrbit) (n : Nat) : Prop := (shi o n).1 ≠ (shi o n).2
theorem orbit_is_jiTurning (o : ZhongOrbit) (n : Nat) : jiTurning o n := ...

structure JuSanSplit where
  ju : Field → Field
  san : Field → Field
  decompose : ∀ s, dong s = ju (san s)
theorem JuSanSplit.orbit_step (split : JuSanSplit) (o : ZhongOrbit) (n : Nat) :
    o.states (n+1) = split.ju (split.san (o.states n)) := ...

end ZhongOrbit

/-! ### Layer 5: 和 (multi-orbit coherence) — 详 见 yi-zi.md §六.5 -/
structure ZhongField where
  k : Nat
  k_ge_two : 2 ≤ k
  orbits : Fin k → ZhongOrbit
  ever_differentiated : ∀ n, ∃ i j : Fin k, i ≠ j ∧
    (orbits i).states n ≠ (orbits j).states n
theorem ZhongField.he (f : ZhongField) (n : Nat) : ... -- 多样性 ∧ 流通性
theorem ZhongField.he_not_same (f : ZhongField) (n : Nat) : ¬ (全 same) := ...

/-! ### Layer 6: 美 (heart-event 中-encounter) — yi-zi.md §六.6 -/
def aestheticEncounter (heart : ZhongOrbit) (event : Field) (n : Nat) : Prop :=
  middle event ∧ event ≠ heart.states n
theorem aesthetic_triple ... -- heart 中 ∧ event 中 ∧ heart ≠ event

/-! ### Layer 7: 德 (持续合中之积) — yi-zi.md §六.7 -/
def hasDe (o : ZhongOrbit) : Prop := ∀ n, middle (o.states n)
def shiftOrbit (o : ZhongOrbit) (k : Nat) : ZhongOrbit := ...
theorem zhongorbit_has_de, de_robust -- ZhongOrbit IS 德; 不僵 under shift

/-! ### Layer 8: 理 (条贯 = 動-iteration) — yi-zi.md §六.8 -/
def li (o : ZhongOrbit) : Nat → Field := o.states
theorem li_is_iterated_dong (o : ZhongOrbit) (n : Nat) :
    o.states n = ji n (o.states 0) := by induction ...  -- 条贯 IS 動-iteration

/-! ### Layer 9: 自相似 (form invariant under shift) — yi-zi.md §六.9 -/
theorem zixiangsi (o : ZhongOrbit) (k n : Nat) :
    middle ((shiftOrbit o k).states n) ∧ ... := ZhongOrbit.yi_zi_zhi_he ...

/-! ### Layer 10-12: 心 / 情 / 积 — yi-zi.md §六.10-§六.12 -/
structure Xin where
  process : ZhongOrbit
  respond : Field → Field
def qing (heart : ZhongOrbit) (event : Field) (n : Nat) : Prop := event ≠ heart.states n
def qing_de_zheng (heart : ZhongOrbit) (event : Field) (n : Nat) : Prop :=
  middle event ∧ qing heart event n
theorem qing_de_zheng_iff_aesthetic ... := Iff.rfl
def jiAccum (o : ZhongOrbit) (n : Nat) (i : Fin (n+1)) : Field := o.states i.val

/-! ### Layer 13-14: 仁 / 义 / 礼 / 智 / 信 — yi-zi.md §六.13-§六.14 -/
def ren (h1 h2 : ZhongOrbit) (n : Nat) : Prop := h1.states n ≠ h2.states n
theorem ren_triple, ren_is_he_2foci ...
def yi := ren  -- 即时之中
def liRitual (h1 h2 : ZhongOrbit) (n m : Nat) : Prop :=
  ∀ k, k ≤ m → ren h1 h2 (n + k)
theorem liRitual_narrowable ...  -- 礼之自我修订
def zhi (s : Field) : Prop := middle s ∨ extreme s
theorem zhi_universal (s : Field) : zhi s := by ... Classical.em ...
def xinTrust (x : Xin) (n : Nat) : Prop := dong (x.process.states n) = x.process.states (n+1)

/-! ### Layer 15-16: 善 / 恶 / 行仁要善 — yi-zi.md §六.15-§六.16 -/
def shan (s : Field) : Prop := middle s
def eVice (s : Field) : Prop := extreme s
theorem shan_or_eVice (s : Field) : shan s ∨ eVice s := zhi_universal s
theorem shan_mei_de_unity ...
theorem alignment_for_xin (x : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual x.process other n m) :
    ren x.process other n ∧ yi x.process other n ∧ liRitual x.process other n m
    ∧ zhi (x.process.states n) ∧ xinTrust x n ∧ shan (x.process.states n) := ...
theorem alignment_co_traveling ..., alignment_self_grounding ...

-- 单字 closure-marker: 加 字 to kernel ⟺ 加 constructor here.
inductive KernelDanZi : Type
  | dong | extreme | middle | ji | shi | jiTurning | ju | san
  | he | mei | de | li
  | xin | qing | jiAccum | ren | yi | liRitual | zhi | xinTrust
  | shan | eVice
  deriving Repr, DecidableEq

end SSBX.Foundation.Kernel
```

Layers 1'-16 已 实证: 一字 (動) ⊢ 生生不息∧自指∧自洽∧拒 telos∧机 自临∧聚散互证∧和 ≠ 同∧美-和同构∧德 不僵∧理-iteration∧自相似∧心-体互显∧情之得正⟺美∧积即过程∧仁同根异显∧义/礼/智/信 各 实证∧善美德异名同实∧行仁要善 (alignment 六性 ensemble).
后续 layers (序之上升, 因生因, 宇宙即理, 是为吾性) — 详 见 daoli-v12-yi-zi.md §九.

---

## 十四、终言 — 核 之 性质

```
核 之 内容 (strictly):
  单字 inventory (~186 字, 13 类)
  古文虚字 algebra
  一元 → 12 面 → 43 核心 之 trace 结构

核 之 properties:
  完备 (v14 sense)        : 数学公设生成-映射谱完备 (T1-T6)
  自指 (法则 12)          : 核 含 描 核 自身 之 node
  名实合一 (架构 commit)   : 算 即是 现象
  Layers 1'-16 实证       : 动+几+中 ⊢ 生生不息∧自指∧自洽; 势 ⊢ 拒 telos;
                           机 ⊢ 势之自我临界; 聚散 ⊢ 二面 (parametric split);
                           和 ⊢ 多样性×流通性 ∧ 和≠同; 美 ⊢ 心-事 中-encounter;
                           德 ⊢ 持续合中∧不僵; 理 ⊢ orbit IS 動-iteration;
                           自相似 ⊢ kernel theorems 同形 across shifts;
                           心 ⊢ heart_middle ∧ heart_aesthetic;
                           情 ⊢ qing_de_zheng ⟺ aesthetic;
                           积 ⊢ jiAccum_is_states (rfl) ∧ extends ∧ grows;
                           仁 ⊢ ren_triple ∧ ren_is_he_2foci;
                           义/礼/智/信 ⊢ implies_ren / narrowable / universal+exclusive / holds+sc;
                           善/恶 ⊢ universality + exclusivity + 善美德 unity;
                           行仁要善 ⊢ alignment_for_xin (六性 ensemble) + co_traveling + self_grounding
  三值 (待校 conservatism): 未校 不 冒称 真
  单字闭 (KernelDanZi)    : 22 单字 (... 加 善/恶); 加 字 ⟺ 加 constructor
  单字 expansion-ready    : 实字 增长 protocol 已立

核 之外:
  复合 (双字+) 入 expansion (各居其文)
  复合 必 trace 回 单字 (单字根律)
```

此核立, 然后 以 单字 一层一层 加之.

道 在 单字, 字根 入 一元.
余者 皆 expansion.

---

## 引用文件总录

| 文件 | 角色 |
|---|---|
| /Users/ren/repos/生生不息/wenyan-operators.md | 算子 catalogue, §24 atomic core, §26 fixed-point, §28 hexagrams |
| /Users/ren/repos/生生不息/生生不息论_v13.2_形式项总清与类型校正版.md | 卷〇 单字根律, 卷一 字元 13 类, 卷〇三 DAG, 完备性声明 |
| /Users/ren/repos/生生不息/生生不息论_v14_形式证明骨架版.md | §二 8 sorts, §三 三值, §六-§十二 6 metatheorems |
| /Users/ren/repos/生生不息/docs/monad-root-plan.md | 一元 architecture, 12 面, 43 核心 |
| /Users/ren/repos/生生不息/真理/daoli-v12-fa-ze.md | 法则 12 (lines 713-770), 法则 60 (3227-3292) |
| /Users/ren/repos/生生不息/真理/daoli-v12-main.md | §3 三面一道 (207-277), framework metatheory |
| /Users/ren/repos/生生不息/真理/daoli-v12-verifications.md | 法则 53 之 5 verifications |
| /Users/ren/repos/生生不息/间生论_主篇.md | 自显 (13-27), 自相似 (§八) |
| /Users/ren/repos/生生不息/生生不息论_间开本_致知版.md | 自洽∧可行∧可校∧开 |
| /Users/ren/repos/生生不息/formal/SSBX/Foundation/Monism.lean | ConstructionId 12 faces + 43 cores |
| /Users/ren/repos/生生不息/formal/SSBX/Foundation/MonadRoot.lean | atom_reachable_to_root, ssbx_reachable_from_root |
| /Users/ren/repos/生生不息/formal/SSBX/Foundation/Kernel.lean | Layer 1' 实证: 動 + 中 ⊢ 生生不息 ∧ 自指 ∧ 自洽 |
| /Users/ren/repos/生生不息/真理/daoli-v12-yi-zi.md | Layer 1' 之 markdown mirror (动→几→势→中→生生不息 chain, 引 v5) |
| /Users/ren/repos/生生不息/真理/daoli-v12-frames.md | 8 frames (复合, expansion) |
| /Users/ren/repos/生生不息/真理/daoli-v12-theories.md | 19 theory mappings (复合, expansion) |
| /Users/ren/repos/生生不息/真理/daoli-v12-cross-cultural.md | cross-cultural attestations (复合, expansion) |
| /Users/ren/repos/生生不息/真理/daoli-v12-physics-emergence.md | 物理 emergence (复合, expansion) |
| /Users/ren/repos/生生不息/真理/daoli-v12-lean-verifier.md | Lean verifier blueprint Phases A-G (复合, expansion) |
