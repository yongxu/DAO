# 层级单字映射推荐表（R₀ → L0）

> 状态：v3 定本 (2026-05-11)。strict-uniform R₀..R₈ + V₄ Klein Shi + Cell256。
> 父档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) (R₀..R₈ 形式定本) · [yi-calculus-theorem.md](yi-calculus-theorem.md) (Theorems A–K)
> 作用：给 strict-uniform 九层结构（R₀ 太极 / R₁ 爻 / R₂ 四象 / R₃ 八卦 / R₄ 面 Mian = Ben×Zheng / R₅ 五爻 / R₆ 重卦 / R₇ 因卦 Cell128 / R₈ 果卦 Cell256）+ L0 BaguaWen VM 各自定一套**推荐单字**，并把每个推荐字、备选字都写出**理由**。本表是"详细分析层"，配套：
> - **全景图**：[layer-axis-graph.md](layer-axis-graph.md) — 三轴汇聚 Mermaid 图
> - **代码 ground truth**：[`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) — 解释器查表函数 + 往返定理（已通过 `lake build`）
>
> **关于层级字默认 (defaults subject to refinement)**：本表给出每层推荐单字的 default + 备选 + 理由，但层级字 default 仍以「defaults subject to refinement」状态对待——R₀ / R₅ / R₇ / R₈ 等无传统易学 anchor 的层，其推荐字标 `(provisional, §16)`，最终敲定需要长期使用观察。已 register 之 Lean ground truth 文件是 binding，文档候选字是 advisory。
>
> 旧工作稿 [bagua-operator-name-candidates.md](../40_reference_参考/bagua-operator-name-candidates.md) 已降级为 archive pointer。
> Lean 事实以以下为准（v3 / Cell256 / V₄ Shi state）:
> - R-索引层 alias 文件：[`R0_Taiji.lean`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) / [`R1_Yao.lean`](../../formal/SSBX/Foundation/Hierarchy/R1_Yao.lean) / [`R2_SiXiang.lean`](../../formal/SSBX/Foundation/Hierarchy/R2_SiXiang.lean) / [`R3_Trigram.lean`](../../formal/SSBX/Foundation/Hierarchy/R3_Trigram.lean) / [`R4_Mian.lean`](../../formal/SSBX/Foundation/Hierarchy/R4_Mian.lean) / [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) / [`R6_Hexagram.lean`](../../formal/SSBX/Foundation/Hierarchy/R6_Hexagram.lean) / [`R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) / [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean)
> - 伞档 umbrella：[`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)
> - Lift / Project pair：[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)
> - 算子分类：[`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) (8 atomic XOR generators) / [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) (cuo/zong/hu/错综)
> - O-X 记号系统：[`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean)
> - Bagua 主干：[`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) / [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) (Mian = Ben×Zheng = 16) / [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) (R₇) / [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) (R₈) / [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) (R₈ 分层)
> - 基础类型：[`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) / [`Yuan.lean`](../../formal/SSBX/Foundation/Core/Yuan.lean) / [`MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) / [`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean)

## 0. 评估标准

每个字的取舍按这四项排序，前面优先：

1. **传统准确性**：是否对得上《说卦传》《序卦传》《系辞》或邵雍先天图等经典源。这是 2500 年传统的 anchor，不能轻弃。
2. **代数结构对待**：cuo（全反）的两个字应能读出对待感；同层各字应能在 (Z/2)ⁿ 结构里读出"配对"或"位序"。
3. **冲突最小化**：不抢已 register 的 [CoreAtom](../../formal/SSBX/Foundation/Core/MonadRoot.lean)（44 个）、不抢 identity alias 集（恒/守/定/常/止/安/寂/息/平/和）、不抢 [Sheng.step](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) 等已固定的 reading；如必须双用，则要求**同方向**（语义不矛盾）。
4. **单字独立读得通**：现代汉语读者不需要长上下文也能 disambiguate。如果单字过宽必须依赖 context，则降级为 alias，default 用双字或换字。

## 1. 标记约定

| 标记 | 含义 |
|---|---|
| **粗体字** | 推荐 default |
| `等宽` | Lean 算子名或 literal |
| ⭐ | 本文新定（candidates 里没有或与 candidates 不同） |
| ⚠️ | 与 CoreAtom / identity alias / 经典 reading 撞车，需 context resolver |
| △ | 弱双用（同方向，可读但需注意） |
| ✓ | 干净（无撞车） |

## 2. 全表速览

```
R₀  太极/一元    (1)    canonical 双字 太极 / 一元
                        单字 极 / 始 / 無 (provisional, §16)    identity = 恒
        ↓判 fenToYi          ↑空 heToTaiji
R₁  爻/两仪     (2)    阳 / 阴 (literal)
                        义理读 实 / 虚                yi/neg = 易
        ↓析 fenToSiXiang     ↑约 heToYi
R₂  四象        (4)    canonical 双字 太阳/少阴/少阳/太阴
                        单字 夏 / 秋 / 春 / 冬        (邵雍先天图)
        ↓展 fenToTrigram     ↑略上 / 略中 / 略下
R₃  八卦        (8)    canonical 单字 乾/兑/离/震/巽/坎/艮/坤  字根：卦
                        mode 单字 健/悦/显/起/入/险/止/顺
                        横向 改 / 化 / 变 / 错 / 综 / 错综
                        内取 互 (R₆)
        ↓ +1 bit → R₄
        ↑复 guiyi  (R₃ → R₀)
        ↻周 grandCycle  (R₀ → R₃ → R₀)
R₄  面 Mian     (16)   canonical 单字 面 (Ben × Zheng = 16, BenZheng.lean)
                        Ben 4: 物/动/间/事    Zheng 4: 几/势/机/时
                        无独立 trigram 字, 复用 R₃ + R₁ axis
        ↓ +1 bit → R₅
R₅  五爻         (32)   provisional 单字 五 / 接 / 渐 (provisional, §16)
                        无传统 Yi anchor, 是「(Z/2)ⁿ 机械补全」之产物
        ↓ +1 bit → R₆ (chong 之最后一步)
R₆  重卦        (64)   canonical 序卦传名（不重命名，列冲突表） 字根：重
                        6 爻 flip：改 / 化 / 变 / 临 / 主 / 极
                        整卦：错 / 综 / 互 / 错综
                        度量：度（hex Hamming）/ 达（hex transform）
        ↓ +1 bit (印 yìn = toggle 因 bit) → R₇
R₇  因卦 Cell128 (128) canonical 单字 因 / 印 (provisional, §16)
                        新 atom (state): 因 bit (past-trace, Husserl retention)
                        新 atom (operator): 印 yìn = mask `ooooooox` (toggle 因)
        ↓ +1 bit (投 tóu = toggle 果 bit) → R₈
R₈  果卦 Cell256 (256) canonical 单字 果 / 投 / 道 (provisional, §16; 道 = R₈ origin = V₄ identity)
                        新 atom (state): 果 bit (future-projection)
                        新 atom (operator): 投 tóu = mask `oooooooo·x` (toggle 果)
                        Shi V₄ Klein at R₈: 道 / 已 / 今 / 未 (= identity / σ_P / σ_PT / σ_T)
                        shi 转 (V₄ involution): 错 (cuo) — collapsed from old Z/3 next/prev
                        setShi = 置
                        cell 级算子 = R₆ 算子字 + 格
                           (错格 综格 互格 改格 化格 变格 临格 主格 极格)
        ↓ L0 BaguaWen VM
L0  12 条指令          静 置 翻 互 错 综 侔 会 跳 推 取 终
```

**另两条轴**（详 §三轴并存）：

```
内容线  Γ → 三本(物 / 動 / 間) → 三显(位 / 場 / 際) → 三征(幾 / 勢 / 機) → 网体流
本体读法  差 → 识 → 间 → 事
名册线  M0(一元) → M1(Face×12) → M2(CoreAtom×44) → M3(AtomName×333) → M4(FormalNode/ClaimId)
```

`物 / 動 / 間` 是内容线 三本（不在 R-line 上）；`事` 在本体读法第四阶段（≈ R₈ Shi transition）；`缘` 不在任何已 register 层（候选解释名）。

---

# R₀：太极 / 一元

字根（layer-character default）：**`極`** / **`始`** / **`無`** (provisional, §16) — 单字, 选其一。see also: R₀ Taiji 是 strict-uniform 之 zero-anchor (Unit, |R₀| = 2⁰ = 1)。

## R₀ 元素（1 个）

| 项 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| 元素 canonical | `Yuan.TaiJi` ≅ `Unit` (alias: `SSBX.Foundation.Hierarchy.R0.Taiji`, `R0_Taiji.lean`) | **`太极`** / **`一元`**（双字） | 双字最 canonical：`太极` 出自《系辞》"易有太极"；`一元` 是邵雍《皇极经世》"元一" + 当代 Monad DAG 根名。**双字读起来不会被误读**，是最稳的 default。 |
| 元素单字 alias | 同上 | `极` (provisional, §16) | "太极" 的简称；现代汉语 `极点 / 极致 / 终极` 通用，单字读得通；不撞 CoreAtom。亦可作 layer-character default 候选 `始` (《系辞》"原始反终") 或 `無` (老子"无极而太极")。 |

### R₀ 元素备选清单

- `一` — *理由*：单字"一"代表唯一根；*但*已是 [CoreAtom](../../formal/SSBX/Foundation/Core/MonadRoot.lean) `一元` 的字根、过载严重；适合作 alias，不作单字 default。
- `元` — *理由*：道家"乾元资始"传统读；*但*已是 CoreAtom 一元 的另一字根，且 `monad root name = 一元` 直接撞；不作 default。
- `道` — *理由*：道家根名；*但*太重、且已是 CoreAtom；不作 default。
- `源` — *理由*：源头义清；*但*属内容线读法（"源"是发起处），不属 R₀ (root point) 层；适合作哲学 alias。
- `空` — *理由*：佛学 unit 义；*但*已是 `heToTaiji` 算子 default；R₀ 元素与回根算子若同字会失去层次。
- `无` — *理由*：道家"无极"传统；*但*偏负面单字；适合作"无极"双字 alias 或 layer-character 候选 `無` (provisional, §16)。

## R₀ 算子（identity）

| Lean | 作用 | 推荐 | 推荐理由 |
|---|---|---|---|
| `id` （代数 identity） | 任何卦/爻不动 | **`恒`** | 《系辞》"恒久不已"出处；现代汉语 `恒久 / 永恒` 通用；candidates 已 promote；与 L0 `.nop` 的 `静` 分工（前者是数学恒等，后者是操作无操作）。 |

### R₀ identity 备选

- `静` — *理由*：操作语境的"无动作"；*但*留给 L0 `.nop`（VM 操作语义）；二者分层。
- `定` — *理由*：稳定义；*但* `定` 字过载（决定 / 必定 / 安定）；适合作 alias。
- `守` — *理由*：守护义；*但* `守` 在 candidates 里候选作 R₃ 坤的 mode 字（已被我换为 `顺`），保留作 alias。
- `常` — *理由*：道家"道法常"；*但*偏义理，不作算子 default。
- `止` — *理由*：停止义；*但*已给 R₃ 艮的 mode 字（说卦"艮，止也"），分层。
- `安` / `寂` / `息` / `平` / `和` / `一` / `正` — 全都是 identity 集的 alias，可在不同语境作 alias，但 default 只取 `恒`。

## R₀ ↔ R₁ 纵向算子

| 方向 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| R₀ → R₁ 开判 | `fenToYi` (`LiftProject.lean`) | **`判`** | 《系辞》"太极判而二仪生"；现代汉语 `判定 / 判断` 通用；candidates 已 promote。 |
| R₁ → R₀ 收回 | `heToTaiji` (`LiftProject.lean`) | **`空`** | 佛学 unit 义最准（"forget to Unit" = 化为虚空）；现代汉语 `空集 / 空白` 通用；candidates 已 promote。 |

### 纵向备选

- R₀ → R₁：`分` (太宽，必带目标层) / `开` (已是 CoreAtom) / `生` (已给 Sheng.step) / `分阴阳` (双字, alias)
- R₁ → R₀：`归` (太宽) / `极` (太字根) / `归极` (双字 alias) / `归一` (双字 alias) / `合极` (双字 alias)

---

# R₁：爻 / 两仪 / 差

字根（layer-character default）：**`爻`** — 这是传统易学最自然的字根, 已定本。

## R₁ 元素（2 个）

| 元素 | Lean | (爻象) | literal | **推荐义理读** | 推荐理由 |
|---|---|---|---|---|---|
| 阳 | `Yao.yang` (alias: `R1.Yao.yang`, `R1_Yao.lean`) | ⚊ | `阳` | **`实`** ⭐ | 邵雍《观物外篇》"阳为实，阴为虚"出处；R₁ 是"一处差异之两端"，bit-positive 最朴素的读法是 `实`（substantial, present）；现代汉语 `实在 / 真实 / 充实` 通用；不撞 CoreAtom。本文把 candidates 隐含的"升/降"读法降级为 alias，因为升降是运动义，R₁ 还没到运动层（运动是 R₃ 起的）。 |
| 阴 | `Yao.yin` (alias: `R1.Yao.yin`) | ⚋ | `阴` | **`虚`** ⭐ | 同上对偶；现代汉语 `虚拟 / 虚假 / 虚心` 通用；不撞。`实 ↔ 虚` 是 (Z/2) bit 的两端最干净的读法。 |

### R₁ 义理读法备选

- `升 / 降` — *理由*：气机升降，中医/丹道传统；*但*引入运动义，不属 R₁ 本层；**适合**作中医/气功语境 alias，**不适合**作 default。
- `显 / 隐` — *理由*：现象学读法，强调"被看见 vs 未被看见"；*但*"被识"是 R₁ 之上的另一阶段（详 [root-layer-map.md §0](root-layer-map.md) 差/识/间/事），把"显隐"放 R₁ 太早；**适合**作认识论 alias。
- `刚 / 柔` — *理由*：《系辞》"刚柔相推"；*但*这组字传统上用于六十四卦层（"刚来柔来"是 R₆ 卦变之语），R₁ 太早；**适合**作 R₆ alias。
- `进 / 退` — *理由*：动作向；*但*与 `升/降` 同类问题，运动义不属 R₁。
- `正 / 负` — *理由*：数学符号 reading，最 abstract；*但*易学语境疏离；**适合**作形式代数文档 alias，不作易学 default。
- `主 / 从` — *理由*：关系 reading；*但*留给 R₆ 5 爻位 default（君主义），分层。
- `健 / 顺` — *理由*：《说卦》乾健坤顺；*但*已给 R₃ 乾/坤，避免双用。
- `动 / 静` — *理由*：动作语义；*但* `动` 已被 R₃ dong 占用、`静` 已是 L0 `.nop` default，**双重撞车，绝不用**。
- `奇 / 偶` — *理由*：数论 reading；*但*偏数学不偏义理；alias 可。
- `天 / 地` — *理由*：象 reading；*但*已是 R₃ 乾/坤的象别名，分层。

## R₁ 算子（横向 yi）

| Lean | 作用 | 推荐 | 推荐理由 |
|---|---|---|---|
| `Yao.neg` / `yi` | 阴阳互反，involution | **`易`** | 《易经》经名出处（"易者，变也"）；与全系统名一致，作为 yao-flip 算子最权威；现代汉语 `更易 / 易主` 通用；不撞 CoreAtom。 |

### R₁ 算子备选

- `反` — *理由*：现代直观；*但*与 R₃ `cuo`（错=反）撞，且 `反` 字过载；alias 可。
- `翻` — *理由*：现代直观；*但*已给 L0 `.flipYao`（参数化指令）；alias 可。
- `转` / `轉` — *理由*：现代旋转义；*但*已给 R₃/R₆ `zong` 的 alias；不作 default。
- `化` — *理由*：变化义；*但*已给 R₃ `hua`；不作 default。
- `换` — *理由*：替换义；*但*偏物理动作；alias 可。

## R₀ ↔ R₁ 纵向（已在 R₀ 节列）

`判` (R₀→R₁) / `空` (R₁→R₀)。

## R₁ ↔ R₂ 纵向

| 方向 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| R₁ → R₂ 添爻 | `fenToSiXiang` (`LiftProject.lean`) | **`析`** | 形式代数"分解"义最准；现代汉语 `分析 / 解析` 通用；candidates 已 promote；不撞。 |
| R₂ → R₁ 遗忘 | `heToYi` (`LiftProject.lean`) | **`约`** | 数学"约简"义最直接；现代汉语 `约简 / 简约` 通用；candidates 已 promote。 |

### R₁↔R₂ 备选

- 析 备选：`分` (太宽) / `衍` (义理) / `分象` (双字 alias) / `生象` (双字 alias)
- 约 备选：`合` (太宽) / `归` (太宽) / `合仪` (双字 alias) / `归仪` (双字 alias) / `省二` (双字 alias)

---

# R₂：四象

字根（layer-character default）：**`象`** — 这是传统易学最自然的字根, 已定本。

R₂ 这层是邵雍先天图最有 anchor 的一层——"四象配四时"是 1000 年来易学的标准读法。

## R₂ 元素（4 个）

| 元素 | Lean (隐含) | (上爻, 下爻) | canonical 双字 | **推荐单字** | 推荐理由 |
|---|---|---|---|---|---|
| 太阳/老阳 | `(yang, yang)` (alias: `R2.SiXiang.taiYang`, `R2_SiXiang.lean`) | (阳, 阳) | `太阳` / `老阳` | **`夏`** | 邵雍《皇极经世》"太阳之时为夏"出处；极阳之时；现代汉语 `夏天 / 夏至` 通用；不撞 CoreAtom。 |
| 少阴 | `(yang, yin)` (alias: `R2.SiXiang.shaoYin`) | (阳, 阴) | `少阴` | **`秋`** | 邵雍同表"少阴之时为秋"；阳消阴长；现代汉语 `秋天 / 秋收` 通用；不撞。 |
| 少阳 | `(yin, yang)` (alias: `R2.SiXiang.shaoYang`) | (阴, 阳) | `少阳` | **`春`** | 邵雍同表"少阳之时为春"；阴消阳长；现代汉语 `春天 / 春风` 通用；不撞。 |
| 太阴/老阴 | `(yin, yin)` (alias: `R2.SiXiang.taiYin`) | (阴, 阴) | `太阴` / `老阴` | **`冬`** | 邵雍同表"太阴之时为冬"；极阴之时；现代汉语 `冬天 / 冬眠` 通用；不撞。 |

### R₂ 元素备选

- `老 / 二阳` (老阳 alias) — *理由*：传统老阳/少阳的"老"；*但*单字"老"过宽；适合作复合双字 alias。
- `炎 / 凉 / 温 / 幽` — *理由*：气机/温度 reading，比四时更"非时间"；*适合*医学/气功 context alias；*不作* default 因不如四时有先天图加持。
- `昼 / 昏 / 晨 / 夜` — *理由*：日时 reading；*适合*象数 alias；*不作* default 因偏日内时间。
- `炎 / 昃 / 旦 / 冥` — *理由*：极字读法；*但*偏冷僻。
- `老阳 / 少阴 / 少阳 / 老阴` (双字) — *理由*：最传统名；*作* canonical 双字保留，单字 default 仍取四时。

### 为什么 R₂ 用四时而非"老阳/少阴/少阳/老阴"作 default？

两套都很传统，但四时（春夏秋冬）的优势：
1. **每个都是单字**，不需要"老/少"做修饰，default 列更干净
2. **与 R₃ 八卦德对应**：夏 ↔ 健（极阳之相 ↔ 极阳之德）/ 冬 ↔ 顺 / 春 ↔ 起 / 秋 ↔ 止——这种"R₂ 相 ↔ R₃ 德"对应是邵雍图本身的设计
3. **现代汉语完全通用**，无需解释

`老阳/少阴/少阳/老阴` 仍作 canonical 双字保留，文献正式 context 用。

## R₂ 算子

R₂ 内部 V₄ Klein 群结构（XOR 子群）= {id, dong⁰, hua⁰, cuo⁰}（Z/2 × Z/2），但 default 字读层面把横向算子留给 R₃ 起（R₂ 算子主要是纵向：R₁↔R₂ 已列、R₂↔R₃ 在 R₃ 节列）。

## R₂ ↔ R₃ 纵向

| 方向 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| R₂ → R₃ 添爻 | `fenToTrigram` (`LiftProject.lean`) | **`展`** | 升维 / 展开义；现代汉语 `展开 / 展示` 通用；candidates 已 promote。 |
| R₃ → R₂（取下二爻） | `heShang` | **`略上`**（双字） | 略去上爻；候选 `略` 不在 catalogue direct reading，干净；candidates 已 promote。 |
| R₃ → R₂（取初+上爻） | `heZhong` | **`略中`**（双字） | 略去中爻；同上。 |
| R₃ → R₂（取上二爻） | `heXia` | **`略下`**（双字） | 略去初爻；同上。 |

### R₃→R₂ 备选

每个都有这些 alias：`省上/省中/省下`（省略义）/ `去上/去中/去下`（去除义）/ `阙上/阙中/阙下`（缺失义）/ `合上/合中/合下`（合并向上义，但 `合` 字过宽不作 default）/ `舍上/舍中/舍下`（舍弃义）/ `截上/截中/截下`（截取义）。

为什么用 `略`？因为 `略` 在 catalogue 里**没有现存 direct operator reading**（candidates 已 verify），最干净；`省` 与"省略"同义但偏现代汉字 corporate 味；`阙` 偏古；`合` 字过载；`舍` 偏佛学；`截` 偏物理。

---

# R₃：八卦（核心层）

字根（layer-character default）：**`卦`** — 这是传统易学最自然的字根, 已定本（八卦之"卦"）。

R₃ 是整个易学最有传统积淀的一层。每卦都有《说卦传》明确的 canonical 性德。

## R₃ 元素（8 个）—— 详细分析

下面按 cuo 对（全反对）成对介绍，每对 2 卦放一起，方便看对待感。

### 第一对：乾 ↔ 坤（111 ↔ 000）

#### 乾（111）

| 项 | 值 |
|---|---|
| Lean | `Trigram.qian` |
| (y3,y2,y1) | (阳,阳,阳) |
| canonical literal | `乾` |
| 《说卦》性德 | 乾，**健**也 |
| **推荐 mode 字** | **`健`** |

**推荐理由**:
- 《说卦传》原文 7 字之首"乾，健也"——这是中国哲学史上"什么是乾"的最权威定义
- `健` 完全不在 [CoreAtom 列表](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 中，零撞车
- 现代汉语 `健康 / 健全 / 强健` 通用，单字读得通
- 与 R₂ 太阳→夏 概念呼应（极阳之德 vs 极阳之相）

**备选 + 每个理由**:
- `生` ⚠️ — *理由*：道家"乾元资始"读法常作"生生不息"；*但*已是 [Sheng.step](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) default、CoreAtom、T-7 卦名，**三重撞车**，候选改 alias。
- `天` — *理由*：八卦象"乾为天"；*但*单字过宽（天空 / 天命 / 天气），适合作"卦象" alias，不作"卦德" default。
- `元` ⚠️ — *理由*：道家"乾元"传统读；*但*已是 [Monad root 一元](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 的核心 CoreAtom，撞 root 名。
- `刚` — *理由*：刚柔之刚；*但*留给"刚柔"对的 R₆ alias。
- `阳` — *理由*：极阳；*但*已给 R₁ 阳爻 literal，分层。
- `君` — *理由*：君义；*但*留给 R₆ 5 爻位 alias。
- `龙` — *理由*：乾卦六爻全用龙象；*但*偏象不偏德。
- `源` — *理由*：源头义；*但*偏内容线，且 candidates 标"源"为形式代数候选。

#### 坤（000）

| 项 | 值 |
|---|---|
| Lean | `Trigram.kun` |
| (y3,y2,y1) | (阴,阴,阴) |
| canonical literal | `坤` |
| 《说卦》性德 | 坤，**顺**也 |
| **推荐 mode 字** | **`顺`** |

**推荐理由**:
- 《说卦》原文"坤，顺也"
- 现代汉语 `顺利 / 顺序 / 顺从` 通用
- 不在 CoreAtom，零撞车
- 与 乾→健 形成清晰刚柔对待

**备选 + 每个理由**:
- `守` △ — *理由*：守护义传统；*但*属 identity alias 集（恒/守/定/常/止/安/寂/息），双用 identity；改 alias 后 candidates 原选择仍可读。
- `地` — *理由*：八卦象"坤为地"；*但*偏象。
- `承` ⚠️ — *理由*：承乘义传统；*但*已用作爻翼 Y2（2 爻命名），candidates 标记不作 default。
- `柔` — *理由*：刚柔之柔；*但*留给 R₆ alias。
- `阴` — *理由*：极阴；*但*分层。
- `母` — *理由*：坤为母（《说卦》"坤，母也"）；*但*偏伦理。
- `众` — *理由*：邵雍"坤为众"；*但*偏冷僻。
- `安` — *理由*：安顺义；*但*属 identity alias 集，双用。

#### cuo 对待：健 ↔ 顺

刚柔对待，是整个易学最基础的二元——"乾健坤顺"几乎是公认的最深刻一对。

---

### 第二对：兑 ↔ 艮（110 ↔ 001）

#### 兑（110）

| 项 | 值 |
|---|---|
| Lean | `Trigram.dui` |
| (y3,y2,y1) | (阴,阳,阳) |
| canonical literal | `兑` |
| 《说卦》性德 | 兑，**说**（悦）也 |
| **推荐 mode 字** | **`悦`** |

**推荐理由**:
- 《说卦》原文"兑，说也"——"说"字古义即"悦"
- 现代汉语用 `悦` 更通用（`喜悦 / 愉悦 / 悦耳`）
- 不在 CoreAtom，零撞车
- 与 R₃ 艮→止 形成"释放 ↔ 停止"的气机对待

**备选 + 每个理由**:
- `开` ⚠️ — *理由*：候选 candidates 选择，中医气机"开阖"的开；*但*已是 CoreAtom（[MonadRoot.lean](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 列表含 `开/闭`），硬撞车，改 alias。
- `泽` — *理由*：八卦象"兑为泽"；*但*偏象。
- `说` — *理由*：《说卦》原字；*但*现代汉语 `说` 偏 speech 义，作 alias 留古文 context。
- `喜` — *理由*：现代直观；*但* `喜` 字偏情绪不偏德。
- `和` — *理由*：和悦；*但*属 identity alias 集。
- `丽` — *理由*：附丽义；*但*已撞 30 卦 / R₃ 离的备选。

#### 艮（001）

| 项 | 值 |
|---|---|
| Lean | `Trigram.gen` |
| (y3,y2,y1) | (阳,阴,阴) |
| canonical literal | `艮` |
| 《说卦》性德 | 艮，**止**也 |
| **推荐 mode 字** | **`止`** △ |

**推荐理由**:
- 《说卦》原文"艮，止也"
- 现代汉语 `停止 / 截止 / 不止` 通用
- `止` 在 identity alias 集里只是后备 alias 之一（不抢 default `恒`），R₃ 艮 mode 用 `止` 其实是把"艮 = 止"的传统义在系统里保留——这是**有意的弱双用**，不是冲突
- 与 兑→悦 形成"释 ↔ 停"对待

**备选 + 每个理由**:
- `居` — *理由*：candidates 候选，dwell 义；*但* `止` 比 `居` 更准（止是动作终止，居是状态停留——艮卦象本是"止"不是"居"）；改 alias。
- `山` — *理由*：八卦象"艮为山"；*但*偏象。
- `定` — *理由*：稳定义；*但*属 identity alias 集，双用。
- `安` — *理由*：安止义；*但*属 identity alias 集。
- `静` — *理由*：静止义；*但*已给 L0 `.nop` default。
- `束` — *理由*：约束义；*但*偏现代抽象（R₆/R₇ 字根 alias 候选）。

#### cuo 对待：悦 ↔ 止

气机层面的"释放 ↔ 收止"——兑卦象"少女悦"、艮卦象"少男止"，性别也对偶。

---

### 第三对：离 ↔ 坎（101 ↔ 010）

#### 离（101）

| 项 | 值 |
|---|---|
| Lean | `Trigram.li` |
| (y3,y2,y1) | (阳,阴,阳) |
| canonical literal | `离` |
| 《说卦》性德 | 离，**丽**也 |
| **推荐 mode 字** | **`显`** △ |

**推荐理由**:
- `显` 是 [Sheng.toTrigram](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) 的 default（depth-3 Sheng 实现 trigram 的 manifest 义），离用 `显` 与 Sheng manifest 方向一致——**双用是 feature**
- 离卦象"火、日"，传统读"明照"——manifest 是 离 的核心义
- 现代汉语 `显示 / 显著 / 明显` 通用
- 比《说卦》"丽" 更现代化、且 `丽` 与 30 卦（30 卦 = 离卦本身）撞名

**备选 + 每个理由**:
- `丽` ⚠️ — *理由*：《说卦》原字"丽也"；*但*同时是 30 卦传统名（30 卦上下都是离卦，故 30 卦也叫离 / 重明 / 丽），R₃ 与 R₆ 撞名，避免；改义理 alias。
- `明` — *理由*：现代直接（`明亮 / 明天`），离卦象"光明"；*但* `明` 与 35 卦"晋"的"明出地上"alias 重；可作离的 alias，default 仍取 `显`。
- `附` — *理由*：《说卦》"丽"通"附丽"；*但*偏关系不偏德。
- `照` — *理由*：照耀义；*但*偏动作。
- `火` — *理由*：八卦象"离为火"；*但*偏象。
- `日` — *理由*：八卦象"离为日"；*但*偏象。

#### 坎（010）

| 项 | 值 |
|---|---|
| Lean | `Trigram.kan` |
| (y3,y2,y1) | (阴,阳,阴) |
| canonical literal | `坎` |
| 《说卦》性德 | 坎，**陷**也 |
| **推荐 mode 字** | **`险`** |

**推荐理由**:
- 《说卦》"坎，陷也"，但 `险` 是同义现代字
- candidates 已把 `险` 列为坎的 alias 之一
- 现代汉语 `危险 / 险峻 / 风险` 通用
- 与 离→显 形成"明 ↔ 险"的对待

**备选 + 每个理由**:
- `塞` — *理由*：candidates 候选，气机"塞"读法；*但*偏物理"堵"义，比 `险` 偏负而具体；改 alias。
- `陷` — *理由*：《说卦》原字；*但*现代偏负面（陷阱 / 陷落），不如 `险` 中性；alias 可。
- `水` — *理由*：八卦象"坎为水"；*但*偏象。
- `穴` — *理由*：陷阱义；*但*偏冷僻。
- `深` — *理由*：深陷义；*但*偏物理。

#### cuo 对待：显 ↔ 险

明暗 / 安险对待——离卦"明"（火、日）vs 坎卦"险"（水、陷），意象层差异最大。

---

### 第四对：震 ↔ 巽（100 ↔ 011）

#### 震（100）

| 项 | 值 |
|---|---|
| Lean | `Trigram.zhen` |
| (y3,y2,y1) | (阴,阴,阳) |
| canonical literal | `震` |
| 《说卦》性德 | 震，**动**也 |
| **推荐 mode 字** | **`起`** ⭐ |

**推荐理由**:
- 《说卦》原字 `动` 已被 R₃ dong 算子（flip y1）占用，**绝不能再给 震 mode 字**
- `起` 是震的次义（《说卦》"震起"、《序卦》"震者，万物萌动而起也"），保留"震一阳生于下而上发"的意象
- 现代汉语 `起来 / 起步 / 起源` 通用
- 不撞 CoreAtom
- 与 巽→入 形成"上发 ↔ 深入"的对待

**备选 + 每个理由**:
- `动` ⚠️ — *理由*：《说卦》原字；*但*已是 R₃ `dong`（flip y1）default、且裸 `动` candidates 标记不直落坐标；**绝不作** default。
- `元` ⚠️ — *理由*：candidates 候选，"震为长子" / 元发义；*但*已是 [Monad root 一元](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 核心字根，硬撞车，改 alias。
- `雷` — *理由*：八卦象"震为雷"；*但*偏象。
- `奋` — *理由*：奋起义直接；现代汉语 `奋起 / 奋发` 通用；适合作 alias，default 仍取 `起` 因为更短更通用。
- `振` — *理由*：振动义；*但*偏物理。
- `发` — *理由*：发动义；*但* `发` 字过载（发现 / 发生 / 发送）。
- `兴` — *理由*：兴起义；*但*偏现代正面色彩。

#### 巽（011）

| 项 | 值 |
|---|---|
| Lean | `Trigram.xun` |
| (y3,y2,y1) | (阳,阳,阴) |
| canonical literal | `巽` |
| 《说卦》性德 | 巽，**入**也 |
| **推荐 mode 字** | **`入`** △ |

**推荐理由**:
- 《说卦》原字"巽，入也"——直接取经文最权威
- 现代汉语 `入门 / 进入 / 入手` 通用
- 与 震→起 形成"起 ↔ 入"对待（升降 / 出入）

**风险**:
- `入` 在边界/气机语境里有宽义（candidates §冲突表标"边界/气机冲突"）；裸 `入` 在 mode context 外需 disambiguate

**备选 + 每个理由**:
- `申` — *理由*：candidates 候选，"申，伸也"传统读；*但*现代汉语单字"申" 偏申请 / 申明义，不再读"伸入"；改 alias。
- `风` — *理由*：八卦象"巽为风"；*但*偏象。
- `顺` — *理由*：《说卦》兼读"巽，顺也"；*但*已给坤，避免双用。
- `伸` — *理由*：伸展义；*但*与 `申` 同源但 `伸` 不在 candidates 候选中。
- `潜` — *理由*：深入义；*但*偏冷僻。
- `渗` — *理由*：渗入义；*但*偏物理。

#### cuo 对待：起 ↔ 入

升降 / 出入对待——震是"一阳生于下而上发起"，巽是"一阴生于下而向上深入"，二者方向相对。

---

## R₃ 八卦元素总表

| 卦 | (y3y2y1) | literal | mode 字 | 《说卦》 | cuo 对 |
|---|---|---|---|---|---|
| 乾 | 阳阳阳 | `乾` | **`健`** | 健 | ↔ 坤(顺) |
| 兑 | 阴阳阳 | `兑` | **`悦`** | 说 | ↔ 艮(止) |
| 离 | 阳阴阳 | `离` | **`显`** | 丽 | ↔ 坎(险) |
| 震 | 阴阴阳 | `震` | **`起`** | 动 | ↔ 巽(入) |
| 巽 | 阳阳阴 | `巽` | **`入`** | 入 | ↔ 震(起) |
| 坎 | 阴阳阴 | `坎` | **`险`** | 陷 | ↔ 离(显) |
| 艮 | 阳阴阴 | `艮` | **`止`** | 止 | ↔ 兑(悦) |
| 坤 | 阴阴阴 | `坤` | **`顺`** | 顺 | ↔ 乾(健) |

## R₃ 横向算子（爻位 flip 与整卦）

| Lean | 作用 | 推荐 | 推荐理由 |
|---|---|---|---|
| `dong` (Atomic.lean) | flip y1（初爻翻转） | **`改`** | 现代 `改正 / 修改` 直接；candidates 已 promote；与 `动` 拉开（`动` 是家族 alias） |
| `hua` (Atomic.lean) | flip y2（中爻翻转） | **`化`** | 《说卦》"化"古义即变化；现代 `变化 / 化解` 通用 |
| `bian` (Atomic.lean) | flip y3（上爻翻转） | **`变`** | 同 `化` 出处；现代直接 |
| `cuo` (V4Outer.lean) | 三爻全反 | **`错`** | 错卦传统名；candidates 已 promote |
| `zong` (V4Outer.lean) | 反序 | **`综`** | 综卦传统名；candidates 已 promote |
| `cuoZong` (V4Outer.lean) | 错 ∘ 综 | **`错综`**（双字） | 双字最 canonical；单字 `交` 候选已被 Z-4 占用 |

### R₃ 横向算子备选（每条简注）

- `dong` 备选：`动`（家族 alias 不直落坐标）/ `动初` 双字 / `初变` 双字 / `翻初` 双字
- `hua` 备选：`动中` 双字 / `中变` 双字 / `翻中` 双字 / `承化` 双字
- `bian` 备选：`动上` 双字 / `上变` 双字 / `翻上` 双字 / `极变` 双字
- `cuo` 备选：`錯`（繁体）/ `反`（撞 Yao.neg）/ `旁通` 双字（《焦氏易林》）/ `对待` 双字（邵雍）
- `zong` 备选：`綜`（繁体）/ `覆`（古名）/ `倒` / `转`（与"旋转"撞）
- `cuoZong` 备选：`綜錯` / `综错` / `自反` 双字（代数）/ `反覆` 双字（动作）/ `交`（撞 Z-4）

## R₃ → R₆ 重卦 (3-step composite via R₄/R₅)

注：v3 / strict-uniform 视角下，「chong」(重卦) 是 +3 bit 之 composite，分解为 R₃ → R₄ (Mian) → R₅ (五爻) → R₆ (重卦) 三步 +1 bit lift。「乘」作为 high-level surface name 仍保留；底层 mechanically 是三步 lift。

| Lean | 作用 | 推荐 | 推荐理由 |
|---|---|---|---|
| `chong` (composite via `LiftProject.lean`) | R₃ × R₃ → R₆ (= 3-step lift) | **`乘`** | 代数 product 传统读法；《说卦》"乘六龙以御天"已含 product 义；现代汉语 `乘除 / 乘车` 通用；candidates 已 promote |

### chong 备选

- `重`（单字过载，需 context；适合作"双重"alias）
- `重卦`（双字最直接，正式 context alias）
- `叠` / `疊`（直观但偏物理）
- `合卦`（双字，但 `合` 字过载）
- `配`（偏弱）

## R₃ → R₀ / R₀ → R₃ 全程

| Lean | 作用 | 推荐 | 推荐理由 |
|---|---|---|---|
| `guiyi` | 任卦归一（R₃ → R₀） | **`复`** | 道家"复归于无极"传统；现代汉语 `复归 / 恢复` 通用；与 24 卦"复"同字（context 区分） |
| `grandCycle` | R₀ → R₃ → R₀ 闭环 | **`周`** | 周行 / 周天传统；现代汉语 `周期 / 周而复始` 通用；candidates 已 promote |

### guiyi / grandCycle 备选

- `复` 备选：`归一` 双字 / `归极` 双字 / `总归` 双字 / `复归` 双字 / `合极` 双字
- `周` 备选：`大循环` 三字 / `周行` 双字 / `生生归一` 四字 / `循环` 双字

---

# R₄：面 Mian (Ben × Zheng = 16) ⭐ v3 新显式纳入

字根（layer-character default）：**`面`** — 取「Ben × Zheng = 16 面」之「面」 (`BenZheng.lean` 主干名，已 register)。

R₄ 是 strict-uniform (Z/2)⁴ = 16-element layer, 在 v1 之旧编号下被 chong jump 跳过、v2.1 / v3 显式纳入。**结构**: $R_4 = \mathrm{Mian} = \mathrm{Ben} \times \mathrm{Zheng} = (\mathbb{Z}/2)^2 \times (\mathbb{Z}/2)^2 = (\mathbb{Z}/2)^4$，Ben（zong-fixed trigrams）4 = (Z/2)²、Zheng（zong-mobile trigrams）4 = (Z/2)²。Mian = Ben × Zheng = 16 = (Z/2)⁴。

## R₄ 元素（16 个）

| 项 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| canonical | `Mian` (`BenZheng.lean`, alias: `R4.Mian`, `R4_Mian.lean`) | `面` | 已 register 的主干名，**Ben×Zheng = 16 面**之"面" |
| 16 面之 default 名 | 沿用 `BenZheng.lean` 之 16-命 表 | (依 BenZheng 已 register 之 4 本 × 4 征 双字组合) | 物/动/间/事 × 几/势/机/时 = 16；详 `BenZheng.lean` |

### R₄ 元素备选

- `命` — *理由*：邵雍《皇极经世》"元会运世" 之"命"读法；*但*偏哲学，且未 register；备选 layer-character 候选 (provisional, §16)
- `Ben×Zheng` 双字写法（"本征"）— *理由*：直接表 Ben × Zheng；*但*过工程感
- `Quadrant` — 不汉化 reading

## R₄ ↔ R₃ / R₄ ↔ R₅ 纵向

| 方向 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| R₃ → R₄ 添 1 yao | `liftToMian` (`LiftProject.lean`) | **`延`** (provisional) | "延 1 爻"义；备选 `升` (与"升降"alias 冲突)、`续` (CoreAtom) |
| R₄ → R₃ 投影 | `projectMianToTrigram` (`LiftProject.lean`) | **`摄`** (provisional) | "摄取" / "摄影"义；投影 reading |
| R₄ → R₅ 添 1 yao | `liftToWuyao` (`LiftProject.lean`) | **`延`** | 同上 |

注：R₄ 之 16 命由 `BenZheng.lean` 提供 ontological 内容（Mian 之 4 本 × 4 征 = 16）；本表对其字根不重新命名，沿用 BenZheng 之 default。

---

# R₅：五爻 (5-yao) ⭐ v3 新显式纳入 (provisional, §16)

字根（layer-character default）：**`五`** / **`接`** / **`漸`** (provisional, §16) — R₅ 是 R-hierarchy 中**唯一无传统 Yi anchor** 之层, layer-character default 仍未敲定。

R₅ 是 strict-uniform (Z/2)⁵ = 32-element layer, 无传统 Yi anchor — 它 mathematical 存在但 philosophical 上未独立刻画; 是「(Z/2)ⁿ 机械补全」之产物。最弱 ontological 层。

## R₅ 元素（32 个）

| 项 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| canonical | `Wuyao` (`R5_Wuyao.lean`, abbrev for `Mian × Bool` 或 `Cell32`) | `五爻` (双字) (provisional, §16) | 描述性 baseline (no traditional Yi name) |
| 单字候选 | 同上 | `五` (provisional, §16) | 单字简称；过宽（数字 5），需 context |
| 备选 | 同上 | `接` (provisional, §16) | "连接 R₄ 与 R₆ 之过渡" reading |
| 备选 | 同上 | `漸` / `渐` (provisional, §16) | "gradual" reading；与卦名 #53 `渐` 撞 |
| 备选 | 同上 | `临` (provisional, §16) | "approaching" reading；与卦名 #19 `临` 撞、且与 R₆ flip4 占用之 `临` 冲突 — 此候选不推荐 |
| 备选 | 同上 | `进` (provisional, §16) | "advance" reading；与 #35 `晋` 字音近 |

注：R₅ 之 layer-character default 选择有意保持 open——长期使用决定。

## R₅ ↔ R₄ / R₅ ↔ R₆ 纵向

| 方向 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| R₄ → R₅ | `liftToWuyao` (`LiftProject.lean`) | **`延`** (provisional) | 同 R₃→R₄ |
| R₅ → R₆ | `liftToHexagram` (`LiftProject.lean`) | **`成`** ⚠️ (provisional) | "成卦"义；但 `成` 已是 CoreAtom |

---

# R₆：重卦（Hexagram, 64 卦）

字根（layer-character default）：**`重`** — 取「重卦」之「重」 (重叠两个 trigram, 已定本)。

R₆ 是 strict-uniform (Z/2)⁶ = 64-element layer (v1 之旧 R₄, v3 之 R₆)。

## R₆ 元素（64 个）：保留传统名

64 卦每卦都有《序卦传》/《杂卦传》canonical 名，**不应在我们的形式系统里重新命名**。但要记录与其它 registry 的撞车情况。

### R₆ 元素撞车清单

| 卦序 | 卦名 | 撞车对象 | 处理 |
|---|---|---|---|
| 24 | `复` | `guiyi` 算子 default | context 区分（卦名 vs 算子） |
| 30 | `离` | R₃ trigram `离`（30 卦上下都是离） | 本就同字，靠 R₃/R₆ type 区分 |
| 32 | `恒` | R₀ identity 算子 default | context 区分 |
| 50 | `鼎` | candidates 已改 default 为 `器`，`鼎` 降为 alias | 接受 candidates 处理 |
| 51 | `震` | R₃ trigram `震` | 51 卦上下都是震，本就同字 |
| 52 | `艮` | R₃ trigram `艮` | 同上 |
| 57 | `巽` | R₃ trigram `巽` | 同上 |
| 58 | `兑` | R₃ trigram `兑` | 同上 |
| 41 | `损` | candidates §"signature seed" | seed 是 operator 注释，卦名优先 |
| 42 | `益` | 同上 | 同上 |

64 卦中 8 个纯卦（乾坤坎离震艮巽兑）在 R₃ / R₆ 共字是易学本来设计，不是 bug。

## R₆ 单爻翻转（6 个）⭐ 核心决定（v3 仍 binding）

R₃ 已有 `改/化/变` 对应 flip y1/y2/y3。R₆ 把这套提升到 6 爻，前三个延续，后三个 `flip4/5/6` 是 candidates 留待——本表定 `临 / 主`。

### `flip1` / `dongInner` — 翻初爻

- **推荐**: `改`（沿用 R₃）
- **推荐理由**: 与 R₃ 一致避免分裂；初爻是"事之始"，"改正于始"的儒家义合
- **备选**:
  - `初变` 双字 — 位置明确，正式 context
  - `动初` 双字 — 传统名
  - `翻初` 双字 — 操作直观
  - `起` — 与 R₃ 震→起呼应，但已给 震 mode，避免双用

### `flip2` / `huaInner` — 翻 2 爻

- **推荐**: `化`（沿用 R₃）
- **推荐理由**: 同上；2 爻是"地中"，化育义合
- **备选**:
  - `中变` / `二变` 双字 — 位置明确
  - `承变` 双字 — 2 爻"承位"读
  - `承` — 已用作爻翼 Y2，不作 default
  - `中化` 双字 — 义理 alias

### `flip3` / `bianInner` — 翻 3 爻

- **推荐**: `变`（沿用 R₃）
- **推荐理由**: 同上；3 爻在内外卦交际，变义最显
- **备选**:
  - `三变` / `上变` 双字（"上"指内卦上） — 位置明确
  - `际变` 双字 — 内外际
  - `内极` 双字 — 内卦之极

### `flip4` / `dongOuter` — 翻 4 爻 ⭐

- **推荐**: **`临`** ⭐
- **推荐理由**:
  - 4 爻在爻位说是"近君位"或"诸侯位"——不君不臣，临察上下
  - 19 卦本身名"临卦"，象辞"君子以教思无穷，容保民无疆"——"临"字本就有 4 爻位的传统义
  - 现代汉语 `临到 / 临场 / 光临 / 莅临` 通用
  - 不撞 CoreAtom，不在 identity alias 集
  - cuo 对：与 R₆ `flip3 (变)` 形成"内卦上 ↔ 外卦下"位序对待
- **备选**:
  - `近` — *理由*：4 爻"近君位"最直接；*但*单字"近"过宽（近距离 / 近来 / 近代），需 context；alias 可
  - `进` — *理由*：4 爻"进而上"传统读；*但* `进` 字宽义易撞
  - `四变` 双字 — *理由*：明确无歧义；*适合*技术 context alias
  - `动四` 双字 — *理由*：传统"动 X"序列；alias
  - `交` — *理由*：4 爻是内外卦交接；*但* `交` 已是 cuoZong 候选，不作 default
  - `交变` 双字 — *理由*：内外交接的变；alias

### `flip5` / `huaOuter` — 翻 5 爻 ⭐

- **推荐**: **`主`** ⭐
- **推荐理由**:
  - 5 爻是"君位 / 天子位"——传统称"九五之尊"
  - 现代汉语 `主人 / 主持 / 主导 / 主体` 通用
  - candidates 标记"主体冲突"——但在 R₆ mode context 内不会撞，5 爻位本就是 master / host 位
  - cuo 对：与 R₆ `flip2 (化)` 形成"地中 ↔ 君位"对待
- **备选**:
  - `君` — *理由*：传统"君位"最直接；*但*现代汉语偏古，不如 `主` 通用；alias 可
  - `位` — *理由*：5 爻"得位"传统说；*但* `位` 字过宽（爻位说每爻都谈位），不作 default
  - `中` — *理由*：5 爻"得中"；*但* 2 爻也"得中"（地中），且 `中` 字严重过载
  - `正` — *理由*：5 爻"得正"；*但* `正` 字已是 identity alias 之一
  - `五变` / `君变` 双字 — alias
  - `中正` 双字 — *理由*：5 爻最常被赞"中正"；*适合*义理 context alias

### `flip6` / `bianOuter` — 翻上爻

- **推荐**: `极`（candidates 已选）
- **推荐理由**:
  - 上爻是"亢龙有悔"的极位
  - 现代汉语 `极点 / 极端 / 积极` 通用
  - candidates 已 promote
- **备选**:
  - `亢` — *理由*：《乾·上九》"亢龙"；*但*偏负面
  - `穷` — *理由*：物极必反；*但*偏负面
  - `终` — *理由*：终位；*但*已给 L0 `.halt` default
  - `上变` / `极变` 双字 — alias
  - `宗` — *理由*：上爻"宗庙位"古说；*但*偏冷僻

### R₆ flip 综合表

| Lean | 作用 | 推荐 | 爻位读 | 主要备选 |
|---|---|---|---|---|
| `flip1` / `dongInner` (Atomic.lean) | flip 初 | **`改`** | 事之始 | 起 / 动初 |
| `flip2` / `huaInner` (Atomic.lean) | flip 2 | **`化`** | 地中 / 化育 | 承变 / 中化 |
| `flip3` / `bianInner` (Atomic.lean) | flip 3 | **`变`** | 内外际 | 际变 / 内极 |
| `flip4` / `dongOuter` (Atomic.lean) ⭐ | flip 4 | **`临`** | 近君位 / 临察 | 近 / 临变 |
| `flip5` / `huaOuter` (Atomic.lean) ⭐ | flip 5 | **`主`** | 君位 / 主导 | 君 / 中正 |
| `flip6` / `bianOuter` (Atomic.lean) | flip 上 | **`极`** | 亢极 / 物极 | 亢 / 终 |

## R₆ 整卦算子

| Lean | 作用 | 推荐 | 推荐理由 |
|---|---|---|---|
| `Hexagram.cuo` (V4Outer.lean) | 6 爻全反 | **`错`** | 与 R₃ 同字；错卦传统名 |
| `Hexagram.zong` (V4Outer.lean) | 反序 | **`综`** | 与 R₃ 同字；综卦传统名 |
| `Hexagram.hu` (V4Outer.lean) | 取中四爻成互卦 | **`互`** | theorem-backed exact |
| `cuoZongBody` (V4Outer.lean) | 错 ∘ 综 | **`错综`**（双字） | 与 R₃ 同 |

各算子的备选与 R₃ 同款，不重复。

## R₆ 度量算子

| Lean | 作用 | 推荐 | 推荐理由 |
|---|---|---|---|
| `hexHammingDist` | 两卦差爻数 | **`度`** | 度量义最直接；现代 `度量 / 温度` 通用；与 R₃ 距离 `隙` 分层（R₃ 用隙，R₆ 用度） |
| `hexTransform` | 直接变换 a → b | **`达`** | "由此至彼"的儒家义；现代 `到达 / 达成` 通用；与 R₃ transform 同字（跨层共用一字）|
| `pathFromTo` | 最短翻爻路径 | **`径`** | 路径义；现代 `径直 / 路径` 通用；不撞 |
| `FlipCombo.apply` | 8 / 64 翻爻群作用 | **`群`** | 形式代数群论；与 X-4 荀子群义需 context |

### R₆ 度量备选

- `度` 备选：`距` (现代但偏物理) / `差` (字过载) / `数` (太宽) / `间` (内容线) / `隙` (R₃ 用)
- `达` 备选：`通` (process 义偏弱) / `至` (点向不是 a↔b) / `贯` (抽象) / `迁` (新给 shiNext) / `通变` 双字
- `径` 备选：`路` / `轨` / `途` / `道` (CoreAtom 撞) / `变径` 双字
- `群` 备选：`局` / `类` / `变组` 双字 / `卦变` 双字

---

# R₇：因卦 Cell128（= Hexagram × YinBit）⭐ v3 新显式纳入 (provisional)

字根（layer-character default）：**`因`** / **`印`** (provisional, §16) — R₇ 引入「因 bit」(past-trace, Husserl retention 之 binary 标记) + 「印」(yìn, toggle 因 之 XOR 算子)。

R₇ 是 strict-uniform (Z/2)⁷ = 128-element layer (= 64 hex × 2 因-state)。

## R₇ 元素（128 个）

| 项 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| canonical | `Cell128` (`Cell128.lean`, alias: `R7.YinHex`, `R7_YinHex.lean`) | `因卦` 双字 / `因` 单字 (provisional, §16) | "因 bit" 之 marker；现象学：因 ≈ Husserl retention |
| 新 state atom | 因 bit (位置 7) — past-trace | `因` | `o` (位置 7) = 无因, `x` (位置 7) = 有因 |
| 新 operator | 印 (yìn) = toggle 因 = mask `ooooooox` (R₇ scope) | **`印`** (provisional, §16) | "印记"义 (signet, imprint) — 与「因」之 binary mark 同字根；备选 `留` / `始` / `起` |

## R₇ 时序候选字 (provisional)

| 候选 | 义理 | 备注 |
|---|---|---|
| 因 (yīn) | 因果之因；retention | 当前 default state name |
| 印 (yìn) | 印记 / signet；toggle 算子 | 当前 default operator name |
| 留 | 残留义 | alias |
| 始 | 开始义 | alias，与 R₀ `始` 候选有 overlap |
| 起 | 起始义 | alias，已给 R₃ 震 mode |

注：详 §16 (per yi-calculus-theorem.md §16 关于命名 caveat)。

## R₇ ↔ R₆ / R₇ ↔ R₈ 纵向

| 方向 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| R₆ → R₇ 添 因 bit | `liftToCell128` (`LiftProject.lean`) | **`含`** (provisional) | "含因"义；备选 `添` / `带` |
| R₇ → R₆ 投影 (forget 因) | `forgetYin` (`LiftProject.lean`) | **`忘`** (provisional) | "遗忘"义 |
| R₇ → R₈ 添 果 bit | `liftToCell256` (`LiftProject.lean`) | **`续`** (provisional) | "续果"义 |

---

# R₈：果卦 Cell256（= Hexagram × Shi V₄ Klein）⭐ v3 闭合层 (provisional)

字根（layer-character default）：**`果`** / **`投`** / **`道`** (provisional, §16) — R₈ 引入「果 bit」(future-projection) + 「投」(tóu, toggle 果) + 「道」(R₈ 之 origin choice = V₄ identity)。

R₈ 是 strict-uniform (Z/2)⁸ = 256-element layer = 64 × 4 = R-hierarchy **闭合层** (无 R₉, 无第 9 个独立 binary axis)。R₈ 之 origin (`oooooooo` = 道) 与 R₀ (太极 / Unit) 之关系：太极是「无分」之 absolute ground; 道是 (Z/2)⁸ 内 origin choice — 是太极**在 R₈ 维度上的具体投影 / 落地**。

## R₈ 元素（256 个）= 64 卦 × Shi (V₄ Klein-4)

R₈ 把 R₆ 的 64 卦乘上 4 个 V₄ Klein Shi 状态，得到 256 个"卦时格"。

| 项 | Lean | 推荐 | 推荐理由 |
|---|---|---|---|
| canonical | `Cell256` (`Cell256.lean`, alias: `R8.GuoHex`, `R8_GuoHex.lean`) | `果卦` 双字 / `果` 单字 (provisional, §16) | "果 bit" 之 marker；现象学：果 ≈ Husserl protention |
| 新 state atom | 果 bit (位置 8) — future-projection | `果` | `o` (位置 8) = 无果, `x` (位置 8) = 有果 |
| 新 operator | 投 (tóu) = toggle 果 = mask `oooooooox` (R₈ scope) | **`投`** (provisional, §16) | "投射"义 (project, throw forward) — 与「果」之 binary projection 同字根 |
| R₈ origin | `(qian, dao)` = `oooooooo` = V₄ identity | **`道`** (provisional, §16) | R₈ origin = V₄ identity = no-op = 永真 cell；**一字承担五重身份**: origin / identity / no-op / 永真 cell / dao |

## R₈ Shi V₄ Klein-4（4 个，replaces v1 Z/3 cycle）

Shi 在 R₈ 实现为 V₄ Klein-4 群 (cuo²=id, zong²=id, 错综²=id, V₄ closure)，**不是** Z/3 cycle (v1 之 next/prev 已 deprecated)。

| 元素 | Lean | (因, 果) bit | V₄ 元 | R₈ cell (与乾) | 推荐字 | 推荐理由 |
|---|---|---|---|---|---|---|
| 道（origin） | `Shi.dao` | (0, 0) | identity | `oooooooo` | **`道`** (provisional, §16) | R₈ origin = V₄ identity；老子"道法自然"；**一字承担五重身份**：origin / identity / no-op / 永真 cell / dao |
| 已（过去） | `Shi.ji` | (1, 0) | σ_P (cuo) | `ooooooxo` | **`已`** | 现代汉语 `已经 / 已然 / 已往` 通用；古义"已往"也通；不撞 |
| 今（现在） | `Shi.jin` | (1, 1) | σ_PT (错综) | `ooooooxx` | **`今`** | 现代汉语 `今天 / 现今 / 如今` 通用；古义即"现在"；不撞 |
| 未（未来） | `Shi.wei` | (0, 1) | σ_T (zong) | `ooooooox` | **`未`** | 现代汉语 `未来 / 未济` 直接；64 卦最末"未济"自然呼应；不撞 |

注：V₄ Klein-4 之 group multiplication: 道 = e; 已·已 = 道; 未·未 = 道; 今·今 = 道; 已·未 = 今; 已·今 = 未; 未·今 = 已 (Z/2 × Z/2 closure)。

### Shi 元素备选

- 已 备选：`既`（古义"既往"，alias）/ `往`（动作向，alias）/ `过`（现代但太宽）/ `先`（"先前"alias）
- 今 备选：`现`（现代直接，alias）/ `见`（古义"现身"，偏冷）/ `当`（"当下"alias）/ `时`（太宽）
- 未 备选：`将`（"将来"，alias）/ `来`（"来日"，alias）/ `后`（"后来"，alias）/ `未来` 双字（alias）
- 道 备选：`元`（与 monad root 撞）/ `源` (内容线读法) / `空` (heToTaiji default 已给) — 详 §16

`道 / 已 / 今 / 未` 都是单字、现代通用、传统也用、互不撞——**这一组 (V₄ Shi)** 在 v3 强化定本（替代 v1 之 Z/3 cycle）。

## R₈ Shi V₄ transition 算子 ⭐ v3 修订（替代 v1 Z/3 迁/溯）

v3 / V₄ Klein 视角下: Shi-side 之 transition 全部是 V₄ involution (cuo²=id)，**所有 transition 算子 collapse 为同一个 `Shi.cuo`** (V₄ self-inverse)。v1 之 Z/3 cycle (next^[3]=id) 已被 cuo^[2]=id 替代。

| Lean | 作用 | 推荐 | 推荐理由 |
|---|---|---|---|
| `Shi.cuo` / `shiCuo` (R8_GuoHex.lean) | V₄ involution on Shi | **`错`** (Shi-side) | V₄ self-inverse；与 hex-side `Hexagram.cuo` 同字（跨层共字），区分靠 type |
| `Shi.zong` / `shiZong` (R8_GuoHex.lean) | V₄ second involution on Shi | **`综`** (Shi-side) | V₄ second self-inverse；同上 |
| `Shi.cuoZong` / `shiCuoZong` (R8_GuoHex.lean) | V₄ composite | **`错综`** (Shi-side) | V₄ closure 之第三 involution |
| (legacy `ShiTransition.next/.prev`) | Z/3 cycle (deprecated) | `迁` / `溯` (provisional, retained as surface alias) | 在 V₄ 下 `迁` 和 `溯` 双双 collapse 为 `Shi.cuo`（详 `LayerCharacterMap.lean` `ShiTransition.apply`）；保留只为 backward compatibility |

### Shi-side V₄ 算子备选

- `错` (Shi-side) 备选：用「错时」双字 disambiguate from hex-side cuo
- `综` (Shi-side) 备选：「综时」双字
- `错综` (Shi-side) 备选：「错综时」三字
- legacy 迁/溯：保留作 surface alias，但 underlying = V₄ involution

### shi 转换备选

- `迁` 备选：
  - `推`（时间推移直观；*但*已给 L0 `.push` default，撞车）
  - `进`（方向直接；*但*与 4 爻位"进"alias 撞）
  - `行`（已是 CoreAtom）
  - `演`（演进义；偏过程不偏离散步进）
  - `next` / `下一` 双字（工程感强）

- `溯` 备选：
  - `退`（与 `进` 对；*但* `进` 没用作 default，对偶失衡）
  - `回`（直观；*但*偏 generic）
  - `复`（已给 guiyi default）
  - `逆`（数学"逆"义；适合作 alias）
  - `prev` / `上一` 双字（工程感强）

## R₈ setShi 算子

| Lean | 作用 | 推荐 | 推荐理由 |
|---|---|---|---|
| `setShi sh` | 将当前 cell 时态置为 sh (V₄ Shi) | **`置`** | candidates 已选；`置` 是 primitive setter 最干净单字（"置 道"读作"把 Shi 置为道"）；现代汉语 `设置 / 置入` 通用 |

### setShi 备选

- `设` — 现代直接但偏 generic（设计 / 设定）
- `定` — 已是 identity alias
- `更` — 替换义但太宽
- `调` — 偏 fine-tune
- `令` — 古义"使为"；偏冷
- `易` — 已给 R₁ yi 算子

## R₈ Cell-级算子（R₆ 提升 + `格`）

candidates 设计：在 Cell 语境下，把 R₆ 算子字加 `格` 后缀做 disambiguation：

| 算子 | Lean | Cell-语境 default |
|---|---|---|
| `hexCuo` 提升 | Cell256 hex-side 全反 | **`错格`**（双字） |
| `hexZong` 提升 | Cell256 hex-side 反序 | **`综格`**（双字） |
| `hexHu` 提升 | Cell256 互 | **`互格`**（双字） |
| `flip1..6` 提升 | Cell256 单爻翻转 | **`改格 / 化格 / 变格 / 临格 / 主格 / 极格`**（双字） |

加 `格` 是因为 Cell context 内 `错 / 综 / 互 / 改 / 化 / 变 / 临 / 主 / 极` 这些字本身已被 R₃/R₆ 用，加 `格` 表示"在格位上做这件事"。

## R₈ 元素的"卦+时"复合表达

每个 cell 可写为 "卦名 + 时" 双字，例如：

| (R₆ 卦, R₈ Shi) | 读法 |
|---|---|
| (乾, 道) | `乾道` |
| (乾, 已) | `乾已` |
| (乾, 今) | `乾今` |
| (乾, 未) | `乾未` |
| (未济, 今) | `未济今` |（未济是 64 卦末，2 字 + 1 字 = 3 字）|
| (既济, 已) | `既济已` |（双字 + 单字）|

用 mode 字（健 等）替代卦名也成立："健今"读作"乾在今的格位"——但这要求 reader 知道"健 = 乾 mode 字"的映射。建议正式 context 仍用 canonical 卦名，mode 字仅用于强调"这是该卦的德行向" 的语境。

注：v3 / 256 cell layout 之 8-bit string：`[y₁ y₂ y₃ y₄ y₅ y₆ 因 果]` (LTR, 初爻在左)，`oooooooo` (8 个 o) = 道-anchor (V₄ identity at 乾·道)；详 yi-RO-hierarchy.md §2.1。

---

# L0：BaguaWen VM 指令（12 条）

L0 是 Cell256 上的受控虚拟机 (v3, V₄ Shi)。candidates §"L0 BaguaWen 指令锚点" 已基本 settled，下面把 default 字按"现代汉字 + 双字必要时"原则展开：

## L0 指令明细

### `.nop` — 空操作

- **推荐**: **`静`**
- **推荐理由**: 操作语境的"无动作"；现代汉语 `安静 / 静止 / 静态` 通用；与代数 identity `恒` 分工（前者是 VM 操作"什么都不做"，后者是数学 endo-map id）
- **备选**:
  - `恒`（让给代数 identity，避免双用）
  - `不动` 双字（candidates 当前 token，已接 alias）
  - `守` / `定` / `常` / `止` / `安` / `寂` / `息` / `平` / `和` / `一` / `正`（identity alias 集，作 alias）

### `.setShi` — 置时

- **推荐**: **`置`**
- **见 R₈.setShi 节**

### `.flipYao` — 翻爻（参数化）

- **推荐**: **`翻`**
- **推荐理由**: 现代直接（`翻转 / 翻动`）；不抢 R₃/R₆ 的 `改 / 化 / 变`，因为它是参数化指令（接受爻位号）≠ 裸算子
- **备选**:
  - `转` / `轉`（已给 zong alias）
  - `反`（已给 cuo alias）
  - `换` / `換`（替换义；alias 可）
  - `易`（已给 R₁ yi）
  - `改`（已给 R₃ dong）
  - `动`（家族 alias 不直落）
  - `倒`（偏物理）
  - `更`（太宽）

### `.hu` — 互（无参数）

- **推荐**: **`互`**
- **推荐理由**: 与 R₆ 同字；context 区分 R₆-mode 与 L0-instr
- **备选**:
  - `交`（已给 cuoZong 候选）
  - `相`（太宽）
  - `中`（过载）

### `.cuo` — 错（无参数）

- **推荐**: **`错`**
- **推荐理由**: 与 R₆ 同字
- **备选**:
  - `錯`（繁体 alias）
  - `反`（撞 yi alias）
  - `旁通` 双字（古名 alias）

### `.zong` — 综（无参数）

- **推荐**: **`综`**
- **推荐理由**: 与 R₆ 同字
- **备选**:
  - `綜`（繁体 alias）
  - `覆`（古名 alias）
  - `转`（撞 zong-like 通用读）

### `.branchYaoEq` — 比爻分支

- **推荐**: **`侔`**
- **推荐理由**: 《墨经》"侔，比辞而俱行也"——专指相等 / 相当；冷僻但单义、零冲突；比裸 `比` 更精确
- **备选**:
  - `比`（现代直接，但宽义大）
  - `校`（校验义，偏现代）
  - `同`（太宽）
  - `等`（数学 alias 可）

### `.branchShiEq` — 比时分支

- **推荐**: **`会`**
- **推荐理由**: "相会 / 正逢其时"古义；现代汉语 `会面 / 会合 / 相会` 通用
- **备选**:
  - `侔`（已给 branchYaoEq）
  - `值`（值班 / 当值义，偏现代）
  - `同`（太宽）
  - `逢`（古义"相逢"，alias 可）
  - `遇`（偶遇义，alias 可）

### `.jump` — 跳

- **推荐**: **`跳`**
- **推荐理由**: VM 控制流直接
- **备选**: `跃`（动作；alias 可）/ `往`（方向；偏弱）/ `至`（点向；偏弱）

### `.push` — 推

- **推荐**: **`推`**
- **推荐理由**: VM 直接；与 R₈ `迁` (legacy alias) 分层（前者是栈操作，后者是 V₄ involution surface alias）
- **备选**: `入`（已给 巽 mode）/ `压`（偏物理）/ `纳`（偏古）

### `.pop` — 取

- **推荐**: **`取`**
- **推荐理由**: VM 直接
- **备选**: `出`（与 `入` 对，偏 generic）/ `脱`（偏物理）/ `提`（偏现代）

### `.halt` — 终

- **推荐**: **`终`**
- **推荐理由**: 现代直接（`终止 / 终结`）
- **备选**: `止`（已给 R₃ 艮）/ `停`（偏现代）/ `息`（属 identity alias 集）

## L0 指令汇总表

| YiInstr | 当前 token | 推荐 | 主要备选 |
|---|---|---|---|
| `.nop` | `不动` | **`静`** | 恒（代数）/ 守 / 立 |
| `.setShi` | `设时` | **`置`** | 设 / 调 |
| `.flipYao` | `翻爻` | **`翻`** | 转 / 易 / 反 |
| `.hu` | `互` | **`互`** | 交 |
| `.cuo` | `错` | **`错`** | 反 |
| `.zong` | `综` | **`综`** | 转 / 覆 |
| `.branchYaoEq` | `比爻` | **`侔`** | 比 / 校 / 同 |
| `.branchShiEq` | `比时` | **`会`** | 侔 / 值 / 同 |
| `.jump` | `跳` | **`跳`** | 跃 / 往 |
| `.push` | `推` | **`推`** | 入 / 压 / 纳 |
| `.pop` | `取` | **`取`** | 出 / 提 / 脱 |
| `.halt` | `终` | **`终`** | 止 / 停 / 息 |

---

# 三轴并存：内容线 / 本体读法 / 名册线

> 上面 R₀–L0 全在**生成线**和它的 VM 上。`物 / 動 / 間 / 事 / 缘` 这些字**不在生成线上**——它们属于另外几条轴。这一节把这三条轴的位置和字根全摆清楚。

## A. 速答：事 / 间 / 物 在哪里？

| 字 | 形式位置 | Lean 锚点 | 与 R-line 的关系 | 单字状态 |
|---|---|---|---|---|
| 物 | 内容线 三本之一 + CoreAtom 之一 | [`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean) + [`MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) | 双线交点："承载状态的项"——R-line 任一层的元素都可读为"物" | ✓ 已是 canonical 单字 + 已 register |
| 動 / 动 | 内容线 三本之一 | [`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean) | 与 R₃ `dong` 算子 family 同字根（生成线 horizontal flip y1）。**两层不同**：内容线的 `動` 是"变化本身的本体"，R₃ 的 `dong` 是"翻初爻"这一具体算子 | ⚠️ 单字撞 R₃ dong，需 context |
| 間 / 间 | 内容线 三本之一 + 本体读法第三阶段 | [`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean) + [root-layer-map.md §0](root-layer-map.md) | 间 ≈ 关系空间；R-line 没有原生的 "relation between elements" 节点，间 是补这一空位的 | ✓ canonical 单字 |
| 事 | 本体读法第四阶段 ≈ R₈ Cell256 transition | 隐含于 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) 的 Shi V₄ transition | 事 = "关系在某一时态/位点上发生"≈ Cell256 之间的一条 V₄ transition | ✓ canonical 单字（未在 CoreAtom 列表，但作 conceptual anchor）|
| 缘 | **不属于任何已 register 层** | — | 只在 root-layer-map.md §4 作"解释名"提及；可读为 relation edge label，但未提升为 CoreAtom | ❌ 未 register，候选状态 |

## B. 三轴关系图

```
    （生成线 R-line, strict-uniform R₀..R₈）          （内容线）              （名册线 M-line）

    R₀  太极 / 一元 ── ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ Γ  (论域)  ─ ─ ─ ─ ─ ─ ─ M0  一元
        │                                                │                          │
    R₁  爻 / 两仪                                        ↓                          M1  Face (12)
        │                                              三本                          │
    R₂  四象                                       物 / 動 / 間  ←──── 间           M2  CoreAtom (44)
        │                                                │                          │
    R₃  八卦                                             ↓                          M3  AtomName
        │                                              三显                          │
    R₄  面 Mian (Ben×Zheng=16)                     位 / 場 / 際                   M4  FormalNode / ClaimId
        │                                                │
    R₅  五爻 (provisional, §16)                          ↓
        │                                              三征
    R₆  重卦                                      (幾 / 勢 / 機) ─────── 事
        │                                                │
    R₇  因卦 Cell128 (+因 bit, 印 mask)                  │
        │                                                ↓
    R₈  果卦 Cell256 (+果 bit, 投 mask) ──→ Shi V₄ Klein {道, 已, 今, 未}
        │
    L0  BaguaWen VM (on Cell256)            开闭 / 网体流
                                                   │
                                                   ↓
                                            生生不息论
```

**三条线的分工**：

- **生成线 (R-line)** 答 "怎么从一元长出可计算的易结构"——这是**形式**。
- **内容线** 答 "我们在谈什么样的本体范畴"——这是**内容**。
- **名册线 (M-line)** 答 "一个正式名字怎么回根"——这是**回溯**。

`物 / 動 / 間 / 事` 都在内容线上（间另兼本体读法第三阶段）；`缘` 在三条线之外、是"未定的解释名"。

## C. 内容线 L1：三本（物 / 動 / 間）

形式位置：[`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean) 的 `JianRoot` inductive，3 个构造子。

### 物 (wu)

| 项 | 值 |
|---|---|
| Lean | `JianRoot.wu` |
| 义理 | discrete individuality / 承载状态的项 |
| canonical literal | **`物`** |
| 与 R-line 关系 | R₀–R₈ 任一层的元素都可读为"物"——它是"被识别、被稳定、可进入关系"的项的总称 |

**推荐字 `物` 的理由**:
- `物` 是 [CoreAtom 列表](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 中已 register 的核心字根，不需要找替代
- 现代汉语 `物 / 物体 / 事物 / 实物` 通用，单字读得通
- 古今汉语都以 `物` 表"个别的承载者"，从《系辞》"方以类聚，物以群分" 到现代汉语都一致

**备选义理读（每个理由）**:
- `项` — *理由*：现代代数"项 (term)"义直接；*但*偏数学，弱了"承载者"的本体感；alias 可
- `体` — *理由*：体用之"体"传统读，《周易程氏传》体用论；*但* `体` 字过载（身体 / 主体 / 体系），需 context
- `实` — *理由*：实在义；*但*已给 R₁ 阳-义理读，避免双用
- `质` — *理由*：本质义；*但*偏抽象本质，不偏个别承载
- `具` — *理由*：具体义；*但*偏弱
- `件` — *理由*：现代"一件物"；*但*偏现代量词

### 動 / 动 (dong)

| 项 | 值 |
|---|---|
| Lean | `JianRoot.dong` |
| 义理 | continuous process / 变化本身 |
| canonical literal | **`動`**（繁）/ **`动`**（简） |
| 与 R-line 关系 | ⚠️ 与 R₃ `dong` 算子 family（horizontal flip y1）同字根 |

**与 R₃ dong 的关系**：

这是本表里**最重要的一处分层**：

| 维度 | 内容线 `動` | R₃ `dong` 算子 |
|---|---|---|
| 是什么 | "变化本身"作为本体范畴 | "翻初爻"这一具体算子 |
| 类型 | `JianRoot` 构造子之一（type-level） | `Trigram → Trigram` 函数 |
| 作 default | 内容线讨论中作 `動 / 动` 默认 | R₃ 算子 default 用 `改`（不直接用 `动`，避免本层撞车） |
| candidates 标记 | — | "动 / 動 保留为 R₃ 生成元家族 alias；裸 `动` 不直接落到某个坐标" |

所以 `动` 这一字在系统里**有意分层**：
- 当上下文是"内容/本体范畴"时，`动` 读作 `JianRoot.dong`（变化本身）
- 当上下文是"R₃/R₆ 算子"时，`动` 是 `dong/hua/bian` 家族 alias（具体翻爻动作），但 default 用 `改` 避免裸 `动` 直落坐标

**推荐字 `動 / 动` 的理由**:
- 已是 [CoreAtom](../../formal/SSBX/Foundation/Core/MonadRoot.lean)，不需要替代
- 现代汉语 `动 / 运动 / 动态` 通用
- 古今汉语都以 `动` 表"运动 / 变化"

**备选义理读**:
- `行` — *理由*：行动义传统（《系辞》"在天成象，在地成形，变化见矣"）；*但*已是 CoreAtom；alias 可
- `变` — *理由*：变化义；*但*已给 R₃ `bian`（flip y3）；不作内容线 default
- `化` — *理由*：化育义；*但*已给 R₃ `hua`（flip y2）
- `运` — *理由*：运动义；*但*偏现代物理
- `流` — *理由*：流动义；*但*已有"流"字在内容线下游（"网体流"）

### 間 / 间 (jian)

| 项 | 值 |
|---|---|
| Lean | `JianRoot.jian` |
| 义理 | relational structure / between-ness / 关系空间 |
| canonical literal | **`間`**（繁）/ **`间`**（简） |
| 与 R-line 关系 | R-line 没有原生的"元素之间的关系"节点；`間` 补这一空位 |
| 与本体读法关系 | 同时是本体读法第三阶段（详 §E） |

**推荐字 `間 / 间` 的理由**:
- 古今汉语 `间 / 之间 / 中间 / 间隙 / 关系` 都以 `间` 为核心
- 不撞 CoreAtom（44 字列表里没有 `间`）
- 与"间"作 third stage of 本体读法 一致

**备选义理读**:
- `际` — *理由*：交际义；*但*已给三显（际是 間 的 manifestation）；分层
- `隙` — *理由*：缝隙义；*但*已给 R₃ hammingDist；分层
- `关` — *理由*：关系义；*但*偏现代抽象，且 `关` 字过载
- `联` — *理由*：联系义；*但*偏现代
- `缘` — *理由*：因缘义；*但*未 register、且属解释名（详 §F）
- `系` — *理由*：联系义；*但*与"系辞"撞名

## D. 内容线 L2：三显（位 / 場 / 際）

| 三显字 | Lean | 三本来源 | 义理 | 推荐 default |
|---|---|---|---|---|
| 位 | `JianAspect.wei` | 物 的 manifestation | 位置 / position | **`位`**（canonical）|
| 場 / 场 | `JianAspect.chang` | 動 的 manifestation | 场 / field | **`場`** / **`场`**（canonical）|
| 際 / 际 | `JianAspect.ji` | 間 的 manifestation | 接口 / 交际 / interface | **`際`** / **`际`**（canonical）|

### 位

- **推荐**: `位`
- **推荐理由**: 古今汉语都以 `位` 表"位置 / 名位 / 爵位"，从《周易》"圣人之大宝曰位" 到现代汉语都通；不撞 CoreAtom
- **备选**:
  - `所` — *理由*：处所义；*但* `所` 偏 abstract（"所在")，单字弱
  - `处` — *理由*：现代直接；*但*偏 generic（处于 / 处理 / 处所）
  - `点` — *理由*：现代几何"点"；*但*太抽象
  - `次` — *理由*：序次；*但*偏序数
  - `居` — *理由*：居处；*但*已给 R₃ 艮 mode 的 alias
- **与 R₆ 5 爻位"位"alias 的关系**：内容线 `位` 是位置本体，R₆ 5 爻 `位` 是 5 爻位的别名（candidates 已标"`位` 字过宽，不作 default"）；分层。

### 場 / 场

- **推荐**: `場` / `场`
- **推荐理由**: 现代物理 `场 / 场域 / 电场 / 磁场` 通用；古义 `场` = "场所" 传统；与"動 之 manifestation = 場"（运动之展开必有场）逻辑一致
- **备选**:
  - `域` — *理由*：领域义；*但*偏现代抽象 territory
  - `境` — *理由*：境界义；*但*偏佛学
  - `区` — *理由*：现代直接；*但*太 administrative
  - `界` — *理由*：界限 / 边界；*但*偏边界不偏内部
  - `空间` 双字 — *理由*：现代精确；*但*双字太重

### 際 / 际

- **推荐**: `際` / `际`
- **推荐理由**: 古今汉语 `际 / 国际 / 交际 / 边际` 都以 `际` 表"交接处"，《周易》"乾坤其易之缊邪？乾坤毁则无以见易" 隐含际义；与"間 之 manifestation = 際"（关系之具体接面）逻辑一致
- **备选**:
  - `接` — *理由*：现代直接；*但*偏 verb（动作）
  - `连` — *理由*：连接义；*但*偏 verb
  - `交` — *理由*：交接义；*但*已被 Z-4 占用 + cuoZong 候选
  - `缝` — *理由*：缝合处；*但*偏物理
  - `面` — *理由*：界面义；*但*已给 M1 Face

## E. 内容线 L3：三征（幾 / 勢 / 機）

| 三征字 | Lean | 三本来源 | 义理 | 推荐 default |
|---|---|---|---|---|
| 幾 / 几 | `JianMark.ji` | 物 的 dynamic mark | 端倪 / 萌芽 / contingency | **`幾`** / **`几`** |
| 勢 / 势 | `JianMark.shi` | 動 的 dynamic mark | 趋势 / momentum | **`勢`** / **`势`** |
| 機 / 机 | `JianMark.jiMoment` | 間 的 dynamic mark | 时机 / occasion | **`機`** / **`机`** |

### 幾 / 几

- **推荐**: `幾` / `几`
- **推荐理由**: 《系辞》"知几其神乎"出处——`幾` 是中国哲学最深的"萌芽 / 端倪"概念；现代汉语 `几乎 / 几微` 通用（虽语义偏离）；繁体 `幾` 与简体 `几` 在哲学语境里仍指"萌动之始"
- **备选**:
  - `兆` — *理由*：征兆义；*但*偏占卜
  - `萌` — *理由*：萌芽义；*但*偏植物意象
  - `端` — *理由*：开端义；*但*偏 generic
  - `朕` — *理由*：朕兆古义；*但*偏冷僻
  - `微` — *理由*：微妙义；*但*偏程度

### 勢 / 势

- **推荐**: `勢` / `势`
- **推荐理由**: 古今汉语 `势 / 形势 / 趋势 / 势能` 通用；《孙子》"势者，因利而制权"——这是中国哲学最核心的"动态趋势"概念；不撞 CoreAtom
- **备选**:
  - `趋` — *理由*：趋向义直接；*但*偏 verb
  - `向` — *理由*：方向义；*但*偏 spatial
  - `力` — *理由*：力量义；*但*偏物理
  - `态` — *理由*：状态义；*但*偏 static

### 機 / 机

- **推荐**: `機` / `机`
- **推荐理由**: 古汉语 `機` = "时机 / 机会 / 关键节点"（《周易》"机者，动之微，吉之先见者也"——与 `幾` 同源但分化），现代汉语 `时机 / 良机 / 机会` 仍通；繁简对应清楚
- **备选**:
  - `时` — *理由*：时机义；*但*已是 R₈ Shi 的字根（道/已/今/未 V₄ Klein）
  - `会` — *理由*：会合义；*但*已给 L0 `.branchShiEq`
  - `期` — *理由*：期会；*但*已是 CoreAtom
  - `候` — *理由*：时候义；*但*偏现代
  - `刻` — *理由*：时刻；*但*偏点

## F. 本体读法：差 / 识 / 间 / 事

来自 [root-layer-map.md §0](root-layer-map.md)——这是比 R-line / 内容线 / 名册线 都更先一层的"差异如何成为可说之物"四阶段。

| 阶段 | 字 | 推荐 | 与 R / 内容线 关系 |
|---|---|---|---|
| 差 | **`差`** | 一处差异本身 | ≈ R₁ 爻 / yao（"差异之两端"）|
| 识 | **`识`** | 差异被分辨、可命名 | 中间过渡：从"有差"到"被指认"；不属任一线的明确层 |
| 间 | **`间`** | 已识之差之间的关系 | ≈ 内容线 三本中的 `間` |
| 事 | **`事`** | 关系在时态 / 位点上发生 | ≈ R₈ Cell256 之间的 V₄ Shi transition |

### 差

- **推荐**: `差`
- **推荐理由**: 古今汉语 `差 / 差异 / 差别 / 差距` 通用；现代代数 / 集合论"差"义直接；不撞
- **备选**:
  - `异` — *理由*：差异义；*但*偏 abstract
  - `分` — *理由*：分别义；*但*太宽 + 已用作纵向算子（fenToYi）
  - `别` — *理由*：分别义；*但*偏现代
  - `离` — *理由*：分离义；*但*已给 R₃ 离卦

### 识

- **推荐**: `识`
- **推荐理由**: 古今汉语 `识 / 认识 / 识别 / 识字` 通用；佛学"转识"传统；现代汉语 `识` 表"识别 / 知" 直接；不撞 CoreAtom（虽然有"识"作"觉知" alias 在某些 face context）
- **备选**:
  - `知` — *理由*：知觉义；*但*偏 epistemic
  - `辨` — *理由*：辨别义；*但*偏 verb
  - `认` — *理由*：现代认知；*但*偏现代
  - `察` — *理由*：察觉义；*但*偏过程

### 间（同上 §C）

`间` 在本体读法是第三阶段（关系），在内容线是 三本之一（`間`）——是同一字两个 register 位置（同方向，弱双用）。

### 事

| 项 | 值 |
|---|---|
| 推荐 | **`事`** |
| 形式锚 | ≈ R₈ Cell256 之间的 V₄ Shi transition（"事之发生" = 卦时格之间的 V₄ involution）|
| 状态 | canonical 单字，但**未在 [CoreAtom 列表](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 中 register**——作为 conceptual anchor 使用 |

**推荐 `事` 的理由**:
- 古今汉语 `事 / 事件 / 事实 / 故事` 通用——`事` 是中文里最自然的"发生之物"
- 不撞 CoreAtom（虽然 candidates 里有 `事 / 故 / 因` 等候选讨论）
- 在 [root-layer-map.md §0](root-layer-map.md) 已确立"事 ≈ Cell256 transition"的读法

**备选**:
- `件` — *理由*：现代"事件"中的"件"；*但*偏量词
- `故` — *理由*：古义"故事 / 缘故"；*但*偏因果不偏发生
- `因` — *理由*：因果义；*但*偏因不偏果（注：v3 `因` 已 register 为 R₇ Cell128 layer-character 候选，详 R₇ 节）
- `行` — *理由*：行为义；*但*已是 CoreAtom
- `作` — *理由*：作为义；*但*偏 verb
- `成` — *理由*：完成义；*但*已是 CoreAtom

**事 是否应 register 为 CoreAtom？**:

观察：`事` 在系统里多次作为 conceptual anchor 出现（本体读法、Cell transition、内容线下游），但目前未 register。建议在下一轮 CoreAtom roster 评审时考虑提升——尤其因为 [Cell256](../../formal/SSBX/Foundation/Bagua/Cell256.lean) 的 V₄ Shi transition 已 theorem-backed，`事` 可作为它的 surface alias。这是**待办项**（详 §I）。

## G. 缘：不属任何已 register 层

| 项 | 值 |
|---|---|
| 状态 | **未 register**——既不是 CoreAtom、也不是 AtomName、也不是 R-line / 内容线的形式构造子 |
| 在哪里出现 | 仅作"解释名"出现于 [root-layer-map.md §4](root-layer-map.md)、[Kernel.lean](../../formal/SSBX/Foundation) 的注释、佛学 / 易学讨论 |
| 候选语义 | "被识之差之间的相接 / 相依" / relation edge label / coupling |

**为什么 `缘` 当前不应 register？**:

1. 它的语义与 `間 / 际` 高度重叠——但比二者多了"因缘 / 缘起"的佛学色彩
2. 没有明确的 Lean 构造子需要它作 surface
3. 如果 register，需要先决定它是：
   - 一个新的 `CoreAtom`（与 物/動/間 平级）？
   - 一个新的 `JianAspect`（在三显之列）？
   - 一个 `DirectEdge` / relation label（在 DAG 上的边读法）？
   - 还是只在某种 effect / event reading 下用？

**未来如果要 register**:
- 最可能的位置是 **DAG relation label**——`缘` 表示 monad DAG 中"非父子"但"相接"的边类型
- 次可能是新增 `CoreAtom`，与 `因 / 果 / 缘` 一组佛学因果范畴（注：v3 之 `因` / `果` 已 register 为 R₇ / R₈ layer-character 候选；`缘` 仍解释名）
- 现在保持"解释名"是稳妥选择

**备选未来字**:
- `因` — 因果对的"因"（v3: R₇ Cell128 layer-character 候选）
- `连` — 连接义
- `系` — 联系义（但与"系辞"撞）
- `接` — 接触义
- `依` — 相依义（"依他起"佛学读法）

## H. 名册线 (M-line) 速览

完整 M-line 字根映射不在本表范围内（本表聚焦生成线 + 内容线 + 本体读法），但放一个速览表方便交叉参考：

| M 层 | Lean | 字根状态 | 字数 |
|---|---|---|---|
| M0 一元 | `MonadNode.root` | 单字 `一 / 元`，双字 `一元`（与 R₀ 共用）| 1 |
| M1 Face | `MonadNode.face` | 12 个面单字：文 / 物 / 生 / 理 / 心 / 人 / 模 / 审校 / 价值 / 证明 / 注意 / 真理 | 12（部分双字）|
| M2 CoreAtom | `MonadNode.core` | 44 个 CoreAtom 单字：一 / 元 / 之 / 法 / 行 / 成 / 序 / 物 / 场 / 形 / 动 / 变 / 生 / 续 / 开 / 闭 / 审 / 校 / 证 / 真 / 正 / 邪 / 夺 / 共 / 仁 / 道 / 模 / 度 / 期 / 算 / 理 / 心 / 聚 / 焦 / 意 / 识 / 注 / 人 / 做 / 齐 / 控 / 天 / 子 | 44 |
| M3 AtomName | `MonadNode.atom` | 333 个登记字（详 [Roster.lean](../../formal/SSBX/Foundation/Core/Roster.lean)）| 333 |
| M4 FormalNode | `MonadNode.formal` | 标识符（不一定是字）| ~134 |

**注意**：M2 CoreAtom 列表中 `物 / 动 / 变 / 场 / 际 / 开 / 闭 / 行 / 成 / 序 / 度 / 法` 等许多字都同时在内容线 / 生成线出现——这是设计上故意的"字根复用"，不是 bug。但**必须 disambiguate**：CoreAtom 是 monad DAG 上的节点位（M2 层身份），R-line 上的同字是该字的 operator/element 角色。两者是两个不同的 type。

## I. 内容线 + 本体读法 待办

下面这些是本节梳理出来的、属内容线 / 本体读法的工作未项：

- [ ] `事` 是否提升为 [CoreAtom](../../formal/SSBX/Foundation/Core/MonadRoot.lean)？理由：Cell256 V₄ Shi transition 已 theorem-backed，`事` 可作 surface anchor
- [ ] `缘` 的形式位置裁决：DAG relation label vs 新 CoreAtom vs 新 JianAspect？需要先决定 relation-label 系统的形状（独立任务）
- [ ] `差` / `识` 是否提升为 CoreAtom？目前作 conceptual anchor 用，但本体读法四阶段都是核心读法
- [ ] `動` / `动` 在内容线 vs R₃ 算子的 disambiguation 规则需要在 [WenSurface](../../formal/SSBX/Foundation/Wen) 写明：context-prefix（如 `内容/动`、`R₃/动`）或 type-resolver 自动判断
- [ ] 三显 `位 / 場 / 際` 与 R₆ 5 爻位 `位` / R₃ 八卦"場" / R₆ flip3 alias `际` 的多层共字 disambiguation
- [ ] 三征 `幾 / 勢 / 機` 在文档 / surface 的繁简选择（建议默认简体 `几 / 势 / 机`，繁体保留作正式 context alias）
- [ ] R₅ (五爻) layer-character default 敲定 (currently provisional, §16): `五` vs `接` vs `漸`
- [ ] R₇ / R₈ layer-character default 敲定 (currently provisional, §16): `因` / `印`, `果` / `投` / `道`

---

# 跨层贯通

## 跨层 cuo 对待全表

| 层 | cuo 关系 | 字读对待 | 对待感 |
|---|---|---|---|
| R₁ | 阳 ↔ 阴 | **实 ↔ 虚** | bit 二端 |
| R₂ | (阳阳)↔(阴阴) | **夏 ↔ 冬** | 极阳之时 ↔ 极阴之时 |
| R₂ | (阳阴)↔(阴阳) | **秋 ↔ 春** | 阳消阴长 ↔ 阴消阳长 |
| R₃ | 乾 ↔ 坤 | **健 ↔ 顺** | 刚柔 |
| R₃ | 兑 ↔ 艮 | **悦 ↔ 止** | 释停 |
| R₃ | 离 ↔ 坎 | **显 ↔ 险** | 明陷 |
| R₃ | 震 ↔ 巽 | **起 ↔ 入** | 升降 / 出入 |
| R₆ | flip1 ↔ flip4 | **改 ↔ 临** | 内之始 ↔ 外之始 |
| R₆ | flip2 ↔ flip5 | **化 ↔ 主** | 地中 ↔ 君位 |
| R₆ | flip3 ↔ flip6 | **变 ↔ 极** | 内之极 ↔ 外之极 |
| R₇ | 印（toggle 因 bit） | **印 ↔ id** | 有因 ↔ 无因 (involution) |
| R₈ | 投（toggle 果 bit） | **投 ↔ id** | 有果 ↔ 无果 (involution) |
| R₈ Shi V₄ | 道 ↔ 今 (σ_PT), 已 ↔ 未 (σ_T·σ_P) | **道 ↔ 今**, **已 ↔ 未** | V₄ Klein opposites (PT-symmetry) |

## 跨层概念呼应（不撞但相关的字）

| R₂ 相 | R₃ 德 | 概念对应 |
|---|---|---|
| 夏 | 健（乾） | 极阳之相 ↔ 极阳之德 |
| 冬 | 顺（坤） | 极阴之相 ↔ 极阴之德 |
| 春 | 起（震） | 少阳萌发 ↔ 震起萌动 |
| 秋 | 止（艮） | 少阴肃杀 ↔ 艮止收敛 |

| R₁ 端 | R₃ 德 | 概念关系 |
|---|---|---|
| 实（阳） | 健（乾） | 实是 bit 状态，健是状态形成的德性 |
| 虚（阴） | 顺（坤） | 虚是 bit 状态，顺是状态形成的德性 |

| R₇ bit / R₈ bit / R₈ Shi | 角色 | 现象学对应 |
|---|---|---|
| 因 bit (R₇, 位置 7) | past-trace | Husserl retention |
| 果 bit (R₈, 位置 8) | future-projection | Husserl protention |
| 道 (R₈ origin, V₄ identity) | 永真 cell / no-op | "无可识之差" (absolute ground in R₈) |
| 已 / 今 / 未 (V₄ non-identity) | past / present / future | three modes of temporal apperception |

## 字符复用表（同字跨层）

| 字 | 出现位置 | disambiguation 规则 |
|---|---|---|
| `恒` | R₀ identity / 32 卦名 | context 区分（R₀ context vs R₆ 卦名 context）|
| `复` | R₀→R₃ guiyi / 24 卦名 | 同上 |
| `离` | R₃ trigram / 30 卦名 | R₃ vs R₆ type 区分 |
| `震` | R₃ trigram / 51 卦名 | 同上 |
| `艮` | R₃ trigram / 52 卦名 | 同上 |
| `巽` | R₃ trigram / 57 卦名 | 同上 |
| `兑` | R₃ trigram / 58 卦名 | 同上 |
| `坎` | R₃ trigram / 29 卦名 | 同上 |
| `坤` | R₃ trigram / 2 卦名 | 同上 |
| `乾` | R₃ trigram / 1 卦名 | 同上 |
| `显` | R₃ 离 mode / Sheng.toTrigram | 同方向，弱双用 |
| `止` | R₃ 艮 mode / identity alias | 同方向，弱双用 |
| `入` | R₃ 巽 mode / 气机宽义 | mode context 内不撞 |
| `改 / 化 / 变` | R₃ dong/hua/bian / R₆ flip1/2/3 | R₃ vs R₆ type 区分 |
| `错 / 综 / 互` | R₃ / R₆ / Cell / R₈ Shi-side 算子 | type 区分 + Cell 加 `格` 后缀 + R₈ Shi-side disambiguate |
| `道 / 已 / 今 / 未` | R₈ Shi V₄ Klein / 自然语言 | context；道 = V₄ identity + 五重身份 |
| `主` | R₆ flip5 / 主体宽义 | mode context |
| `临` | R₆ flip4 / 19 临卦 | R₆ 算子 vs 卦名 |
| `极` | R₆ flip6 / 太极 / R₀ alias 候选 | flip6 是动作、太极是元素；R₀ alias 候选 `极` provisional |
| `静` | L0 .nop / 现代静止 | L0 context |
| `周` | R₀↔R₃ grandCycle / 周期 | context |
| `因 / 印` | R₇ Cell128 (provisional, §16) / 自然语言 | R₇ provisional layer-character + state/operator pair |
| `果 / 投` | R₈ Cell256 (provisional, §16) / 自然语言 | R₈ provisional layer-character + state/operator pair |
| `道` | R₈ Shi 之 origin / V₄ identity / no-op / 永真 cell / CoreAtom | **五重身份**, R₈ 之 ontological 闭合 |
| `面` | R₄ Mian / 多个 face context / 自然语言 | R₄ canonical layer-character (Ben×Zheng=16) |
| `物` | 内容线 三本 / M2 CoreAtom | 同字双登记，不冲突（三本 = 类型层身份，CoreAtom = DAG 节点） |
| `動 / 动` | 内容线 三本 / R₃ dong / M2 CoreAtom | **三层共字**：内容/算子/DAG 节点；R₃ default 用 `改` 避免裸字直落坐标 |
| `間 / 间` | 内容线 三本 / 本体读法第三阶段 | 同方向，**有意双登记** |
| `事` | 本体读法第四阶段 / R₈ Cell256 V₄ Shi transition / 自然语言 | conceptual anchor，未 register 为 CoreAtom |
| `位` | 内容线 三显 / R₆ 5 爻位 alias / 自然语言 | 5 爻位 alias 不作 default；三显 default 仍取 `位` |
| `場 / 场` | 内容线 三显 / M2 CoreAtom | 同 `物` 的双登记关系 |
| `際 / 际` | 内容线 三显 / R₆ flip3 内极 alias | flip3 default 是 `变`，alias 不冲突 |
| `幾 / 几` | 内容线 三征 / 自然语言"几" | context 区分 |
| `勢 / 势` | 内容线 三征 / 自然语言"势" | context 区分 |
| `機 / 机` | 内容线 三征 / 自然语言"机" | context 区分 |
| `差` | 本体读法第一阶段 / R₁ yao alias / 自然语言 | "差异之两端"读法在 R₁ / 本体读法都通；同方向 |
| `识` | 本体读法第二阶段 / 某些 face context | conceptual stage，未 register |
| `缘` | 仅作解释名 / 未登记 | 不属任何已形式化层 |

## 现代汉字 vs 古字 vs 异体

我们的 default 都倾向**现代汉字**，古字和异体只作 alias：

| default（现代） | 古字 alias | 繁体 alias |
|---|---|---|
| 悦 | 说（古"悦"通"说"）| — |
| 顺 | — | — |
| 错 | — | 錯 |
| 综 | — | 綜 |
| 静 | — | 靜 |
| 已 | 既（古义"已"）| — |
| 今 | 现 / 见（"现"通"见"）| — |

## 双字 vs 单字（哪些层只能用双字）

| 层 / 算子 | 推荐 default | 是双字的原因 |
|---|---|---|
| R₀ 元素 canonical | `太极` / `一元` | 单字过载严重 |
| R₂ 元素 canonical | `太阳/少阴/少阳/老阴` | 单字 `太/少/阳/阴` 字根都已用 |
| R₃→R₂ 略上/略中/略下 | `略上` / `略中` / `略下` | 单字 `略` 不足以指明哪一爻 |
| `cuoZong` 错综 | `错综` | 单字 `交` 已被 Z-4 占用 |
| `chong` 重卦 alias | `重卦` | 单字 `重` 过载 |
| Cell-级算子 | `错格` 等 | 加 `格` 后缀 disambiguate cell vs hex |
| R₅ 五爻 | `五爻` (provisional, §16) | 单字 `五` 太宽 (数字) |
| R₇ / R₈ "因卦/果卦" 双字 | `因卦` / `果卦` (provisional, §16) | 单字 `因` / `果` 字根过载 (因果论 / 数学) |

# 实施顺序（按 candidates §推荐 promotion 顺序 + 本表新决定）

按以下 5 阶段 promote。每阶段在 [WenSurface](../../formal/SSBX/Foundation/Wen) 添加 executable alias：

## 阶段 1：R₃ 八卦 mode 字 ⭐ 含本表新决定
```
健 / 悦 / 显 / 起 / 入 / 险 / 止 / 顺  (R₃ mode)
恒 / 改 / 化 / 变 / 错 / 综 / 互 / 错综  (R₃/R₆ 横向，已 promote)
```

## 阶段 2：R₆ 单爻 + R₈ Cell256 算子 ⭐ 含 临 / 主 新决定
```
临 / 主 / 极  (R₆ flip4/5/6 outer)
错格 / 综格 / 互格 / 改格 / 化格 / 变格 / 临格 / 主格 / 极格  (R₈ Cell-级)
```

## 阶段 3：R₈ V₄ Shi + setShi
```
道 / 已 / 今 / 未  (R₈ Shi V₄ Klein)
错 / 综 / 错综  (Shi-side V₄ involutions, disambiguate from hex-side)
置  (setShi)
迁 / 溯 (legacy surface alias, retained for backward-compat; underlying = V₄ involution)
```

## 阶段 4：R₇ / R₈ layer-character (provisional, §16)
```
因 / 印  (R₇ Cell128 state + operator, provisional)
果 / 投  (R₈ Cell256 state + operator, provisional)
道  (R₈ origin, V₄ identity, 五重身份, provisional)
```

## 阶段 5：纵向 / 派生 / R₀-R₂ element + R₄/R₅ provisional
```
略上 / 略中 / 略下 / 约 / 空 / 复 / 判 / 析 / 展 / 乘 / 生 / 显 / 编 / 周  (纵向)
延 / 摄 / 含 / 忘 / 续 / 成  (R₄↔R₅↔R₆↔R₇↔R₈ 纵向, provisional)
达 / 径 / 群 / 隙 / 度  (派生 / 诊断)
实 / 虚  (R₁ 义理读，新)
夏 / 秋 / 春 / 冬  (R₂ 单字, 新)
极 / 始 / 無  (R₀ 单字 alias，新，provisional)
面  (R₄ canonical)
五 / 接 / 漸  (R₅ provisional, §16)
```

## 阶段 6：理论范式 alias（不进 default resolver）

详 candidates §"理论范式后备字库"——15 个范式（形式代数 / 象数易 / 爻辞 / 梅花 / 先天图式 / 后天图式 / 纳甲 / 八宅 / 奇门 / 儒家义理 / 道家生成 / 佛学 / 中医 / 计算机 VM）的 alias 字，作为文档候选保留。

# 已知风险与缓解

## 风险 1：`入 / 止 / 显` 的弱双用（R₃）

| 字 | 双用对方 | 风险 | 缓解 |
|---|---|---|---|
| `显`（离 mode） | `Sheng.toTrigram` default | manifest 方向一致，无冲突 | 表脚注一行 |
| `止`（艮 mode） | identity alias 集后备 | identity default 是 `恒` 不是 `止`，弱双用 | 表脚注一行 |
| `入`（巽 mode） | 气机宽义 alias | mode 外需 disambiguate | 表脚注一行 |

**fallback**：如果 `入 / 止` 双用观察后觉得太重，可切换到混合方案 `健 / 悦 / 显 / 起 / 申 / 险 / 居 / 顺`（把 入/止 退为 alias，default 用 candidates 工作稿的 申/居）。仅需更新本表 R₃ 一处。

## 风险 2：`临 / 主` 是新决定（R₆）

flip4/5 candidates 标"待定"，本表新定 `临 / 主`。理由充分（19 临卦 / 五爻君位）但缺少长期使用观察。

**缓解**：先在文档层 promote，过 1-2 个 release 后再考虑 promote 为 surface alias。如发现使用中歧义，可切到 `近 / 君`（更传统）或 `四变 / 五变`（更技术）。

## 风险 3：v1 `迁 / 溯` 已 deprecated 为 V₄ involution surface alias（R₈）

v1 之 `迁 / 溯` (Z/3 shi cycle next/prev) 在 v3 / V₄ 下 collapse 为 V₄ involution `Shi.cuo`。`迁 / 溯` 保留作 surface alias 仅为 backward-compat；underlying semantics 是 V₄ self-inverse。

**缓解**：新代码请直接用 `错 / 综 / 错综 (Shi-side)` 或 V₄ 表达；`迁 / 溯` 文档明确标 (deprecated, V₄-collapsed)。

## 风险 4：R₅ / R₇ / R₈ layer-character defaults 是 provisional (§16)

R₅ (`五` / `接` / `漸`), R₇ (`因` / `印`), R₈ (`果` / `投` / `道`) 之 layer-character defaults 在 v3 仍为 provisional。`道` 是 V₄ identity + 五重身份, 是 ontological 上 binding 之 anchor (R₈ origin choice)，但作为 layer-character literal default 仍 subject to refinement。

**缓解**：长期使用观察决定。详 yi-calculus-theorem.md §16 关于 layer-character defaults refinement timeline。

## 风险 4：跨层卦名共字（30 离 / 32 恒 / 50 鼎 等）

64 卦中 8 个纯卦在 R₃ / R₆ 共字，是易学本来设计；其余如 24 复 / 32 恒 / 50 鼎 等的撞车需 type / context resolver。

**缓解**：candidates §"当前代码落地口径" 已记录 50 卦 default 改为 `器`（`鼎` 仍 alias）；其余靠 type 区分。

# 与现有文件的关系

| 文件 | 关系 |
|---|---|
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) | **父档**：v3 strict-uniform R₀..R₈ 形式定本。本表所依据之层级 enumeration / cardinalities / V₄ Shi / Cell256 全在 yi-RO-hierarchy。 |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) | Theorems A–K (含 Lean 列, layer-character defaults refinement timeline 在 §16)。 |
| [root-layer-map.md](root-layer-map.md) | 本表是 root-layer-map.md 的"字根定本"补充——前者讲"层级和算子的形式结构"，本表讲"每层每算子用什么字"。两者交叉引用。 |
| [bagua-operator-name-candidates.md](../40_reference_参考/bagua-operator-name-candidates.md) | 本表的前身工作稿。本表完成后，candidates 文件可降级为 archive pointer（保留是为避免外部回链断裂）。 |
| [LayerCharacterMap.lean](../../formal/SSBX/Text/LayerCharacterMap.lean) | **代码 ground truth**：解释器查表函数 + 往返定理（已通过 `lake build`）；R₁ essence / R₂ season / R₃ virtue+literal / R₆ flipPosition / R₈ ShiTransition (V₄-collapsed) / L0 modernAlias 之 binding 表。 |
| [RHierarchy.lean](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) | **R-索引 umbrella**：R₀_Taiji..R₈_GuoHex 全部 alias shim + LiftProject + Atomic/V4Outer operators。 |
| [R0_Taiji.lean](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) ~ [R8_GuoHex.lean](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) | R-索引层 alias shim 9 件（R₀..R₈）。 |
| [LiftProject.lean](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | Lift / Project pair 之 ground truth（fenToYi / heToTaiji / fenToSiXiang / heToYi / fenToTrigram / heShang / heZhong / heXia / liftToMian / liftToWuyao / liftToHexagram / liftToCell128 / liftToCell256 / forgetYin / projectMianToTrigram 等）。 |
| [Operators/Atomic.lean](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) | 8 atomic XOR generators (dongInner/huaInner/bianInner/dongOuter/huaOuter/bianOuter/印yin/投tou)。 |
| [Operators/V4Outer.lean](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) | V₄ outer 算子 (cuo / zong / hu / 错综) 之 hex-side + Shi-side propagation。 |
| [OXNotation.lean](../../formal/SSBX/Foundation/Notation/OXNotation.lean) | O-X 记号系统 (o = yang, x = yin)。 |
| [BaguaAlgebra.lean](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | 本表 R₃ / R₆ 横向 / 纵向算子的 ground truth。 |
| [BenZheng.lean](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | R₄ Mian = Ben × Zheng = 16 之 ground truth（4 本 × 4 征 = 16 命）。 |
| [Cell128.lean](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | R₇ 因卦 (Cell128 = Hexagram × YinBit) + 印 yin XOR mask 之 ground truth。 |
| [Cell256.lean](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | R₈ 果卦 (Cell256 = Hexagram × Shi V₄ Klein) + 投 tou + V₄ Shi (道/已/今/未) 之 ground truth。 |
| [Cell256Stratify.lean](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | Cell256 之分层 (stratification)。 |
| [Yi.lean](../../formal/SSBX/Foundation/Yi/Yi.lean) | 本表 R₁ / R₃ trigram literal 的 ground truth。 |
| [Yuan.lean](../../formal/SSBX/Foundation/Core/Yuan.lean) | 本表 R₀ / R₁ / Yao.neg 的 ground truth。 |
| [MonadRoot.lean](../../formal/SSBX/Foundation/Core/MonadRoot.lean) | 本表的 CoreAtom 撞车清单的 ground truth。 |
| [JianOntology.lean](../../formal/SSBX/Foundation/Jian/JianOntology.lean) | 物 / 動 / 間 三本的 ground truth（不属本表 R 系列，是内容线）。 |
| [OperatorSignatures.lean](../../formal/SSBX/Text/OperatorSignatures.lean) | 14 seed signatures 的 ground truth（与 CoreAtom 不同概念，注意区分）。 |

# 后续待办

- [ ] 把本表内容并入 [root-layer-map.md](root-layer-map.md)，按 [docs-next-10-formal-root-layer-map-md plan](../../.claude/plans/docs-next-10-formal-root-layer-map-md-c-ticklish-sun.md) 执行
- [ ] [bagua-operator-name-candidates.md](../40_reference_参考/bagua-operator-name-candidates.md) 降级为 archive pointer
- [ ] R₃ mode 字 `健 / 悦 / 显 / 起 / 入 / 险 / 止 / 顺` 在 [OperatorAnchors.lean](../../formal/SSBX/Text/OperatorAnchors.lean) 注册为 surface alias（独立任务）
- [ ] R₆ `临 / 主` 在 OperatorAnchors 注册（独立任务）
- [ ] R₈ V₄ Shi `道 / 已 / 今 / 未` + Shi-side 错/综/错综 在 OperatorAnchors 注册（独立任务）
- [ ] R₁ 义理读 `实 / 虚` 是否需要进 OperatorAnchors（讨论：alias 是否需要在 surface 层 register）
- [ ] R₂ 四时字 `春 / 夏 / 秋 / 冬` 同上
- [ ] R₅ / R₇ / R₈ layer-character provisional (`五`/`接`/`漸`, `因`/`印`, `果`/`投`/`道`) 长期使用观察后敲定 default — refinement timeline 详 §16
- [ ] 6-8 个月后审视 `入 / 止` 双用情况，评估是否切换 fallback
