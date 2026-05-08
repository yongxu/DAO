# 八卦算子命名候选与范式审阅

> Review table only. This page does not change parser, resolver, evaluator, or Lean theorem names.
> Primary sources in this repository: `Foundation/Yi/Yi.lean`, `Foundation/Bagua/BaguaAlgebra.lean`, `Foundation/Bagua/BaguaWenSpec.lean`, `Foundation/Wen/WenDef.lean`, `Foundation/Wen/WenSurface/Semantics.lean`.

目的：把八卦层现有算子、候选名字、不同范式下的读法、以及当前命名风险放在一张可审阅表里。这里的“八卦算子”分三层：

- `T3`：三爻八卦 `Trigram` 上的代数算子。
- `T6`：六爻卦 `Hexagram` 与 `Cell192` 上的提升算子。
- `L0 baguaWen`：受控 VM 指令 token；它们冻结，不应被 surface 命名随意重用。

## 当前结论

- `错 / 綜 / 综 / 互 / 重 / 生生 / 归一` 这些名字基本稳，可以继续保留。
- `彖` 类似前表：传统名应做 default，解释性名做 alias。八卦算子里对应原则是：`错/综/互` 做 default，`反/转/藏/显` 做语义别名。
- `动` 不适合直接做三爻 flip 的公开 default。它在 catalogue 里已有多处动义，且“动爻”在占筮语境可指任一爻，不天然等于 `y1`。
- `改 / 化 / 变` 目前可执行映射到 `y1/y2/y3` 翻转，但位置不透明。更好的公开 default 是组合名：`初变 / 中变 / 上变`。
- `反` 当前可作为 object-level `错` 的 alias，但不宜做 default；它同时可读成否定、取逆、反向、反身。
- `推 / 取 / 易` 在 L0 是 VM 栈指令，在 WenSurface/catalogue 又有别的读法。必须保持 instruction context 限定。
- `合 / 分` 是好字，但太泛。八卦纵向投影/扩维应使用限定名，如 `合上 / 合中 / 合下`、`分爻`、`重卦`。

## 八卦值名参考

这些是值名，不是算子。它们适合作为 literal / alias 表，不应和 transform 算子混在同一 resolver 层。

| 卦 | bits 下→上 | 自然象 | 家族象 | 常见先天方位 | 常见后天方位 | 常见五行 | 适合 default | 主要别名 | 命名风险 |
|---|---|---|---|---|---|---|---|---|---|
| 乾 | 111 | 天 | 父 | 南 | 西北 | 金 | `乾` | 天 / 健 / 父 | `天`太泛，保留为 alias。 |
| 兑 | 110 | 泽 | 少女 | 东南 | 西 | 金 | `兑` | 泽 / 悦 / 说 | `悦/说`易撞情态、言说。 |
| 离 | 101 | 火 | 中女 | 东 | 南 | 火 | `离` | 火 / 丽 / 明 | `火`自然但太物象；`明`已有 operator。 |
| 震 | 100 | 雷 | 长男 | 东北 | 东 | 木 | `震` | 雷 / 动 / 起 | `动`冲突多，不宜 default。 |
| 巽 | 011 | 风 | 长女 | 西南 | 东南 | 木 | `巽` | 风 / 入 / 顺 | `入/顺`已有运动/医学读法。 |
| 坎 | 010 | 水 | 中男 | 西 | 北 | 水 | `坎` | 水 / 险 / 陷 | `水`可读物象，`险`偏义理判断。 |
| 艮 | 001 | 山 | 少男 | 西北 | 东北 | 土 | `艮` | 山 / 止 | `止`已有 stop/operator 读法。 |
| 坤 | 000 | 地 | 母 | 北 | 西南 | 土 | `坤` | 地 / 顺 / 母 | `地/顺`太泛，保留 alias。 |

## T3 核心算子候选

| exact object | Lean / current | theorem-backed meaning | 推荐 default | 保留 alias | 象数 / 占筮读法 | 形式读法 | 当前问题 |
|---|---|---|---|---|---|---|---|
| identity | implicit / `不动` in L0 | no state change | `不动` | 恒 / 守 / identity | 静守本卦 | identity endomap | `不动`只在 L0 token 中冻结；数学文档可写`恒`。 |
| y1 flip | `dong`, WenDef `flip1`, surface `改` | flip bottom yao | `初变` | 改 / 动初 / 翻初 | 初爻动、初爻变 | generator e1 of `(Z/2)^3` | `动`泛化过强；`改`不说明位置。 |
| y2 flip | `hua`, WenDef `flip2`, surface `化` | flip middle yao | `中变` | 化 / 动中 / 翻中 | 中爻动、中爻变 | generator e2 | `化`很自然，但作为单字不说明是中爻。 |
| y3 flip | `bian`, WenDef `flip3`, surface `变` | flip top yao | `上变` | 变 / 动上 / 翻上 | 上爻动、上爻变 | generator e3 | `变`可指整体变卦，单字 default 太宽。 |
| full complement | `Trigram.cuo` | flip all three yao | `错` | 錯 / 反 / 旁通 | 错卦、阴阳全反 | bitwise complement | 当前命名稳；`反`只作 alias。 |
| order reversal | `Trigram.zong` | reverse y1/y2/y3 | `综` | 綜 / 覆 / 倒 / 转 | 综卦、覆卦 | order reversal involution | 当前命名稳；`转`不宜做 default。 |
| complement then reverse | `cuoZong` | `错 ∘ 综` | `错综` | 錯綜 / 综错 | 错综合看 | Klein four composite | 当前命名稳。 |
| arbitrary transform | `transform a b` | flip differing coordinates | `通变` | 路 / 径 / 至 | 八卦互通 | path in cube graph | 不应暴露为单字；它是派生构造。 |
| path witness | `pathFromTo` | shortest flip path | `变径` | 路 / 程 / 变路 | 由此卦至彼卦 | Hamming path | 可留文档名，不急入 surface。 |

## T3 纵向算子

| exact object | Lean / current | theorem-backed meaning | 推荐 default | 保留 alias | 范式读法 | 当前问题 |
|---|---|---|---|---|---|---|
| drop top yao | `heShang` | `Trigram -> SiXiang`, keep y1,y2 | `合上` | 省上 / 去上 / 取下二 | 八卦合为四象 | `合上`像“关闭”，需要文档注明“去上而合”。 |
| drop middle yao | `heZhong` | keep y1,y3 | `合中` | 省中 / 去中 / 取初上 | 抽去中介 | 单字`合`不足以区分三种投影。 |
| drop bottom yao | `heXia` | keep y2,y3 | `合下` | 省下 / 去下 / 取上二 | 去始留成 | 同上。 |
| SiXiang to Yi | `heToYi` | drop second coordinate | `合仪` | 合一 / 归仪 | 四象归两仪 | `合`必须带目标层。 |
| Yi to Taiji | `heToTaiji` | forget to Unit | `归一` | 归极 / 归太极 | 复归太极 | 当前名稳。 |
| TaiJi to Yi | `fenToYi` | introduce a yao | `分仪` | 生仪 / 分阴阳 | 太极生两仪 | `分`太泛，需带目标层。 |
| Yi to SiXiang | `fenToSiXiang` | add second yao | `分象` | 生象 / 成四象 | 两仪生四象 | 当前无 public surface，可先文档化。 |
| SiXiang to Trigram | `fenToTrigram` | add third yao | `分卦` | 生卦 / 成卦 | 四象生八卦 | `分卦`比单字`分`清楚。 |
| Trigram to Unit | `guiyi` | universal collapse to Unit | `归一` | 归太极 | 万殊归一 | 当前名稳。 |
| full cycle | `grandCycle` | split to trigram then return | `大循环` | 生归 / 周行 | 生生而复归 | 文档名即可，不必进 parser。 |

## T6 / Hexagram 提升算子

| exact object | Lean / current | theorem-backed meaning | 推荐 default | 保留 alias | 当前问题 |
|---|---|---|---|---|---|
| hex complement | `Hexagram.cuo`, WenDef `cuoH`, Cell `cuoC` | flip all six yao | `错` | 錯 / 反 / 错卦 | 稳。Cell 层可写`错格`以避和 Hex 混淆。 |
| hex reversal | `Hexagram.zong`, WenDef `zongH`, Cell `zongC` | reverse all six positions | `综` | 綜 / 覆 / 转 / 综卦 | 稳；`转`只作 alias。 |
| mutual hexagram | `Hexagram.hu`, WenDef `huH`, Cell `huC` | middle-four extraction to 互卦 | `互` | 互卦 / 互体 / 内互 | 稳；注意它不是 binary “互相”。 |
| hex cuo-zong | `Hexagram.cuoZong`, WenDef `cuoZongH` | `错 ∘ 综` | `错综` | 錯綜 / 综错 | 稳。 |
| inner y1 flip | `dongInner`, WenDef `flip1H` | flip hex y1 | `初变` | 改 / 翻初 | 当前 surface `改`可执行但不透明。 |
| inner y2 flip | `huaInner`, WenDef `flip2H` | flip hex y2 | `承变` | 化 / 翻二 | 若沿前表六爻名，y2 是`承`。 |
| inner y3 flip | `bianInner`, WenDef `flip3H` | flip hex y3 | `际变` | 变 / 翻三 | `变`单字应保留 alias。 |
| outer y4 flip | `dongOuter`, Cell `flip4C` | flip hex y4 | `近变` | 翻四 / 外初变 | WenDef Hex 层暂未公开 `flip4H`，Cell 层已有。 |
| outer y5 flip | `huaOuter`, Cell `flip5C` | flip hex y5 | `主变` | 翻五 / 外中变 | 同上。 |
| outer y6 flip | `bianOuter`, Cell `flip6C` | flip hex y6 | `极变` | 翻上 / 外上变 | 同上。 |
| inner-outer combine | `chong`, `Hexagram.oplus` | inner trigram + outer trigram -> Hexagram | `重卦` | 重 / 合卦 / 内外合 | `重`单字可作 alias；default 建议二字。 |

## L0 baguaWen 指令名审阅

L0 已冻结；这里不建议改 token，只说明哪些名字不应在 surface 文义层无上下文复用。

| token | YiInstr | VM meaning | 是否稳 | 备注 |
|---|---|---|---|---|
| `不动` | `nop` | no-op | 稳 | 很适合 instruction context。 |
| `设时` | `setShi` | set `已/今/未` | 稳 | 二字清楚。 |
| `翻爻` | `flipYao` | flip selected one of six yao | 稳 | 比单字`动/变`更好。 |
| `互` | `hu` | mutate current hex by `Hexagram.hu` | 稳 | 与 Hex operator 同名，可由 instruction context 消歧。 |
| `错` | `cuo` | mutate current hex by `Hexagram.cuo` | 稳 | 同上。 |
| `综` | `zong` | mutate current hex by `Hexagram.zong` | 稳 | 同上。 |
| `比爻` | `branchYaoEq` | branch on yao equality | 稳 | 二字避免和 catalogue `比` 冲突。 |
| `比时` | `branchShiEq` | branch on time equality | 稳 | 同上。 |
| `跳` | `jump` | set pc | 稳 | instruction context 明确。 |
| `推` | `push` | push current cell to history | 有风险但冻结 | Surface `推` 已是 Hex increment；必须靠 L0 syntax/context 消歧。 |
| `取` | `pop` | pop history to current | 有风险但冻结 | 也可读 projection/extraction；保留 L0。 |
| `终` | `halt` | halt | 稳 | 与 endpoint `终` 有语义重叠，可由 instruction context 消歧。 |
| `易` | `swap` | swap current and history head | 有风险但冻结 | `易`作为 general transform 太大；VM 里保持冻结。 |

## 不同范式下的命名

| 范式 | 关注对象 | 自然名字 | 不宜做 default 的名字 | 建议 |
|---|---|---|---|---|
| 形式代数 | finite bit-vector / group action | flip, complement, reverse, projection, product | 动 / 化 / 变 单字 | 用 `初变/中变/上变`、`错/综`、`合上/分卦`。 |
| 象数易 | 卦象、动爻、错综互 | 动爻、变爻、错卦、综卦、互卦、重卦 | 仅用`动`指某一固定坐标 | `错/综/互/重卦`直接保留；爻变用组合名。 |
| 占筮 / 梅花 | 本卦、互卦、变卦、体用 | 动、变、互、体、用 | 把`变`单字固定为上爻 flip | `变`做 alias，default 用位置限定。 |
| 儒家义理 | 改过、化成、中正、复归 | 改、化、复、正、中 | 以道德义替代 bit semantics | 可作解释 alias，不做 theorem-backed default。 |
| 道家生成 | 生、化、反、复、归 | 生生、反、复、归一 | `反`覆盖`错/综/逆/否定` | `反`只作 alias；exact 用`错`。 |
| 术数 / 风水 | 后天方位、五行、九宫 | 震东、离南、坎北、兑西等 | 用方位名替代卦名 | 方位只在 paradigm column 出现，不进 core default。 |
| 中医 / 气机 | 升降、开阖枢、阴阳五行 | 升、降、开、阖、枢 | 把医学气机当八卦 core transform | 作为 domain mapping，不进入八卦算子 default。 |
| 计算机 / VM | stack, branch, jump, halt | 推、取、易、比爻、跳、终 | 让 VM token 污染 surface evaluator | L0 保持冻结，surface 另设类型化读法。 |

## 当前命名问题清单

| 名 | 当前出现 | 问题 | 建议 |
|---|---|---|---|
| `动 / 動` | catalogue 多处，BaguaAlgebra internal `dong` 语义相近 | 可指任一动爻，不应等于 y1 flip | 不做 default；保留 `动初/动中/动上` alias。 |
| `化` | T-1 exact y2 flip；也有儒/荀子等化义 | 单字不说明位置 | 对外 default 用`中变`，`化`作 alias。 |
| `变 / 變` | T-2 exact y3 flip；也可指整体变卦 | 单字过宽 | 对外 default 用`上变`，`变`作 alias。 |
| `改` | T-5 exact y1 flip | 表“修正”而不是坐标 | 保留 alias；公开 default 用`初变`。 |
| `反` | T-6 as cuo、N-6、Z-31、CHU-7 等 | 否定 / 取逆 / 反向 / 错卦混杂 | 不做 default；exact object transform 用`错`。 |
| `转 / 轉` | T-9 exact zong-like；也可泛指 rotation | 与`综`关系需说明 | default 用`综`，`转`作 alias。 |
| `合` | I-7、G-8、vertical projection | 泛义过大 | 用限定名：`合上/合中/合下/重卦`。 |
| `分` | I-6、X-5、ZA-4、SUN-12 等 | 泛义过大 | 用限定名：`分仪/分象/分卦`。 |
| `推` | L0 push、T-10 Hex increment、Z-29 演推 | 强冲突 | L0 instruction context 与 surface evaluator 必须分开。 |
| `取` | L0 pop，常见 projection/extraction | 将来易与 `取爻/取翼` 冲突 | projection 使用二字名，L0 保留。 |
| `易` | L0 swap、T-3 binary exchange、总名“易” | 太大 | 只在明确 instruction/exchange context 用。 |

## 推荐 default 集

### 八卦 T3

```text
不动
初变 / 中变 / 上变
错 / 综 / 错综
合上 / 合中 / 合下
分仪 / 分象 / 分卦
重卦
归一 / 生生 / 大循环
```

### 六爻 T6

```text
初变 / 承变 / 际变 / 近变 / 主变 / 极变
错 / 综 / 互 / 错综
重卦
错格 / 综格 / 互格   （Cell192 context）
```

### L0 VM

```text
不动 / 设时 / 翻爻 / 互 / 错 / 综
比爻 / 比时 / 跳 / 推 / 取 / 终 / 易
```

L0 保持冻结；上面只是说明它们属于 instruction namespace。

## 后续 promotion 检查

1. 若把 `初变/中变/上变` 加入 WenSurface，先决定它们是 `Hex -> Hex` 还是 `Trigram -> Trigram`。当前 evaluator 公开的是 Hex 层。
2. 若补 `近变/主变/极变`，需要给 Hex 层 `flip4H/flip5H/flip6H` 对应 `WenDef.Tm`，或只在 Cell 层 promotion。
3. `反/转/动/化/变/合/分/推/取/易` 必须走 type/context resolver；裸 token 无上下文时应报 ambiguous。
4. `错/综/互/重卦` 是最安全的第一批 public names；它们和当前 theorem-backed denotation 对齐最好。
