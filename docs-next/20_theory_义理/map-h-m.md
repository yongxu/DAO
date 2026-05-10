# H-M 映射

H-M 是形式化与自省段。它关心八卦代数、全集、192 格、不完备、完备性审计和文道微核。读法要比 A-G 更严格：凡称“证明”，必须能追到 Lean、生成报告或明示的公理边界。

索引入口：[../_generated/lean-index.md](../_generated/lean-index.md)、[../_generated/claim-index.md](../_generated/claim-index.md)、[../_generated/trust-boundary.md](../_generated/trust-boundary.md)、[../_generated/markdown-index.md](../_generated/markdown-index.md)。

## 总表

| 段 | 旧入口 | 本区读法 | 核心检查 |
|---|---|---|---|
| H | `义理/H_证明报告.md` | 八卦算子代数报告 | 是否可追到 `BaguaAlgebra` |
| I | `义理/I_八卦全集.md` | 字、符、爻、算子目录 | 是否只是全集描述，还是有完备性声明 |
| J | `义理/J_理之不完备_哥德尔在192.md` | 192 与不完备解释 | 是否依赖编码、公理、运行边界 |
| K | `义理/K_完备性审计.md` | 元层审计 | 是否区分缺项、越界、重复、未证 |
| L | `义理/L_文道一也_自释与微核.md` | 文言可执行与自释 | 是否混同解释器、自举和真理 claim |
| M | `义理/M_证明报告_256_理之不完备.md` | 不完备形式报告 (v3 重号，原名 M_证明报告_192_理之不完备.md) | 是否追到 `GodelLi` 与信任边界 |

## H：八卦代数证明报告

H 是证明报告，不是源码替代。它的任务是把形式层结论翻译成人类可读的义理语言。当前应把 `Foundation/Bagua` + `Foundation/Hierarchy` 作为主要落点，尤其关注 `BaguaAlgebra`、`CuoInvariance`、`Cell128`、`Cell256`、`Cell256Stratify`、`RHierarchy` 等模块在 [../_generated/lean-index.md](../_generated/lean-index.md) 中的存在状态。(v3 重号：旧 Cell192 已删除，由 Cell256 + V₄ Klein Shi 取代。)

阅读时分三层：

| 层 | 可接受说法 | 不宜说法 |
|---|---|---|
| 构造层 | 已定义八卦、爻位、算子 | 因为传统如此所以成立 |
| 性质层 | 某些不变量或等式被证明 | 全部义理都已证明 |
| 解释层 | 证明可读成互通、错综、归一 | 解释本身等同 Lean 定理 |

## I：八卦全集

I 是目录性文件，价值在于给全体系一个枚举界面。它适合回答“有哪些字、符、爻、算子、层级”，不适合单独回答“这些映射为何完备”。

与 docs-next 的关系：

- 全集清单查 [../_generated/markdown-index.md](../_generated/markdown-index.md) 和 [../_generated/operator-index.md](../_generated/operator-index.md)。
- Lean 模块清单查 [../_generated/lean-index.md](../_generated/lean-index.md)。
- 若涉及名册完备、算子表完备，查 [../_generated/claim-index.md](../_generated/claim-index.md) 中相关 machineChecked claim。

## J：192 与不完备

J 的重点是边界，而不是夸张结论。192 可读作八卦、史维、命题或运行格的扩张空间；不完备则说明某类系统一旦能表达足够强的自指与计算，就不能同时取得所有想要的封闭性。

本区保留三条判断：

| 判断 | 含义 |
|---|---|
| 可表达 | 系统能编码足够多的对象、程序或命题 |
| 可反身 | 系统能谈论自身某些语句或运行 |
| 有边界 | 证明依赖公理、编码、燃料、部分函数或外部元理论 |

具体信任边界以 [../_generated/trust-boundary.md](../_generated/trust-boundary.md) 为准。该索引目前列出 `partial def`、`axiom`、`opaque` 等边界项；义理页不可把这些边界抹平。

## K：完备性审计

K 提供一种维护方法：看体系是否有缺层、重名、错配、越权和未标注假设。它不是证明所有内容完备，而是帮助定位风险。

建议审计清单：

| 项 | 问题 |
|---|---|
| 名称 | 同一词是否跨层混用 |
| 映射 | 义理概念是否有明确形式目标 |
| 证明 | 是定理、计算结果、登记项、还是公理依赖 |
| 边界 | 是否标出 partial、axiom、opaque 或外部假设 |
| 史料 | 是否越过冻结边界重写来源 |

K 与 [bridge-to-lean.md](bridge-to-lean.md) 配合使用：先审计义理命题，再找 Lean 或生成索引落点。

## L：文道一也

L 连接“文”与“道”：文言形式、可执行片段、自释、微核、归一叙述。它最容易出现层级混淆，因此要分开：

| 层 | 内容 | 可验证入口 |
|---|---|---|
| 文本层 | 字、句、文言算子、语法 | operator index、markdown index |
| 执行层 | parser、eval、compile、自解释器 | Lean index 的 `Foundation/Wen` |
| 自释层 | 系统能描述部分自身结构 | Lean 模块与注记 |
| 真理层 | 关于道、真道、绝对 claim | claim index 与公理账本 |

“文道一也”在 docs-next 中应写成桥接命题：某些文本结构可执行，某些执行结构可反身解释，某些 claim 仍依赖账本或公理。

## M：GodelLi 证明报告

M 是 J 的形式化报告面。它应与 [../_generated/lean-index.md](../_generated/lean-index.md) 中 `SSBX.Foundation.Bagua.GodelLi` 对照，并接受 [../_generated/trust-boundary.md](../_generated/trust-boundary.md) 标出的 `kleene_recursion_axiom` 等边界。

阅读 M 时不要只看结论句，要看依赖：

- 编码对象是什么。
- 自指或递归定理通过何种接口给出。
- 哪些部分由 Lean 检查，哪些部分是公理接口。
- 是否把系统内不可判定误读成现实中一切不可知。

## 本段边界

H-M 的共同要求是“证明语气可追踪”。若追不到 Lean、claim index、生成报告或明确公理，仍可作为义理解释保留，但不写成已证结论。
