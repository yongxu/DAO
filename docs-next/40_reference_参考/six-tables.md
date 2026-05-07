# 六表参考

六表位于根目录 `六表_实虚史真/`，是实、虚、史、真和 192 格的人工表格入口。docs-next 只提供读法和指针。

## 表格入口

| 表 | 路径 | 读法 |
|---|---|---|
| 表一 | `六表_实虚史真/表一_六征本表.md` | 六征基础表 |
| 表二 | `六表_实虚史真/表二_史维三态.md` | 史维三态 |
| 表三 | `六表_实虚史真/表三_实虚modal三态.md` | 实虚 modal 三态 |
| 表四 | `六表_实虚史真/表四_真假认识三态.md` | 真假认识三态 |
| 表五 | `六表_实虚史真/表五_三轴27格.md` | 三轴 27 格 |
| 表六 | `六表_实虚史真/表六_192格全表.md` | 64 卦乘史三态的 192 格 |

## 与形式层的关系

六表不是 Lean 生成文件。需要形式核对时，优先查：

- `../_generated/lean-index.md` 中的 `Foundation/Bagua` cluster。
- `formal/SSBX/Foundation/Bagua/Cell192.lean`。
- `formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`。
- `formal/SSBX/notes/zhouyi-position-operator-report.md`。
- `../_generated/diagram-index.md` 中 Position Operator Graph。

## 读法边界

- 表格可作为义理分类和审计导航。
- 表格本身不等于 Lean theorem。
- 192 格的覆盖口径要区分表格覆盖、算子空间覆盖和证明覆盖。
- 涉及不完备、可判定、对角化时，应回到 BaguaTuring 和 GodelLi 相关模块。

## 更新规则

若六表变动，应重新生成 docs-next 索引并检查：

- `../_generated/markdown-index.md` 是否收录新路径。
- `../_generated/crossrefs.md` 是否出现新的 Lean path mention 或 symbol hit。
- `../20_theory_义理/core-framework.md` 和 `../20_theory_义理/formal-and-proof.md` 是否需要调整摘要。
