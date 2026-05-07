# Foundation/Jian

`Foundation/Jian` 处理「间」：关系、间隔、模式、本体与到易层的桥接。它是从对象到关系结构的重要中层。

## 模块职责

- `Jian.lean`：基础 Jian 结构。
- `JianOntology.lean`：间的本体三联架构。
- `JianModeKernel.lean`：模式核。
- `JianMinimality.lean`：最小性与约束。
- `JianSTLC.lean`：与简单类型 lambda 演算相关的形式桥。
- `JianYiBridge.lean`：Jian 与 Yi 的连接。

完整路径和声明统计见 [../_generated/lean-index.md](../_generated/lean-index.md)。

## 读法

Jian 层关注「关系如何被组织」。它不是单纯的注释层，也不是经验层。其 theorem 可用于说明：

- 间结构的定义关系。
- 模式核如何约束对象。
- STLC 桥如何提供形式语法/类型参照。
- 与 Yi 的连接点在哪里。

## 不要过读

Jian 的形式化不自动证明所有哲学文本中的「间」解释都正确。若某说明依赖旧义理文档、历史源流或经验阐释，应回到相应文档与 claim ledger。

## 查证路径

- 读模块：查 [../_generated/lean-index.md](../_generated/lean-index.md) 的 `Foundation/Jian` 簇。
- 读说明：查 `formal/SSBX/notes/JianOntology.md`。
- 读桥接：结合 [yi-bagua.md](./yi-bagua.md) 与 `JianYiBridge.lean`。
