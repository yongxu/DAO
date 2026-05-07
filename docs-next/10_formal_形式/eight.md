# Foundation/Eight

`Foundation/Eight` 是八个专题方向的形式中层。它把 Core 的基础结构连接到现代数学、逻辑、统计、行为和心智等主题。

## 模块

当前簇包括：

- `DongLi.lean`：动力。
- `LeiYing.lean`：类与映。
- `LuoJi.lean`：逻辑。
- `ShuSuan.lean`：数与算。
- `TongJi.lean`：统计。
- `WuXiang.lean`：物象。
- `XinZhi.lean`：心智。
- `XingWei.lean`：行为。

完整统计见 [../_generated/lean-index.md](../_generated/lean-index.md)。

## 职责

Eight 层不是旧义理文档的全文形式化；它提供每个专题的形式接口、局部结构和桥接点。它常用于：

- 给主题分区提供统一入口。
- 把术语转为 Lean 对象。
- 给 Modern 层或义理互证提供中间节点。
- 标出哪些地方仍需模型、经验或外部数学库补强。

## 与 Modern 的区别

Eight 更像项目内部的专题骨架；Modern 更像引入现代数学和科学形式的桥接库。若需要概率、测度、范畴、自然演绎、ODE、量子或神经模型，应读 [modern.md](./modern.md)。

## 避免过claims

例如统计模块存在，不等于所有统计结论已实证；心智模块存在，不等于神经科学 claim 已闭合；行为模块存在，不等于行动正邪判定已经验校准。相关 claim 必须回查 [../_generated/claim-index.md](../_generated/claim-index.md) 与 [pending.md](./pending.md)。
