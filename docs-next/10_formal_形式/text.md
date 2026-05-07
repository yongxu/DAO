# Text：字、义位与算子

Text 层把文字资源变成可审计对象。它不替代 Lean theorem，但为 claim、算子和名册提供可追溯账本。

## 主要内容

- `Glyph.lean`：字与字形相关结构。
- `SenseSyntax.lean`：义位语法。
- `OperatorReadings.lean`、`OperatorSignatures.lean`：算子读法与签名。
- `WenyanOperators.lean`：文言算子表。
- `Operator*Semantics.lean`：算子族、cell、instruction、reachability 等语义接口。
- `Completeness.lean`：文字与算子覆盖性的机器检查入口。

完整模块路径见 [../_generated/lean-index.md](../_generated/lean-index.md)。

## 算子索引

算子数量、分组与代码表以 [../_generated/operator-index.md](../_generated/operator-index.md) 为准。人工文档不要复制整张表，只引用索引。

算子表的读法：

- code/group/title/id 是登记事实。
- 完备性 theorem 说明表与形式名册之间的覆盖关系。
- 单个算子的哲学解释仍需回到义理文档或来源文本。
- 算子表齐备不等于所有使用该算子的经验 claim 已证明。

## 文本完备

[../_generated/claim-index.md](../_generated/claim-index.md) 中的 `rosterTextComplete` 与 `wenyanOperatorTableComplete` 标为 machineChecked。它们说明登记/覆盖层面的机器核验已闭合。

这类 theorem 的强度是账本强度：它证明「表与名册的关系」而不是「表中每个义理判断都为真」。

## 与 Wen 的区别

Text 层偏重登记、读法、签名和覆盖；[wen.md](./wen.md) 讨论 `Foundation/Wen` 的微核、文言语法、求值、自释、自举与 quine 路线。

## 边界

文本层常见误读是把「可定位」「被登记」「被覆盖」写成「已由 Lean 证明其义理正确」。正确写法应区分：

- 登记事实：表里有此项。
- 覆盖事实：Lean 已核对表与名册。
- 语义接口：形式上给出解释框架。
- 义理 claim：需看 claim ledger 的状态。
