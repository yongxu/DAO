# Pending 接口

Pending 是形式层故意保留的经验与模型边界。它的存在是为了防止未校准内容混入 machineChecked claim。

## 当前项目口径

pending 项以 [../_generated/registry-index.md](../_generated/registry-index.md) 为准。人工文档只解释读法，不维护最终清单。

常见 pending 类型包括：

- 经验校准。
- 阈值设定。
- 审校数据。
- 开势投影。
- 度期计算。
- 邪续相关接口。

## Pending 模块

`formal/SSBX/Pending/Interfaces.lean` 定义接口边界；`formal/SSBX/Pending/Examples.lean` 给出示例或案例连接。完整模块信息见 [../_generated/lean-index.md](../_generated/lean-index.md)。

## 正确写法

可以写：

- 「该项目前是 pending interface」。
- 「模型案例给出计算结果，但充分性仍依赖 ledger 或校准」。
- 「阈值协议由 claim ledger 记录，状态需查 claim-index」。

不要写：

- 「Lean 已证明经验阈值正确」。
- 「正邪判定已无条件闭合」。
- 「模型输出等于现实真值」。

## 与 claim ledger

Pending 与 claim ledger 分工不同：

- Pending 标出尚未闭合的接口位置。
- Claim ledger 标出具体 claim 的状态。
- Model 可提供计算或案例。
- Lean theorem 只覆盖已形式化且已类型检查的命题。

因此读推荐案例、Ω、Ω_B、Π_开、阈值协议等内容时，应同时看 [../_generated/claim-index.md](../_generated/claim-index.md) 与本页口径。
