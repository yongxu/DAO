# Lean 到义理

本页说明从 Lean 事实读回义理文本的口径。Lean 是机器检查层；义理页是解释层。二者可以互证，但不能互相替代。

## 读取顺序

1. 先查 `../_generated/lean-index.md`，确认模块、文件与声明所在 cluster。
2. 再查 `../_generated/claim-index.md`，确认相关 claim 是 machineChecked、modelComputed 还是 ledgerDependent。
3. 若涉及信任边界，先读 `../_generated/trust-boundary.md` 与 `../10_formal_形式/trust-boundaries.md`。
4. 最后回到 `../20_theory_义理/`，只把已确认的形式事实映射为解释语言。

## 常见映射

| Lean 区域 | 可读作 | 不可读作 |
|---|---|---|
| `Foundation/Core` | 根源、生成、注意、人类对齐等基础构件 | 全部价值论已闭合 |
| `Foundation/Bagua` | 八卦计算、Cell128/Cell256、有限执行与不完备路线 | 无条件去公理化完成 |
| `Foundation/Hierarchy` | R₀..R₈ 严格-uniform 阶梯 (R-index alias shims + LiftProject + Operators/{Atomic,V4Outer}) | v3 新增 |
| `Foundation/Notation` | OX["..."] 8-字符 256-格 macro | v3 新增 |
| `Foundation/Wen` | 文、算子、解释器、自释相关工程 | 文言自然语言全覆盖 |
| `Foundation/Modern` | 现代数学和跨域接口的形式桥 | 经验科学结论已由 Lean 证明 |
| `Text` | 字形、算子表、读法与完备性登记 | 每个传统训诂都已定本 |
| `Truth` | claim ledger 与语义状态 | 所有旧文 claim 均 machineChecked |

## 强度词

写义理说明时应保留 Lean 强度：

| Lean/索引状态 | 义理写法 |
|---|---|
| theorem / proved / machineChecked | 「Lean 已检查」「形式层已闭合」 |
| modelComputed | 「模型给出计算结果」「案例层可复现」 |
| registry | 「登记完备」「名册完备」 |
| axiomBacked | 「依赖明示公理或 ledger」 |
| ledgerDependent | 「由账本承接，非机器闭合证明」 |
| pending | 「接口待落地」「经验或协议层未闭合」 |

## 引用格式

人工文档优先引用生成索引，而不是复制 Lean 统计：

- 模块位置：`../_generated/lean-index.md`
- claim 状态：`../_generated/claim-index.md`
- 信任边界：`../_generated/trust-boundary.md`
- 图文件：`../_generated/diagram-index.md`
- 字元和 pending：`../_generated/registry-index.md`

若需要解释某个 theorem 的含义，可以提 Lean 文件路径，但不要在 docs-next 中重写证明。证明变化由 Lean 和生成索引反映。

## 边界

- `kleene_recursion_axiom` 下的结论必须写成「在此 axiom 下」。
- `opaque theOne` 是抽象 witness，不是新增 axiom。
- `YiState.run` 是执行边界；证明路径应引用 fuel 版本或有限见证。
- pending interface 不得被义理页写成已证明命题。
