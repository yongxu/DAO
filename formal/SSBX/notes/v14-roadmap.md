# v14 形式证明骨架 · 三分原则与 roadmap

来源：`史料/生生不息论_v14_形式证明骨架版.md` §十一 + §十四。

v14 是从 v13.2 specification 进入 proof assistant 的第一层骨架。其核心工程指引有二：句子三分原则（写规范时必守），与机器验证 roadmap（往后做什么）。

## 定义、公理、接口假设——三分原则（v14 §十一）

v14 严格分离三类句子。每条入式句子必先归类。

### 定义

可展开、可替换、无经验承诺。例如：

$$
\mathrm{开} := \mathrm{未} \wedge \mathrm{可} \wedge \mathrm{应} \wedge \mathrm{转}
$$

判别：是否可被任意上下文中的等价表达式替换？若是，归定义。

### 公理或结构假设

用于对象理论内部。例如：

- 非递归字图无环
- 注册表唯一
- 生成项有根

判别：不可展开（无 `:=`），但承担形式系统内部的结构约束。

### 接口假设

经验模型必须提供。例如：

$$
I_F, K_\Gamma, w_\Gamma, \Omega, \Omega_B, \Pi_{\mathrm{开}}, Q_{\mathrm{audit}}
$$

判别：模型实例化时才有具体语义；未实例化者，对应输出进入 $\mathsf{U}$。

接口假设可以被不同模型实例化；若未实例化，则输出进入 $\mathsf{U}$。

## 下一步机器验证任务（v14 §十四）

1. **将 Markdown 中的元定理逐步迁入 Lean 模块**——v14 §六–§十二 的六条元定理（无籍不得入式 / 复词展开有根 / 递归项有语义 / 类型保持 / 非递归展开终止 / 数学接口有根）应逐条进入 Lean。
2. **为 `MathAxiomMap` 增加根字清单与映射标签的注册表**——参见 [`math-axiom-map.md`](./math-axiom-map.md) 的 11 行表，每行需在 `Foundation/Core/MathAxiomMap.lean` 中以可枚举的注册表形式登记 Roots / Map / Contract。
3. **把当前接口假设逐步替换为具体定义**——目前 v14 列出 7 个接口假设（$I_F, K_\Gamma, w_\Gamma, \Omega, \Omega_B, \Pi_{\mathrm{开}}, Q_{\mathrm{audit}}$）；每替换一个接口为具体定义，对应输出从 $\mathsf{U}$ 提升为可校之三值结果。
4. **为推荐系统案例建立一个小模型，证明**：

$$
\mathrm{正行}(i_2) \wedge \mathrm{义}(i_2) \wedge \mathrm{善}(i_2) \wedge \mathrm{仁}(i_2)
$$

并将「候选真道」保留为依赖度期数据的条件定理。

## 与现状对照（编校注，非源内容）

下表为编校期对当前 repo 现状之判断，不在 v14 源中；新增/扩展之机器验证应回填此表。

| v14 任务 | 当前实现 | 状态 |
|---|---|---|
| 元定理迁入 Lean | `Foundation/Core/MathAxiomMap.lean` 已实现「数学接口有根」之元定理六骨架 | 部分（六条中已有一） |
| `MathAxiomMap` 注册表 | Lean 已有 placeholder；尚未把 11 行表逐行注册 | 未做 |
| 接口假设 → 定义 | `Foundation/Wen/Operators.lean` 给出部分单字算子，但 7 个接口假设大多未替换 | 未做 |
| 推荐系统小模型 | `生生不息论_三本文完整版/02_补篇〇_可运行模型与实例化校正版/09_〇九、最小跑通案例_推荐系统与共开.md` 有伪代码，Lean 未建模型 | 未做 |
