# 计算机与编程概念 Overlay Mapping

> 状态：draft v0.1 (2026-05-13)
> 范围：把计算机科学与编程语言常用概念映射到现有 `R0..R8` root language tree 条目，作为审名、教学和跨学科引用索引。
> 口径：本页不改 canonical root 名，不新增坐标，也不把现代计算机概念声称为形式系统 primitive。形式真值仍以 bitstring、cell / operator role 和 XOR mask 为准。

## 判断

计算机/编程概念是目前最容易对齐的一组现代概念，因为 root tree 本身已经采用了接近计算模型的接口：

- `cell` 对应 state / value / data carrier。
- `operator` 对应 function / transition / program action。
- `恒` 对应 identity / no-op。
- `印` 对应 trace / log / witness / effect evidence。
- `投` 对应 projection / future computation / thunk-like plan。
- `未 / 已 / 今` 对应 future / past / current execution state。

需要谨慎的是：本 tree 对 computation 的结构很强，但不直接编码 hardware architecture、time complexity、numeric probability、network protocol 或 memory layout。

## 读法原则

1. 编程概念优先按 denotational / operational role 映射，而不是按某一种语言语法映射。
2. `cell` 是 value/state；`operator` 是 transition/action；这比诸子 overlay 更接近形式系统本身。
3. `記 / 述 / 象 / 質` 负责 data representation、syntax、serialization 与 literal/value。
4. `綱 / 維 / 契 / 合` 负责 type、interface、binding、module 与 composition。
5. `徑 / 履 / 作 / 臨 / 節` 负责 program path、execution、control flow 和 effect discipline。
6. `印 / 投 / 未 / 已 / 今` 负责 log、trace、promise/projection、history 和 current runtime state。

## 总表

| 计算机/编程概念 | 推荐锚点 | 辅助锚点 | 读法 | 状态 |
|---|---|---|---|---|
| bit / boolean | `R1-o-cell` 阳/实；`R1-x-cell` 阴/虚 | `R1-x-operator` 易 | binary value, boolean state, bit flip | 已公开 |
| byte / word | R8 bitstring / Cell256 | R4-R8 layer vectors | fixed-width bitvector / machine word；R8 正好给 256 cell carrier | 强 overlay |
| value | cell role；`R5-ooxoo-cell` 質 | `R5-xxooo-cell` 象 | value as carrier element; literal/value as 質 or 象 | 强 overlay |
| state | cell role；R8 `今·*` family | R7 `有跡 / 無跡` family | current state, latent state, trace state | 强 overlay |
| function | operator role | `R6-oooooo-operator` 恒、nonzero XOR masks | state transformer / pure function in this interface | 已公开 |
| no-op / identity | `恒` operators | `R6-oooooo-operator`, `R8-oooooooo-operator` | identity function, no state change | 已公开 |
| data structure | `R5-xoxxo-cell` 綱；`R5-xoxxx-cell` 維 | `契 / 合 / 記 / 述` | schema, structure, linked relation, serialized form | 强 overlay |
| type | `綱 / 維` | `R6-xxxxox-cell` 比、`R6-oxoooo-cell` 同人 | type as classification, invariant, structural constraint | 强 overlay |
| term / expression | `R5-xxooo-cell` 象；`R5-xxxxx-cell` 述 | `R5-ooxoo-cell` 質 | syntax tree / expression as representable form | 强 overlay |
| statement / command | `R5-oooox-cell` 作；`R5-xxxxx-cell` 述 | `R5-oooxx-cell` 履 | command as enacted instruction; statement as written action | 强 overlay |
| variable / name | `R5-xxxxo-cell` 記；`R5-xxxxx-cell` 述 | `契 / 合` | recorded name, declared binding, named reference | 强 overlay |
| binding | `R5-xoxoo-cell` 契；`R5-xoxox-cell` 合 | `綱 / 維` | binding as contract/tally and union with environment | 强 overlay |
| environment / context | `R4-xoxx-cell` 間時；`綱 / 維` | R8 `今·*` family | scoped context, current environment, relation over time | 强 overlay |
| module | `綱 / 維` | `R6-xooxox-cell` 井、`R6-xoooxo-cell` 鼎 | organized component, public vessel, shared interface | 强 overlay |
| API / interface | `契 / 合 / 節` | `述 / 記 / 綱 / 維` | contract, compatibility, constraints, documented surface | 强 overlay |
| program | `述 + 徑 + 履 + 作` | `恒 / 改 / 變化` operators | written path that can execute into action | 强 overlay |
| runtime | R8 `今·*` family | `履 / 作 / 印` | current execution state and live effects | 强 overlay |
| control flow | `R5-oooxo-cell` 徑；`R5-xxoxo-cell` 向；`R5-xxoxx-cell` 赴 | `臨 / 節 / 履` | path, branch direction, goto/approach, execution route | 强 overlay |
| branch / conditional | R4 `機 / 幾 / 兆` cells；`R5-xxoox-cell` 占 | `臨 / 節` | condition, decision point, guarded transition | 强 overlay |
| loop | `R6-oxxxxx-cell` 复；`恒` operator | `履 / 記` | repetition, fixed point-ish return, iterative execution | 强 overlay |
| recursion | `复 + 述 / 作` | `徑 / 恒` | self-returning program description/action | 强 overlay |
| effect | `印` operators；R7/R8 `有跡` family | `易外` operators | observable trace left by computation | 强 overlay |
| IO | `易外` operators；`印` operators | `易內` for input into internal state | crossing system boundary and leaving trace | 强 overlay |
| log / trace | `印` operators；R7 `有跡·*` cells | `R5-xxxxo-cell` 記 | trace, log, witness, audit record | 强 overlay |
| promise / future / thunk | `投` operators；R8 `未·*` family | `R5-xxoox-cell` 占 | deferred projection, future computation, pending result | 强 overlay |
| cache | `記 + 今/已` | `恒 / 复` | retained result for current or past computation | 说明性 overlay |
| persistence / storage | `記 / 述 / 有跡 / 已` | `井` as shared store metaphor | durable record and retrievable trace | 强 overlay |
| parser | `幾 / 機 / 兆 + 述` | `象 / 記` | reading signs into syntax/AST | 强 overlay |
| grammar | `綱 / 維 / 節` | `述` | production constraints and well-formed structure | 强 overlay |
| compiler | `述 -> 作`；`象 -> 質` | `改 / 變化` operators | translate written form into executable/actionable form | 强 overlay |
| interpreter | `觀 + 作` | `今 / 記 / 印` | evaluate expression in current state and produce trace | 强 overlay |
| evaluation | operator application | `臨 / 作 / 印` | applying a transition to a state | 已公开 |
| test | `觀 + 印 + 中孚` | `記 / 述` | observe output, witness behavior, check truth/invariant | 强 overlay |
| debugging | `觀 + 記 + 印 + 改` | R8 `已 / 今` cross-check | inspect trace, compare state, patch transition | 强 overlay |
| exception / error | `R6-xoxoox-cell` 困；`R6-xxoxox-cell` 蹇 | `R6-oxxoxo-cell` 噬嗑、`R6-xxxooo-cell` 否 | blocked execution, obstruction, forced break, failure state | 说明性 overlay |
| transaction | `未济 / 既济` | `中孚 / 印 / 复` | pending vs committed completion; traceable commit/rollback | 强 overlay |
| concurrency | `R6-oxoooo-cell` 同人；`R6-xxxxox-cell` 比 | `R6-xoxxoo-cell` 涣、`R6-xxxoox-cell` 萃 | concurrent actors, coordination, split/gather | 说明性 overlay |
| synchronization | `契 / 合 / 節` | `中孚 / 比` | protocol, handshake, locking/constraint, consistency | 强 overlay |
| race condition | `讼 / 困 / 蹇` | `涣` | conflict over shared state, obstruction, disorder | 说明性 overlay |
| security / capability | `節 / 契 / 綱 / 維` | `印 / 觀` | permission boundary, contract, auditability | 说明性 overlay |

## 编程语言 Crosswalk

| 语言概念 | Root-tree 对应 | 说明 |
|---|---|---|
| syntax | `象 / 述 / 記` | representable form, written expression, token/record. |
| semantics | cell/operator interpretation | meaning as state and transition behavior. |
| denotation | cell role / operator role | value denotation or function denotation. |
| operational step | operator application | `s -> op(s)` style transition. |
| type checking | `綱 / 維 / 節 + 觀` | schema constraints inspected against term/value. |
| scope | `間 / 綱 / 維` | relation-bounded environment. |
| closure | `契 + environment + 述` | binding plus captured context and code body. |
| purity | absence of `印 / 易外` in prose reading | no observable trace or external boundary crossing. |
| side effect | `印 / 易外` | effect leaves trace or crosses outward. |
| referential transparency | `恒 / 中孚` | stable substitution and inner truth; only as explanatory overlay. |

## 系统与运行时

| 系统概念 | 推荐锚点 | 说明 |
|---|---|---|
| process | `今 + 履 / 作` | live execution path. |
| thread | `徑 / 履` within a process | a path of execution; concurrency needs relation anchors. |
| scheduler | `臨 / 節 / 觀` | choosing which path to run under constraints. |
| message passing | `易外 + 契 / 合 + 印` | boundary crossing, protocol agreement, trace. |
| shared memory | `井 / 比 / 記` | shared store, holding-together relation, record. |
| database | `記 / 述 / 井` | persistent records and shared access. |
| network | `通 / 達 / 渠` | channel, reachability, route. |
| protocol | `契 / 節 / 綱 / 維` | agreed constraints and structural contract. |

## 不完全对上的部分

| 概念 | 目前状态 | 建议说法 |
|---|---|---|
| hardware architecture | 弱 overlay | 可借 `R1 bit / R8 word / 井 storage` 说明，但不声称覆盖 CPU/cache/bus 细节。 |
| asymptotic complexity | 无直接 root | 可用 prose 讨论 cost，但 root table 不编码 Big-O 或资源函数。 |
| numeric types | 弱 overlay | bitvector 有结构锚点；整数/浮点/精度规则需要额外定义。 |
| garbage collection | 说明性 overlay | 可借 `剥 / 涣 / 記` 读释放与记录清理，但不是正式内存模型。 |
| distributed consensus | 说明性 overlay | 可借 `比 / 中孚 / 印 / 契` 说明一致性，但不编码协议。 |
| probabilistic programming | 弱 overlay | `投 / 占 / 印` 支持预测-证据读法，但没有概率权重。 |

## 引用建议

- 正式 root table 仍引用 `layers/R*.md` 中的 `id`、`ox`、`role` 和 public candidate。
- 计算机/编程术语出现在 prose 时，可引用本页表格作为 overlay index。
- 对外文档中可以说“state/function/effect/trace/projection have direct functional anchors”，但不要说硬件、复杂度或完整语言语义已经被 root tree 覆盖。
- 若将来要增强形式化，优先补 `投 / 印 / 未 / 已 / 今` 的 evaluator examples，以及 `綱 / 維 / 契 / 合` 的 type/interface examples。
