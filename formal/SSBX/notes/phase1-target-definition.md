# Phase 1 Target Definition

## 前置

- Lean 靶文件：`formal/SSBX/Foundation/Wen/MetaInterp/TargetContract.lean`
- 当前去公理路线：`formal/SSBX/notes/zero-axiom-roadmap.md`
- 信任边界：`docs-next/10_formal_形式/trust-boundaries.md`
- 运行边界：`formal/SSBX/notes/run-boundary.md`

## Lean 锚点

| 名称 | 位置 | 口径 |
|---|---|---|
| `LeanChecksYiSemantics` | `TargetContract.lean` | `HaltsWith P h []` 与 ordinary `Halts P h` 一致 |
| `ProgramEncodingRoundTrip` | `TargetContract.lean` | raw `ProgEnc.encProg` 在给定长度与 `AllEncodable` 下可回读 |
| `FramedProgramRoundTrip` | `TargetContract.lean` | `LenProgInput` / framed input 在显式前提下可回读 |
| `MetaInterpTargetSpec` | `TargetContract.lean` | 当前 pure YiInstr 元解释器靶：bounded universal interpreter |
| `FramedMetaInterpTargetSpec` | `TargetContract.lean` | parser-friendly 的 framed-input 工程 lane |
| `FullBridgeTarget` | `TargetContract.lean` | 去除 `kleene_recursion_axiom` 所需的完整前提包 |
| `target_contract_phase1_summary` | `TargetContract.lean` | Phase 1 公开汇总定理 |

## Claim

Phase 1 只完成一件事：把“YiInstr 与 CIC 的关系”改写成可审计的 Lean 证明靶。

严格说，当前靶不是 `YiInstr = CIC`，也不是“文言自己证明自己”。当前靶是：

> Lean 作为元理论先固定 YiInstr 语义、编码、元解释器、s-m-n、对角化 compiler 与 cuo-restricted Church-Turing 的接口；文言程序随后只作为这些接口的 witness，由 Lean 检查。

## 边界声明

- CIC 目前只是外部形式模或元层说法；本轮没有定义 CIC 语法、typing、reduction，也没有给出 CIC compiler。
- `YiInstr` 是对象机器；其证明路径使用 `runFuel`，不是 partial `run`。
- `kleene_recursion_axiom` 仍未移除；`FullBridgeTarget → KleeneInverter` 只是把剩余前提包接回现有 `KleeneInternal.path_to_zero_axiom`。
- `MetaInterpTargetSpec` 使用当前 bounded universal interpreter 靶；`FramedMetaInterpTargetSpec` 明确记录 length-framed 工程 lane，但还没有桥接成 full `UniversalInterpSpec`。

## 完成度审计

| 项 | 状态 | 说明 |
|---|---|---|
| YiInstr operational semantics | machineChecked | `BaguaTuring` + `HaltsWith`/`Halts` 空输入一致 |
| raw program encoding | machineChecked | 需要 instruction count 与 `AllEncodable` |
| framed program encoding | machineChecked | 需要 `ProgLenBounded` 与 `AllEncodable` |
| bounded meta interpreter witness | typed target | 下一阶段要给出具体 `List YiInstr` |
| full universal interpreter | typed target | 仍是去公理化完整链条所需前提 |
| s-m-n compiler | typed target | 受无 arbitrary `Cell192` literal 与 empty-stack branch 限制 |
| diagonal compiler package | typed target | 仍需 fixed point 与 Bool inverter compiler |
| cuo-restricted Church-Turing | typed target | 与当前 `GodelLi.KleeneInverter` 口径一致 |
| strict `YiInstr ↔ CIC` | non-goal | 没有 CIC object calculus 前，不作等价命题 |

## 主定理入口

`target_contract_phase1_summary` 机器检查以下事实：

- Lean 已有 YiInstr 语义与编码锚点。
- full universal target 可推出 bounded target。
- `FullBridgeTarget` 足以推出当前 `KleeneInverter`。
- Wenyan history-equality fixed point target 足以推出 halting-only fixed point。
- strict `YiInstr ↔ CIC` 明确标为 non-goal。
- proof order 是 Lean target 先于 Wenyan witness。

## 验证命令

```bash
lake build SSBX.Foundation.Wen.MetaInterp.TargetContract
```
