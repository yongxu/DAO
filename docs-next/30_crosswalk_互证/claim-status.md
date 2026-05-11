> 状态：v3 (2026-05-11) — claim 状态读法 + v3 当前 live claim 摘录。完整状态以 `../_generated/claim-index.md` 为准。

# Claim 状态读法

> 状态：v3 定本 (2026-05-11) — Cell256 / V₄ Shi / 严格 uniform R₀..R₈

`ClaimLedger` 把文本 claim、模型结果和形式证明放入同一张账本。它是审计工具，不是把所有 claim 自动升级为 theorem 的机制。

## 状态总览

最新状态以 `../_generated/claim-index.md` 为准。本页只解释读法 + 列出 v3 当前关键 live claim。

| 状态 | 含义 | 文档写法 |
|---|---|---|
| `machineChecked` | Lean 已检查对应 theorem 或 registry 性质 | 可写「形式层已闭合」 |
| `modelComputed` | 由具体模型或案例计算给出 | 可写「模型案例给出」 |
| `ledgerDependent` | 由 ledger、文本来源或公理映射承接 | 应写「账本承接」 |

## Kind 与状态

| Kind | 常见状态 | 说明 |
|---|---|---|
| `definition` | `ledgerDependent` | 定义来自旧文或 ledger，未必是 theorem |
| `proved` | `machineChecked` | 已有 Lean theorem 支撑 |
| `registry` | `machineChecked` | 表或名册完备性由 Lean 检查 |
| `modelInterface` | `ledgerDependent` | 接口存在，但经验充分性未闭合 |
| `axiomBacked` | `ledgerDependent` | 依赖明示公理或 claim ledger |
| `caseResult` | `modelComputed` 或 `ledgerDependent` | 具体案例可能已算出，也可能仍依赖解释 |

## v3 当前关键 live claim（精选 15 条）

| # | claim | kind | status | 锚 |
|---|---|---|---|---|
| 1 | **Cell256 R₈ closure 收口**：基数 256 + R₀..R₈ strict-uniform + P/T/Y closure + (Z/2)⁸ 群作用 simply-transitive on `(qian, dao)` + BenZheng 投影 + 位置-算子树双射 + xuGua256 (序卦 256 cell 扩展) | `proved` (bundle) | `machineChecked` | `Cell256Stratify.lean § 7` `R8_complete` |
| 2 | **R8_complete axiom audit**：`#print axioms R8_complete` 仅含 Lean 核心 axioms `propext` 与 `native_decide`（无项目自定义 axiom 介入） | `proved` | `machineChecked`（审计已审） | `Cell256Stratify.lean § Axiom audit` |
| 3 | **Cell256 = (Z/2)⁸ Abelian 群** + **Cayley fusion 严格成立**（`ε ∘ ι = id`，`ι` 单射，`ι` 群同态） | `proved` | `machineChecked` | `Cell256.lean § 7` `cell256_phaseA_summary` + § 7.6 |
| 4 | **R₀..R₈ 8 对 lift/project 全 retract**（`proj ∘ lift = id`，faithful Rₙ ↪ R_{n+1}） | `proved` | `machineChecked` | `LiftProject.lean § 9` `liftProject_summary` |
| 5 | **印 / 投 = XOR-with-mask atomic 算子**：each involution；commute；`yin_mask ⊕ tou_mask = (qian, jin)` (V₄ central) | `proved` | `machineChecked` | `Cell256.lean § 8` + `Operators/Atomic.lean` `atomic_all_involutive` |
| 6 | **{id, cuo, zong, cuoZong} on Hexagram = V₄ Klein**（每元 involution、abelian、composite 关系全成立）；`hu` 不在 V₄，但其唯一不动点 = `{乾, 坤}` | `proved` | `machineChecked` | `Operators/V4Outer.lean § 7` `v4_outer_summary` |
| 7 | **Self-similarity v1 gaps closed**：R₁ ≃ R₀⊕R₀、R₆ 三路汇聚、R₈ ≃ R₇×Bool | `proved` | `machineChecked` | `SelfSimilarity.lean` `self_similarity_gap_summary` |
| 8 | **R₈ V₄ partition + R-O / character self-duality**：R₈ ≃ R₆ × trace bit × projection bit；每个 temporal-state fiber 64；Way (道) = origin = no-op；`R8 ≃ XorOperator`；operator composition is representative XOR, both on representatives and inside `XorOperator`；finite Boolean character image self-duality；OX coordinate roundtrip 与 full-negation masks anchored | `proved` | `machineChecked` | `V4Tensor.lean` `V4Tensor.r8_eq_r6_times_trace_projection`, `V4Tensor.r8_temporal_coordinate_summary`, `V4Tensor.r8_temporal_state_fiber_card_eq_64`, `V4Tensor.way_origin_operator_summary`, `V4Tensor.r8_operator_character_duality_summary`, `V4Tensor.r8_character_duality_computation_summary`, `V4Tensor.r8_negation_ox_operator_summary`, `V4Tensor.r8_equiv_xor_operator`, `V4Tensor.r8_equiv_mask_character_image`, `V4Tensor.ox_full_neg_mask_eq`; `OXNotation.lean` `OXNotation.ox_coordinate_complete_summary` |
| 9 | **Kernel post-Cayley collapse**：R₇ Kernel motion 无 terminus，center universal | `proved` | `machineChecked` | `Kernel.lean` `kernel_post_cayley_collapse_summary` |
| 10 | **WayJudge closure + concrete bilingual identity**：Sexp evaluator 成功结果闭在 R₇；Chinese-form 与 o/x-form concrete programs 对齐 | `proved` | `machineChecked` | `DaoJudge.lean` `DaoJudge.eval_chinese_earth_eq_ascii_earth`, `DaoJudge.judge_bilingual_same_earth_self`, `DaoJudge.way_judge_closure_bilingual_summary` |
| 11 | **Classical text ↔ R-hierarchy direct bridge**：classical-language aliases 与 YiInstr / R₈ operator execution / WayJudge 对齐 | `proved` (typed skeleton) | `machineChecked` | `ClassicalTextRHierarchyBridge.lean` `classical_text_way_judge_rhierarchy_bridge_summary` |
| 12 | **Quantum ↔ R₈ finite bridge skeleton**：Pauli X basis action、R₃ basis flips、R₈ V₄⁴ + finite function-space regular representation `R8 → ℂ` with involutive faithful translations | `proved` (typed skeleton) | `machineChecked` | `QuantumR8Bridge.lean` `r8_regular_representation_quantum_bridge_summary`, `r8_regular_translate_involutive`, `r8_regular_translate_faithful` |
| 13 | **Base-256 self-interpreter structural assembly**：concrete `metaInterpProg` has fixed length, outer-loop fetch entry, encoded-program split/decode bridge, zero-arity read-tag micro-witness, concrete fetch-with-peel / dispatch segment witnesses, exact halted and running fetch routes from real fetch-loop entry, all-op absolute-pc dispatch routes, and 7-fuel halt execution smoke witness | `proved` (typed skeleton) | `machineChecked` | `WenyanSelfInterp.lean` `ProgEnc.encProg_cons`, `ProgEnc.encProg_append`, `ProgEnc.encProg_splitAt_get?`, `ProgEnc.decInstr_current_after_split`; `MetaInterp/SkipInstr.lean` `SkipInstr.encProg_cons_zeroArity_eq`, `SkipInstr.skipOneInstr_simulates_encProg_cons_zeroArity`; `MetaInterp/Fetch.lean` `fetchEntryState_pc_counter_peel_exposes_halted_flag`; `MetaInterp/FetchProg.lean` `fetchProgWithPeel`, `fetchEntryState_pc_counter_peel_then_haltDetectEntry_shifted`, `fetchProg_haltDetect_running_to_dispatch_at_fuel`; `MetaInterp/Assembly.lean` `metaInterpProg_base256_structural_summary`, `metaInterpProg_fetchProgWithPeel_at_offset`, `metaInterpProg_fetch_peel_to_haltDetect_at_fuel`, `metaInterpProg_fetch_routes_halted_exact`, `metaInterpProg_fetch_routes_running_to_dispatch_exact`, `metaInterpProg_dispatch_routes_nop_at_fuel`, `metaInterpProg_dispatch_routes_pop_at_fuel`, `metaInterpProg_dispatch_routes_halt_at_fuel`, `metaInterpProg_dispatch_halt_executes_halt` |
| 14 | **Exact-fuel semantic-compose frontier**：embedded prologue U.0a and zero-step/prologue compose are proved; U.0 composition is machine-checked from explicit loop/padding semantic obligations; U.1/U.2/U.3 now have a no-sorry obligation interface; generic META halted padding is proved; Strategy-B fixed-parameter boundary is machineChecked; budget fuel is only an upper-bound lane | `proved` (conditional) | `machineChecked` | `MetaInterp/Universal.lean` `metaStart_runFuel_five_eq_postPrologue`, `metaInterpProg_simulates_zero_steps`, `semantic_compose_frontier_summary`, `semantic_loop_obligation_frontier_summary`, `metaInterpProg_meta_halted_padding`, `universal_compose_current_boundary_summary`, `metaInterpProg_simulates` |
| 15 | **0 sorry 跨已迁文件**（V₄ temporal-state 迁移过程中未引入 sorry；commits `7de5064`, `0003224`, `8e4406e` 之 lake build 全 3648/3648） | `registry` | `machineChecked`（构建侧） | `git log` + `lake build`；摘要见 `../_generated/lean-index.md` |

## v3 当前 live claim — pending（精选 2 条）

| # | claim | status | 备注 |
|---|---|---|---|
| 16 | **Classical-language self-interpreter full semantic universal-compose theorem** | `pending` | embedded prologue U.0a、zero-step/prologue compose、exact-fuel U.0 composition frontier、U.1/U.2/U.3 obligation interface、generic META halted padding、Strategy-B fixed-parameter boundary、encoded-program split/decode bridge、zero-arity read-tag micro-witness、push/pop sim-side encoded-history bridges、aligned `nop` exact BlockPre-to-BlockPost witness、trivial-jump exact witness、pc=0 fetch exact dispatch route、pc-counter peel exposes halted-flag bridge、shifted peel-to-halt-detect exact fuel witness、concrete `fetchProgWithPeel` assembly splice、exact halted/running fetch routes from real fetch-loop entry、halted/running fetch current-shape witnesses、instruction-indexed dispatch route wrapper、halt-opcode current-shape-vs-step witness、all-op absolute-pc dispatch routes、halt-arm route 与 halt execution smoke witness 已 machineChecked；当前阻塞点已 machine-exposed：running fetch 到达 dispatch 时 `cur` 仍是 halted-flag cell，history 是 post-peel tail，而不是 opcode tag + restored `encMetaHistory`；halt opcode 执行后 META VM halted=true 但 history 仍是旧 `encMetaHistory`，而 simulated `.halt` step 需要把 encoded halted flag 改成 true；仍缺 replacing placeholder walker with real concrete fetch decode/restore、hard-block exact META-block execution witnesses、parameterized sub-dispatch 构造 `SemanticLoopObligations`，以及 arbitrary-program simulation。详 `MetaInterp/Universal.lean` / `MetaInterp/Fetch*.lean` / `MetaInterp/Dispatch.lean` / `MetaInterp/Assembly.lean`。 |
| 17 | **Physical Pauli-string / analytic unitarity bridge** | `pending` | `QuantumR8Bridge.lean` 已给 one-bit basis、R₃ basis flips、R₈ regular representation 与 finite function-space carrier `R8 → ℂ`；未构造 physical Pauli-string system 或 inner-product/unitarity semantics。 |

## 审读规则

- 读 claim 前先看 status，不只看 label。
- label 是人读标题，不是证明强度。
- source 是来源提示，不等于完整证明。
- claim 若依赖 pending interface，必须保留 pending 口径。
- 同一主题可同时有 machineChecked 子命题和 ledgerDependent 总 claim。
- v3 之新 atomic / V₄ outer / R-hierarchy 算子 / 印 / 投 之 machineChecked 状态见上表 #1–#7；引用时以这些锚为准。

## 与信任边界的关系

`axiomBacked` 不一定表示 Lean 里新增 axiom。它可能表示 claim ledger 依赖旧文、公理账本或外部充分性假设。真正的形式信任边界以 `../_generated/trust-boundary.md` 和 `../10_formal_形式/trust-boundaries.md` 为准。

当前必须特别标明：

- `kleene_recursion_axiom` 相关结论依赖该 axiom（已拆为 4 件具名原子；详 `KleeneCarrier.lean`）。
- `theOne` 是 opaque witness，不能当作可展开构造。
- `YiState.run` 是 partial execution boundary，证明层优先用 fuel 版本。
- `R8_complete` 之依赖只含 Lean 核心 `propext + native_decide`，不引入项目 axiom — 这是 v3 算子系统之主基线。

## Cell192 → Cell256 迁移对 claim 状态的影响 (2026-05-10/11)

V₄ Shi / Cell256 升级后，与 Cell192 cardinality 直接绑定的 claim 已被替换或重号；本页的状态分类（`machineChecked` / `modelComputed` / `ledgerDependent`）与 Kind taxonomy 不依赖具体 cardinality，因此本页本身**不需要按 cell-cardinality 改写**。需要留意的具体迁移：

- `Cell192OperatorComplete` → `Cell256OperatorComplete`（Self-description witness，仍 `machineChecked`）。
- 旧 `R6_complete` / `R7_complete` bundle → **`R8_complete`** in `Cell256Stratify.lean`，axiom audit = `{propext, native_decide}`，**0 项目自定义 axiom**。
- 旧 wen-constructive coverage 等下游 cascade 引理保留旧名（避免重命名传播），但现在只按 Cell256-indexed legacy audit inventory 读取；不作为 root ontology 或完整语义证据（详见 `../30_crosswalk_互证/old-to-new.md` Cell192→Cell256 节）。

具体 claim 列表与状态以 `../_generated/claim-index.md` 为准。

## 更新检查

改动 `ClaimLedger.lean` 或相关 theorem 后，应重新生成 `../_generated/claim-index.md`。人工页只改解释口径，不手写替代统计。

## 形式锚

- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — `R8_complete` + axiom audit
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — `cell256_phaseA_summary`
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — `cell128_phaseA_summary`
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — `liftProject_summary`
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — `atomic_all_involutive`
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — `v4_outer_summary`
- [`formal/SSBX/Foundation/Wen/WenyanSelfInterp.lean`](../../formal/SSBX/Foundation/Wen/WenyanSelfInterp.lean) — `ProgEnc.encProg_splitAt_get?`, `ProgEnc.decInstr_current_after_split`; full self-interpreter route remains non-universal
- [`formal/SSBX/Foundation/Wen/MetaInterp/SkipInstr.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/SkipInstr.lean) — `SkipInstr.encProg_cons_zeroArity_eq`, `SkipInstr.skipOneInstr_simulates_encProg_cons_zeroArity`
- [`formal/SSBX/Foundation/Wen/MetaInterp/Block_PushPop.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/Block_PushPop.lean) — `encMetaHistory_push_step`, `encMetaHistory_pop_step_nonempty`, `encMetaHistory_pop_step_emptyHist`
- [`formal/SSBX/Foundation/Wen/MetaInterp/ExecuteBlock.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/ExecuteBlock.lean) — `executeBlock_nop_simulates_aligned`, `encMetaHistory_nop_step`, `encMetaHistory_halt_step`
- [`formal/SSBX/Foundation/Wen/MetaInterp/Block_Jump.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/Block_Jump.lean) — `executeBlock_jump_simulates_trivial`, `encMetaHistory_jump_step`, `encMetaHistory_jump_step_trivial`
- [`formal/SSBX/Foundation/Wen/MetaInterp/Assembly.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/Assembly.lean) — `metaInterpProg_base256_structural_summary`, `metaInterpProg_fetchProg_at_offset`, `metaInterpProg_dispatchProg_at_offset`, `metaInterpProg_fetch_routes_running_to_dispatch_at_fuel`, `metaInterpProg_dispatch_routes_halt_at_fuel`, `metaInterpProg_dispatch_halt_executes_halt`
- [`formal/SSBX/Foundation/Wen/MetaInterp/Universal.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/Universal.lean) — `metaInterpProg_simulates_zero_steps`, `semantic_compose_frontier_summary`, `semantic_loop_obligation_frontier_summary`, `metaInterpProg_meta_halted_padding`, `universal_compose_current_boundary_summary`
- [`formal/SSBX/Foundation/Wen/MetaInterp/Fetch.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/Fetch.lean) — `fetchProtocol_simulates_pc0_to_dispatch`, `pc_counter_peel_history_head_is_halted_flag`
- [`formal/SSBX/Foundation/Wen/MetaInterp/FetchProg.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/FetchProg.lean) — `fetchProg_routes_halted_at_fuel`, `fetchProg_routes_running_to_dispatch_at_fuel`
- [`formal/SSBX/Foundation/Squaring/SelfSimilarity.lean`](../../formal/SSBX/Foundation/Squaring/SelfSimilarity.lean) — `self_similarity_gap_summary`
- [`formal/SSBX/Foundation/Squaring/V4Tensor.lean`](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean) — `V4Tensor.r8_temporal_coordinate_summary`, `V4Tensor.r8_temporal_state_fiber_card_eq_64`, `cell_is_operator`, `V4Tensor.r8_operator_character_duality_summary`, `V4Tensor.r8_character_duality_computation_summary`, `V4Tensor.r8_negation_ox_operator_summary`, `V4Tensor.ox_full_neg_mask_eq`
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OXNotation.ox_coordinate_complete_summary`
- [`formal/SSBX/Foundation/Wen/ClassicalTextRHierarchyBridge.lean`](../../formal/SSBX/Foundation/Wen/ClassicalTextRHierarchyBridge.lean)
- [`formal/SSBX/Foundation/Modern/QuantumR8Bridge.lean`](../../formal/SSBX/Foundation/Modern/QuantumR8Bridge.lean)
