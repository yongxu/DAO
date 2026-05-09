# Foundation/Modern

`Foundation/Modern` 收纳现代数学、逻辑、概率、物理与神经相关桥接。它让项目概念能与现代形式工具对话，但不把所有外部理论都重新证明一遍。

## 主题范围

模块簇覆盖：

- 范畴与 Yoneda：`CatOp`、`CatExt`、`YonedaFull`。
- 实数与分析：`RCauchy`、`RCauchyExt`、`Lebesgue`、`LebesgueDepth`。
- 概率与大数：`Kolmogorov`、`KolmogorovExt`、`IIDWlln`。
- 逻辑：`NaturalDeduction`。
- 动力系统：`ODESmoothness`、`PicardLindelofGen`。
- 量子与物理接口：`Quantum`、`QuantumRelativityNoGo`、`QuantumRelativityIntegration`、`QuantumRelativityMarkovBridge`、`QuantumRelativityWenBoundary`、`QuantumRelativityConcreteBridge`、`OperatorCellGridMarkovBridge`、`QuantumRelativityFiniteProbabilityBridge`、`QuantumRelativityPathCausalBridge`、`QuantumRelativityAmplitudeChannelBridge`、`QuantumRelativityInterferenceBridge`、`QuantumRelativityNonzeroPathAmplitudeBridge`、`QuantumRelativityTwoPathInterferenceBridge`、`QuantumRelativityDiscretePhaseBridge`、`QuantumRelativityDiscreteActionBridge`、`QuantumRelativityFinitePathSumBridge`、`QuantumRelativityFinitePathSumAlgebraBridge`、`QuantumRelativityEndpointIndexedPathFamilyBridge`、`QuantumRelativityEndpointSupportNormalizationBridge`、`QuantumRelativityTwoRouteEnumerationBridge`、`QuantumRelativityPathIdentityBridge`、`QuantumRelativityFiniteKeyQuotientBridge`、`QuantumRelativityPathQuotientBridge`、`QuantumRelativityCanonicalRepresentativeBridge`、`QuantumRelativityQuotientSupportBridge`、`QuantumRelativityQuotientSupportAlgebraBridge`、`QuantumRelativityObservableLedgerBridge`、`QuantumRelativityActionPhaseLawBridge`、`QuantumRelativityStepwiseUnificationBridge`、`QuantumRelativityFiniteProbabilityNormalizationBridge`、`QuantumRelativityNormalizedMassBridge`、`QuantumRelativityBornWeightNormalizationBridge`、`QuantumRelativityBornDistributionBridge`、`QuantumRelativityChannelComposeBridge`、`QuantumRelativityChannelComposeAssociativityBridge`、`QuantumRelativitySumOverMiddleChannelBridge`、`QuantumRelativitySumOverMiddleBornBoundaryBridge`、`QuantumRelativityUnitaryCPTPLedgerBridge`、`QuantumRelativityBornRuleDerivationBridge`、`QuantumRelativityPathWeightMultiplicationBridge`、`QuantumRelativityNontrivialChannelLawBridge`、`QuantumRelativityBornMeasurementBridge`、`SUN`、`BochnerPL`。
- 神经与对齐接口：`Neuro`、`DaoLi`。
- 卦位：`HexagramPosition`。

完整清单见 [../_generated/lean-index.md](../_generated/lean-index.md)。

## 读法

Modern 层的定理通常是局部形式结构或桥接定理。它们说明「某个现代框架可以怎样嵌入或对应」，不是说明该领域所有定理都已在本仓库重建。

## 与 Mathlib 的关系

若模块依赖 Lean/Mathlib 已有对象，应按普通形式化项目读：本仓库证明的是它声明并通过构建的内容；外部库提供的定理由依赖项承担。

## 与经验接口

现代模型常会通向 pending 或 ledgerDependent claim。例如神经、推荐、阈值、正邪判定、Ω 充分性等，不能因为有现代形式桥接就写成经验闭合。

查证时：

- theorem 与模块覆盖看 [../_generated/lean-index.md](../_generated/lean-index.md)。
- claim 状态看 [../_generated/claim-index.md](../_generated/claim-index.md)。
- pending 项看 [../_generated/registry-index.md](../_generated/registry-index.md)。
