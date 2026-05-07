# PendingName 经验接口落地方案

本文只给 6 个 `PendingName` 的落地接口方案，不改变名册语义。

已读上下文：

- `Roster.lean`：`邪续 / 开势投影 / 审校数据 / 正邪阈值 / 度期计算 / 经验校准` 目前均为 `PendingName`，`entryOf` 给出 `kind = .pending`、`sort = .truth`、无 roots/deps；`真` 是 `externalAudit`，依赖 `所是 / 相关度期 / 审校不败`。
- `Truth/Basic.lean`：经验承诺应落在 ledger 或 certificate 边界内，尤其是 `audit_reliability_axiom`、`threshold_reliability_axiom`、`case_data_reliability_axiom`，以及 `SemanticAdequacy` 的 `formal_semantics` / `text_mapping` 双条件。
- README / formal README：5 个原始接口为 `域 / 格 / 权 / 生 / 校`；6 个 pending interface 明确“await empirical calibration”；v14 规则要求定义、公理、接口假设分离，未实例化接口输出保持未知。

## 总体约束

接口落地时不应直接把 `PendingName` 改成 generated/recursive。最小可行路径是新增独立 Lean 模块，例如 `SSBX.Pending.Interfaces`，用结构体封装经验模型、数据、阈值、校验证书，并只证明“给定这些证书时，输出满足某 predicate”。是否把某接口从 pending 提升为 claim，应由后续 ledger 变更单独处理。

所有经验输出默认用 `SSBX.Core.Tri`：

- `top`：有证书，且证书推出对应 predicate。
- `bot`：有证书，且证书推出 predicate 的反面或互斥判定。
- `unk`：数据不足、阈值未覆盖、审校失败、或模型未实例化。

最小通用形状：

```lean
structure ExperienceInterface (Input Output : Type) where
  run : Input -> Output
  validInput : Input -> Prop
  certifies : Input -> Output -> Prop
  sound : forall x, validInput x -> certifies x (run x)
```

实际落地时可不抽出这个通用结构，但每个接口至少要有同等的 `run / validInput / certifies / sound` 边界。

下列 Lean 片段是接口草图，省略 namespace、imports 和部分参数前缀；真正落地时应把 predicate 参数化到对应结构体字段，或放入结构体 namespace 中。

建议落地顺序：

1. `审校数据`
2. `经验校准`
3. `正邪阈值`
4. `度期计算`
5. `开势投影`
6. `邪续`

理由：后四者都需要可追溯数据和校准证书；`邪续` 又依赖阈值、度期、投影和审校。

## 审校数据

### 形式输入

- 一个声明域 `Claim : Type`。
- 一个记录域 `Record : Type`。
- 一个来源域 `Source : Type`。
- 记录列表或可枚举记录集 `records : List Record`。
- 映射：`claimOf : Record -> Claim`、`sourceOf : Record -> Source`。
- 判定关系：`supports : Record -> Claim -> Prop`、`defeats : Record -> Claim -> Prop`。
- 独立性关系：`independent : Record -> Record -> Prop`。

### 输出

- `auditVerdict : Claim -> Tri`。
- 可选的证据包：对 `top` 给出互证/独立来源 witness；对 `bot` 给出 defeated witness；数据不足时返回 `unk`。

### 可验证 predicate

```lean
def WellFormedAuditData : Prop :=
  records.Nodup
  -- 每条 record 可追源，claim/source 映射全定义。

def AuditSupports (c : Claim) : Prop :=
  ∃ r1 r2,
    r1 ∈ records ∧ r2 ∈ records ∧
    r1 ≠ r2 ∧
    independent r1 r2 ∧
    supports r1 c ∧ supports r2 c ∧
    ¬ (∃ d, d ∈ records ∧ defeats d c)

def AuditDefeats (c : Claim) : Prop :=
  ∃ d, d ∈ records ∧ defeats d c
```

Lean 只验证这些关系与 witness，不声称原始世界事实自动可靠；原始数据可靠性进入 `case_data_reliability_axiom` 或后续更细 ledger。

### 需要的数据

- 原始 observation / annotation / reviewer decision。
- record id、claim id、source id、采集时间或版本。
- 来源独立性说明。
- 数据 schema、校验规则、hash 或不可变引用。
- 支持/反驳关系的标注依据。

### Lean 可落地的最小接口

```lean
structure AuditDataInterface where
  Claim : Type
  Record : Type
  Source : Type
  records : List Record
  claimOf : Record -> Claim
  sourceOf : Record -> Source
  supports : Record -> Claim -> Prop
  defeats : Record -> Claim -> Prop
  independent : Record -> Record -> Prop
  verdict : Claim -> SSBX.Core.Tri
  top_sound :
    forall c, verdict c = SSBX.Core.Tri.top -> AuditSupports c
  bot_sound :
    forall c, verdict c = SSBX.Core.Tri.bot -> AuditDefeats c
```

### 验收标准

- 有一个有限样例数据集可 `native_decide` 检查 `records.Nodup`。
- 对至少一个 claim 证明 `verdict c = top -> AuditSupports c`。
- 对至少一个被反驳 claim 证明 `verdict c = bot -> AuditDefeats c`。
- 数据缺字段、来源不独立或有 defeat 时不得给 `top`。

## 经验校准

### 形式输入

- 一个经验域 `Domain : Type`。
- 一个模型参数域 `Param : Type`。
- 训练/验证证据 `Evidence : Type`。
- 拟合函数 `fit : Evidence -> Param`。
- 损失或偏差函数 `loss : Param -> Evidence -> Nat`。
- 容许界 `tolerance : Nat`。
- 审校数据接口 `A : AuditDataInterface`，用于证明证据可用。

### 输出

- `param : Param`。
- `calibrated : Param -> Tri` 或 `CalibrationCertificate param`。

### 可验证 predicate

```lean
def Calibrated (p : Param) (eTrain eValid : Evidence) : Prop :=
  loss p eTrain <= tolerance ∧
  loss p eValid <= tolerance ∧
  EvidenceAudited eTrain ∧
  EvidenceAudited eValid
```

若使用随机或统计过程，Lean 侧最小验收只检查离散化后的 certificate，例如误差上界、样本覆盖和 holdout 结果；概率解释留给 ledger。

### 需要的数据

- 训练集、验证集、域说明、特征 schema。
- 参数版本、拟合配置、损失函数定义。
- holdout 切分规则和样本覆盖说明。
- 数据审校证书。
- 与旧参数或 baseline 的差异报告。

### Lean 可落地的最小接口

```lean
structure CalibrationInterface where
  Domain : Type
  Param : Type
  Evidence : Type
  fit : Evidence -> Param
  loss : Param -> Evidence -> Nat
  tolerance : Nat
  audited : Evidence -> Prop
  verdict : Evidence -> Evidence -> SSBX.Core.Tri
  calibrated :
    Param -> Evidence -> Evidence -> Prop
  top_sound :
    forall train valid,
      verdict train valid = SSBX.Core.Tri.top ->
      calibrated (fit train) train valid
```

### 验收标准

- `calibrated` 不依赖不可计算黑箱；黑箱只产生可检查 certificate。
- 训练/验证数据均有审校证书。
- `top_sound` 证明包含训练误差和验证误差两个上界。
- 更换数据或 tolerance 时，Lean 证明失败或返回 `unk`，不能静默沿用旧证书。

## 正邪阈值

### 形式输入

- 一个被判定对象域 `X : Type`，可为状态、行动、路径或 claim。
- 分数函数 `rightScore evilScore : X -> Nat`。
- 阈值 `rightCut evilCut : Nat`。
- 灰区宽度或冲突规则 `margin : Nat`。
- 审校数据和经验校准证书。

### 输出

- `classifyRight : X -> Tri`。
- `classifyEvil : X -> Tri`。
- 可选：统一输出 `right / evil / mixed / unknown` 的有限枚举。

### 可验证 predicate

```lean
def RightByThreshold (x : X) : Prop :=
  rightCut <= rightScore x ∧
  evilScore x + margin < evilCut ∧
  ThresholdDataAudited x

def EvilByThreshold (x : X) : Prop :=
  evilCut <= evilScore x ∧
  rightScore x + margin < rightCut ∧
  ThresholdDataAudited x

def ThresholdConflict (x : X) : Prop :=
  rightCut <= rightScore x ∧ evilCut <= evilScore x
```

冲突和灰区必须输出 `unk` 或显式 `mixed`，不得强行二分。

### 需要的数据

- 标注样本和审校记录。
- 正/邪分数计算规则。
- 阈值选择记录、版本、校准集表现。
- false positive / false negative 容忍目标。
- 灰区、冲突、缺失数据处理规则。

### Lean 可落地的最小接口

```lean
structure ThresholdInterface where
  X : Type
  rightScore : X -> Nat
  evilScore : X -> Nat
  rightCut : Nat
  evilCut : Nat
  margin : Nat
  audited : X -> Prop
  classifyRight : X -> SSBX.Core.Tri
  classifyEvil : X -> SSBX.Core.Tri
  right_top_sound :
    forall x, classifyRight x = SSBX.Core.Tri.top -> RightByThreshold x
  evil_top_sound :
    forall x, classifyEvil x = SSBX.Core.Tri.top -> EvilByThreshold x
  conflict_not_top :
    forall x, ThresholdConflict x ->
      classifyRight x ≠ SSBX.Core.Tri.top ∧
      classifyEvil x ≠ SSBX.Core.Tri.top
```

### 验收标准

- `thresholdProtocol` 可映射到该接口，且 sourceRef 非空。
- 样例对象覆盖 right、evil、conflict、unknown 四类。
- 冲突样例证明不能同时给 `classifyRight = top` 与 `classifyEvil = top`。
- 阈值版本可追溯到校准数据。

## 度期计算

### 形式输入

- 一个 `SSBX.Core.GammaProcess.Model`。
- 一个 `DaoCriteria M`，沿用现有字段 `Path / relevant / canContinue / badAt`。
- 当前场 `g : M.Gamma`。
- 路径 `p : D.Path`。
- 候选度 `d : M.Degree` 与候选期 `t : M.Horizon`。
- 经验校准和审校证书。

### 输出

- `relevance : g -> p -> d -> t -> Tri`。
- `cycle : g -> p -> d -> t -> Tri`，表示该度期窗口内可续且不坏。
- 可选：`bestScope : g -> p -> Option (M.Degree × M.Horizon)`。

### 可验证 predicate

```lean
def RelevantDegreePeriod
    (M : SSBX.Core.GammaProcess.Model)
    (D : SSBX.Core.GammaProcess.DaoCriteria M)
    (g : M.Gamma) (p : D.Path) (d : M.Degree) (t : M.Horizon) : Prop :=
  D.relevant g p d t

def DegreePeriodContinues
    (M : SSBX.Core.GammaProcess.Model)
    (D : SSBX.Core.GammaProcess.DaoCriteria M)
    (g : M.Gamma) (p : D.Path) (d : M.Degree) (t : M.Horizon) : Prop :=
  D.relevant g p d t ∧
  D.canContinue g p d t ∧
  ¬ D.badAt g p d t
```

这直接对齐 `TrueDao` 中“相关范围 + 可续 + 非坏”的结构。

### 需要的数据

- 时间窗、尺度、采样频率、缺测规则。
- 路径或行动序列的状态 trace。
- 相关性标注或计算规则。
- 可续/坏点判断所需的 outcome 数据。
- 校准证书和审校证书。

### Lean 可落地的最小接口

```lean
structure DegreePeriodInterface
    (M : SSBX.Core.GammaProcess.Model)
    (D : SSBX.Core.GammaProcess.DaoCriteria M) where
  relevance :
    M.Gamma -> D.Path -> M.Degree -> M.Horizon -> SSBX.Core.Tri
  cycle :
    M.Gamma -> D.Path -> M.Degree -> M.Horizon -> SSBX.Core.Tri
  relevance_top_sound :
    forall g p d t,
      relevance g p d t = SSBX.Core.Tri.top ->
      D.relevant g p d t
  cycle_top_sound :
    forall g p d t,
      cycle g p d t = SSBX.Core.Tri.top ->
      D.relevant g p d t ∧
      D.canContinue g p d t ∧
      ¬ D.badAt g p d t
```

### 验收标准

- 可用一个 finite `Gamma / Path / Degree / Horizon` 小模型跑通。
- `cycle_top_sound` 可作为候选真道条件定理的前提。
- 缺少 relevant witness 时返回 `unk`。
- 同一数据版本下输出确定；更换窗口或尺度会生成新 certificate。

## 开势投影

### 形式输入

- 一个 `SSBX.Core.GammaProcess.Model`。
- `OpenCriteria M`。
- 当前场 `g : M.Gamma`。
- 可行间 `i : IntervalDomain M g`。
- 投影期 `t : M.Horizon` 或有限 future trace。
- 经验校准、度期计算和审校证书。

### 输出

- `projectOpen : (g : M.Gamma) -> IntervalDomain M g -> Tri`。
- 可选：投影分数 `openScore : ... -> Nat` 和主要 witness，例如 `Tendency M g`、`Opportunity M C g`、`Open M C (step M g i)`。

### 可验证 predicate

```lean
def OpenProjectionSound
    (M : SSBX.Core.GammaProcess.Model)
    (C : SSBX.Core.GammaProcess.OpenCriteria M)
    (g : M.Gamma)
    (i : SSBX.Core.GammaProcess.IntervalDomain M g) : Prop :=
  SSBX.Core.GammaProcess.Open M C (SSBX.Core.GammaProcess.step M g i) ∧
  (SSBX.Core.GammaProcess.Tendency M g ∨
   SSBX.Core.GammaProcess.Opportunity M C g)
```

若实际实现只能投影到有限 horizon，应把 predicate 改为 `OpenWithinTrace`，并显式给出 trace witness；不要把有限投影冒称为无限未来真。

### 需要的数据

- 当前状态和可行间集合。
- `historicalLaw / openLaw / validInterval` 的实例数据。
- `weight / coupling / grid` 的校准值。
- future trace、模拟配置或观测后验。
- 度期窗口和审校证书。

### Lean 可落地的最小接口

```lean
structure OpenProjectionInterface
    (M : SSBX.Core.GammaProcess.Model)
    (C : SSBX.Core.GammaProcess.OpenCriteria M) where
  projectOpen :
    (g : M.Gamma) ->
    SSBX.Core.GammaProcess.IntervalDomain M g ->
    SSBX.Core.Tri
  top_sound :
    forall g i,
      projectOpen g i = SSBX.Core.Tri.top ->
      OpenProjectionSound M C g i
```

### 验收标准

- 对至少一个 finite process 证明 `top_sound`。
- 若 `i` 非 valid interval，Lean 类型层无法调用 `projectOpen`。
- 投影结论必须带 horizon 或 trace 版本号。
- 只证明“模型内投影 sound”，不把经验未来直接写成无条件 theorem。

## 邪续

### 形式输入

- 一个 `SSBX.Core.GammaProcess.Model`。
- `OpenCriteria M` 和价值/阈值接口。
- trace 域 `Trace : Type`。
- `states : Trace -> List M.Gamma`。
- 每个窗口或状态的邪判定 `evilAt : Trace -> Nat -> Tri`。
- 持续窗口下界 `minWindows : Nat`。
- 审校数据、正邪阈值、度期计算和开势投影证书。

### 输出

- `evilContinuation : Trace -> Tri`。
- 可选：导致邪续的窗口 witness 列表。

### 可验证 predicate

```lean
def EvilWindow (tau : Trace) (n : Nat) : Prop :=
  evilAt tau n = SSBX.Core.Tri.top

def EvilPersists (tau : Trace) : Prop :=
  ∃ ns : List Nat,
    ns.length >= minWindows ∧
    ns.Nodup ∧
    forall n, n ∈ ns -> EvilWindow tau n

def EvilContinuation (tau : Trace) : Prop :=
  TraceAudited tau ∧
  EvilPersists tau ∧
  ¬ TraceHasDefeater tau
```

若还要连接 `闭 / 夺 / 伪 / 偏`，可增加：

```lean
def EvilContinuationStrong (tau : Trace) : Prop :=
  EvilContinuation tau ∧
  ∃ n, ClosesOrTakesOrFalsifies tau n
```

### 需要的数据

- 跨期状态 trace、行动日志、outcome 日志。
- 每个窗口的正/邪分数和阈值版本。
- 反证或人工复核记录。
- 与开势投影的对照：哪些行动持续压低可开性或扩大闭合。
- 最小持续期 `minWindows` 的经验校准依据。

### Lean 可落地的最小接口

```lean
structure EvilContinuationInterface where
  Trace : Type
  minWindows : Nat
  evilAt : Trace -> Nat -> SSBX.Core.Tri
  audited : Trace -> Prop
  hasDefeater : Trace -> Prop
  evilPersists : Trace -> Prop
  evilContinuation : Trace -> SSBX.Core.Tri
  persists_sound :
    forall tau,
      evilPersists tau ->
      ∃ ns : List Nat,
        ns.length >= minWindows ∧
        ns.Nodup ∧
        forall n, n ∈ ns -> evilAt tau n = SSBX.Core.Tri.top
  top_sound :
    forall tau,
      evilContinuation tau = SSBX.Core.Tri.top ->
      audited tau ∧ evilPersists tau ∧ ¬ hasDefeater tau
```

### 验收标准

- 单点邪判定不能推出 `邪续`；必须有 `minWindows` 个独立窗口。
- 有 defeat record 时输出不得为 `top`。
- 可构造一个正例 trace 和一个反例 trace，分别证明 top sound 与 not-top。
- 与 `正邪阈值` 共用同一阈值版本，避免“邪续”另设未登记标准。

## 汇总验收

6 个接口全部落地时，至少需要这些共同验收条件：

- 所有新增 Lean 文件无 `sorry`，且不增加全局 axiom；必要经验承诺只经 ledger 字段进入。
- `top`/`bot` 都有 soundness theorem；缺数据必须走 `unk`。
- 每个接口有一个 finite fixture，可用 `native_decide` 或普通 theorem 检查。
- 经验数据有 schema、版本、hash/sourceRef、审校结论。
- `Roster.lean` 中 `PendingName` 不在同一 PR 内改变 kind；若未来要升级名册状态，应另开变更并同步 `Truth/ClaimLedger`。

## 改动文件

- `formal/SSBX/notes/pending-interfaces.md`

## 2026-05-07 有限样例实例

本轮新增 `formal/SSBX/Pending/Examples.lean`，只实例化有限 toy 数据，不改变
`PendingName` 的名册状态，也不把样例解释成外部世界事实。样例状态由
`SSBX.Pending.Examples.statusOf` 明确覆盖 6 个 pending name：

- `审校数据 / auditData`：已实例化。`ToyAudit` 给出 3 条记录、3 个来源、
  3 个 claim；`stable` 由两个独立来源支持且无 defeat，`defeated` 有 defeat
  witness，`thin` 因无有效输入返回 `unk`。
- `经验校准 / calibration`：已实例化。`ToyCalibration` 给出训练、验证、过期、
  未审校四类 evidence；`train/valid` 满足误差上界与审校条件，`train/stale`
  证明为 `bot`，未审校输入返回 `unk`。
- `正邪阈值 / threshold`：已实例化。`ToyThreshold` 覆盖 right、evil、conflict、
  unknown 四类对象；冲突对象证明 right/evil 两侧都不能返回 `top`。
- `度期计算 / degreePeriod`：本轮明确保留为条件接口，只给
  `Conditional.degreePeriod_cycle_top`，即给定接口实例和 `top` 输出时可推出
  `relevant ∧ canContinue ∧ ¬ badAt`。
- `开势投影 / openProjection`：本轮明确保留为条件接口，只给
  `Conditional.openProjection_top`，即给定接口实例和 `top` 输出时可推出
  `OpenProjectionSound`。
- `邪续 / evilContinuation`：本轮明确保留为条件接口，只给
  `Conditional.evilContinuation_top`，即给定接口实例和 `top` 输出时可推出
  `audited ∧ EvilPersists ∧ ¬ hasDefeater`。

证明方向复核：三个已实例化接口都沿用 `Interfaces.lean` 的方向，即
`run x = top/bot -> predicate/¬predicate`；缺少有效输入由
`unknown_on_invalid` 约束为 `unk`。这避免了从 toy 数据无条件推出外部经验事实。

验证命令：

```bash
/Users/ren/.elan/bin/lake build SSBX.Pending.Examples
```
