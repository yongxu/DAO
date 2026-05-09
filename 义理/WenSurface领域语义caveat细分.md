# WenSurface 领域语义 caveat 细分

**范围**：本文细分原 `projection-anchor`、`pair-carrier`、`duplicate-facet / aggregate / list` 三大类 domain caveat。它们已经是 exact theorem-backed executable mechanics；这里讨论的是如何从 carrier/anchor 升级成真正领域语义与领域律。

**当前来源**：

```bash
./.lake/build/bin/wenyan-surface --coverage
./.lake/build/bin/wenyan-surface --operators projection-anchor
./.lake/build/bin/wenyan-surface --operators pair-carrier
./.lake/build/bin/wenyan-surface --operators duplicate-facet
./.lake/build/bin/wenyan-surface --operators singleton-aggregate
./.lake/build/bin/wenyan-surface --operators binary-aggregate
./.lake/build/bin/wenyan-surface --operators ternary-aggregate
./.lake/build/bin/wenyan-surface --operators list-projection
```

## 第一批执行计划

第一批执行 `W1 SpatialFrame`、`W7 PairRelationCore`、`W9 AggregateCore` 三个工作包，共关闭 `55` 个 domain caveat。第二批执行 `W2 AspectFrame`，再关闭 `22` 个文法 / 时态 / 副词相位 projection caveat。第三批执行 `W3 NameObjectFrame` 的 projection anchor 子集，再关闭 `18` 个名物 / 本体 / 方法 accessor caveat。第四批执行 `W4 MedicineFrame` 的 projection anchor 子集，再关闭 `14` 个医家生理 / 诊断 / 历气 accessor caveat。第五批执行 `W6 DivinationCognitionFrame` 的 projection anchor 子集，再关闭 `10` 个占候 / 认知 / 庄楚 accessor caveat。第六批执行 `W5 InstitutionFrame` 的 projection anchor 子集，再关闭 `27` 个史书 / 法家 / 儒礼 / 兵家 / 杂家 accessor caveat。第七批执行 pair relation 四分法：`directed`、`naming/measure`、`protocol`、`Zhuangzi`，再关闭 `58` 个 pair caveat。第八批执行剩余窄 carrier law：identity/no-op、application wrapper、predicate anchor、truth marker，再关闭 `45` 个 caveat。合并后剩余 caveat 数为 `0`。

精确数量变化如下：

| 类别 | 合并前 | 第一批后 | 第二批后 | 第三批后 | 第四批后 | 第五批后 | 第六批后 | 第七批后 | 第八批后 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| projection anchors | 100 | 91 | 69 | 51 | 37 | 27 | 0 | 0 | 0 |
| pair carriers | 67 | 58 | 58 | 58 | 58 | 58 | 58 | 0 | 0 |
| duplicate-facet / singleton-aggregate / binary-aggregate / ternary-aggregate / list-projection | 13 / 17 / 2 / 4 / 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| identity / application / predicate / truth | 20 / 12 / 9 / 4 | 20 / 12 / 9 / 4 | 20 / 12 / 9 / 4 | 20 / 12 / 9 / 4 | 20 / 12 / 9 / 4 | 20 / 12 / 9 / 4 | 20 / 12 / 9 / 4 | 20 / 12 / 9 / 4 | 0 |

当前已登记 typed domain laws：`249`。当前剩余 domain caveats：`0`。

## 总览

| 大类 | 数量 | 当前 mechanics | 升级目标 |
|---|---:|---|---|
| projection anchors | 100 | `Hex -> Hex` / anchor projection | 为每组建立领域 record / accessor / invariant |
| pair carriers | 67 | 二元 exact carrier | 区分 relation、transition、protocol、naming、domain relation |
| aggregate / facet / list | 37 | singleton / binary / ternary / duplicate / head | 建立 collection、facet、aggregate law |

这些 `204` 个不建议逐个 ad hoc 消 caveat。更稳的路线是先补少数共用接口，再把算子批量挂到接口上。

## Projection Anchors：100

projection anchor 的共同问题是：现在可执行，但“投影到什么领域字段”还没有被形式化。优先实现方式是定义小型领域 frame，例如 `SpatialFrame`、`AspectFrame`、`NameObjectFrame`、`MedicineFrame`，每个 projection anchor 对应一个 accessor，并补 accessor law。

| 子类 | 数量 | 算子 | 需要的领域接口 |
|---|---:|---|---|
| 几何 / 结构 / 端点基础 | 9 | `R-5`; `C-4`, `C-5`, `C-6`, `C-7`, `C-8`; `B-1`, `B-2`, `B-7` | center / inside / outside / surface / interior / begin / end / extreme |
| 文法 / 时态 / 副词相位 | 22 | `S-9`, `S-10`, `S-11`, `S-12`, `S-13`, `S-14`, `S-16`, `S-17`, `S-18`; `A-1`, `A-2`, `A-3`, `A-7`, `A-8`, `A-9`, `A-10`, `A-15`, `A-16`, `A-17`, `A-18`, `A-19`, `A-20` | aspect / tense / nominalizer / marker / frequency / intensity |
| 本体 / 方法 / 名物 | 18 | `H-1`, `H-2`, `H-3`, `H-4`, `H-6`, `H-7`; `P-2`, `P-6`, `P-7`, `P-10`, `P-12`, `P-18`, `P-19`, `P-21`, `P-24`; `G-2`, `G-4`, `G-5` | dao / principle / tendency / mechanism / image / name / object / reality / place / kind |
| 史书 / 春秋褒贬 | 7 | `E-1`, `E-4`, `E-5`, `E-6`, `E-7`, `E-8`, `E-9` | textual record / taboo / critique / approval / deletion / writing / praise-blame |
| 法家 / 制度测度 | 3 | `L-3`, `L-12`, `L-15` | power / interest / measure |
| 医家 / 占候生理 | 14 | `Y-6`, `Y-7`, `Y-8`, `Y-10`, `Y-11`, `Y-12`, `Y-13`, `Y-14`, `Y-15`, `Y-23`, `Y-24`, `Y-25`, `Y-26`, `Y-27` | qi / blood / essence / rise-fall / open-close-pivot / channel / exterior-interior / cold-heat / deficiency-excess / free-stagnant / calendar-candidate / diagnosis |
| 儒礼 / 性化 | 6 | `X-1`, `X-3`; `LIJ-4`, `LIJ-5`, `LIJ-7`, `LIJ-11` | nature / acquired transformation / ritual position / ritual form / centrality / solitude |
| 占候 / 认知 / 庄楚 | 10 | `Z-23`, `Z-24`, `Z-26`, `Z-27`, `Z-34`, `Z-35`, `Z-38`; `ZHU-9`, `ZHU-10`; `CHU-4` | sprout / omen / divination / observation / inspection / realization / heavenly principle / direction / ascent |
| 兵家 | 6 | `SUN-1`, `SUN-3`, `SUN-4`, `SUN-5`, `SUN-7`, `SUN-8` | formation / empty / full / irregular / indirect / direct |
| 杂家 / 内业 / 月令 | 5 | `ZA-3`, `ZA-5`, `ZA-6`, `ZA-7`, `ZA-11` | heart-ruler / essence / season-time / ordinance / supervision |

**推荐实现批次**：

1. `SpatialFrame`：先关几何 / 结构 / 端点基础 9 个。
2. `AspectFrame`：再关文法 / 时态 / 副词相位 22 个。
3. `NameObjectFrame`：统一本体、墨经、名家 18 个。
4. `MedicineFrame`：医家 14 个单独一批，避免和礼法、兵家抢接口。
5. `InstitutionFrame`：史书、法家、儒礼、兵家、杂家合并或分批，共 27 个。
6. `DivinationCognitionFrame`：占候、认知、庄楚 10 个。

## Pair Carriers：67

pair carrier 的共同问题是：现在只是能接两个值的 exact carrier，尚未说明这两个值之间是什么领域关系。它们应分成五种接口，而不是一个“大 Pair”。

| 子类 | 数量 | 算子 | 需要的领域接口 |
|---|---:|---|---|
| 通用配对 / 并置 / 合成 | 9 | `R-12`, `R-13`, `R-14`, `R-15`; `C-2`; `N-8`; `I-7`; `G-8`; `D-8` | pair / conjunction / inclusion / distinction / merge / remainder |
| 有向变换 / 因果 / 运动 | 29 | `T-3`, `T-11`; `K-5`; `H-5`; `P-8`; `L-2`; `Y-16`, `Y-19`, `Y-28`; `X-2`, `X-13`, `X-15`; `Z-20`, `Z-25`, `Z-28`; `ZHU-6`, `ZHU-7`, `ZHU-8`; `SUN-2`, `SUN-9`, `SUN-10`, `SUN-11`, `SUN-13`; `CHU-1`, `CHU-3`, `CHU-5`, `CHU-6`, `CHU-7`; `ZA-10` | directed edge / transform / influence / treatment / learning / strategy / return |
| 名言 / 度量 / 指称关系 | 8 | `P-11`, `P-13`, `P-22`; `G-1`, `G-7`, `G-11`; `E-2`, `E-3` | measure relation / circular relation / explanation / designation / separation / naming / saying |
| 规范 / 制度 / 礼法协议 | 17 | `L-1`, `L-8`, `L-16`; `X-7`, `X-10`; `LIJ-1`, `LIJ-2`, `LIJ-3`, `LIJ-8`, `LIJ-10`, `LIJ-12`, `LIJ-13`, `LIJ-14`; `SUN-14`; `CHU-8`; `ZA-1`, `ZA-8` | rule / appointment / reward-punishment / righteousness / rank-degree / ritual ordering / self-watch / knowledge / emptiness / present-check |
| 庄子专属关系 | 4 | `ZHU-3`, `ZHU-4`, `ZHU-11`, `ZHU-12` | free wandering / forgetting / mirroring-response / trap-to-catch relation |

**推荐实现批次**：

1. `PairRelationCore`：先关通用配对 / 并置 / 合成 9 个。
2. `DirectedRelation`：处理有向变换 / 因果 / 运动 29 个；这批可再按医家、兵家、楚辞拆给不同 agents。
3. `NamingMeasureRelation`：处理名言 / 度量 / 指称 8 个。
4. `ProtocolRelation`：处理规范 / 制度 / 礼法协议 17 个。
5. `ZhuangziRelation`：庄子 4 个单独做，避免把“忘 / 镜 / 筌”硬塞进一般制度关系。

## Aggregate / Facet / List：37

这批的共同目标是把“carrier constructor”升级为 collection / facet / aggregate 的小代数。它们最适合先实现一套通用接口，再把各领域解释挂上去。

| 子类 | 数量 | 算子 | 需要的领域接口 |
|---|---:|---|---|
| 双面 / 二分 facet | 13 | `H-8`; `G-9`; `D-4`; `L-6`; `Y-1`, `Y-21`, `Y-22`; `X-5`, `X-8`, `X-12`; `ZHU-5`; `SUN-12`; `ZA-4` | facet pair / complementary aspects / partition |
| singleton collection | 17 | `P-3`; `L-5`, `L-13`, `L-14`; `Y-2`, `Y-9`; `X-4`, `X-6`, `X-9`; `Z-7`, `Z-16`, `Z-17`, `Z-21`, `Z-30`; `CHU-9`; `ZA-9`, `ZA-12` | singleton / set seed / institutional unity / gathered collection |
| binary aggregate | 2 | `X-14`, `Z-19` | binary fold / accumulation |
| ternary aggregate | 4 | `X-11`, `X-16`, `ZHU-2`, `CHU-2` | ternary composition / transform / teaching / wandering / seeking |
| list projection | 1 | `Z-18` | head / decomposition / scatter |

**更细实现拆分**：

| 实现块 | 数量 | 算子 | 建议 |
|---|---:|---|---|
| `Facet2` 核心 | 6 | `H-8`, `D-4`, `L-6`, `Y-1`, `Y-21`, `Y-22` | 先定义二面、互补、可取左/右 |
| 社会 / 名分 partition | 6 | `G-9`, `X-5`, `X-8`, `X-12`, `SUN-12`, `ZA-4` | 在 `Facet2` 上补 domain label：名分、分合、官分 |
| 特殊 self facet | 1 | `ZHU-5` | 单独处理“丧己”，不要强行等同普通二分 |
| collection seed | 8 | `P-3`, `X-4`, `Z-7`, `Z-16`, `Z-17`, `Z-21`, `Z-30`, `CHU-9` | `singleton` + membership law |
| institutional aggregate | 7 | `L-5`, `L-13`, `L-14`, `X-6`, `X-9`, `ZA-9`, `ZA-12` | 法令统一、礼制、统调都需要 collective invariant |
| medical / cosmological aggregate | 2 | `Y-2`, `Y-9` | 五行、神应作为 sealed finite family |
| fold / ternary / projection | 7 | `X-14`, `Z-19`, `X-11`, `X-16`, `ZHU-2`, `CHU-2`, `Z-18` | 实现 fold2、fold3、head/split laws |

## 建议并发切块

这些分组之间依赖很少，适合并行：

| 工作包 | 范围 | 依赖 |
|---|---|---|
| W1 SpatialFrame | projection 9 | 无 |
| W2 AspectFrame | projection 22 | 无 |
| W3 NameObjectFrame | projection 18 + pair naming 8 | 无 |
| W4 MedicineFrame | projection 14 + pair medicine 3 + facet/aggregate medicine 4 | `Facet2` 可选 |
| W5 InstitutionFrame | projection 27 + protocol pair 17 + institutional aggregate 7 | `PairRelationCore` 可选 |
| W6 DivinationCognitionFrame | projection 10 + directed divination pair 3 + collection seed 部分 | 无 |
| W7 PairRelationCore | pair generic 9 | 无 |
| W8 DirectedRelation | pair directed 29 | `PairRelationCore` 可选 |
| W9 AggregateCore | aggregate/facet/list 37 | 无 |
| W10 ZhuangziRelation | ZHU pair 4 + ZHU facet 1 + ZHU projection 2 + ZHU ternary 1 | `AggregateCore` 可选 |

## 验收口径

每个工作包完成时，至少应满足：

1. 对应 operator 仍是 exact theorem-backed executable。
2. caveat 不再只是 `projection-anchor` / `pair-carrier` / `carrier-constructor`，而能指向具体 domain law。
3. CLI 的 `--operator <ID>` 能显示该算子的领域语义状态。
4. 不把领域解释伪装成 Hex 文档语义；需要有 Lean 层 definition 或 theorem anchor。
5. 计数保持可审计：从原 `domain caveats: 249` 中移出的数量要能由 theorem 或 registry entry 复核。
