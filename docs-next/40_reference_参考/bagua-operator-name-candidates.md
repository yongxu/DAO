# 八卦算子命名候选表

> 校对状态：工作稿。Lean 事实以 `formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`、`formal/SSBX/Foundation/Bagua/Cell192.lean`、`formal/SSBX/Text/OperatorAnchors.lean`、`formal/SSBX/Text/OperatorInstructionSemantics.lean` 为准。

## 当前结论

- T3 三个生成元 default 采用 `改 / 化 / 变`，与 WenDef exact surface 以及 `BaguaAlgebra.dong/hua/bian` 对齐。
- `动 / 動` 保留为 T3 生成元家族 alias；裸 `动` 不直接落到某个坐标，需上下文或写成 `动初 / 动中 / 动上`。
- 代数 identity default 采用 `恒`；L0 `.nop` 单字 default 采用 `静`，并保留 `恒/守/定/常/止/安/寂/息/平/和` 等 alias。
- T3 八卦对象名和模式字是两层：值 literal 仍是 `乾/兑/...`；若讨论 operator/mode default，则采用当前 `JianMode` 字：`生/开/显/元/申/塞/居/守`。
- `pathFromTo` default 改为 `径`。它在 glyph registry 里出现过，但当前没有发现 `OperatorReadings` 中的直接读法冲突；它比 `变径` 更干净。
- `cuoZong` 的短名候选仍可审 `交`，但 `交` 已有 Z-4 泛交互读法；当前实现不抢单字 `交`，先接 `错综/錯綜/综错/綜錯` exact aliases。
- `transform / hexTransform` default 改为 `达`；`FlipCombo.apply` 文档 default 改为 `群`。
- 纵向投影 default 改用 `略上 / 略中 / 略下`。`省上 / 省中 / 省下` 和 `合上 / 合中 / 合下` 保留为 alias。
- L0 current tokens 不是最终命名承诺；`不动/设时/翻爻/比爻/比时` 均列单字候选。
- 下表边界是“八卦 / 六爻 / Cell192 / L0 指令锚点”的完整命名校对表，不替代 371 通用 operator catalogue。

## 当前代码落地口径

- 已接 WenSurface executable aliases：`恒/静/靜/定/常/安/寂/息` identity；`错综/錯綜/综错/綜錯/反覆/反复/交错/交錯` cuoZong；`动初/初动/动中/动二/承变/中化/动上/动三/际变/内极` 等内三爻 exact flip；`复/復/归一/归极/总归/复归` return-to-root identity；`展/展开` extension。
- 已接 L0 parser aliases：`.nop` 可写 `静/一/正/立/成/...`；`.setShi` 可写 `置 今`；`.flipYao` 可写 `翻 三爻`；branch 可写 `侔 ... 至 ...` / `会 今 至 ...`。canonical printer 仍输出旧 token。
- 已接第 50 卦 default：`器` 与 alias `鼎` 都读同一卦；`鼎` 仍保留 unpromoted gap 诊断，`鼎 乾` 不会偷接 operator 语义。
- 未接为 runtime alias：`达/径/群/隙` 等 path/transform/group/distance 候选，以及 `空/判/析/编/周/略上` 等纵向层级名；这些需要新 codomain 或 primitive，不能用 catalogue carrier shape 冒充 exact evaluator。

## 完整校对主表

覆盖口径：8 个 T3 值/模式锚点、11 个 T3 横向/判别函数、14 个 T3 纵向/生成函数、16 个 T6/Cell192 函数或命名上下文、12 个 L0 指令锚点。总计 61 行校对项。

### T3 八卦值与模式锚点

这 8 行同时记录两个不同层级：`乾/兑/...` 是八卦值 literal；`生/开/...` 是 `JianMode` 的 operator/mode default。之前把二者放在 `当前 default / 当前模式字` 两列里，容易误读。若要写“八卦值”，default 应是卦名；若要写“模式算子”，default 应是模式字。

| Lean anchor | 卦值 literal | 模式 default | 后备/别名 | 其他范式候选 | 校对备注 |
|---|---:|---:|---|---|---|
| `Trigram.qian` | `乾` | `生` | 健 / 天 / 元 | 形式：源；儒：健；道：生 | `生`已有算子义；在 mode context 可作 default。 |
| `Trigram.dui` | `兑` | `开` | 悦 / 泽 | 象数：悦；气机：开 | `开`适合作 mode default，`悦`作卦象 alias。 |
| `Trigram.li` | `离` | `显` | 丽 / 附 / 明 | 儒：明；佛：照；术数：火 | `丽`与 30 卦冲突；mode 用`显`更稳。 |
| `Trigram.zhen` | `震` | `元` | 动 / 雷 / 起 | 象数：动；气机：升 | `动`不能抢 T3 flip default；mode 仍用`元`。 |
| `Trigram.xun` | `巽` | `申` | 入 / 风 / 顺 | 儒：顺；术数：风 | `入`有边界/气机冲突；mode 用`申`。 |
| `Trigram.kan` | `坎` | `塞` | 险 / 水 / 陷 | 象数：险；中医：藏 | `险`可作值 alias，不做 transform。 |
| `Trigram.gen` | `艮` | `居` | 止 / 山 / 定 | 儒：止；道：静 | `止`已有 identity/stabilize 读法；mode 用`居`。 |
| `Trigram.kun` | `坤` | `守` | 顺 / 地 / 承 | 儒：顺承；道：藏 | `守`可解释坤德，也可作 identity alias。 |

### T3 横向变换与判别

| 层 | Lean/current | theorem-backed meaning | 当前 default | 保留 alias | 后备候选（范式来源） | 校对备注 |
|---|---|---|---:|---|---|---|
| T3 | identity / L0 `.nop` | no state change | `恒` | 静 / 靜 / 不动 / 守 / 定 / 常 / 止 / 安 / 寂 / 息 / 平 / 和 / 一 / 正 / identity | 常（道家）/ 一（代数）/ 定（术数） | `恒`最适合代数 identity；L0 no-op 可用`静`。 |
| T3 | `dong` / Hex `flip1H` | flip bottom yao | `改` | 动 / 動 / 动初 / 動初 / 初变 / 翻初 | 起（始位）/ 初动（筮法）/ 革（义理） | 已有 exact surface `改`，位置 alias 用`初`补足。 |
| T3 | `hua` / Hex `flip2H` | flip middle yao | `化` | 动中 / 動中 / 中变 / 翻中 | 交（中介）/ 通（通变）/ 承化（义理） | `化`自然，但裸字在儒道语境宽。 |
| T3 | `bian` / Hex `flip3H` | flip top yao | `变` | 动上 / 動上 / 上变 / 翻上 | 成（终位）/ 应（上应）/ 极变（六爻类推） | `变`可指整体变卦，需 type/context 消歧。 |
| T3 | `Trigram.cuo` | flip all three yao | `错` | 錯 / 反 / 旁通 / 对待 | 反（道家）/ 对（先天图式）/ 易（形式互补） | `反`歧义大，只作 alias。 |
| T3 | `Trigram.zong` | reverse yao order | `综` | 綜 / 覆 / 倒 / 转 | 覆（象数）/ 倒（直观）/ 旋（几何） | `综`优于`转`，传统名更准。 |
| T3 | `cuoZong` | `错 ∘ 综` | `错综` | 錯綜 / 综错 / 綜錯 / 自反 / 反自 / 交 / 反覆 | 交（义理）/ 复合（形式） | `交`简洁但已有 Z-4 泛交互读法；当前实现先用复词 exact alias，单字`交`待 resolver 支持 arity/context 后再审。 |
| T3 | `transform a b` | direct transform from a to b | `达` | 通变 / 互通 / 至 / 贯 | 达（儒）/ 迁（变化）/ 贯（形式） | `达`表示由此至彼，比`通变`更适合单字。 |
| T3 | `pathFromTo` | shortest flip path | `径` | 路 / 程 / 轨 / 途 / 道 / 变径 | 途（筮法）/ 轨（形式）/ 历（过程） | `径`在 glyph registry 出现过，但当前无 direct reading 冲突。 |
| T3 | `hammingDist` | differing yao count | `隙` | 度 / 距 / 差 / 殊 / 隔 / 间 | 度（量化）/ 隙（象数） | `隙`更像两卦之间的差隙；`度`留给 Hex distance。 |
| T3 | `FlipCombo.apply` | one of 8 flip-group actions | `群` | 变组 / 八变 / 卦变 / 变类 | 群（形式）/ 局（术数） | `群`是形式代数好字，但已有 X-4 荀子群义。 |

### T3 纵向、生成、复合

| 层 | Lean/current | theorem-backed meaning | 当前 default | 保留 alias | 后备候选（范式来源） | 校对备注 |
|---|---|---|---:|---|---|---|
| T3→T2 | `heShang` | drop top yao, keep bottom+middle | `略上` | 省上 / 去上 / 阙上 / 合上 / 取下二 / 留下二 / 舍上 / 截上 | 略上（文献）/ 舍上（义理）/ 截上（图形） | `略`表达 omit，比`省`更口语少义；二者都可保留。 |
| T3→T2 | `heZhong` | drop middle yao, keep bottom+top | `略中` | 省中 / 去中 / 阙中 / 合中 / 取初上 / 留初上 / 舍中 / 截中 | 略中 / 舍中 / 截中 | `中`单字冲突大，必须组合。 |
| T3→T2 | `heXia` | drop bottom yao, keep middle+top | `略下` | 省下 / 去下 / 阙下 / 合下 / 取上二 / 留上二 / 舍下 / 截下 | 略下 / 舍下 / 截下 | `下`单字不能独立 promotion。 |
| T2→T1 | `heToYi` | four-images to one yao | `约` | 合仪 / 合一 / 归仪 / 省二 | 约（形式）/ 归（道家） | `约`表达 contraction/reduction，比`合仪`适合单字。 |
| T1→T0 | `heToTaiji` | forget to Unit | `空` | 归极 / 归一 / 归太极 / 合极 | 空（佛学）/ 复（道家） | `空`适合 forget-to-unit，但佛学色彩强。 |
| T3→T0 | `guiyi` | collapse any trigram to TaiJi | `复` | 归一 / 归极 / 总归 / 复归 | 复（道家）/ 会（儒） | `复`已有 T-7/24 卦读法，需 context。 |
| T0→T1 | `fenToYi` | introduce one yao | `判` | 分仪 / 生仪 / 分阴阳 | 判（形式）/ 开（道家） | `判`表示太极判为阴阳，单字可读。 |
| T1→T2 | `fenToSiXiang` | introduce second yao | `析` | 分象 / 生象 / 四象 | 析（形式）/ 衍（义理） | `析`比`分象`更适合单字。 |
| T2→T3 | `fenToTrigram` | introduce third yao | `展` | 分卦 / 生卦 / 成卦 | 展（形式）/ 演（义理） | `展`表示展开升维。 |
| T3×T3→T6 | `chong` | inner/outer combine to Hexagram | `乘` | 重卦 / 重 / 合卦 / 叠卦 | 乘（代数 product）/ 复（义理） | `乘`已有 R-10 乘凌/乘位读法，需 product context。 |
| hierarchy | `Sheng.step` | add a yao in hierarchy | `生` | 生生 / 递生 / 层生 | 衍（义理）/ 发（道家） | `生`已有多义，但作为 Sheng.step 很自然。 |
| Sheng 3 | `toTrigram` | depth-3 Sheng to Trigram | `显` | 成卦 / 入卦 / 归卦 | realize（形式）/ 显（象） | `显`已有 Z-9 manifest 语义，方向一致。 |
| Sheng 3 | `ofTrigram` | Trigram to depth-3 Sheng | `编` | 藏 / 载卦 / 藏卦 / 编卦 / 录 / 载 | encode（计算）/ 藏（道家） | `编`是好词：直指 encode/structure into Sheng，且当前未见 direct reading 冲突。 |
| cycle | `grandCycle` | TaiJi→Trigram→TaiJi | `周` | 大循环 / 周行 / 生生归一 / 循环 | 复（道家）/ 周（易传） | `周`适合 cycle，短而古。 |

### T6 / Hexagram / Cell192 层

| 层 | Lean/current | theorem-backed meaning | 当前 default | 保留 alias | 后备候选（范式来源） | 校对备注 |
|---|---|---|---:|---|---|---|
| T6 | identity / `hexIdBody` | Hex identity | `恒` | 静 / 靜 / 不动 / 正 / 守 / 定 / 常 / 止 / 安 / 寂 / 息 / 平 / 和 / 一 / 立 / 成 | 常 / 定 / 平 / 和 | 多个 catalogue alias 已接 identity，resolver 必须靠 type/context。 |
| T6 | `dongInner` / `Cell192.flip1` | flip yao 1 | `改` | 初变 / 动初 / 翻初 | 起 / 初动 | 与 T3 `改`对齐。 |
| T6 | `huaInner` / `Cell192.flip2` | flip yao 2 | `化` | 二变 / 承变 / 动二 | 承 / 中化 | `承`已用于爻翼 Y2，慎作 default。 |
| T6 | `bianInner` / `Cell192.flip3` | flip yao 3 | `变` | 三变 / 际变 / 动三 | 际 / 内极 | `三`先做数字，`际`可作后备。 |
| T6 | `dongOuter` / `Cell192.flip4` | flip yao 4 | 待定 | 近 / 四变 / 动四 / 交变 | 临 / 进 / 交 | 四爻名义未定；`近`可读但不够强。 |
| T6 | `huaOuter` / `Cell192.flip5` | flip yao 5 | 待定 | 主 / 五变 / 动五 / 君变 | 位 / 中 / 正 | 五爻可用`主`，但会与主体/主谓冲突，先待定。 |
| T6 | `bianOuter` / `Cell192.flip6` | flip yao 6 | `极` | 极变 / 上变 / 动上 / 终变 | 亢 / 穷 / 终 | `极`比`极变`更适合单字 default。 |
| T6 | `Hexagram.cuo` / `Cell192.hexCuo` | flip all six yao | `错` | 錯 / 反 / 旁通 | 对 / 反 / 易 | `错`最稳。 |
| T6 | `Hexagram.zong` / `Cell192.hexZong` | reverse six yao order | `综` | 綜 / 覆 / 倒 / 转 | 覆 / 旋 / 反覆 | `转`只作 alias。 |
| T6 | `Hexagram.hu` / `Cell192.hexHu` | mutual hexagram from middle four yao | `互` | 互卦 / 中互 / 交互 | 相 / 交 / 中 | `互`已 theorem-backed exact。 |
| T6 | `cuoZongBody` | cuo then zong on Hex | `错综` | 錯綜 / 综错 / 綜錯 / 自反 / 反自 / 交 | 反覆 / 交错 | `交`与 Z-4 冲突；当前实现保留`交`原读法，复词 aliases 走 exact cuoZong。 |
| T6 | `hexTransform a b` | direct transform between hexagrams | `达` | 通变 / 互通 / 至 / 贯 | 迁 / 通 / 往 | 与 T3 transform 同名即可。 |
| T6 | `hexHammingDist` | differing yao count | `度` | 隙 / 距 / 差 / 殊 / 隔 / 数 / 间 | 隙 / 数 | `度`适合 Hex-level metric；与 L-15 法家度冲突需 metric context。 |
| Cell192 | `setShi` | set temporal cell state | `置` | 设时 / 置时 / 定时 | 已 / 今 / 未 | `设时`是当前 token，单字候选用`置`。 |
| Cell192 | time tags | cell temporal component | `已 / 今 / 未` | 往 / 见 / 将 | 过去 / 现在 / 未来 | 三时字目前稳定，但仍可审阅。 |
| Cell192 | `错格 / 综格 / 互格` | Cell-level form transform | `错格 / 综格 / 互格` | 错时格 / 综时格 / 互时格 | 格（术数/形式） | 当语境是 Cell192 时加`格`可消歧。 |

### L0 BaguaWen 指令锚点

L0 是受控 VM；下表不把现有 token 当最终冻结名，只记录当前 token 与可替换单字。`setShi sh` 不是 `设` 和 `时` 两个算子的组合，而是一个带参数的 primitive：它把当前 Cell192 的时间坐标改成 `sh : Shi`，保留 Hex 不变。`设/置` 是动作，“时”是被设置的维度。

| YiInstr kind | 当前 token | 单字 default 候选 | 语义层 | 是否 Cell endomap | 后备单字 | 冲突备注 |
|---|---:|---:|---|---|---|---|
| `.nop` | `不动` | `静` | current-cell | yes | 靜 / 恒 / 守 / 定 / 常 / 止 / 安 / 寂 / 息 / 平 / 和 / 一 / 正 | `静`用于 operational no-op 很自然；`恒`保留给代数 identity。 |
| `.setShi` | `设时` | `置` | current-cell | yes | 设 / 設 / 定 / 令 / 更 / 易 / 移 / 转 / 轉 / 调 / 調 / 时 / 時 | `置 今` 可读作 set current Shi to 今；`时`本身更像维度名。 |
| `.flipYao` | `翻爻` | `翻` | current-cell | yes | 动 / 動 / 变 / 變 / 易 / 改 / 反 / 转 / 轉 / 换 / 換 / 倒 / 更 | 参数化指令，不等于裸 `动`。 |
| `.hu` | `互` | `互` | current-cell | yes | 交 / 相 | 与 Hex exact 同名可接受。 |
| `.cuo` | `错` | `错` | current-cell | yes | 錯 / 反 | `反`不做 default。 |
| `.zong` | `综` | `综` | current-cell | yes | 綜 / 覆 / 转 | `综`优先。 |
| `.branchYaoEq` | `比爻` | `侔` | state/control | no | 比 / 校 / 同 | `侔`专指相等/相当，比裸`比`少冲突。 |
| `.branchShiEq` | `比时` | `会` | state/control | no | 侔 / 值 / 同 | `会`取“相会/正逢其时”，但需再查 catalogue。 |
| `.jump` | `跳` | `跳` | state/control | no | 跃 / 往 / 至 | VM 控制流专用。 |
| `.push` | `推` | `推` | state/control | no | 入 / 压 / 纳 | `推`在 surface 已有 Hex increment/application 读法。 |
| `.pop` | `取` | `取` | state/control | no | 出 / 脱 / 提 | `取`不宜作 projection default。 |
| `.halt` | `终` | `终` | state/control | no | 止 / 停 / 息 | `终/止`都有 catalogue 冲突，VM context 必须显式。 |

## 理论范式后备字库

这些字可以供人工挑选，但不自动 promotion。进入 resolver 前必须查重并指定 type/context。

| 范式 | 适合表达 | 可选字/短语 | 不建议直接 default 的点 |
|---|---|---|---|
| 形式代数 | identity, involution, product, projection, path, distance | 恒 / 一 / 逆 / 复合 / 投 / 积 / 径 / 隙 / 度 / 群 | 太现代的`群/投`只适合文档，不适合古文 surface。 |
| 象数易 | 动爻、变卦、错综互、重卦 | 动 / 变 / 错 / 综 / 互 / 重 / 之 / 往来 | `动`和`变`都需要坐标或目标类型。 |
| 爻辞 / 蓍筮 | 本卦、之卦、动爻、变爻 | 本 / 之 / 动 / 变 / 占 / 筮 / 爻 | `之`已是 application marker，不能轻改。 |
| 梅花 / 体用 | 本互变、体用关系 | 本 / 互 / 变 / 体 / 用 / 应 | `体/用`属于应用范式，不是 core transform。 |
| 先天图式 | 对待、互补、反复、定位 | 对 / 反 / 错 / 复 / 定 / 位 | `反`覆盖否定/逆/错，风险高。 |
| 后天图式 | 方位、流行、五行气化 | 东 / 南 / 西 / 北 / 中 / 流 / 行 | 方位名不应替代卦值或算子名。 |
| 纳甲 / 京房 | 世应、飞伏、六亲、卦气 | 世 / 应 / 飞 / 伏 / 纳 / 亲 / 气 | `应`和爻位关系冲突，另开 domain 表。 |
| 八宅 / 风水 | 宅命、星、方、吉凶 | 宅 / 命 / 星 / 生气 / 天医 / 绝命 | 吉凶星名不进入八卦 core。 |
| 奇门 / 九宫 | 宫、门、星、神、局 | 宫 / 门 / 星 / 神 / 局 / 飞 / 转 | 九宫移动不是 T3/T6 bit algebra。 |
| 儒家义理 | 改过、化成、中正、诚、守 | 改 / 化 / 正 / 中 / 诚 / 守 / 成 | 可作解释 alias，但 theorem meaning 仍是 flip/identity。 |
| 道家生成 | 生、化、反、复、归、常 | 生 / 化 / 反 / 复 / 归 / 常 / 玄 | `反`和`复`都多义；`常`可作`恒`后备。 |
| 佛学/玄学 | 空、缘、照、藏、转识 | 空 / 缘 / 照 / 藏 / 转 / 觉 | 目前不是 core 证明范式，只适合文档候选。 |
| 中医 / 气机 | 升降、出入、开阖枢、平和 | 升 / 降 / 出 / 入 / 开 / 阖 / 枢 / 平 / 和 | `平/和`已有 identity-like medical aliases。 |
| 计算机 / VM | stack, branch, jump, halt, state | 推 / 取 / 跳 / 终 / 置 / 翻 / 侔 / 会 | L0 namespace 要和 surface default 分开审阅。 |

## 单字替代矩阵

这里按你点名的范式列“可替代双字的单字”。`推荐`列是当前工作稿倾向；其它列是可审阅后备。

| 对象/操作 | 推荐 | 逻辑 | 形式代数 | 计算机 / VM | 先天图式 | 儒家 | 道家 | 佛学/玄学 | 备注 |
|---|---:|---|---|---|---|---|---|---|---|
| identity / no-op | `恒` / `.nop` 用 `静` | 真 / 等 / 同 | 恒 / 一 / id | 空指令：静 / 恒 / 守 | 定 / 中 | 守 / 正 / 安 / 平 / 和 | 常 / 静 / 无为 | 如 / 定 / 寂 / 空 | 代数 identity 用`恒`，VM no-op 用`静`。 |
| set temporal coordinate | `置` | 赋 / 令 | 置 / 定 | 设 / 写 / 置 / 调 | 位 / 时 | 定 / 令 / 安 | 移 / 易 / 转 | 安 / 置 | `setShi sh` 是 primitive，不是组合；多字都可在 VM context alias。 |
| flip one yao | `翻` | 否 / 反 | 翻 / 反 / 换 | 翻 / 切 / toggle | 易 / 反 | 改 / 更 | 化 / 转 | 转 / 变 | 若是具体坐标，仍用 `改/化/变/...`。 |
| branch on yao equality | `侔` | 等 | 等 / 侔 | 比 / 校 | 应 | 同 | 齐 | 等 | `侔`比`比`更少泛关系冲突。 |
| branch on time equality | `会` | 等 | 值 / 会 | 比 / 校 | 会 | 时 / 会 | 遇 | 缘 | `会`取“相会/正逢”。 |
| path witness | `径` | 路 | 径 / 轨 | 路 | 道 | 途 | 径 / 道 | 道 | `径`比`变径`自然；现只见 glyph registry 占用。 |
| direct transform | `达` | 蕴涵到达 | 达 / 至 | 跳 / 转 | 通 | 达 | 通 | 到 | `达`适合 a→b。 |
| cuo-zong composite | `错综`；`交`待审 | 合取? | 交 / 复 | 合成 | 交 | 交 | 反覆 | 缘 | `交`有 Z-4 冲突；当前代码不覆盖单字，复词 aliases 已可执行。 |
| flip-combo class/group | `群` | 类 | 群 | 枚 | 局 | 类 | 众 | 众 | `群`已有 X-4。 |
| projection T2→T1 | `约` | 抽 | 约 / 投 | 取 | 约 | 约 | 归 | 空 | `约`比`合仪`更单字。 |
| forget to TaiJi | `空` | 单元 | 空 / 终 | 丢 | 极 | 归 | 复 | 空 | 佛学色彩强，但精确。 |
| collapse to TaiJi | `复` | 归约 | 复 / 归 | 归 | 复 | 复 | 复 | 归 | `复`有 T-7/24 卦冲突。 |
| split T0→T1 | `判` | 分支 | 判 | 分配 | 判 | 判 | 开 | 分 | 太极判阴阳，语义强。 |
| split T1→T2 | `析` | 分解 | 析 | 展开 | 析 | 分 | 衍 | 分 | `析`适合 second coordinate。 |
| split T2→T3 | `展` | 扩张 | 展 | 展开 | 生 | 成 | 生 | 现 | `展`适合升维。 |
| product/combine T3×T3→T6 | `乘` | 积 | 乘 / 积 | 配 | 重 | 合 | 重 | 合 | `乘`有 R-10 乘位冲突。 |
| hierarchy step | `生` | 造 | 生 / 后继 | 构 | 生 | 生 | 生 | 起 | `生`多义但核心。 |
| Sheng→Trigram | `显` | 实现 | 显 | 解码 | 显 | 明 | 见 | 显 | 与 manifest 方向一致。 |
| Trigram→Sheng | `编` | 编码 | 编 / 码 | 编码 | 藏 | 录 / 编 | 藏 | 藏识 | `编`比`藏`更贴近 encode，`藏`保留为义理 alias。 |
| grand cycle | `周` | 闭环 | 周 / 环 | 循环 | 周 | 周 | 复 | 轮 | `周`自然。 |
| distance | T3 `隙` / T6 `度` | 度量 | 度 / 距 / 隙 | 差 | 隙 | 度 | 分 | 别 | T3 用差隙感，Hex metric 用`度`。 |

## 冲突字与处理建议

| 字/短语 | 冲突来源 | 建议 |
|---|---|---|
| `动 / 動` | 八卦生成元、动爻、其它 catalogue 动义 | 保留 alias；裸字报 ambiguous 或依 expected type。 |
| `中` | 爻位、关系、价值判断、方位 | 不做算子 default；只在组合名中使用。 |
| `正` | position relation、identity/normalize | 可作 identity alias，不抢`恒`。 |
| `反` | 错卦、否定、反向、取逆 | 只作 alias；object transform default 用`错`。 |
| `转 / 轉` | zong-like reversal、旋转、流程转移 | default 用`综`，`转`作 alias。 |
| `合` | projection、composition、union、relation | 纵向 projection 用`省*`，合成用`重卦`。 |
| `分` | split、role differentiation、partition | 必须带目标层：`分仪/分象/分卦`。 |
| `推` | L0 push、Hex increment、operator application | 必须走 namespace/type resolver。 |
| `取` | L0 pop、projection/extraction | 不作 projection default；用`省/取下二`等组合。 |
| `之` | application marker、之卦语义 | 保持语法 marker 优先。 |
| `承` | 爻翼 Y2、承乘关系、二爻命名 | 不作 T6 y2 default，可作解释别名。 |
| `鼎` | 第 50 卦传统名、器名/gap | 第 50 卦 default 用`器`，`鼎/已鼎/今鼎/未鼎`保留 alias。 |
| `交` | Z-4 泛交互、错综复合候选 | 暂不作为 `cuoZong` 默认实现；需 resolver 支持 arity/context 后再打开。 |
| `达` | 字元表已有，方向/通达义宽 | 可作 transform default，要求 source/target 或 function context。 |
| `群` | X-4 荀子群义、形式群义 | 可作 FlipCombo/group 文档名，resolver context 必须明确。 |
| `乘` | R-10 乘位/乘凌、代数 product | 可作 `chong` default，但需 T3×T3→T6 type。 |
| `复` | T-7 复归、24 卦复、collapse 候选 | 可作 `guiyi`，必须靠目标 type disambiguate。 |
| `空` | 佛学义强、unit/forget 义 | 可作 `heToTaiji`，但不要泛化为否定/空值。 |
| `度` | L-15 法家度、distance/measure | 可作 distance 候选，暂不强推。 |
| `静 / 靜` | F-11 归静、L-10 君静、ZA-2 心术静得 | 适合 `.nop` default；代数 identity 仍用`恒`。 |
| `径` | glyph registry 中已有字元，未见 direct operator reading | 适合 `pathFromTo` default；保留 `路/轨/途/道`。 |
| `略` | 未见 direct operator reading；有省略/略去义 | 适合 T3 projection prefix：`略上/略中/略下`。 |
| `编` | 未见 direct operator reading；有编次/编码义 | 适合 `ofTrigram` default；`藏`保留义理 alias。 |
| `隙` | glyph registry 中已有字元，未见 direct operator reading | 适合 T3 hamming distance 的差隙感。 |

## 推荐 promotion 顺序

1. T3/T6 exact context：`恒 / 改 / 化 / 变 / 错 / 综 / 互 / 错综 / 錯綜 / 综错 / 綜錯`，其中复词 = `cuoZong`。
2. Cell192 context：`极 / 错格 / 综格 / 互格`；四爻、五爻 default 暂待定。
3. 纵向 context：`略上 / 略中 / 略下 / 约 / 空 / 复 / 判 / 析 / 展 / 乘 / 生 / 显 / 编 / 周`。
4. 派生/诊断 context：`达 / 径 / 群 / 隙 / 度`，其中 T3 distance 用`隙`，Hex distance 用`度`。
5. 其它范式字先作为 alias 或文档候选，不进入默认 resolver。
