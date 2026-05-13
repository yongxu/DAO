# R4-R8 字梯：面 / 內 / 重 / 因 / 果

> 状态：审名 v0.2 (2026-05-13)。
> 范围：给 R4..R8 的公开字、reader grammar、备选字与形式逻辑读法收口一版。
> 边界：本文先定 surface / 文档读法；Lean carrier 与 theorem 仍以现有 `Mian`、`Wuyao`、`Hexagram`、`Cell128`、`Cell256` 为准，尚未把这些字全部注册成 parser 或 root registry。
> 形式锚：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) · [BenZheng.lean](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) · [R5_Wuyao.lean](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) · [Cell128.lean](../../formal/SSBX/Foundation/Bagua/Cell128.lean) · [Cell256.lean](../../formal/SSBX/Foundation/Bagua/Cell256.lean)

## 0. 总决议

| R | size | 层名推荐 | 新增位 | 位值 | 算子推荐 | 形式读法 |
|---|---:|---|---|---|---|---|
| R4 | 16 | 面 | 本 × 征 已在面中 | 16 单字见下表 | 暂沿用位置 / XOR mask | `Mian = Ben × Zheng` |
| R5 | 32 | 內 | 內 | 內本 / 內征 | 易內 | `Mian × Bool` |
| R6 | 64 | 重 | 外 | 外本 / 外征；合为 本本 / 本征 / 征本 / 征征 | 易外 | `Mian × Bool × Bool ≃ Hexagram` |
| R7 | 128 | 因 | 因 | 無因 / 有因 | 印 | `Hexagram × YinBit` |
| R8 | 256 | 果 | 果 | 無果 / 有果；合为 Shi V4 | 投 | `Hexagram × (YinBit × GuoBit)` |

读法原则：

- R4 给单字，不再只读作「本×征 pair」。
- R5/R6 先给结构名：`內本·動`、`本征·動`；可读单字作为 alias。传统六十四卦名仍是 R6 的强 alias，但不是这份结构字梯的唯一入口。
- R7/R8 保持 state/action 分工：`因` 是位，`印` 是 toggle 因；`果` 是位，`投` 是 toggle 果。
- R8 的四个 Shi 仍按 `(因, 果)` 读：`道 = 00`，`已 = 10`，`未 = 01`，`今 = 11`。

## 1. R4 面：十六字定表

`R4 = 面 = Ben × Zheng`。行是本，列是征。

| | 幾 | 勢 | 機 | 時 |
|---|---|---|---|---|
| 物 | 動 | 行 | 化 | 流 |
| 動 | 萌 | 長 | 發 | 續 |
| 間 | 緣 | 通 | 會 | 系 |
| 事 | 兆 | 趨 | 變 | 史 |

简繁别名：

| 文言 default | 可接受现代别名 |
|---|---|
| 長 / 發 / 續 / 緣 / 會 / 趨 / 變 | 长 / 发 / 续 / 缘 / 会 / 趋 / 变 |
| 動 / 間 / 幾 / 勢 / 機 / 時 | 动 / 间 / 几 / 势 / 机 / 时 |

四征的英文没有完全准确单词：

| 征 | 推荐 gloss | 不推荐单独等同 |
|---|---|---|
| 幾 | incipient sign / subtle trace | trace only |
| 勢 | tendency / momentum / force-disposition | force only |
| 機 | hinge / pivot / occasion | machine |
| 時 | timing / timely occasion | clock-time only |

## 2. R5 內：面加內位

推荐：`R5 = 內 = 面 × 內位`，`內位 ∈ {本, 征}`。

当前 Lean 已有 `Wuyao = Mian × Bool`；本文把这个 Bool 的公开读法定为 `內`，但不声称现有 Lean 声明名已经改成 `Nei`。

| 项 | 推荐 | 备选 | 取舍 |
|---|---|---|---|
| 层名 | 內 | 五爻 / 中 / 裏 / 藏 / 含 / 蘊 | `內` 可文言直读，又不借用六十四卦名；`五爻` 只说 cardinality。 |
| 位值 | 內本 / 內征 | 本側 / 征側 | 明确承接 R4 的本征结构。 |
| 算子 | 易內 | 內易 / 納 / 轉內 / 反內 | `易內` 最不神秘，形式上就是 toggle inner bit。 |

R5 reader grammar：

```text
R5Name ::= R5Glyph | 內本·R4Name | 內征·R4Name
```

R5 单字 alias 的取字逻辑：

- `內本` 读作该面在内里的承体、根、质、路、纲、记等，偏名词 / 所成。
- `內征` 读作该面在内里的趋向、发用、显相、牵引、达成等，偏动词 / 所显。
- 能用会文言文者可直读的单字则用单字；不稳处保留组合名作 canonical fallback。

| R4 面 | 內本推荐 | 內本读法 | 內本备选 | 內征推荐 | 內征读法 | 內征备选 |
|---|---|---|---|---|---|---|
| 動 | 力 | 动之内在能 | 勢 / 勁 / 能 | 作 | 动之发作 | 起 / 振 / 動 |
| 行 | 徑 | 行之所由路 | 道 / 途 / 路 | 履 | 行之践履 | 踐 / 往 / 進 |
| 化 | 質 | 化之所变质 | 形 / 體 / 素 | 革 | 化之改易 | 易 / 遷 / 變 |
| 流 | 源 | 流之所出 | 本 / 泉 / 脈 | 衍 | 流之延布 | 注 / 派 / 逝 |
| 萌 | 芽 | 萌之初体 | 蘖 / 苗 / 胚 | 茁 | 萌而向长 | 生 / 發 / 滋 |
| 長 | 根 | 长之所植 | 幹 / 基 / 株 | 滋 | 长之增益 | 育 / 茂 / 蕃 |
| 發 | 蓄 | 发之前蓄 | 藏 / 韞 / 蘊 | 啟 | 发而开启 | 興 / 揭 / 開 |
| 續 | 緒 | 续之线端 | 絲 / 端 / 序 | 繼 | 续而相承 | 承 / 紹 / 連 |
| 緣 | 由 | 缘之所由 | 因 / 故 / 端 | 牽 | 缘之牵连 | 連 / 引 / 屬 |
| 通 | 渠 | 通之渠道 | 道 / 門 / 路 | 達 | 通而抵达 | 亨 / 貫 / 徹 |
| 會 | 契 | 会之相合券 | 符 / 約 / 節 | 合 | 会而合聚 | 聚 / 集 / 同 |
| 系 | 綱 | 系之总绳 | 紀 / 紐 / 繩 | 維 | 系而维持 | 繫 / 持 / 統 |
| 兆 | 象 | 兆之可见象 | 候 / 徵 / 幾 | 占 | 兆之可占 | 卜 / 讖 / 測 |
| 趨 | 向 | 趋之所向 | 志 / 方 / 嚮 | 赴 | 趋而赴之 | 趨 / 奔 / 就 |
| 變 | 故 | 变之前态 | 舊 / 常 / 本 | 更 | 变而更新 | 改 / 易 / 革 |
| 史 | 記 | 史之所记 | 典 / 籍 / 錄 | 述 | 史而传述 | 書 / 載 / 敘 |

裸字碰撞说明：

- `道`、`因`、`勢`、`動` 等已在其他层或内容线有强用途，所以在 R5 表中只列备选，不作推荐。
- `履`、`革` 等也是六十四卦名；作为 R5 单字 alias 时必须由 reader context 判定，组合名 `內征·行` / `內征·化` 仍是无歧义写法。
- 这 32 字先是 surface alias 表，不是 Lean constructor；形式锚仍是 `R5 = Mian × Bool`。

形式逻辑读法：

```text
R5 = R4 × Bool
內本 = false
內征 = true
易內(w) = w xor e_in
```

其中 `e_in` 是只开 R5 新位的 XOR mask。实现上暂对应 `R5_Wuyao.flip5` 的 surface reading。

## 3. R6 重：內外交成四隅

推荐：`R6 = 重 = 面 × 內位 × 外位`。`重` 是层名；新增位读 `外`。

| 內 \ 外 | 外本 | 外征 |
|---|---|---|
| 內本 | 本本 | 本征 |
| 內征 | 征本 | 征征 |

| 项 | 推荐 | 备选 | 取舍 |
|---|---|---|---|
| 层名 | 重 | 疊 / 複 / 卦 | `重` 有重卦传统 anchor，且是文言动词。 |
| 新增位 | 外 | 表 / 末 / 上 | `外` 与 R5 `內` 成对。 |
| 算子 | 易外 | 外易 / 疊 / 轉外 / 反外 | `易外` 保持与 `易內` 同型。 |
| R6 cell alias | 六十四卦名 | 结构名 only | 卦名强，但结构名更适合作 R4-R8 统一 grammar。 |

R6 reader grammar：

```text
R6Name ::= Quadrant·R4Name
Quadrant ::= 本本 | 本征 | 征本 | 征征
```

例：

| R4 | 本本 | 本征 | 征本 | 征征 |
|---|---|---|---|---|
| 動 | 本本·動 | 本征·動 | 征本·動 | 征征·動 |
| 行 | 本本·行 | 本征·行 | 征本·行 | 征征·行 |
| 會 | 本本·會 | 本征·會 | 征本·會 | 征征·會 |
| 史 | 本本·史 | 本征·史 | 征本·史 | 征征·史 |

形式逻辑读法：

```text
R6 = R4 × Bool × Bool
本本 = (false, false)
本征 = (false, true)
征本 = (true,  false)
征征 = (true,  true)
易外(h) = h xor e_out
```

Lean 边界：现有 `Hexagram.quadrant` 已有 `本本 / 本征 / 征本 / 征征` 四象限，并按 inner/outer trigram 的本征性定义。本文的 structure grammar 与这个象限读法一致；但 `LiftProject.liftR5toR6` 的 bit layout 仍是现有 y1..y6 编码，后续若要把 `內/外` 做成 parser-level first-class bit，需要单独补 registry / theorem。

## 4. R7 因：重加因位

推荐：`R7 = 因 = 重 × 因位`，`因位 ∈ {無因, 有因}`。

| 项 | 推荐 | 备选 | 取舍 |
|---|---|---|---|
| 层名 / 位名 | 因 | 緣 / 故 / 由 / 本 | `因` 能读作前因、条件、past trace，且和 `果` 成对。 |
| 位值 | 無因 / 有因 | 未印 / 已印 | state 不应混入 action；故不用「印」作位值。 |
| 算子 | 印 | 記 / 留 / 銘 / 痕 | `印` 是留下印记，适合作 toggle 因的 action。 |

R7 reader grammar：

```text
R7Name ::= 無因·R6Name | 有因·R6Name
```

形式逻辑读法：

```text
R7 = R6 × Bool
無因 = false
有因 = true
印(c) = c xor e_yin
```

当前 Lean 对应：`Cell128.YinBit = Bool`，`Cell128.yin` / `yinM`。

## 5. R8 果：因再加果位

推荐：`R8 = 果 = 重 × 因位 × 果位`，`果位 ∈ {無果, 有果}`。

| 项 | 推荐 | 备选 | 取舍 |
|---|---|---|---|
| 层名 / 位名 | 果 | 效 / 成 / 應 / 末 | `果` 与 `因` 成对，读成 projection / consequence。 |
| 位值 | 無果 / 有果 | 未投 / 已投 | state 不应混入 action；故不用「投」作位值。 |
| 算子 | 投 | 發 / 施 / 致 / 射 | `投` 有投射、投置、投向未来之义，和 `印` 的 past trace 成对。 |

Shi V4：

| 因 | 果 | Shi | 读法 | formal |
|---|---|---|---|---|
| 無因 | 無果 | 道 | 未被因果分化的基准态 | `(false, false)` |
| 有因 | 無果 | 已 | 因已成，果未投 | `(true, false)` |
| 無因 | 有果 | 未 | 因未成，果已投向未至 | `(false, true)` |
| 有因 | 有果 | 今 | 因与果相交之现行态 | `(true, true)` |

R8 reader grammar：

```text
R8Name ::= 道·R6Name | 已·R6Name | 未·R6Name | 今·R6Name
```

例：

```text
道·本本·動
已·本本·動
未·本本·動
今·本本·動
```

形式逻辑读法：

```text
R8 = R6 × Bool × Bool
投(c) = c xor e_guo
印投(c) = c xor e_yin xor e_guo
```

当前 Lean 对应：`Cell256.GuoBit = Bool`，`Cell256.Shi`，`Cell256.tou` / `touM`，以及 Shi V4 `{道, 已, 未, 今}`。

## 6. 跨语言对照

| 位置 | 文言推荐 | 现代中文 | English | formal logic |
|---|---|---|---|---|
| R4 层 | 面 | 面 / 面向 / 命面 | face / aspect-cell | `Ben × Zheng` |
| R5 位 | 內 | 内侧选择 | inner bit / internal selection | `Bool`, `e_in` |
| R6 层 | 重 | 重叠 / 重卦 | stacked / doubled | product extension to `R6` |
| R6 位 | 外 | 外侧选择 | outer bit / external selection | `Bool`, `e_out` |
| R7 位 | 因 | 前因 / 条件痕迹 | causal trace / antecedent mark | `Bool`, `e_yin` |
| R7 算子 | 印 | 标记 / 留印 | imprint | `xor e_yin` |
| R8 位 | 果 | 后果 / 投射结果 | projection / consequence | `Bool`, `e_guo` |
| R8 算子 | 投 | 投射 / 投置 | project / cast | `xor e_guo` |
| Shi | 道/已/未/今 | 基准/过去/未来/现在 | identity / past / future / present | `Bool × Bool ≃ V4` |

形式逻辑语言里不应强造自然语言名。推荐接口是：

```lean
structure R8Surface where
  r6  : Hexagram
  yin : Bool
  guo : Bool
```

或等价的 dependent record / product type。自然语言字只作为 pretty-printer / parser alias，不作为 theorem 的替代。

## 7. 已有 / 未有

| 项 | 已有 | 未有 | 推荐下一步 |
|---|---|---|---|
| R4 十六字 | `Mian.label` 已有 16 labels | 简繁 default 未统一到公开 registry | 把本表作为 registry source，保留简体 alias。 |
| R5 carrier | `Wuyao = Mian × Bool`、`flip5`、枚举定理 | `內 / 內本 / 內征 / 易內` 尚未进 parser / registry | 先加 surface registry，不急着重命名 Lean type。 |
| R6 structure | `Hexagram`、`Quadrant`、四象限定理、64 卦名 | `Quadrant·R4Name` 未生成 64 结构名表 | 生成结构名 alias，并保留传统卦名。 |
| R7 | `Cell128`、`YinBit`、`yin` / `yinM` | 旧审名页仍标 provisional | 将 因/印 升为 default surface。 |
| R8 | `Cell256`、`Shi`、`GuoBit`、`tou` / `touM` | root-language tree 尚未按本文重生成 | 将 果/投 + 道/已/未/今 作为 R8 default surface。 |
| reader grammar | 本文已给 | WenScript / Native parser 尚未接入 | 新增一个小型 parse / pretty-print 层，不改 kernel。 |

## 8. 不做的声明

- 本文不声称 R5 已有新的独立传统 Yi ontology；`內` 是优先 surface 字，不是新 theorem。
- 本文不删除六十四卦名；R6 的结构名用于统一生成，卦名继续作传统 alias。
- 本文不改 `Cell256` 之 V4 Shi 定义；`道/已/未/今` 仍以现有 Lean `Shi` 为准。
- 本文不把自然语言字当形式证明；所有完备性、闭包、自反、involution 仍看 Lean theorem。
