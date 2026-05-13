# Root Language Tree Naming Scheme — 命名原则、备选与理由

> 状态：draft v0.2 (2026-05-13)
> 角色：解释 `layers/R0.md` 到 `layers/R8.md` 的命名方案。每个具体 entry 的短理由在 layer 表中；本文给出成组的备选原因。
> R4..R8 的最新结构字梯见 [`../r4-r8-character-ladder.md`](../r4-r8-character-ladder.md)。本目录下 `layers/R*.md` 是 2026-05-11 生成草表，尚未按该字梯重生成。

## 0. 口径

本组文件采用 `1023` 审名口径：

```text
1 未分根 + 1022 interface readings = 1023 review entries
```

其中 `1022` interface 口径是每个 root 同时列 `cell` 与 `operator`。R0 也重复，是为了审阅接口完整；本体口径仍可采用 `1021`。

## 1. 总原则

| 优先级 | 原则 | 理由 |
|---|---|---|
| 1 | 经典已有字优先 | R3 八卦、R6 六十四卦、R8 Shi 已有强 anchor |
| 2 | 现代中文可读 | 审阅和后续解释需要不用长注释也能读 |
| 3 | formal logic 明确 | 每项必须能读成 carrier element 或 XOR mask action |
| 4 | 未定不造字 | 无稳定字时用 ox，避免把临时解释伪装成定名 |
| 5 | 备选留账 | 每个 provisional 层都说明为什么不直接定 |

## 2. 各层 cell 命名

| 层 | default | 备选 | 理由 |
|---|---|---|---|
| R0 | 太极 / 一元 | 极 / 一 / 元 / 道 / 源 / 空 / 无 | 太极/一元最稳；单字易撞车，故多作 alias |
| R1 | 阳/阴；义理读实/虚 | 刚柔、显隐、正负、天/地、升/降 | 实/虚最贴近 bit 的有/无、实/虚结构；升降带运动义，暂不作 default |
| R2 | 太阳/少阴/少阳/太阴；单字春夏秋冬 | 老阳/少阴/少阳/老阴、昼昏晨夜、炎凉温幽 | 四时有邵雍先天图 anchor，且单字稳定 |
| R3 | 乾兑离震巽坎艮坤；德字健悦显起入险止顺 | 天泽火雷风水山地；健说丽动入陷止顺 | 卦名 canonical；德字来自说卦，少数字按现代可读性调和 |
| R4 | 16 单字：動行化流 / 萌長發續 / 緣通會系 / 兆趨變史 | Ben×Zheng pair：物/動/間/事 × 幾/勢/機/時 | 单字作公开读法，pair 作审计结构。 |
| R5 | 內：內本 / 內征，并有 32 单字 alias | 五爻、中、裏、藏、含、蘊 | `內` 可文言直读，并把 `Mian × Bool` 接回本征结构；单字 alias 见 `r4-r8-character-ladder.md`；Lean type 名暂仍 `Wuyao`。 |
| R6 | 重：本本 / 本征 / 征本 / 征征 + R4 面名 | King Wen 64 卦名；疊、複、卦 | `重` 有重卦传统 anchor；64 卦名作强 alias，结构名用于统一生成。 |
| R7 | 因：無因 / 有因 | 緣、故、由、本 | `因` 与 R8 `果` 成对；state/action 分开。 |
| R8 | 果：道/已/未/今 | 效、成、應、末；Shi 其他翻译 | Shi V4 已是 v3 canonical；道为 identity first-class。 |

## 3. operator 命名

| 范围 | default | 备选 | 理由 |
|---|---|---|---|
| zero mask | 恒 | 静、定、守、常、止、安、寂、息、平、和 | 恒作数学 identity；静留给 VM nop |
| R1 nonzero | 易 | 反、翻、转、化、换 | 易是原子互易，最 canonical |
| R2 masks | ox fallback + 中文说明 | 初易/二易/并易 | R2 无独立 classical lateral op，不强造古字 |
| R3 masks | 改/化/变/错 | 动/中/上、翻初/翻中/翻上 | 改化变已在项目中稳定；错=三爻全反 |
| R5 structural axis | 易內 | 內易、納、轉內、反內 | `易內` 直接读作 toggle inner bit，不强造单字。 |
| R6 structural axis | 易外 | 外易、疊、轉外、反外 | `易外` 与 `易內` 同型；传统六爻 flip 字仍保留。 |
| R6 masks | 改/化/變/臨/主/極/錯 | 六位爻辞名：初二三四五上 | position-operator-tree 已采用这组六位 flip 字；与结构字梯并行。 |
| R7 masks | R6 atoms + 印 | 記、留、銘、痕 | 印 = toggle 因，state/action 分明。 |
| R8 masks | R6 atoms + 印/投；印投 | 發、施、致、射 | 投 = toggle 果；印投 = Shi PT 双轴翻。 |

## 4. formal logic 统一读法

每个 cell row：

```text
bits : Rn = (Z/2)^n
```

每个 operator row：

```text
lambda s : Rn, bits xor s
```

所以完整性来自生成规则，不来自手工枚举 transform rows。审阅字可以变化，但 formal logic 读法不变。

## 5. 审阅建议

建议按层审：

1. 先定 R0-R3，因为这些有传统 anchor。
2. 再定 R6/R8，因为这些有 King Wen 与 Shi V4 anchor。
3. R4..R8 按 [`../r4-r8-character-ladder.md`](../r4-r8-character-ladder.md) 审：先确认 surface 字，再重生成 `layers/R*.md`。
4. 审完后再回写 Lean registry，不要把自然语言字误当 theorem。
