> 状态：v3 (2026-05-11) — 八卦算子命名候选表（已归档；增 v3 settled / open 状态列）。原是 R3/R4/Cell192/L0 字根命名工作稿；v3 阶段印 / 投 / 道 / 因 / 果 已升 first-class 但其字面 settled，本表保留作命名考古档案。

# 八卦算子命名候选表（已归档）

> **状态：已被替代（2026-05-09，v3 重号 2026-05-11）**。本文件原是 R3/R4/Cell192/L0 字根命名的工作稿（其中 Cell192 已在 v3 删除，由 Cell128 (R₇) + Cell256 (R₈) = Hexagram × V₄ Klein Shi 取代）。该工作已完成并并入下列三件套：
>
> - **字根定本与备选分析**：[`docs-next/10_formal_形式/layer-character-map.md`](../10_formal_形式/layer-character-map.md)
> - **全景映射图与三轴汇聚**：[`docs-next/10_formal_形式/layer-axis-graph.md`](../10_formal_形式/layer-axis-graph.md)
> - **代码 ground truth**：[`formal/SSBX/Text/LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean)
>
> 本文件保留以避免外部回链断裂，下次清理时可删除。

## v3 命名状态摘要（2026-05-11）

v3 阶段（Cell256 + V₄ Klein Shi）之关键命名：

| 字 | v3 状态 | 备注 |
|---|---|---|
| 道（R₈ origin / V₄ identity / no-op / 永真 cell） | **provisional canonical** | settled in v3；one-character anchor for 5 identities；详 [`glossary.md`](glossary.md) |
| 印（R₇ atomic 算子 = toggle YinBit） | **provisional canonical** | settled in v3 (2026-05-08~10)；XOR-mask form 在 `Cell256.lean § 8`；备选名 印/留, 始/起 仍在 yi-calculus-theorem.md §16 之 caveat 区 |
| 投（R₈ atomic 算子 = toggle GuoBit） | **provisional canonical** | settled in v3；备选 望 / 期 同上 |
| 因（R₇ binary axis / state attribute） | **provisional canonical** | settled in v3；备选 始 / 持 |
| 果（R₈ binary axis / state attribute） | **provisional canonical** | settled in v3；备选 终 / 期 |
| 道 / 已 / 今 / 未（V₄ Shi 四态） | **provisional canonical** | settled in v3 (Cell256.lean § 1)；非 cyclic，含 V₄ identity (道) 与 PT 中心 (今) |
| 五爻（R₅，无传统 anchor） | **provisional, descriptive baseline** | settled-as-baseline；其它候选（接 / 临 / 渐 / 进）仍 open |
| Mian（R₄ = Ben × Zheng） | **canonical** | settled (2026-05-07 BenZheng 形式落地) |

「provisional canonical」= v3 主线接受为入选标准；后续若有更佳 anchor 仍可换。「open」= 未定。

## 主要变更摘要（旧工作稿 → 新定本，含 v3 status）

| 层级 | 旧 default（本工作稿原案） | 新 default（已落定） | v3 状态 | 变更原因 |
|---|---|---|---|---|
| R3 乾 mode | 生 | **健** | settled | `生` 撞 Sheng.step / T-7 / CoreAtom |
| R3 兑 mode | 开 | **悦** | settled | `开` 已是 CoreAtom，硬撞车 |
| R3 离 mode | 显 | **显** | settled | 不变 |
| R3 震 mode | 元 | **起** | settled | `元` 撞 Monad root 一元 |
| R3 巽 mode | 申 | **入** | settled | `申` 偏冷僻；`入`是《说卦》原文 |
| R3 坎 mode | 塞 | **险** | settled | `险`比`塞`现代通用且为坎 alias |
| R3 艮 mode | 居 | **止** | settled | `止`是《说卦》原文，更准 |
| R3 坤 mode | 守 | **顺** | settled | `守`属 identity alias 集 |
| R4 flip4 | 待定 | **临** | settled | 19 临卦同字 / 4 爻近君位 |
| R4 flip5 | 待定 | **主** | settled | 5 爻君位 / 主导义 |
| R5 shiNext | 未给 | **迁** | settled (旧工作稿层) | 「时迁」古义；注：**v3 之 R₅ 是 Wuyao 五爻**，与此 R5 shiNext 不同概念 |
| R5 shiPrev | 未给 | **溯** | settled (旧工作稿层) | 「溯往」古义；同上 R₅ vs Wuyao 之 caveat |
| R1 阳/阴 义理读 | 未给 | **实 / 虚** | settled | 邵雍《观物外篇》"阳为实, 阴为虚" |
| R2 四象单字 | 未给 | **春 / 夏 / 秋 / 冬** | settled | 邵雍《皇极经世》先天图配四时 |
| **道 (R₈ origin)** | 未在旧工作稿 | **道** | **settled in v3 (2026-05-10)** | V₄ identity / no-op / 永真 cell；one-character five-fold anchor |
| **印 (R₇ atomic 算子)** | 未在旧工作稿 | **印** | **settled provisional in v3** | XOR-mask form at Cell128/Cell256；备选 印/留 / 始/起 |
| **投 (R₈ atomic 算子)** | 未在旧工作稿 | **投** | **settled provisional in v3** | XOR-mask form at Cell256；备选 望 / 期 |
| **因 / 果（R₇/R₈ state axes）** | 未在旧工作稿 | **因 / 果** | **settled provisional in v3** | YinBit / GuoBit；备选 始/终 / 持/期 |
| **Shi V₄ 四态 (R₈)** | (旧工作稿用 Z/3) | **道 / 已 / 今 / 未** | **settled in v3** | V₄ Klein 群；非 cyclic |

详细取舍理由（含每字 6-8 个备选 + 每个备选理由）见 [layer-character-map.md](../10_formal_形式/layer-character-map.md)。v3 新增字（道 / 印 / 投 / 因 / 果 / 已 / 今 / 未）之命名 caveats 见 `formal/SSBX/Foundation/Bagua/Cell256.lean § 1` 头部注释 + [`yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md) §16。

## 形式锚

- [`docs-next/10_formal_形式/layer-character-map.md`](../10_formal_形式/layer-character-map.md) — 字根定本
- [`formal/SSBX/Text/LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) — code ground truth
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — v3 印 / 投 / 道 / Shi V₄ 之命名 caveats
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — v3 因 / 印 之命名 caveats
- [`docs-next/40_reference_参考/glossary.md`](glossary.md) — v3 术语短释
