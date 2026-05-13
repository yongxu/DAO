# 儒家核心词 Overlay Mapping

> 状态：draft v0.1 (2026-05-13)
> 范围：把儒家核心字/词映射到现有 `R0..R8` root language tree 条目，作为审名、教学和引用索引。
> 口径：本页不改 canonical root 名，不新增坐标，也不把德目声称为形式系统的 primitive。形式真值仍以 bitstring、cell / operator role 和 XOR mask 为准。

## 读法原则

1. `天 / 地` 已经有稳定公开锚点：R3 八卦的 `乾 / 坤`，R6 六十四卦的 `乾 / 坤`，以及 R8 的 Shi×卦扩展。
2. `身 / 心` 不宜直接占用一个 root 名。`心` 更像 `易內` 这类 inward operation；`身` 更像 `履 / 作 / 徑` 这类 embodied path 与 enactment。
3. `仁義禮智信` 是规范性 overlay，不是五个独立坐标。它们应映射到已有 cell、operator 和卦名群，而不是替换 root public names。
4. 若一个儒家词可由古文/经典字直接读懂，优先落到现有古文单字；其次用当代中文或形式逻辑说明；最后才用透明组合。
5. `印` 只读作 trace / witness / verification，不直接等于德目 `信`。`信` 的德性锚点优先是 `中孚`。

## 总表

| 儒家词 | 推荐锚点 | 辅助锚点 | 读法 | 状态 |
|---|---|---|---|---|
| 天 | `R3-ooo-cell` 乾；`R6-oooooo-cell` 乾 | R8 的 `*-乾` family | 乾为天、健、creative pole | 已公开 |
| 地 | `R3-xxx-cell` 坤；`R6-xxxxxx-cell` 坤 | R8 的 `*-坤` family | 坤为地、顺、receptive pole | 已公开 |
| 道 | `OX["oooooooo"]`；R8 道 Shi family | `R6-oooooo-operator` 恒作为 no-op 参考 | 道是 anchor，不是德目；可承载天地方向的全局读法 | 已公开 |
| 心 | `R5-oooox-operator` 易內；R6/R7/R8 的 `易內` operators | `中孚`、`无妄`、`恒` | inward turn、反求诸己、正心 | 强 overlay |
| 身 | `R5-oooxx-cell` 履；`R6-ooxooo-cell` 履 | `R5-ooooo-cell` 力、`R5-oooox-cell` 作、`R5-oooxo-cell` 徑；`改+易內` operators | 履身、践行、修身的 embodied path | 强 overlay |
| 仁 | `R6-oxoooo-cell` 同人；`R6-oxoxoo-cell` 家人 | `R5-xoxoo-cell` 契、`R5-xoxox-cell` 合、`R5-xoxxx-cell` 維；`易外` operators | 亲亲、推己及人、relation-forming | 强 overlay |
| 義 | `R6-ooxooo-cell` 履；`R6-oxxooo-cell` 无妄 | `R6-ooxxxx-cell` 临；`改`、`臨` operators | 所当行、宜、裁断与临事 | 强 overlay |
| 禮 | `R6-ooxooo-cell` 履；`R6-ooxxox-cell` 节 | `R6-oxoxxo-cell` 贲、`R6-oxoxoo-cell` 家人；`R5-xoxxo-cell` 綱、`R5-xoxxx-cell` 維 | 节文、秩序、可践之仪 | 强 overlay |
| 智 | `R4-oooo-cell` 物幾；`R4-ooxo-cell` 物機；`R4-xxoo-cell` 事幾 | `R5-xxooo-cell` 象、`R5-xxoox-cell` 占；`R6-xxxxoo-cell` 观 | 知幾、见兆、观象而判断 | 强 overlay |
| 信 | `R6-ooxxoo-cell` 中孚 | `R6-oxxooo-cell` 无妄；R7/R8 `印` operators 仅作 witness/verification | 内实、中孚、可验 | 强 overlay |
| 忠 | `易內` operators；`R6-ooxxoo-cell` 中孚 | `R6-xoooxx-cell` 恒 | 尽己、守内在一致性 | 说明性 overlay |
| 恕 | `易外` operators；`R6-oxoooo-cell` 同人 | `R6-oxoxoo-cell` 家人、`R5-xoxox-cell` 合 | 推己及人、由内达外 | 说明性 overlay |
| 孝悌 | `R6-oxoxoo-cell` 家人 | `R6-ooxooo-cell` 履、`R6-ooxxox-cell` 节、`R5-xoxxo-cell` 綱、`R5-xoxxx-cell` 維 | 家内秩序、亲属伦理、可践之礼 | 说明性 overlay |
| 誠 | `R6-ooxxoo-cell` 中孚；`R6-oxxooo-cell` 无妄 | `R6-xoooxx-cell` 恒 | 内外不欺、无妄而有恒 | 强 overlay |
| 中庸 | `R6-xoooxx-cell` 恒；`R6-ooxxoo-cell` 中孚 | `R6-oooxxx-cell` 泰；道 anchor | 不偏不倚、持续可行的中道 | 说明性 overlay |
| 君子 | `R3-ooo-cell` 乾；`R6-xxoxxx-cell` 谦；`R6-ooxooo-cell` 履 | `R6-oxxooo-cell` 无妄、`R6-ooxxoo-cell` 中孚 | 健、谦、履、诚的合成画像 | 叙述性 overlay |
| 小人 | 不设推荐 root | `R6-xxxooo-cell` 否可作反例语境 | 不宜作为正式审名；只在对比段落使用 | 弱 overlay |

## 五常细分

| 五常 | 首选 | 次选 | 不建议 |
|---|---|---|---|
| 仁 | 同人、家人 | 契、合、維、易外 | 不用一个新 bit 叫 `仁`；会把关系德目误读成坐标 |
| 義 | 履、无妄 | 临、改、臨 | 不把 `義` 直接等同 `法` 或 `裁判` |
| 禮 | 履、节 | 贲、家人、綱、維 | 不把 `禮` 只读成装饰；`贲` 只能作文饰次锚 |
| 智 | 幾、機、兆、象、占、观 | 事幾、物機 | 不把 `智` 读成单纯 information；重点是见机与判断 |
| 信 | 中孚 | 无妄、印 | 不把 `印` 直接升为 `信`；`印` 是证迹/见证，不是德性本身 |

## 身心位置

| 词 | 推荐结构 | 说明 |
|---|---|---|
| 心 | `易內` operator family | 心不是某个 cell，而是 inward turn 的操作读法；与正心、诚意、反求诸己相合。 |
| 身 | `履` cell family | 身不是 pure body object，而是已入路径、可践行的 embodied agency；与修身、践履相合。 |
| 身心合读 | `履 + 易內`；`改+易內` | `履 + 易內` 用于“在所行处反身”；`改+易內` 用于“修身/改过”的动作读法。 |

## 大学八目

| 八目 | 推荐锚点 | 说明 |
|---|---|---|
| 格物 | R4 `物幾 / 物機`；R5 `象 / 占` | 从物之幾、物之機进入可审的象与兆。 |
| 致知 | R4 `幾 / 機 / 兆`；R6 `观` | 致知不是信息堆积，而是把幾、機、兆变成可判断之观。 |
| 誠意 | `中孚 / 无妄` | 内实而无妄。 |
| 正心 | `易內`；`恒` | 反身、守常、使内向操作稳定。 |
| 修身 | `履`；`改+易內`；`作 / 徑` | 在所履之径上作、改、反身。 |
| 齊家 | `家人`；`綱 / 維`；`节` | 家内关系、纲维与节文。 |
| 治國 | `师 / 比 / 临 / 观 / 鼎 / 井` | 组织、聚合、临民、观政、制度器物与公共供给。 |
| 平天下 | `泰`；`乾 / 坤`；道 anchor | 天地通泰与全局 anchor 的 political reading。 |

## 五伦与三纲

| 词 | 推荐锚点 | 说明 |
|---|---|---|
| 君臣 | `师 / 临 / 观 / 鼎 / 井` | 治国关系：组织、临民、观政、制度与公共供给。 |
| 父子 | `家人`；`綱 / 維` | 家内生成关系与维系结构。 |
| 夫妇 | `家人`；`合 / 契`；`中孚` | 家庭结合、约信与内实。 |
| 长幼 | `家人`；`节`；`谦` | 年序、节文与谦让。 |
| 朋友 | `同人`；`合`；`中孚` | 同道相与、合与信。 |
| 三纲 | `綱 / 維`；再分读到 `君臣 / 父子 / 夫妇` | `綱` 可作字面锚点；本页只做 mapping，不替三纲作规范性背书。 |

## 常用补充词

| 词 | 推荐锚点 | 说明 |
|---|---|---|
| 性 | `中孚 / 无妄`；天地方向用 `乾 / 坤` | 不宜单独设 root；可读为内实、无妄与天地赋形的合读。 |
| 命 / 天命 | `乾 / 坤`；道 anchor | 天命读在天地与道的全局结构，不读作一个局部 operator。 |
| 敬 | `易內`；`履`；`节` | 持敬是 inward attention 落到践履与节文。 |
| 学 | `观`；`象 / 占`；`記 / 述` | 学问路径：观、取象、记录、述作。 |
| 教 | `同人 / 家人`；`述`；`观` | 教化在关系中传述，并以观为公共可见。 |
| 政 | `临 / 观 / 鼎 / 井 / 比` | 临民、观政、器制、公共供给与聚合。 |
| 乐 | 暂不设推荐 root | 可在礼乐讨论中依 `和 / 合 / 节` 再审；当前 tree 没有稳定 public `乐` 锚点。 |

## 四端

| 四端 | 德目 | 推荐锚点 | 说明 |
|---|---|---|---|
| 恻隐 | 仁 | 同人、家人、易外 | 由不忍人之心外推为 relation-forming。 |
| 羞恶 | 義 | 履、无妄、改 | 知所不为，并能改。 |
| 辞让 | 禮 | 谦、节、履 | 谦让、节文、可践之仪。 |
| 是非 | 智 | 幾、機、兆、象、占、观 | 分辨是非靠见幾、观象与判断。 |

## 引用建议

- 正式 root table 仍引用 `layers/R*.md` 中的 `id`、`ox`、`role` 和 public candidate。
- 儒家术语出现在 prose 时，可引用本页表格作为 overlay index。
- 若将来要把某个儒家词升入 public naming，必须回到对应层的审字表逐项修改，并说明是否改变 canonical candidate；不能只改本页。
- 对外文档中可说“`仁 / 義 / 禮 / 智 / 信` have stable overlay anchors”，但不要说它们已经是 five primitive roots。
