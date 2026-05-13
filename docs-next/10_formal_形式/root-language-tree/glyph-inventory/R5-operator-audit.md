# R5 Operator Audit

> 状态：审名 v0.2 (2026-05-13)。
> 范围：只审 R5 的 32 个 operator reader names；R5 cell 单字仍见 [R5.md](R5.md)。
> 形式口径：每个 bitstring `m` 表示 `(Z/2)^5` 上的平移 `T_m(s)=m xor s`。若 `e_i` 是第 `i` 位 basis，则 `τ_i = T_{e_i}`，所有 `τ_i` 交换。

## Basis

| bit | mask | 当前原子名 | 形式名 | 备注 |
|---|---|---|---|---|
| y1 | xoooo | 改 | `τ1 = T_{e1}` | 已占用 `改`；因此 y5 不宜再叫 `改`。 |
| y2 | oxooo | 化 | `τ2 = T_{e2}` | 保留。 |
| y3 | ooxoo | 變 | `τ3 = T_{e3}` | 保留。 |
| y4 | oooxo | 臨 | `τ4 = T_{e4}` | 保留。 |
| y5 | oooox | 易內 | `τ5 = T_{e5}` | 可继续找更好单字；`改` 不推荐，因与 y1 冲突。 |

## Naming Rule

- 精确名永远是 `T_m` 或 `τ_i` 的和成；中文名只是 reader alias。
- 能自然成词且不混淆 mask 的组合，可以升为默认公开名，例如 `改變`、`變化`。
- 没有可靠古文或现代汉语准确词时，保留 `A+B`，不要把机械组合伪装成古已有定名。
- `內化`、`內變` 这类可读词先列为候选：它们可读，但现代义或抽象义较强，不急着升为默认名。
- `儒道法佛 / 形式逻辑数学 / 哲学 / 科学` 四列是跨语境表达候选；不是 parser 名，也不是声称各传统已有这 32 个 operator 的严格定名。

## R5 Operator Table

| ox | 形式名 | 当前/推荐公开名 | 儒道法佛 | 形式逻辑/数学 | 哲学 | 科学 | 备选字词 | 判断 |
|---|---|---|---|---|---|---|---|---|
| ooooo | `T_0 = id` | 恒 | 儒: 常/中; 道: 常道/无为; 法: 定法; 佛: 如如/真如/寂静 | identity map; zero vector; neutral element | identity; invariance; no-op | no perturbation; identity transform; baseline | 恒等 | 推荐；准确且常用。 |
| oooox | `T_{e5} = τ5` | 易內 | 儒: 反求诸己/反身; 道: 内观/内守; 法: 术; 佛: 内观/内照 | negate y5; xor with `e5`; involution | inner toggle; internal boundary | latent-state flip; hidden-variable toggle; internal mode switch | 內易、納、入 | 暂保留；不要改为 `改`，否则与 `xoooo` 共名。 |
| oooxo | `T_{e4} = τ4` | 臨 | 儒: 临事/临民; 道: 应物; 法: 临事制断; 佛: 临境/对境 | negate y4; xor with `e4`; involution | encounter; situated application | context switch; boundary condition; interaction event | 临、莅 | 推荐；保留为 y4 原子。 |
| oooxx | `T_{e4+e5} = τ4τ5` | 臨+易內 | 儒: 反身临事; 道: 内观应物; 法: 术应事; 佛: 内观临境 | negate y4,y5; xor with `e4+e5`; involution | internalized encounter; situated inward turn | context-conditioned internal mode switch | 內臨 | 暂保留机械合成；未见准确常用词。 |
| ooxoo | `T_{e3} = τ3` | 變 | 儒: 变易/通变/权; 道: 反者道之动/化; 法: 变法; 佛: 无常/变易 | negate y3; xor with `e3`; involution | change; reversal; contingency | state transition; mutation; perturbation | 变 | 推荐；保留为 y3 原子。 |
| ooxox | `T_{e3+e5} = τ3τ5` | 變+易內 | 儒: 反身通变; 道: 内观其变; 法: 术/变法; 佛: 观无常 | negate y3,y5; xor with `e3+e5`; involution | internal change; change of disposition | latent transition; parameter flip | 內變 | 候选 `內變` 可读，但不是稳固定名；暂不升默认。 |
| ooxxo | `T_{e3+e4} = τ3τ4` | 變+臨 | 儒: 临变/权变; 道: 因变应物; 法: 因时制宜/变法; 佛: 随缘应变 | negate y3,y4; xor with `e3+e4`; involution | change-in-situation; adaptive response | transition under boundary condition; adaptive perturbation | 临变 | `临变` 在汉语中偏“遇变/临机变通”，不精确；暂保留。 |
| ooxxx | `T_{e3+e4+e5} = τ3τ4τ5` | 變+臨+易內 | 儒: 反身临变; 道: 内观应变; 法: 术应变; 佛: 观无常而应缘 | negate y3,y4,y5; xor with `e3+e4+e5`; involution | internalized adaptive change | contextual latent transition | 內變+臨 | 暂保留；组合意义清楚。 |
| oxooo | `T_{e2} = τ2` | 化 | 儒: 教化/化育/化成; 道: 道化/自然化成; 法: 以法化民; 佛: 教化/度化 | negate y2; xor with `e2`; involution | transformation; formation; becoming | transform; morphogenesis; phase change | 化 | 推荐；保留为 y2 原子。 |
| oxoox | `T_{e2+e5} = τ2τ5` | 化+易內 | 儒: 内化/成己; 道: 内炼/内化; 法: 化民之术; 佛: 熏习/转依 | negate y2,y5; xor with `e2+e5`; involution | internalization; inward transformation | internalization; assimilation; representation update | 內化 | `內化` 是好候选，但现代术语义较强；先不默认。 |
| oxoxo | `T_{e2+e4} = τ2τ4` | 化+臨 | 儒: 临民教化; 道: 应物化成; 法: 以法化民; 佛: 应机教化 | negate y2,y4; xor with `e2+e4`; involution | situated transformation; responsive formation | contextual transformation; stimulus-response adaptation | 临化、化臨 | 未见准确常用词；暂保留。 |
| oxoxx | `T_{e2+e4+e5} = τ2τ4τ5` | 化+臨+易內 | 儒: 反身教化; 道: 内观化成; 法: 术化应事; 佛: 内观应机教化 | negate y2,y4,y5; xor with `e2+e4+e5`; involution | internalized situated transformation | context-conditioned internal transformation | 內化+臨 | 暂保留。 |
| oxxoo | `T_{e2+e3} = τ2τ3` | 變化 | 儒: 变化/通变/化育; 道: 万物化生/物化; 法: 变法; 佛: 生灭变化/诸行无常 | negate y2,y3; xor with `e2+e3`; involution | becoming; transformation-through-change | dynamics; phase transition; evolution | 化變 | 推荐；`變化` 是准确汉语成词，formal mask 仍是 y2+y3。 |
| oxxox | `T_{e2+e3+e5} = τ2τ3τ5` | 變化+易內 | 儒: 反身变化; 道: 内观物化; 法: 内术变法; 佛: 观生灭变化 | negate y2,y3,y5; xor with `e2+e3+e5`; involution | internalized becoming | latent dynamics; internal phase transition | 內變化 | 推荐；用 `變化` 收束 y2+y3，y5 仍显式。 |
| oxxxo | `T_{e2+e3+e4} = τ2τ3τ4` | 變化+臨 | 儒: 临变化/权变; 道: 应物变化; 法: 因时变法; 佛: 随缘观无常 | negate y2,y3,y4; xor with `e2+e3+e4`; involution | situated becoming; adaptive transformation | context-driven dynamics; regime transition | 临变化 | 推荐；同上。 |
| oxxxx | `T_{e2+e3+e4+e5} = τ2τ3τ4τ5` | 變化+臨+易內 | 儒: 反身临变化; 道: 内观应物变化; 法: 术应变法; 佛: 内观随缘生灭 | negate y2,y3,y4,y5; xor with `e2+e3+e4+e5`; involution | internalized situated becoming | context-conditioned latent dynamics | 內變化+臨 | 推荐；同上。 |
| xoooo | `T_{e1} = τ1` | 改 | 儒: 改过/迁善; 道: 反复/改观; 法: 更法/改制; 佛: 忏悔/改悔 | negate y1; xor with `e1`; involution | revision; correction; rewrite | edit operation; update; intervention | 改 | 推荐；保留为 y1 原子。 |
| xooox | `T_{e1+e5} = τ1τ5` | 改+易內 | 儒: 改过自新/反求诸己; 道: 内观改心; 法: 内术改制; 佛: 忏悔转心 | negate y1,y5; xor with `e1+e5`; involution | inner revision; self-correction | internal state update; self-correction | 內改 | `內改` 可读性弱；暂保留。 |
| xooxo | `T_{e1+e4} = τ1τ4` | 改+臨 | 儒: 临事改过; 道: 应物改观; 法: 临事改制; 佛: 对境转心 | negate y1,y4; xor with `e1+e4`; involution | situated revision | context-driven update; feedback correction | 临改 | 未见准确常用词；暂保留。 |
| xooxx | `T_{e1+e4+e5} = τ1τ4τ5` | 改+臨+易內 | 儒: 反身临事改过; 道: 内观应物改观; 法: 术中改制; 佛: 内观对境转心 | negate y1,y4,y5; xor with `e1+e4+e5`; involution | internalized situated revision | feedback-driven internal update | 內改+臨 | 暂保留。 |
| xoxoo | `T_{e1+e3} = τ1τ3` | 改變 | 儒: 改过迁善/改变; 道: 反复转化; 法: 变法/更法; 佛: 转变/转依 | negate y1,y3; xor with `e1+e3`; involution | revision plus change; transformation of rule | state update; mutation plus edit; regime shift | 改+變 | 推荐；`改變` 是准确汉语成词，formal mask 仍是 y1+y3。 |
| xoxox | `T_{e1+e3+e5} = τ1τ3τ5` | 改變+易內 | 儒: 反身改变; 道: 内观反复转化; 法: 内术变法; 佛: 内观转依 | negate y1,y3,y5; xor with `e1+e3+e5`; involution | internalized revisionary change | latent regime update | 內改變 | 推荐；用 `改變` 收束 y1+y3，y5 仍显式。 |
| xoxxo | `T_{e1+e3+e4} = τ1τ3τ4` | 改變+臨 | 儒: 临事改变/权变; 道: 应物反复; 法: 因时更法; 佛: 随缘转心 | negate y1,y3,y4; xor with `e1+e3+e4`; involution | situated revisionary change | adaptive update; context-driven regime shift | 临改變 | 推荐；同上。 |
| xoxxx | `T_{e1+e3+e4+e5} = τ1τ3τ4τ5` | 改變+臨+易內 | 儒: 反身临变而改; 道: 内观应物反复; 法: 术中因时更法; 佛: 内观随缘转依 | negate y1,y3,y4,y5; xor with `e1+e3+e4+e5`; involution | internalized situated revisionary change | context-conditioned latent regime update | 內改變+臨 | 推荐；同上。 |
| xxooo | `T_{e1+e2} = τ1τ2` | 改+化 | 儒: 改过教化/迁善; 道: 改观化成; 法: 改制化民; 佛: 转化/教化 | negate y1,y2; xor with `e1+e2`; involution | revision plus transformation | rewrite transform; intervention-induced transformation | 改化 | `改化` 可读但不如 `改變/變化` 稳；暂不升。 |
| xxoox | `T_{e1+e2+e5} = τ1τ2τ5` | 改+化+易內 | 儒: 反身改化; 道: 内观化成; 法: 术中化民; 佛: 熏习转化 | negate y1,y2,y5; xor with `e1+e2+e5`; involution | internalized revision-transformation | internal rewrite transform | 內改化 | 暂保留。 |
| xxoxo | `T_{e1+e2+e4} = τ1τ2τ4` | 改+化+臨 | 儒: 临事改化; 道: 应物改化; 法: 临事改制化民; 佛: 应机转化 | negate y1,y2,y4; xor with `e1+e2+e4`; involution | situated revision-transformation | feedback-driven transform | 改化+臨 | 暂保留。 |
| xxoxx | `T_{e1+e2+e4+e5} = τ1τ2τ4τ5` | 改+化+臨+易內 | 儒: 反身临事改化; 道: 内观应物化成; 法: 术中应事化民; 佛: 内观应机转化 | negate y1,y2,y4,y5; xor with `e1+e2+e4+e5`; involution | internalized situated revision-transformation | context-conditioned internal rewrite transform | 內改化+臨 | 暂保留。 |
| xxxoo | `T_{e1+e2+e3} = τ1τ2τ3` | 改+變化 | 儒: 改过变化/迁善化育; 道: 反复物化; 法: 改制变法; 佛: 转依生灭观 | negate y1,y2,y3; xor with `e1+e2+e3`; involution | revision of becoming; directed transformation | intervention in dynamics; controlled evolution | 改化變 | 推荐；用 `變化` 收束 y2+y3，`改` 仍显式。 |
| xxxox | `T_{e1+e2+e3+e5} = τ1τ2τ3τ5` | 改+變化+易內 | 儒: 反身改过变化; 道: 内观反复物化; 法: 内术变法; 佛: 内观转依生灭 | negate y1,y2,y3,y5; xor with `e1+e2+e3+e5`; involution | internalized revision of becoming | latent controlled dynamics | 內改+變化 | 推荐；同上。 |
| xxxxo | `T_{e1+e2+e3+e4} = τ1τ2τ3τ4` | 改+變化+臨 | 儒: 临事改过变化; 道: 应物反复物化; 法: 因时改制变法; 佛: 随缘转依生灭 | negate y1,y2,y3,y4; xor with `e1+e2+e3+e4`; involution | situated revision of becoming | feedback control of dynamics | 改變化+臨 | 推荐；同上。 |
| xxxxx | `T_{e1+e2+e3+e4+e5} = τ1τ2τ3τ4τ5` | 改+變化+臨+易內 | 儒: 反身临事改过变化; 道: 内观应物反复物化; 法: 术中因时改制变法; 佛: 内观随缘转依生灭 | negate y1,y2,y3,y4,y5; xor with `e1+e2+e3+e4+e5`; involution | fully internalized situated revision of becoming | context-conditioned latent control of dynamics | 內改+變化+臨 | 推荐；同上。 |

## Notes

- `oooxx`、`ooxox`、`ooxxo` 这些没有独立形式逻辑 connective 名；形式逻辑里准确说法就是 `(Z/2)^5` 的 mask translation，或 Boolean vector space 上 xor with constant mask。
- `negate y_i` 指 coordinate negation，不是整句命题否定；多个 y 位表示同时翻转对应坐标。
- 每个非零 `T_m` 都是 involution，但 `involution` 只说明自反性，不能区分是哪一个 mask，所以不能作为公开名。
