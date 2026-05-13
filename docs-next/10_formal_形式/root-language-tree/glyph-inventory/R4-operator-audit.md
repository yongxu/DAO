# R4 Operator Audit

> 状态：审名 v0.1 (2026-05-13)。
> 范围：R4 面的 16 个 operator reader names；R1-R3 见 [R1-R3-operator-audit.md](R1-R3-operator-audit.md)，R5 见 [R5-operator-audit.md](R5-operator-audit.md)。
> 形式口径：每个 bitstring `m` 表示 `(Z/2)^4` 上的平移 `T_m(s)=m xor s`。若 `e_i` 是第 `i` 位 basis，则 `τ_i = T_{e_i}`，所有 `τ_i` 交换。

## Naming Rule

- R4 operator 只审 action surface；R4 cell 的 16 个面名字另由 `r4-r8-character-ladder.md` 管。
- 精确名永远是 `T_m` 或 `τ_i` 的和成；中文名只是 reader alias。
- 能自然成词且不混淆 mask 的组合可升为公开名：`變化 = 化+變`，`改變 = 改+變`。
- 其余多原子组合用 `+` 分隔，不写成 `改化變臨` 这种串。
- `儒道法佛 / 形式逻辑数学 / 哲学 / 科学` 四列是跨语境表达候选；不是 parser 名，也不是声称各传统已有这些 operator 的严格定名。

## R4 Operator Table

| ox | 形式名 | 当前/推荐公开名 | 儒道法佛 | 形式逻辑/数学 | 哲学 | 科学 | 备选字词 | 判断 |
|---|---|---|---|---|---|---|---|---|
| oooo | `T_0 = id` | 恒 | 儒: 常/中; 道: 常道/无为; 法: 定法; 佛: 如如/真如/寂静 | identity map; zero vector; neutral element | identity; invariance; no-op | no perturbation; identity transform; baseline | 恒等 | 推荐；准确且常用。 |
| ooox | `T_{e4} = τ4` | 臨 | 儒: 临事/临民; 道: 应物; 法: 临事制断; 佛: 临境/对境 | negate y4; xor with `e4`; coordinate involution | encounter; situated application | context switch; boundary condition; interaction event | 临、莅 | 推荐；保留为 y4 原子。 |
| ooxo | `T_{e3} = τ3` | 變 | 儒: 变易/通变/权; 道: 反者道之动/化; 法: 变法; 佛: 无常/变易 | negate y3; xor with `e3`; coordinate involution | change; reversal; contingency | state transition; mutation; perturbation | 变 | 推荐；保留为 y3 原子。 |
| ooxx | `T_{e3+e4} = τ3τ4` | 變+臨 | 儒: 临变/权变; 道: 因变应物; 法: 因时制宜/变法; 佛: 随缘应变 | negate y3,y4; xor with `e3+e4`; involution | change-in-situation; adaptive response | transition under boundary condition; adaptive perturbation | 临变 | `临变` 偏“遇变/临机变通”，不精确；暂保留显式组合。 |
| oxoo | `T_{e2} = τ2` | 化 | 儒: 教化/化育/化成; 道: 道化/自然化成; 法: 以法化民; 佛: 教化/度化 | negate y2; xor with `e2`; coordinate involution | transformation; formation; becoming | transform; morphogenesis; phase change | 化 | 推荐；保留为 y2 原子。 |
| oxox | `T_{e2+e4} = τ2τ4` | 化+臨 | 儒: 临民教化; 道: 应物化成; 法: 以法化民; 佛: 应机教化 | negate y2,y4; xor with `e2+e4`; involution | situated transformation; responsive formation | contextual transformation; stimulus-response adaptation | 临化、化臨 | 未见准确常用词；暂保留显式组合。 |
| oxxo | `T_{e2+e3} = τ2τ3` | 變化 | 儒: 变化/通变/化育; 道: 万物化生/物化; 法: 变法; 佛: 生灭变化/诸行无常 | negate y2,y3; xor with `e2+e3`; involution | becoming; transformation-through-change | dynamics; phase transition; evolution | 化變 | 推荐；`變化` 是准确汉语成词，formal mask 仍是 y2+y3。 |
| oxxx | `T_{e2+e3+e4} = τ2τ3τ4` | 變化+臨 | 儒: 临变化/权变; 道: 应物变化; 法: 因时变法; 佛: 随缘观无常 | negate y2,y3,y4; xor with `e2+e3+e4`; involution | situated becoming; adaptive transformation | context-driven dynamics; regime transition | 临变化 | 推荐；用 `變化` 收束 y2+y3，y4 仍显式。 |
| xooo | `T_{e1} = τ1` | 改 | 儒: 改过/迁善; 道: 反复/改观; 法: 更法/改制; 佛: 忏悔/改悔 | negate y1; xor with `e1`; coordinate involution | revision; correction; rewrite | edit operation; update; intervention | 改 | 推荐；保留为 y1 原子。 |
| xoox | `T_{e1+e4} = τ1τ4` | 改+臨 | 儒: 临事改过; 道: 应物改观; 法: 临事改制; 佛: 对境转心 | negate y1,y4; xor with `e1+e4`; involution | situated revision | context-driven update; feedback correction | 临改 | 未见准确常用词；暂保留显式组合。 |
| xoxo | `T_{e1+e3} = τ1τ3` | 改變 | 儒: 改过迁善/改变; 道: 反复转化; 法: 变法/更法; 佛: 转变/转依 | negate y1,y3; xor with `e1+e3`; involution | revision plus change; transformation of rule | state update; mutation plus edit; regime shift | 改+變 | 推荐；`改變` 是准确汉语成词，formal mask 仍是 y1+y3。 |
| xoxx | `T_{e1+e3+e4} = τ1τ3τ4` | 改變+臨 | 儒: 临事改变/权变; 道: 应物反复; 法: 因时更法; 佛: 随缘转心 | negate y1,y3,y4; xor with `e1+e3+e4`; involution | situated revisionary change | adaptive update; context-driven regime shift | 临改變 | 推荐；用 `改變` 收束 y1+y3，y4 仍显式。 |
| xxoo | `T_{e1+e2} = τ1τ2` | 改+化 | 儒: 改过教化/迁善; 道: 改观化成; 法: 改制化民; 佛: 转化/教化 | negate y1,y2; xor with `e1+e2`; involution | revision plus transformation | rewrite transform; intervention-induced transformation | 改化 | `改化` 可读但不如 `改變/變化` 稳；R4 主表用 `+` 消歧。 |
| xxox | `T_{e1+e2+e4} = τ1τ2τ4` | 改+化+臨 | 儒: 临事改化; 道: 应物改化; 法: 临事改制化民; 佛: 应机转化 | negate y1,y2,y4; xor with `e1+e2+e4`; involution | situated revision-transformation | feedback-driven transform | 改化+臨 | 暂保留显式组合。 |
| xxxo | `T_{e1+e2+e3} = τ1τ2τ3` | 改+變化 | 儒: 改过变化/迁善化育; 道: 反复物化; 法: 改制变法; 佛: 转依生灭观 | negate y1,y2,y3; xor with `e1+e2+e3`; involution | revision of becoming; directed transformation | intervention in dynamics; controlled evolution | 改化變 | 推荐；用 `變化` 收束 y2+y3，`改` 仍显式。 |
| xxxx | `T_{e1+e2+e3+e4} = τ1τ2τ3τ4` | 改+變化+臨 | 儒: 临事改过变化; 道: 应物反复物化; 法: 因时改制变法; 佛: 随缘转依生灭 | negate y1,y2,y3,y4; xor with `e1+e2+e3+e4`; involution | situated revision of becoming | feedback control of dynamics | 改變化+臨 | 推荐；用 `變化` 收束 y2+y3，`改/臨` 仍显式。 |

## Notes

- `negate y_i` 指 coordinate negation，不是整句命题否定；多个 y 位表示同时翻转对应坐标。
- 每个非零 `T_m` 都是 involution，但 `involution` 只说明自反性，不能区分是哪一个 mask，所以不能作为公开名。
