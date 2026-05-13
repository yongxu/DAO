# R1-R3 Operator Audit

> 状态：审名 v0.1 (2026-05-13)。
> 范围：R1 爻、R2 四象、R3 八卦的 operator reader names；R5 operator 审名见 [R5-operator-audit.md](R5-operator-audit.md)。
> 形式口径：每个 bitstring `m` 表示 `(Z/2)^n` 上的平移 `T_m(s)=m xor s`。若 `e_i` 是第 `i` 位 basis，则 `τ_i = T_{e_i}`，所有 `τ_i` 交换。

## Naming Rule

- 精确名永远是 `T_m` 或 `τ_i` 的和成；中文名只是 reader alias。
- R1 有传统互易 anchor，非零 operator 可直接叫 `易`。
- R2 没有稳定古典 lateral operator 名；`初易/二易/並易` 可读，但先列为审名候选。
- R3 可沿用项目已稳定的 `改/化/變/錯`；其中 `變化`、`改變` 与 R5 同步，`錯` 表示三爻全反。
- `儒道法佛 / 形式逻辑数学 / 哲学 / 科学` 四列是跨语境表达候选；不是 parser 名，也不是声称各传统已有这些 operator 的严格定名。

## R1 Operator Table

| ox | 形式名 | 当前/推荐公开名 | 儒道法佛 | 形式逻辑/数学 | 哲学 | 科学 | 备选字词 | 判断 |
|---|---|---|---|---|---|---|---|---|
| o | `T_0 = id` | 恒 | 儒: 常/中; 道: 常道/无为; 法: 定法; 佛: 如如/真如/寂静 | identity map; zero vector; neutral element | identity; invariance; no-op | no perturbation; identity transform; baseline | 恒等 | 推荐；准确且常用。 |
| x | `T_{e1} = τ1` | 易 | 儒: 易/变易/阴阳互易; 道: 反者道之动; 法: 更易其法; 佛: 无常/转变 | negate y1; xor with `e1`; Boolean complement; involution | alternation; reversal; polarity switch | binary flip; bit complement; two-state transition | 反、翻、轉、互易 | 推荐；R1 非零 operator 即阴阳互易。 |

## R2 Operator Table

| ox | 形式名 | 当前/推荐公开名 | 儒道法佛 | 形式逻辑/数学 | 哲学 | 科学 | 备选字词 | 判断 |
|---|---|---|---|---|---|---|---|---|
| oo | `T_0 = id` | 恒 | 儒: 常/中; 道: 常道/无为; 法: 定法; 佛: 如如/寂静 | identity map; zero vector; neutral element | identity; invariance; no-op | no perturbation; identity transform; baseline | 恒等 | 推荐；准确且常用。 |
| ox | `T_{e2} = τ2` | ox | 儒: 二位之易; 道: 一端反复; 法: 二柄之一; 佛: 一边转变 | negate y2; xor with `e2`; coordinate involution | second-axis toggle; one-sided change | flip second coordinate; quadrant reflection | 二易、上易、末易 | 现主表仍用 mask fallback；`二易` 可作为可读候选。 |
| xo | `T_{e1} = τ1` | xo | 儒: 初位之易; 道: 一端反复; 法: 二柄之一; 佛: 一边转变 | negate y1; xor with `e1`; coordinate involution | first-axis toggle; one-sided change | flip first coordinate; quadrant reflection | 初易、下易、本易 | 现主表仍用 mask fallback；`初易` 可作为可读候选。 |
| xx | `T_{e1+e2} = τ1τ2` | xx | 儒: 两仪并易; 道: 反复; 法: 二柄并用; 佛: 两边俱转 | negate y1,y2; xor with `e1+e2`; complement; involution | double reversal; full polarity switch | bitwise complement on 2 bits; half-turn | 並易、俱易、錯 | 现主表仍用 mask fallback；若按全反读，可候选 `錯`。 |

## R3 Operator Table

| ox | 形式名 | 当前/推荐公开名 | 儒道法佛 | 形式逻辑/数学 | 哲学 | 科学 | 备选字词 | 判断 |
|---|---|---|---|---|---|---|---|---|
| ooo | `T_0 = id` | 恒 | 儒: 常/中; 道: 常道/无为; 法: 定法; 佛: 如如/寂静 | identity map; zero vector; neutral element | identity; invariance; no-op | no perturbation; identity transform; baseline | 恒等 | 推荐；准确且常用。 |
| oox | `T_{e3} = τ3` | 變 | 儒: 变易/通变/权; 道: 反者道之动/化; 法: 变法; 佛: 无常/变易 | negate y3; xor with `e3`; coordinate involution | change; reversal; contingency | state transition; mutation; perturbation | 變、翻三 | 推荐；保留为第三位原子。 |
| oxo | `T_{e2} = τ2` | 化 | 儒: 教化/化育/化成; 道: 道化/自然化成; 法: 以法化民; 佛: 教化/度化 | negate y2; xor with `e2`; coordinate involution | transformation; formation; becoming | transform; morphogenesis; phase change | 化、翻二 | 推荐；保留为第二位原子。 |
| oxx | `T_{e2+e3} = τ2τ3` | 變化 | 儒: 变化/通变/化育; 道: 万物化生/物化; 法: 变法; 佛: 生灭变化/诸行无常 | negate y2,y3; xor with `e2+e3`; involution | becoming; transformation-through-change | dynamics; phase transition; evolution | 化變 | 推荐；与 R5 的 y2+y3 alias 同步。 |
| xoo | `T_{e1} = τ1` | 改 | 儒: 改过/迁善; 道: 反复/改观; 法: 更法/改制; 佛: 忏悔/改悔 | negate y1; xor with `e1`; coordinate involution | revision; correction; rewrite | edit operation; update; intervention | 改、翻初 | 推荐；保留为第一位原子。 |
| xox | `T_{e1+e3} = τ1τ3` | 改變 | 儒: 改过迁善/改变; 道: 反复转化; 法: 变法/更法; 佛: 转变/转依 | negate y1,y3; xor with `e1+e3`; involution | revision plus change; transformation of rule | state update; mutation plus edit; regime shift | 改+變 | 推荐；与 R5 的 y1+y3 alias 同步。 |
| xxo | `T_{e1+e2} = τ1τ2` | 改化 | 儒: 改过教化/迁善; 道: 改观化成; 法: 改制化民; 佛: 转化/教化 | negate y1,y2; xor with `e1+e2`; involution | revision plus transformation | rewrite transform; intervention-induced transformation | 改+化 | 可读但不如 `改變/變化` 稳；暂保留。 |
| xxx | `T_{e1+e2+e3} = τ1τ2τ3` | 錯 | 儒: 错卦/旁通; 道: 反复; 法: 反制/易位; 佛: 反观/对治 | negate y1,y2,y3; full complement; involution | complement; total reversal; opposite | bitwise complement on 3 bits; parity inversion | 改+化+變、全反 | 推荐；`錯` 是三爻全反的传统可读名。 |

## Notes

- `negate y_i` 指 coordinate negation，不是整句命题否定；多个 y 位表示同时翻转对应坐标。
- 每个非零 `T_m` 都是 involution，但 `involution` 只说明自反性，不能区分是哪一个 mask，所以不能作为公开名。
