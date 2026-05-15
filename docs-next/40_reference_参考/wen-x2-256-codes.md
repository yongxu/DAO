# X² 256 码表

从 `oooooooo` 到 `xxxxxxxx`,8 个对偶轴的全枚举。每条都按"轴的语义 × 结构对称 × F₂⁸ 位置"三层填实。

## 编码方案

8 个 bit 位对应 8 个对偶轴。`o` (= 0) 取轴的阳侧 (生成/源/未分),`x` (= 1) 取阴侧 (承载/显/已分)。从左到右:

| 位 | 轴 | `o` 侧 (0) | `x` 侧 (1) | 类 | X² 回声配对 | palindrome 配对 |
|---|---|---|---|---|---|---|
| 1 | 阴阳 | 阳 | 阴 | 本体 | ↔ 5 (名实) | ↔ 8 (因果) |
| 2 | 有无 | 有 | 无 | 本体 | ↔ 6 (是非) | ↔ 7 (知行) |
| 3 | 体用 | 体 | 用 | 本体 | ↔ 7 (知行) | ↔ 6 (是非) |
| 4 | 形声 | 形 | 声 | 本体 | ↔ 8 (因果) | ↔ 5 (名实) |
| 5 | 名实 | 名 | 实 | 实用 | ↔ 1 (阴阳) | ↔ 4 (形声) |
| 6 | 是非 | 是 | 非 | 实用 | ↔ 2 (有无) | ↔ 3 (体用) |
| 7 | 知行 | 知 | 行 | 实用 | ↔ 3 (体用) | ↔ 2 (有无) |
| 8 | 因果 | 因 | 果 | 实用 | ↔ 4 (形声) | ↔ 1 (阴阳) |

**约定:**

- 编号从 0 (`oooooooo`) 到 255 (`xxxxxxxx`)
- **对偶** = bitwise NOT(即 `255 − n`)
- **(X, X) 构成** = 左 4 bit · 右 4 bit 两半。两半相等 ⇒ *true X²* (X·X 自方)。X² 内含 16 个 self-square 对角元 (n = 17 × h, h ∈ 0..15)
- **palindrome** = 8 位反序 = 自身。F₂⁸ 中 16 个不动点 (mirror invariant)
- **comp-palindrome** = 反序后取补 = 自身。F₂⁸ 中 16 个反不动点 (anti-mirror)
- **subtitle** 自动派生自分解,256 个全部唯一
- **本体类** (位 1–4 / X 左半): 阴阳 · 有无 · 体用 · 形声 — 形上骨架
- **实用类** (位 5–8 / X 右半): 名实 · 是非 · 知行 · 因果 — 实用展开
- **古文**: 仅在 (拟) 或确有典籍原型时填; 其余 200 余条诚实标 `没有`。其他四栏 (现代汉语·英语·形式逻辑·Why) 每条非空。

**关键结构计数:**

- **palindrome**: 16 个 — {0, 24, 36, 60, 66, 90, 102, 126, 129, 153, 165, 189, 195, 219, 231, 255}
- **true X²**: 16 个 — {0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255}
- **comp-palindrome**: 16 个 — {15, 23, 43, 51, 77, 85, 105, 113, 142, 150, 170, 178, 204, 212, 232, 240}
- **palindrome ∩ true X²**: 4 个 — {0, 102, 153, 255} (最对称)
- **true X² ∩ comp-palindrome**: 4 个 — {51, 85, 170, 204} (Walsh 基函数)
- **palindrome ∩ comp-palindrome**: ∅ (定义上互斥)
- **单点阴扰动** (weight 1): 8 个 — {1, 2, 4, 8, 16, 32, 64, 128}, 即首阶 8 个分化方向
- **单点阳留存** (weight 7): 8 个 — {127, 191, 223, 239, 247, 251, 253, 254}, 即末阶 8 个守护方向

---

## 完整列表 (0 → 255)

### `oooooooo` · 0  *[true X² · palindrome]*

**Subtitle**: 纯阳极 · 全生成

- **(X, X)**: (oooo, oooo)  ← true X² (左右半相等)
- **分解**: 阳 · 有 · 体 · 形 · 名 · 是 · 知 · 因
- **对偶**: `xxxxxxxx` · 255
- **古文**: 乾元 / 纯阳 / 太极未分
- **现代汉语**: 八轴齐站生成侧,形上未分化的原点。
- **英语**: All eight dual axes on the generative side; pre-articulation, the absolute affirmation.
- **形式逻辑**: ⊤⁸ / F₂⁸ 加法群单位元 0 / Hamming 0 / palindrome ∩ true X² 之 trivial 顶点
- **Why**: 8 个对偶轴 (阴阳·有无·体用·形声·名实·是非·知行·因果) 一齐站在生成侧。F₂⁸ 中的零向量, 任何其它码都可视作其 XOR-偏离 — Hamming 距离即偏离的轴数。在 X² 表 (16×16 自方表) 的右下角对角元, 也是 palindrome 与 true X² 的交集 4 元 (0,102,153,255) 中熵最低者。

### `ooooooox` · 1

**Subtitle**: 1 阴侧 · 果

- **(X, X)**: (oooo, ooox)
- **分解**: 阳 · 有 · 体 · 形 · 名 · 是 · 知 · 果
- **对偶**: `xxxxxxxo` · 254
- **古文**: **果** — 《说文》"果, 木实也"; 佛家因果论之"果", 因明学之"果", 因→果链之末端
- **现代汉语**: 因果一轴跌入果。果先现而因未现,现象先行,追溯滞后。
- **英语**: Single perturbation on cause-effect (→ effect). The outcome shows before the origin is named; phenomenon precedes causal recognition.
- **形式逻辑**: F₂⁸ 单位向量 e₁ (LSB) / |y|₁ = 1 / d(⊤⁸)=1, d(⊥⁸)=7 / yin ⊂ 实用类
- **Why**: Hamming 1 的 8 个邻居之一, 仅 bit 8 (因果轴) 翻至阴侧。这是从纯阳出发"第一步分化"的 8 个方向之一, 对应"现象学维": 果先于因被看见。其 X² 回声为名实轴 (bit 4=阳), palindrome 镜像为阴阳轴 (bit 1=阳), 两者都未动 — 这一点扰动是孤立的。

### `ooooooxo` · 2

**Subtitle**: 1 阴侧 · 行

- **(X, X)**: (oooo, ooxo)
- **分解**: 阳 · 有 · 体 · 形 · 名 · 是 · 行 · 因
- **对偶**: `xxxxxxox` · 253
- **古文**: **行** — 《说文》"行, 人之步趋也"; 儒家"力行近乎仁"; 王阳明"知行合一"之"行"
- **现代汉语**: 知行一轴入行。未学已动,本能先于反思。
- **英语**: Single perturbation on know-act (→ acting). Movement precedes deliberation; pre-reflective doing.
- **形式逻辑**: F₂⁸ 单位向量 e₂ / |y|₁ = 1 / d(⊤⁸)=1, d(⊥⁸)=7 / yin ⊂ 实用类
- **Why**: Hamming 1 之一, 仅 bit 7 (知行轴) 翻。代表"动作维"的最小启动: 还未生反思, 已有动作 — 王阳明的"知行合一"在此被打破, 行先行而知未起。对偶 #253 (留知失行) 是其在阴极一侧的镜像。

### `ooooooxx` · 3

**Subtitle**: 2 阴侧 · 行 · 果

- **(X, X)**: (oooo, ooxx)
- **分解**: 阳 · 有 · 体 · 形 · 名 · 是 · 行 · 果
- **对偶**: `xxxxxxoo` · 252
- **古文**: **业** — 佛家"行+果=业" (karma); 韩愈《进学解》"业精于勤"; 行因结果之合
- **现代汉语**: 知行+因果 末两轴双翻。行动 → 后果, 实用尾两轴联动。
- **英语**: Yin on the tail two pragmatic axes: action and effect. The "doing→outcome" couplet, while ontology stays pristine.
- **形式逻辑**: |y|₁ = 2 / e₃ / d(⊤⁸)=2, d(⊥⁸)=6 / yin ⊂ 实用类末段 (bit 7,8)
- **Why**: 实用类最末两轴 (知行·因果) 同时入阴 — 行动产生后果, 这是最朴素的实用因果链 "行→果"。本体 4 轴 (阴阳·有无·体用·形声) 全保留生成侧, 6 轴皆阳, 仅末尾闭环动了起来。

### `oooooxoo` · 4

**Subtitle**: 1 阴侧 · 非

- **(X, X)**: (oooo, oxoo)
- **分解**: 阳 · 有 · 体 · 形 · 名 · 非 · 知 · 因
- **对偶**: `xxxxxoxx` · 251
- **古文**: **非** — 《说文》"非, 违也"; 庄子《齐物论》"是非之彰也, 道之所以亏也"
- **现代汉语**: 是非一轴入非。异见初萌,否定意识第一次出现。
- **英语**: Single perturbation on right-wrong (→ wrong/negation). The first emergence of dissent or negative judgment.
- **形式逻辑**: F₂⁸ 单位向量 e₄ / |y|₁ = 1 / d(⊤⁸)=1, d(⊥⁸)=7 / yin ⊂ 实用类
- **Why**: 仅 bit 6 (是非轴) 翻。这是"判断维"的最小启动: 在万象皆是的纯阳中, 第一个"非"破出。庄子《齐物论》视域里, 此即"是非之彰也, 道之所以亏也"。对偶 #251 留是失非。

### `oooooxox` · 5

**Subtitle**: 2 阴侧 · 非 · 果

- **(X, X)**: (oooo, oxox)
- **分解**: 阳 · 有 · 体 · 形 · 名 · 非 · 知 · 果
- **对偶**: `xxxxxoxo` · 250
- **古文**: **殃** — 《诗·小雅》"自取殃咎"; 否定判断 + 后果 = 殃 / 祸; 否者之果
- **现代汉语**: 是非+因果 双翻 (非+果)。错谬的果, 是非之争与现象后果联动。
- **英语**: Two-axis yin: wrong-judgment plus effect. Negation paired with manifest outcome — the "bad result" mode.
- **形式逻辑**: |y|₁ = 2 / e₅ / yin 在 bit 6, 8 (跳过 7)
- **Why**: 是非翻至非, 因果翻至果, 中间 bit 7 (知行) 不动留知。"非果" 的结构 — 有错谬的结果已经显现, 但行动还未起 (还在"知"的阶段)。对偶 #250 翻转。

### `oooooxxo` · 6

**Subtitle**: 2 阴侧 · 非 · 行

- **(X, X)**: (oooo, oxxo)
- **分解**: 阳 · 有 · 体 · 形 · 名 · 非 · 行 · 因
- **对偶**: `xxxxxoox` · 249
- **古文**: **戾** — 《说文》"戾, 曲也"; 非 + 行 = 戾 (悖逆); 《左传》"民将不堪命矣"
- **现代汉语**: 是非+知行 双翻 (非+行)。错行 / 知非而行非, 判断与行动同步偏离。
- **英语**: Two-axis yin: wrong-judgment plus acting. Negation joined with action — the "doing wrong" mode (without yet a closed effect).
- **形式逻辑**: |y|₁ = 2 / e₆ / yin 在 bit 6, 7
- **Why**: 是非翻非, 知行翻行, 因果未动留因。"非行" 结构 — 错的行动正在进行, 但其后果还未闭合 (因果留因)。这是行动伦理的临界态。

### `oooooxxx` · 7

**Subtitle**: 3 阴侧 · 非 · 行 · 果

- **(X, X)**: (oooo, oxxx)
- **分解**: 阳 · 有 · 体 · 形 · 名 · 非 · 行 · 果
- **对偶**: `xxxxxooo` · 248
- **古文**: **罪** — 《说文》"罪, 犯法也"; 非 + 行 + 果 = 罪 (《尚书》"刑期于无刑"); 法家根本范畴
- **现代汉语**: 实用类后三轴翻 (非+行+果), 唯名实留阳。错判断 + 错行动 + 错后果, 三连锁。
- **英语**: Three pragmatic axes flip: wrong-judgment, acting, effect — full pragmatic cascade with naming still pristine.
- **形式逻辑**: |y|₁ = 3 / e₇ / yin 在 bit 6,7,8 (实用类末三位)
- **Why**: 是非·知行·因果 同时入阴, 名实留名。语言/概念层 (名) 仍清明, 但判断·行动·后果一环不漏地走向阴侧 — 这是"言行不一"的极端形态: 心中知道某物的名仍然纯, 但判断、行动、后果都已偏。

### `ooooxooo` · 8

**Subtitle**: 1 阴侧 · 实

- **(X, X)**: (oooo, xooo)
- **分解**: 阳 · 有 · 体 · 形 · 实 · 是 · 知 · 因
- **对偶**: `xxxxoxxx` · 247
- **古文**: **实** — 名家"循名责实" (公孙龙·墨经·荀子《正名》); 朱熹"实理实事"
- **现代汉语**: 名实一轴入实。实超出名,现象溢出语言。
- **英语**: Single perturbation on name-reality (→ reality). The thing exceeds its name; the world overflows its labels.
- **形式逻辑**: F₂⁸ 单位向量 e₈ / |y|₁ = 1 / yin ⊂ 实用类首位
- **Why**: 仅 bit 5 (名实轴) 翻。这是"语义维"的最小启动: 在所有概念清明的纯阳中, 第一个不可言说的"实"开始浮现。公孙龙、墨子、荀子的"名实"辩, 在这一点上裂开。X² 回声是 bit 1 (阴阳轴), 这里阴阳留阳 — 即实虽出名, 但根底仍生成侧。

### `ooooxoox` · 9

**Subtitle**: 2 阴侧 · 实 · 果

- **(X, X)**: (oooo, xoox)
- **分解**: 阳 · 有 · 体 · 形 · 实 · 是 · 知 · 果
- **对偶**: `xxxxoxxo` · 246
- **古文**: **验** — 《说文》"验, 證也"; 实 + 果 = 验证; 韩非《五蠹》"故无验而言之曰诬"
- **现代汉语**: 名实+因果 双翻 (实+果)。现象 → 后果, 语义/果 联动。
- **英语**: Two-axis yin: reality and effect. The "thing produces outcome" coupling, with judgment and action untouched.
- **形式逻辑**: |y|₁ = 2 / e₉ / yin 在 bit 5, 8 (实用类首尾)
- **Why**: 实用类的首 (名实) 与尾 (因果) 翻, 中间 (是非·知行) 留阳。这是一种"沉默的展开" — 实/果 双双显化, 但是非判断与知行实践都未发动。X² 回声: bit 5 ↔ bit 1 (阴阳), bit 8 ↔ bit 4 (形声), 两个回声都留阳, 故无 X² 自方。

### `ooooxoxo` · 10

**Subtitle**: 2 阴侧 · 实 · 行

- **(X, X)**: (oooo, xoxo)
- **分解**: 阳 · 有 · 体 · 形 · 实 · 是 · 行 · 因
- **对偶**: `xxxxoxox` · 245
- **古文**: **务** — 《论语·学而》"君子务本, 本立而道生"; 实 + 行 = 务实; 法家"务力"
- **现代汉语**: 名实+知行 双翻 (实+行)。实际去做, 名超而实行起。
- **英语**: Two-axis yin: reality and acting. The "doing the real" mode — language is left behind in pursuit of concrete action.
- **形式逻辑**: |y|₁ = 2 / e₁₀ / yin 在 bit 5, 7
- **Why**: 名实翻实, 知行翻行, 是非 (bit 6) 与因果 (bit 8) 都留阳。这是"实践理性"在判断尚未表态、后果尚未闭合时的纯行动状态 — 王阳明意义下的"知" (本体未变) 与"行" (实用已动) 之分裂。

### `ooooxoxx` · 11

**Subtitle**: 3 阴侧 · 实 · 行 · 果

- **(X, X)**: (oooo, xoxx)
- **分解**: 阳 · 有 · 体 · 形 · 实 · 是 · 行 · 果
- **对偶**: `xxxxoxoo` · 244
- **古文**: **绩** — 《尚书》"九载, 绩用弗成"; 实 + 行 + 果 = 业绩 (荀子"功业不可成")
- **现代汉语**: 名实+知行+因果 三翻, 唯是非留是。实际的行动产生实际的后果, 但判断仍在"是"上。
- **英语**: Three pragmatic axes flip (reality+acting+effect); right-wrong holds at "is". Pragmatic concretion without judgmental dissent.
- **形式逻辑**: |y|₁ = 3 / e₁₁ / yin 在 bit 5,7,8; yang 在 bit 1-4,6
- **Why**: 实用类四轴中, 仅 是非 留阳; 其它三轴 (名实·知行·因果) 全翻。判断仍是"是", 但行动·后果·语义都已沉到现象侧。"心知是, 而身行结果于实" 的执行态。

### `ooooxxoo` · 12

**Subtitle**: 2 阴侧 · 实 · 非

- **(X, X)**: (oooo, xxoo)
- **分解**: 阳 · 有 · 体 · 形 · 实 · 非 · 知 · 因
- **对偶**: `xxxxooxx` · 243
- **古文**: **妄** — 《说文》"妄, 乱也"; 实 + 非 = 名实不符之妄; 庄子"妄言妄听"
- **现代汉语**: 名实+是非 双翻 (实+非)。现实使语言失效, 错判随之而生。
- **英语**: Two-axis yin: reality and wrong-judgment. The thing exceeds its name and the verdict turns negative — semantic/judgmental couplet.
- **形式逻辑**: |y|₁ = 2 / e₁₂ / yin 在 bit 5, 6 (实用类前两位)
- **Why**: 名实·是非 同时翻 — 现象一旦溢出语言, 判断也随之转否。"实溢名, 是变非" 的语义判断耦合。知行·因果 (bit 7,8) 仍留阳, 故还未到行动与后果。

### `ooooxxox` · 13

**Subtitle**: 3 阴侧 · 实 · 非 · 果

- **(X, X)**: (oooo, xxox)
- **分解**: 阳 · 有 · 体 · 形 · 实 · 非 · 知 · 果
- **对偶**: `xxxxooxo` · 242
- **古文**: **谬** — 《说文》"谬, 狂者之妄言也"; 实 + 非 + 果 = 谬误 (《荀子·正名》"狂生者也")
- **现代汉语**: 名实+是非+因果 三翻, 唯知行留知。"实/非/果" 三联, 行动尚未起。
- **英语**: Three yin axes: reality, wrong-judgment, effect. The know-act axis stays at "knowing" — judgment & outcome moved, action withheld.
- **形式逻辑**: |y|₁ = 3 / e₁₃ / yin 在 bit 5,6,8; yang 仅 bit 1-4,7
- **Why**: 实用类除知行外全翻。现象、判断、后果都已显化, 但行动仍停在认知层 — "知而未行" 的纠结状态。心知是非已变、果已显, 而身未动。

### `ooooxxxo` · 14

**Subtitle**: 3 阴侧 · 实 · 非 · 行

- **(X, X)**: (oooo, xxxo)
- **分解**: 阳 · 有 · 体 · 形 · 实 · 非 · 行 · 因
- **对偶**: `xxxxooox` · 241
- **古文**: **过** — 《论语·学而》"过则勿惮改"; 实 + 非 + 行 = 过失
- **现代汉语**: 名实+是非+知行 三翻, 唯因果留因。"实/非/行" 联动而果未闭。
- **英语**: Three yin axes: reality, wrong-judgment, acting. Cause-effect still at "cause" — judgment and action are wrong, but the outcome has not yet closed.
- **形式逻辑**: |y|₁ = 3 / e₁₄ / yin 在 bit 5,6,7; yang 在 bit 1-4,8
- **Why**: 实用类除因果外全翻。语义、判断、行动皆已沉, 但后果还未来到 — "因尚明而果未现" 的中间态。事在做, 但尚未尝果。

### `ooooxxxx` · 15  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 实 · 非 · 行 · 果

- **(X, X)**: (oooo, xxxx)
- **分解**: 阳 · 有 · 体 · 形 · 实 · 非 · 行 · 果
- **对偶**: `xxxxoooo` · 240
- **古文**: 类泰 (天地交) — 上乾下坤之意
- **现代汉语**: 本体类全阳, 实用类全阴。理论清明而实践全显, "天上地下"的标准对位。
- **英语**: Ontology fully yang, pragmatics fully yin — the "theory pristine, practice manifest" cleavage. 8-bit step function.
- **形式逻辑**: |y|₁ = 4 / Walsh W₃ (阶跃函数) / comp-palindrome (反序后取补 = 自身) / d(⊤⁸)=d(⊥⁸)=4 — 平衡点之一
- **Why**: 前 4 本体类轴 (阴阳·有无·体用·形声) 全阳, 后 4 实用类轴 (名实·是非·知行·因果) 全阴。这是 8-bit 阶跃函数, 也是 Walsh-Hadamard 变换中 W₃。哲学意涵: 本体不动, 实用全开 — 类似《易》泰卦 "天地交而万物通"。对偶 #240 为类否 (本体阴, 实用阳)。comp-palindrome: 配对轴 (1↔8, 2↔7, 3↔6, 4↔5) 各取相反侧。

### `oooxoooo` · 16

**Subtitle**: 1 阴侧 · 声

- **(X, X)**: (ooox, oooo)
- **分解**: 阳 · 有 · 体 · 声 · 名 · 是 · 知 · 因
- **对偶**: `xxxoxxxx` · 239
- **古文**: **声** — 《说文》"声, 音也"; 六书"形声"之"声"; 《礼记·乐记》"声音之道"
- **现代汉语**: 形声一轴入声。声出形外, 听觉从视觉脱出。
- **英语**: Single perturbation on form-sound (→ sound). Audition breaks from form — the voice arises from the silent shape.
- **形式逻辑**: F₂⁸ 单位向量 e₁₆ / |y|₁ = 1 / yin ⊂ 本体类
- **Why**: 仅 bit 4 (形声轴) 翻。在视觉化的纯形中, 第一个声音从中浮现。形声是中国文字学的根本对偶 (《说文》六书中"形声字"占多数), 此码象征"形已具而声始出"的语言起源点。X² 回声为 bit 8 (因果), palindrome 镜像为 bit 5 (名实) — 两边都未动, 这是孤立的本体扰动。

### `oooxooox` · 17  *[true X²]*

**Subtitle**: 2 阴侧 · 声 · 果

- **(X, X)**: (ooox, ooox)  ← true X² (左右半相等)
- **分解**: 阳 · 有 · 体 · 声 · 名 · 是 · 知 · 果
- **对偶**: `xxxoxxxo` · 238
- **古文**: **应** — 《广雅》"应, 当也"; 声 + 果 = 声出应果 (回响); 易经"同声相应" [X² 4↔8]
- **现代汉语**: 形声 + 因果 双阴, 高低半皆 ooox。"声出形外"与"果显因隐"在 X² 表上同步共振。
- **英语**: Form-sound and cause-effect both flip; high half = low half = ooox. The 4th X² pair self-resonates: voice-from-form and effect-from-cause echo each other.
- **形式逻辑**: |y|₁ = 2 / true X² (高低半相等) / 17 = 17 × 1 (X² 表对角元) / X² 配对中第 4 对 (bit 4 ↔ bit 8) 共振
- **Why**: 这是 16 个 true X² 对角元的第 1 个非零项。其 X² 结构意味着: bit 4 (形声) 与 bit 8 (因果) ——这对 X² 配对——同步翻至阴侧。哲学上: "声"(从形分化) 与"果"(从因分化) 是同源的"显化"行为, 此码捕捉它们的共振。其余 6 轴皆留阳, 故本体与实用各自仅这一条裂口。

### `oooxooxo` · 18

**Subtitle**: 2 阴侧 · 声 · 行

- **(X, X)**: (ooox, ooxo)
- **分解**: 阳 · 有 · 体 · 声 · 名 · 是 · 行 · 因
- **对偶**: `xxxoxxox` · 237
- **古文**: **言** — 《说文》"言, 直言曰言"; 声 + 行 = 言 (言语即行动); 论语"先行其言"
- **现代汉语**: 形声 + 知行 双阴 (声+行)。说话即行动, 言为身行的"声行" 联动。
- **英语**: Two-axis yin: sound and acting. Speech-as-action — the "vocal performance" coupling.
- **形式逻辑**: |y|₁ = 2 / e₁₈ / yin 跨本体类与实用类 (bit 4 与 bit 7)
- **Why**: 形声翻声, 知行翻行 — 言与行同步动。这是言语行为理论 (speech-act) 的最简模型: 言语本身就是行动。本体 4 轴中仅形声动, 实用 4 轴中仅知行动, 两类各派一支。

### `oooxooxx` · 19

**Subtitle**: 3 阴侧 · 声 · 行 · 果

- **(X, X)**: (ooox, ooxx)
- **分解**: 阳 · 有 · 体 · 声 · 名 · 是 · 行 · 果
- **对偶**: `xxxoxxoo` · 236
- **古文**: **教** — 《说文》"教, 上所施下所效也"; 声 + 行 + 果 = 教 (《学记》"教也者, 长善而救其失者也")
- **现代汉语**: 形声 + 知行 + 因果 三翻 (声+行+果)。言行果三联, 言→行→果完整链。
- **英语**: Three yin axes: sound, acting, effect — the full "speak → act → consequence" chain.
- **形式逻辑**: |y|₁ = 3 / e₁₉ / yin 在 bit 4,7,8
- **Why**: 形声+知行+因果 三轴同步入阴。这是"言行果"的因果链: 先有发声, 继而行动, 最终结果。是非 (bit 6) 与名实 (bit 5) 留阳 — 即语言与判断仍在生成侧, 但其外显的声—行—果链已经完整展开。

### `oooxoxoo` · 20

**Subtitle**: 2 阴侧 · 声 · 非

- **(X, X)**: (ooox, oxoo)
- **分解**: 阳 · 有 · 体 · 声 · 名 · 非 · 知 · 因
- **对偶**: `xxxoxoxx` · 235
- **古文**: **谤** — 《说文》"谤, 毁也"; 声 + 非 = 谤议 (《左传》"郑人游于乡校以论执政")
- **现代汉语**: 形声 + 是非 双阴 (声+非)。出声即异见, 言论的判断性偏离。
- **英语**: Two-axis yin: sound and wrong-judgment. Vocal dissent — speech that breaks the consensus.
- **形式逻辑**: |y|₁ = 2 / e₂₀ / yin 在 bit 4, 6
- **Why**: 形声·是非 联翻 — 声音出而即载负"非"的判断。这是"批评/异议"的最小结构: 仅当声从形脱出 (说出), 与判断从是滑向非 (反对) 同步发生。知行·因果留阳 — 言论本身就是核, 还未到行动与后果。

### `oooxoxox` · 21

**Subtitle**: 3 阴侧 · 声 · 非 · 果

- **(X, X)**: (ooox, oxox)
- **分解**: 阳 · 有 · 体 · 声 · 名 · 非 · 知 · 果
- **对偶**: `xxxoxoxo` · 234
- **古文**: **訾** — 《说文》"訾, 不思称意也"; 声 + 非 + 果 = 訾毁 (《礼记》"不訾重器")
- **现代汉语**: 形声+是非+因果 三翻 (声+非+果)。批评的言论产生了后果, 而身体未动。
- **英语**: Three yin axes: sound, wrong-judgment, effect. Critical speech bears outcome — without yet activating bodily action.
- **形式逻辑**: |y|₁ = 3 / e₂₁ / yin 在 bit 4,6,8 — 跳过 bit 5 (名实) 与 bit 7 (知行)
- **Why**: 形声·是非·因果 入阴, 名实·知行 留阳。"言不行, 而果已显" 的状态 — 一种纯舆论效应: 仅靠说出与判断, 后果已产生, 而真正的行动 (知行) 与命名 (名实) 仍未变。

### `oooxoxxo` · 22

**Subtitle**: 3 阴侧 · 声 · 非 · 行

- **(X, X)**: (ooox, oxxo)
- **分解**: 阳 · 有 · 体 · 声 · 名 · 非 · 行 · 因
- **对偶**: `xxxoxoox` · 233
- **古文**: **议** — 《说文》"议, 语也"; 声 + 非 + 行 = 议 (《左传》"乡校议政")
- **现代汉语**: 形声+是非+知行 三翻 (声+非+行)。言+判+行三联, 果未来。
- **英语**: Three yin axes: sound, wrong-judgment, acting. Speech, dissent, and action align — outcome pending.
- **形式逻辑**: |y|₁ = 3 / e₂₂ / yin 在 bit 4,6,7
- **Why**: 形声·是非·知行 三轴入阴。这是"批评性实践"的最简形: 出声→异议→行动, 三者同步, 而因果尚留因 — 后果还在酝酿。

### `oooxoxxx` · 23  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 声 · 非 · 行 · 果

- **(X, X)**: (ooox, oxxx)
- **分解**: 阳 · 有 · 体 · 声 · 名 · 非 · 行 · 果
- **对偶**: `xxxoxooo` · 232
- **古文**: **讥** — 《说文》"讥, 诽也"; 声 + 非 + 行 + 果 = 讥讽 (《论语》"君子不出位"); 类泰之偏
- **现代汉语**: 形声+是非+知行+因果 四翻。"声/非/行/果" 完整偏离链 — 类泰的形声扰动版。
- **英语**: Four yin axes: sound, wrong-judgment, acting, effect. The "vocal/critical/active/consequential" cascade — a Tai-trigram analogue tilted by form-sound flip.
- **形式逻辑**: |y|₁ = 4 / comp-palindrome (反序后取补 = 自身) / d(⊤⁸)=d(⊥⁸)=4
- **Why**: 全部 4 个实用类轴翻 (非·行·果) 加上本体类的形声 (声)。其 comp-palindrome 性质: 配对轴 (1↔8, 2↔7, 3↔6, 4↔5) 各取相反侧 — 即 (阳, 果), (有, 行), (体, 非), (声, 名), 每对一阳一阴。类泰 (#15) 在加上形声扰动后变成此码。

### `oooxxooo` · 24  *[palindrome]*

**Subtitle**: 2 阴侧 · 声 · 实

- **(X, X)**: (ooox, xooo)
- **分解**: 阳 · 有 · 体 · 声 · 实 · 是 · 知 · 因
- **对偶**: `xxxooxxx` · 231
- **古文**: **说** — 《说文》"说, 释也"; 声 + 实 = 说 (《孟子》"诗者, 不可以文害辞, 不可以辞害志") [palindrome 中轴 4↔5]
- **现代汉语**: 形声+名实 双阴 (声+实)。palindrome 第 4 配对 (中轴) 同步入阴 — 语言与现象的核心裂口。
- **English**: Form-sound and name-reality both flip — the 4th palindrome pair (the central one) self-resonates. The two "expression" axes mirror each other.
- **形式逻辑**: |y|₁ = 2 / palindrome (bit 4 ↔ bit 5 配对同侧) / 高低半在镜对意义下重合
- **Why**: palindrome 把 8 轴两两配对 (1↔8, 2↔7, 3↔6, 4↔5), 此码是第 4 对 (中心对 — 形声↔名实) 单独翻至阴侧, 其它三对都在阳侧。形声与名实, 一个是"表达侧" (字形/语音), 一个是"指涉侧" (名/物), 此码象征语言系统两端同时滑向实/声 — 表里同步松动。对偶 #231 为同对回阳。

### `oooxxoox` · 25

**Subtitle**: 3 阴侧 · 声 · 实 · 果

- **(X, X)**: (ooox, xoox)
- **分解**: 阳 · 有 · 体 · 声 · 实 · 是 · 知 · 果
- **对偶**: `xxxooxxo` · 230
- **古文**: **述** — 《论语·述而》"述而不作, 信而好古"; 声 + 实 + 果 = 述 (传述史实)
- **现代汉语**: 形声+名实+因果 三翻 (声+实+果)。语言两端 (声·实) 都松, 加后果显现。
- **英语**: Three yin axes: sound, reality, effect. Both ends of language slacken (声·实) and the outcome manifests.
- **形式逻辑**: |y|₁ = 3 / e₂₅ / yin 在 bit 4,5,8 / palindrome 中轴 (4-5) + 极外尾 (8)
- **Why**: 形声·名实 palindrome 中对+ 因果尾。语言系统全松 (声出形、实出名), 而后果已显; 是非·知行留阳。一种"事已成而判断尚未起"的语言事故场景。

### `oooxxoxo` · 26

**Subtitle**: 3 阴侧 · 声 · 实 · 行

- **(X, X)**: (ooox, xoxo)
- **分解**: 阳 · 有 · 体 · 声 · 实 · 是 · 行 · 因
- **对偶**: `xxxooxox` · 229
- **古文**: **演** — 《说文》"演, 长流也"; 声 + 实 + 行 = 演 (演说·演义; 推演)
- **现代汉语**: 形声+名实+知行 三翻 (声+实+行)。语言松动加身体行动, 果未起。
- **英语**: Three yin axes: sound, reality, acting. Linguistic openness paired with bodily action — outcome pending.
- **形式逻辑**: |y|₁ = 3 / e₂₆ / yin 在 bit 4,5,7
- **Why**: 形声·名实·知行 同步阴 — 声·实·行三轴动。是非·因果留阳: 判断仍是, 后果未现。一种"语言 + 行动"双重展开但尚未闭环的中间态。

### `oooxxoxx` · 27

**Subtitle**: 4 阴侧 · 声 · 实 · 行 · 果

- **(X, X)**: (ooox, xoxx)
- **分解**: 阳 · 有 · 体 · 声 · 实 · 是 · 行 · 果
- **对偶**: `xxxooxoo` · 228
- **古文**: **成** — 《说文》"成, 就也"; 声 + 实 + 行 + 果 = 成 (《论语》"先成而后得")
- **现代汉语**: 形声+名实+知行+因果 四翻, 唯是非留是。语言 + 行果三联, 判断仍守"是"。
- **英语**: Four yin axes: sound, reality, acting, effect. The right-wrong axis alone holds at "is" — full pragmatic display under a consistent positive judgment.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 4,5,7,8 (跳过 bit 6 = 是非)
- **Why**: 实用类除是非外全翻, 加本体的形声。"出声·实·行·果"完整链条已动, 而是非判断仍站在"是"。这象征一种自我肯定的实践全展开 — 说·做·成皆然, 唯独不自我否定。

### `oooxxxoo` · 28

**Subtitle**: 3 阴侧 · 声 · 实 · 非

- **(X, X)**: (ooox, xxoo)
- **分解**: 阳 · 有 · 体 · 声 · 实 · 非 · 知 · 因
- **对偶**: `xxxoooxx` · 227
- **古文**: **辩** — 《荀子·非相》"辩说之难"; 声 + 实 + 非 = 辩 (名家·公孙龙·墨经)
- **现代汉语**: 形声+名实+是非 三翻 (声+实+非)。语言两端松 + 判断转否, 行果未起。
- **英语**: Three yin axes: sound, reality, wrong-judgment. Language ends loosen and judgment turns negative — action and outcome held back.
- **形式逻辑**: |y|₁ = 3 / e₂₈ / yin 在 bit 4,5,6
- **Why**: 形声·名实·是非 同时入阴。表达 (声) + 指涉 (实) + 判断 (非) 三者联动, 但知行·因果留阳。这是"愤怒的批判"状态: 说出, 指出现象, 否定判断 — 但还未付诸行动, 后果亦未来。

### `oooxxxox` · 29

**Subtitle**: 4 阴侧 · 声 · 实 · 非 · 果

- **(X, X)**: (ooox, xxox)
- **分解**: 阳 · 有 · 体 · 声 · 实 · 非 · 知 · 果
- **对偶**: `xxxoooxo` · 226
- **古文**: **诘** — 《说文》"诘, 问也"; 声 + 实 + 非 + 果 = 诘 (诘问 + 否定 + 果)
- **现代汉语**: 形声+名实+是非+因果 四翻, 唯知行留知。说+实+非 + 果, 行动未起。
- **英语**: Four yin axes: sound, reality, wrong-judgment, effect. Know-act holds at "knowing" — judgment turned, outcome arrived, but body still still.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 4,5,6,8 (跳过 bit 7 = 知行)
- **Why**: 实用类除知行外全翻 + 本体形声。语言、判断、后果都已偏离至阴, 但知行仍守"知"。一种"心知腹诽而身未动"的纯精神反抗。

### `oooxxxxo` · 30

**Subtitle**: 4 阴侧 · 声 · 实 · 非 · 行

- **(X, X)**: (ooox, xxxo)
- **分解**: 阳 · 有 · 体 · 声 · 实 · 非 · 行 · 因
- **对偶**: `xxxoooox` · 225
- **古文**: **诤** — 《说文》"诤, 止也" (引申谏诤); 声 + 实 + 非 + 行 = 诤 (《孝经》"父有诤子")
- **现代汉语**: 形声+名实+是非+知行 四翻, 唯因果留因。说+实+非+行, 果尚未闭。
- **英语**: Four yin axes: sound, reality, wrong-judgment, acting. Cause-effect holds at "cause" — full deployment except the outcome has not yet returned.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 4,5,6,7 / yang 仅 bit 1,2,3,8
- **Why**: 形声·名实·是非·知行 四轴入阴, 因果留阳。即声·实·非·行 完整批评性实践链已起, 而其后果尚在因侧未现。一种 "革命方动, 果未临" 的临界状态。

### `oooxxxxx` · 31

**Subtitle**: 3 阳侧 · 阳 · 有 · 体

- **(X, X)**: (ooox, xxxx)
- **分解**: 阳 · 有 · 体 · 声 · 实 · 非 · 行 · 果
- **对偶**: `xxxooooo` · 224
- **古文**: **统** — 《说文》"统, 纪也"; 阳 + 有 + 体 三阳 = 统 (统系/根本; 《周易》"大哉乾元, 万物资始")
- **现代汉语**: 唯本体三轴 (阴阳·有无·体用) 留阳, 形声及实用四轴全阴。本体根基明而上层 5 轴皆显化。
- **英语**: Only three ontological axes (yin-yang, being-nonbeing, substance-function) hold yang; form-sound plus all four pragmatic axes are yin. Foundation pristine, upper structure fully manifest.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,2,3 / d(⊤⁸)=5, d(⊥⁸)=3
- **Why**: 形声 + 实用 4 轴 (名实·是非·知行·因果) 全部入阴, 仅本体类最深的 3 轴 (阴阳·有无·体用) 留阳。这是"根基纯净, 上层全开"的近极阴状态。哲学上接近"理事无碍"的反面: 事 (实用) 全显, 而仅最抽象的本体仍守。

### `ooxooooo` · 32

**Subtitle**: 1 阴侧 · 用

- **(X, X)**: (ooxo, oooo)
- **分解**: 阳 · 有 · 用 · 形 · 名 · 是 · 知 · 因
- **对偶**: `xxoxxxxx` · 223
- **古文**: **用** — 王弼《老子注》"以无为体, 以无为用"; 道德经"无之以为用"
- **现代汉语**: 体用一轴入用。用从体出, 功用第一次从本体中浮现。
- **英语**: Single perturbation on substance-function (→ function). Function emerges from substance — the first crack of utility from essence.
- **形式逻辑**: F₂⁸ 单位向量 e₃₂ / |y|₁ = 1 / yin ⊂ 本体类
- **Why**: 仅 bit 3 (体用轴) 翻。中国哲学的 "体用" 范畴 (王弼: "本体为体, 妙用为用") 在此被推动: 体一直在生成侧, 而用第一次显化。X² 回声: bit 3 ↔ bit 7 (知行) — 知行留阳, 故"体起用而知不行"。

### `ooxoooox` · 33

**Subtitle**: 2 阴侧 · 用 · 果

- **(X, X)**: (ooxo, ooox)
- **分解**: 阳 · 有 · 用 · 形 · 名 · 是 · 知 · 果
- **对偶**: `xxoxxxxo` · 222
- **古文**: **功** — 《说文》"功, 以劳定国也"; 用 + 果 = 功 (儒家"建功立业"); 法家"按功而赏"
- **现代汉语**: 体用+因果 双阴 (用+果)。用→果 联动, 本体派生功用, 功用结出后果。
- **英语**: Two-axis yin: function and effect. Substance gives function, function bears effect — the "essence-instantiated outcome" couplet.
- **形式逻辑**: |y|₁ = 2 / e₃₃ / yin 在 bit 3, 8 (本体核心 + 实用尾)
- **Why**: 体用翻用, 因果翻果。这是"本体 → 现象"的最简形式: 体一动而用即现, 因起处即有果显。其余 6 轴留阳 — 即名实判断仍清, 行动未起 — 故是一种纯"形上派生"的轨迹。

### `ooxoooxo` · 34  *[true X²]*

**Subtitle**: 2 阴侧 · 用 · 行

- **(X, X)**: (ooxo, ooxo)  ← true X² (左右半相等)
- **分解**: 阳 · 有 · 用 · 形 · 名 · 是 · 行 · 因
- **对偶**: `xxoxxxox` · 221
- **古文**: **施** — 《说文》"施, 旗旖施也"; 用 + 行 = 施 (论语"施于有政"; 大学"修身齐家治国"之"施") [X² 3↔7]
- **现代汉语**: 体用 + 知行 双阴, 高低半皆 ooxo。"用从体出"与"行从知出"在 X² 表上同步共振。
- **英语**: Substance-function and know-act both flip — the 3rd X² pair self-resonates. Function from substance mirrors action from knowing.
- **形式逻辑**: |y|₁ = 2 / true X² (高低半相等 = ooxo) / 34 = 17 × 2 (X² 对角元第 2 个)
- **Why**: bit 3 (体用) 与 bit 7 (知行) 同步入阴 — 这是 X² 配对 (1↔5, 2↔6, **3↔7**, 4↔8) 的第 3 对单独共振。哲学意涵: 体用的关系结构与知行的关系结构是同源的"派生" — 都是从本源 (体/知) 流向应用 (用/行)。此码捕捉这两个派生的同步发生。

### `ooxoooxx` · 35

**Subtitle**: 3 阴侧 · 用 · 行 · 果

- **(X, X)**: (ooxo, ooxx)
- **分解**: 阳 · 有 · 用 · 形 · 名 · 是 · 行 · 果
- **对偶**: `xxoxxxoo` · 220
- **古文**: **役** — 《说文》"役, 戍边也"; 用 + 行 + 果 = 役 (劳役; 法家"务力役")
- **现代汉语**: 体用+知行+因果 三翻 (用+行+果)。本体派生 + 行动派生 + 后果, 三联实用化。
- **英语**: Three yin axes: function, acting, effect. Substance-function, know-act, cause-effect — three derivative axes synchronize toward yin.
- **形式逻辑**: |y|₁ = 3 / e₃₅ / yin 在 bit 3,7,8 / 三轴在本体-实用的派生侧
- **Why**: 体用 (本体侧) + 知行·因果 (实用尾) — 三轴皆从源向流派生。即"体出用, 知出行, 因出果"三派生同步发生。形声·名实·是非 留阳, 故象征仅"派生维"运转而表达·语义·判断维都未动的纯运行态。

### `ooxooxoo` · 36  *[palindrome]*

**Subtitle**: 2 阴侧 · 用 · 非

- **(X, X)**: (ooxo, oxoo)
- **分解**: 阳 · 有 · 用 · 形 · 名 · 非 · 知 · 因
- **对偶**: `xxoxxoxx` · 219
- **古文**: **误** — 《说文》"误, 谬也"; 用 + 非 = 误用; 韩非"误国"; 体之用错位为非 [palindrome 3↔6]
- **现代汉语**: 体用 + 是非 双阴 (用+非)。palindrome 第 3 配对 (内层) 同侧入阴 — 本体派生与判断派生联动。
- **英语**: Substance-function and right-wrong both flip — the 3rd palindrome pair (inner) self-resonates. Function and dissent rise together.
- **形式逻辑**: |y|₁ = 2 / palindrome (bit 3 ↔ bit 6 同侧入阴) / yin ⊂ {bit 3, 6}
- **Why**: palindrome 第 3 配对 (体用 ↔ 是非) 单独翻。这两轴都关乎"派生与否定" — 体用是本体的功能性派生, 是非是肯定的否定性派生。两者同步入阴: 用与非 同现。"功用初起即载否定"。对偶 #219 为同对回阳。

### `ooxooxox` · 37

**Subtitle**: 3 阴侧 · 用 · 非 · 果

- **(X, X)**: (ooxo, oxox)
- **分解**: 阳 · 有 · 用 · 形 · 名 · 非 · 知 · 果
- **对偶**: `xxoxxoxo` · 218
- **古文**: **损** — 易经"损"卦; 用 + 非 + 果 = 损 (《道德经》"为道日损")
- **现代汉语**: 体用+是非+因果 三翻 (用+非+果)。本体派生功用,功用载否定, 否定得后果。
- **英语**: Three yin axes: function, wrong-judgment, effect. Function-laden-with-negation produces consequence.
- **形式逻辑**: |y|₁ = 3 / e₃₇ / yin 在 bit 3,6,8
- **Why**: 体用·是非·因果 三轴入阴。形声·名实·知行 留阳 — 即语言层稳, 行动未起, 而本体功用 + 判断否定 + 后果 三者已链。一种"未发声却已成事"的暗中变化。

### `ooxooxxo` · 38

**Subtitle**: 3 阴侧 · 用 · 非 · 行

- **(X, X)**: (ooxo, oxxo)
- **分解**: 阳 · 有 · 用 · 形 · 名 · 非 · 行 · 因
- **对偶**: `xxoxxoox` · 217
- **古文**: **暴** — 《说文》"暴, 晞也" (引申猛烈); 用 + 非 + 行 = 暴 (孟子"以暴易暴")
- **现代汉语**: 体用+是非+知行 三翻 (用+非+行)。本体派生 + 否定判断 + 行动, 果未至。
- **英语**: Three yin axes: function, wrong-judgment, acting. Function-load + negative judgment + action — outcome pending.
- **形式逻辑**: |y|₁ = 3 / e₃₈ / yin 在 bit 3,6,7
- **Why**: 体用·是非·知行 三轴入阴, 因果留因。"用·非·行"链已起, 但还未结果。这是负向行动的最初执行: 功用已现、判断为非、动作已出, 仅果未来。

### `ooxooxxx` · 39

**Subtitle**: 4 阴侧 · 用 · 非 · 行 · 果

- **(X, X)**: (ooxo, oxxx)
- **分解**: 阳 · 有 · 用 · 形 · 名 · 非 · 行 · 果
- **对偶**: `xxoxxooo` · 216
- **古文**: **刑** — 法家根本; 用 + 非 + 行 + 果 = 刑 (《韩非子》"明赏罚之刑"; 罚之施)
- **现代汉语**: 体用+是非+知行+因果 四翻, 唯名实留名。本体 1 轴 + 实用 3 轴, 名义尚清。
- **英语**: Four yin axes: function, wrong-judgment, acting, effect. Only name-reality stays at "name" — the words are still pure, everything else has tilted.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 3,6,7,8 / d(⊤⁸)=d(⊥⁸)=4
- **Why**: 本体类的体用 + 实用类的"非·行·果"三尾全翻, 仅名实保住名侧。即"知非而行非而果非"已展开, 但语言概念层未变 — 一种 "实践全反转, 语言尚守" 的格局。是非翻而名不翻的张力: 判断已变但措辞未改。

### `ooxoxooo` · 40

**Subtitle**: 2 阴侧 · 用 · 实

- **(X, X)**: (ooxo, xooo)
- **分解**: 阳 · 有 · 用 · 形 · 实 · 是 · 知 · 因
- **对偶**: `xxoxoxxx` · 215
- **古文**: **利** — 《说文》"利, 銛也"; 用 + 实 = 利 (《周易》"利者义之和"; 法家"务力"; 墨家"兼相爱, 交相利")
- **现代汉语**: 体用 + 名实 双阴 (用+实)。本体功用现, 现象超出名 — 体出用与实出名同步。
- **英语**: Two-axis yin: function and reality. Substance gives function, name gives way to reality — two parallel emanations.
- **形式逻辑**: |y|₁ = 2 / e₄₀ / yin 在 bit 3, 5 (本体派生 + 实用首)
- **Why**: 体用·名实 同步翻。两者都是"从源向显"的派生: 体→用是本体侧, 名→实是语义侧。两者同步入阴, 这是哲学上"本体派生 与 语义派生"的并行触发。

### `ooxoxoox` · 41

**Subtitle**: 3 阴侧 · 用 · 实 · 果

- **(X, X)**: (ooxo, xoox)
- **分解**: 阳 · 有 · 用 · 形 · 实 · 是 · 知 · 果
- **对偶**: `xxoxoxxo` · 214
- **古文**: **效** — 《说文》"效, 象也"; 用 + 实 + 果 = 效 (法家"按效赏罚")
- **现代汉语**: 体用+名实+因果 三翻 (用+实+果)。本体派生 + 现实显化 + 后果, 行未起判未变。
- **英语**: Three yin axes: function, reality, effect. Substance-derived function, language-overflown reality, manifest outcome — all without bodily action or judgment shift.
- **形式逻辑**: |y|₁ = 3 / e₄₁ / yin 在 bit 3,5,8
- **Why**: 体用·名实·因果 三轴入阴。"用·实·果" 三联展开, 而是非·知行·形声 留阳。一种"暗中发生且产生后果"的纯派生事件。

### `ooxoxoxo` · 42

**Subtitle**: 3 阴侧 · 用 · 实 · 行

- **(X, X)**: (ooxo, xoxo)
- **分解**: 阳 · 有 · 用 · 形 · 实 · 是 · 行 · 因
- **对偶**: `xxoxoxox` · 213
- **古文**: **事** — 《说文》"事, 职也"; 用 + 实 + 行 = 事 (孟子"事亲为大"; 朱熹"格物穷理"之"物事")
- **现代汉语**: 体用+名实+知行 三翻 (用+实+行)。本体出用, 名让位实, 行动起 — 而判断与因果未动。
- **英语**: Three yin axes: function, reality, acting. Substance-function, name-reality, know-act — three derivative pairs synchronize; judgment and cause-effect untouched.
- **形式逻辑**: |y|₁ = 3 / e₄₂ / yin 在 bit 3,5,7 / 全部为奇位 bit (中间偶数)
- **Why**: 体用 (3) · 名实 (5) · 知行 (7) — 三个奇数 bit 轴入阴, 即"派生轴族"全启动。这三轴形式上都是"派生关系" (体→用, 名→实, 知→行), 它们一起翻意味着系统的派生维全部启动, 而判断与因果维仍守源侧。

### `ooxoxoxx` · 43  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 用 · 实 · 行 · 果

- **(X, X)**: (ooxo, xoxx)
- **分解**: 阳 · 有 · 用 · 形 · 实 · 是 · 行 · 果
- **对偶**: `xxoxoxoo` · 212
- **古文**: **政** — 《论语·为政》"为政以德"; 用 + 实 + 行 + 果 = 政 (法家"务实之政"); comp-palindrome
- **现代汉语**: 体用+名实+知行+因果 四翻, 唯是非留是。"用·实·行·果"四联, 判断仍肯定。
- **英语**: Four yin axes: function, reality, acting, effect. The right-wrong axis alone holds — full positive practical engagement.
- **形式逻辑**: |y|₁ = 4 / comp-palindrome / yin 在 bit 3,5,7,8
- **Why**: 4 个派生轴 (用·实·行·果) 同步入阴 + 是非留是。这是"积极实践模式" — 本体派出功用, 名让位于实, 知化为行, 因结出果, 而判断始终肯定。comp-palindrome 结构: 配对轴 (1↔8, 2↔7, 3↔6, 4↔5) 各取相反侧, 故每对都"半阴半阳"。

### `ooxoxxoo` · 44

**Subtitle**: 3 阴侧 · 用 · 实 · 非

- **(X, X)**: (ooxo, xxoo)
- **分解**: 阳 · 有 · 用 · 形 · 实 · 非 · 知 · 因
- **对偶**: `xxoxooxx` · 211
- **古文**: **弊** — 《说文》"弊, 顿仆也" (引申败坏); 用 + 实 + 非 = 弊 (法家"弊政"; 韩非"国之大弊")
- **现代汉语**: 体用+名实+是非 三翻 (用+实+非)。本体派生 + 语义现实 + 否定判断, 三联意识动。
- **英语**: Three yin axes: function, reality, wrong-judgment. Derivation, reality-overflow, and negation align — purely conscious.
- **形式逻辑**: |y|₁ = 3 / e₄₄ / yin 在 bit 3,5,6
- **Why**: 体用·名实·是非 三轴入阴, 知行·因果留阳。"用·实·非" 三联 — 派生 + 实出 + 否定, 一种意识层的批判, 但身未动果未现。

### `ooxoxxox` · 45

**Subtitle**: 4 阴侧 · 用 · 实 · 非 · 果

- **(X, X)**: (ooxo, xxox)
- **分解**: 阳 · 有 · 用 · 形 · 实 · 非 · 知 · 果
- **对偶**: `xxoxooxo` · 210
- **古文**: **败** — 《说文》"败, 毁也"; 用 + 实 + 非 + 果 = 败 (《左传》"师败绩"; 法家"败之实")
- **现代汉语**: 体用+名实+是非+因果 四翻, 唯知行留知。"用+实+非+果", 行未起。
- **英语**: Four yin axes: function, reality, wrong-judgment, effect. Know-act stays at "knowing" — mental cascade fully run, body unmoved.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 3,5,6,8 (跳过 7)
- **Why**: 实用类除知行外全翻 + 本体体用。即"用·实·非·果"四联展开, 而身仍未动 — 纯精神层的批判性结果。心知一切已变, 而身体未介入。

### `ooxoxxxo` · 46

**Subtitle**: 4 阴侧 · 用 · 实 · 非 · 行

- **(X, X)**: (ooxo, xxxo)
- **分解**: 阳 · 有 · 用 · 形 · 实 · 非 · 行 · 因
- **对偶**: `xxoxooox` · 209
- **古文**: **乱** — 《说文》"乱, 治也" (反训); 用 + 实 + 非 + 行 = 乱 (《尚书》"治乱兴亡")
- **现代汉语**: 体用+名实+是非+知行 四翻, 唯因果留因。"用·实·非·行" 四联, 果未临。
- **英语**: Four yin axes: function, reality, wrong-judgment, acting. Cause-effect stays at "cause" — full critical action launched, outcome pending.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 3,5,6,7 (跳过 8)
- **Why**: 实用类除因果外全翻 + 本体体用。这是"完整的批判性实践" 已经发动而结果未到 — 一种革命前夜的张力态。

### `ooxoxxxx` · 47

**Subtitle**: 3 阳侧 · 阳 · 有 · 形

- **(X, X)**: (ooxo, xxxx)
- **分解**: 阳 · 有 · 用 · 形 · 实 · 非 · 行 · 果
- **对偶**: `xxoxoooo` · 208
- **古文**: **昭** — 《诗·大雅》"昭哉嗣服"; 阳 + 有 + 形 三阳 = 昭 (昭明)
- **现代汉语**: 唯阴阳·有无·形声 三轴留阳, 体用及实用四轴全阴。形上轴中"体用"反转, 余皆守。
- **英语**: Three axes hold yang: yin-yang, being-nonbeing, form-sound; substance-function plus all four pragmatic axes are yin.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,2,4 (跳过 bit 3) / d(⊤⁸)=5, d(⊥⁸)=3
- **Why**: 仅本体最外的 3 轴 (阴阳·有无·形声) 留阳, 而本体核心的体用 + 实用 4 轴全翻。即"形象层与最深极性都还在生成侧, 但体用派生 + 整个实用层已沉到现象"。一种"形未变而事尽变"的近极阴。

### `ooxxoooo` · 48

**Subtitle**: 2 阴侧 · 用 · 声

- **(X, X)**: (ooxx, oooo)
- **分解**: 阳 · 有 · 用 · 声 · 名 · 是 · 知 · 因
- **对偶**: `xxooxxxx` · 207
- **古文**: **唱** — 《说文》"唱, 导也"; 用 + 声 = 唱 (《礼记·乐记》"一倡而三叹")
- **现代汉语**: 体用 + 形声 双阴 (用+声)。本体后两轴皆翻 — 功用现而声音出。
- **英语**: Two-axis yin: function and sound. The two latter ontological axes flip — function emerges and voice arises.
- **形式逻辑**: |y|₁ = 2 / e₄₈ / yin ⊂ 本体类后两位 (bit 3, 4)
- **Why**: 体用·形声 同时翻 — 本体的"派生维" (体→用) 与"表达维" (形→声) 联动。阴阳·有无 仍留, 实用 4 轴尽阳。即"本体上层两轴动而下层根基纯, 实用尚未启动" — 一种近源的本体震荡。

### `ooxxooox` · 49

**Subtitle**: 3 阴侧 · 用 · 声 · 果

- **(X, X)**: (ooxx, ooox)
- **分解**: 阳 · 有 · 用 · 声 · 名 · 是 · 知 · 果
- **对偶**: `xxooxxxo` · 206
- **古文**: **召** — 《说文》"召, 评也"; 用 + 声 + 果 = 召 (《孟子》"祸福无门, 唯人自召")
- **现代汉语**: 体用+形声+因果 三翻 (用+声+果)。本体后两轴 + 实用末轴, "用·声·果"三联。
- **英语**: Three yin axes: function, sound, effect. Latter ontology shifts and the outcome materializes — speech/function lead to result.
- **形式逻辑**: |y|₁ = 3 / e₄₉ / yin 在 bit 3,4,8
- **Why**: 体用·形声·因果 三轴入阴, 名实·是非·知行 留阳。"用-声-果" — 这是 X² 配对中 bit 3↔7 (没动) 与 bit 4↔8 (动) 的不对称启动 + 体用单振。语言判断仍清, 仅本体上层 + 因果末端动。

### `ooxxooxo` · 50

**Subtitle**: 3 阴侧 · 用 · 声 · 行

- **(X, X)**: (ooxx, ooxo)
- **分解**: 阳 · 有 · 用 · 声 · 名 · 是 · 行 · 因
- **对偶**: `xxooxxox` · 205
- **古文**: **表** — 《说文》"表, 上衣也" (引申显露); 用 + 声 + 行 = 表 (表态·表达; 《礼记》"作表敦俗")
- **现代汉语**: 体用+形声+知行 三翻 (用+声+行)。本体两轴 + 实用一轴, 表达加行动。
- **英语**: Three yin axes: function, sound, acting. Ontology's pair (function + voice) couples with bodily action.
- **形式逻辑**: |y|₁ = 3 / e₅₀ / yin 在 bit 3,4,7
- **Why**: 体用·形声·知行 入阴 — 本体的"派生 + 表达"两轴加实用的"行动"轴。是非·因果·名实 留阳: 即"出声·施用·行动"已现, 但判断、后果、命名都未动。一种"言行结合"前夕。

### `ooxxooxx` · 51  *[true X² · comp-palindrome]*

**Subtitle**: 4 阴侧 · 用 · 声 · 行 · 果

- **(X, X)**: (ooxx, ooxx)  ← true X² (左右半相等)
- **分解**: 阳 · 有 · 用 · 声 · 名 · 是 · 行 · 果
- **对偶**: `xxooxxoo` · 204
- **古文**: **节** — 《周易》节卦"节亨"; 周期 Walsh W₂ 算子; 《尚书》"协时月正日, 同律度量衡"; 2-bit 周期 4 节奏 [K.4 双重身份]
- **现代汉语**: **节** — Walsh W₂ 周期算子。本体后两轴 (体用·形声) + 实用后两轴 (知行·因果) 同步入阴; "用·声·行·果" 高低半 ooxx 周期 4 重复 — 节奏 / 律拍。
- **英语**: Period-4 self-square. Both halves equal (ooxx); the back-half doublet "function/sound" mirrors back-half doublet "acting/effect". Walsh W₂ basis.
- **形式逻辑**: |y|₁ = 4 / true X² (high = low = ooxx) / comp-palindrome / Walsh W₂ (二阶频率)
- **Why**: 2-bit 周期模式 (00,11) 重复 4 次。它是 true X² ∩ comp-palindrome 4 元组 {51, 85, 170, 204} 之一, 这 4 个码恰好对应 F₂⁸ 上 4 个 Walsh-Hadamard 基函数 W₂ 模式。哲学意涵: 本体的"派生+表达"两轴 (3,4) 与实用的"行动+后果"两轴 (7,8) 同步阴 — X² 第 3 与第 4 配对联振。

### `ooxxoxoo` · 52

**Subtitle**: 3 阴侧 · 用 · 声 · 非

- **(X, X)**: (ooxx, oxoo)
- **分解**: 阳 · 有 · 用 · 声 · 名 · 非 · 知 · 因
- **对偶**: `xxooxoxx` · 203
- **古文**: **讽** — 《说文》"讽, 诵也" (引申劝谏); 用 + 声 + 非 = 讽 (《毛诗序》"主文而谲谏")
- **现代汉语**: 体用+形声+是非 三翻 (用+声+非)。本体后两轴 + 实用否定判断。
- **英语**: Three yin axes: function, sound, wrong-judgment. Latter ontology speaks dissent.
- **形式逻辑**: |y|₁ = 3 / e₅₂ / yin 在 bit 3,4,6
- **Why**: 体用·形声·是非 三轴入阴, 余 5 轴留阳。即"功用+发声+否定" 三联, 而其它都未动 — 一种"用声否决"的近源批评态。

### `ooxxoxox` · 53

**Subtitle**: 4 阴侧 · 用 · 声 · 非 · 果

- **(X, X)**: (ooxx, oxox)
- **分解**: 阳 · 有 · 用 · 声 · 名 · 非 · 知 · 果
- **对偶**: `xxooxoxo` · 202
- **古文**: **诉** — 《说文》"诉, 告也"; 用 + 声 + 非 + 果 = 诉 (诉讼之诉)
- **现代汉语**: 体用+形声+是非+因果 四翻, 唯名实·知行 留阳。"用·声·非·果", 行止于知名仍清。
- **英语**: Four yin axes: function, sound, wrong-judgment, effect. Name-reality and know-act remain yang — speech/negation produces result without acting.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 3,4,6,8 / 跳过 bit 5,7
- **Why**: 本体后两轴 + 实用奇偶交替 (bit 6, 8 跳过 bit 5, 7) 入阴。一种 "言判生果而身名守源" 的非对称态。

### `ooxxoxxo` · 54

**Subtitle**: 4 阴侧 · 用 · 声 · 非 · 行

- **(X, X)**: (ooxx, oxxo)
- **分解**: 阳 · 有 · 用 · 声 · 名 · 非 · 行 · 因
- **对偶**: `xxooxoox` · 201
- **古文**: **斥** — 《说文》"斥, 却屋也" (引申摒退); 用 + 声 + 非 + 行 = 斥 (斥责)
- **现代汉语**: 体用+形声+是非+知行 四翻, 唯名实·因果 留阳。"用·声·非·行" 不到果。
- **英语**: Four yin axes: function, sound, wrong-judgment, acting. Name-reality and cause-effect hold — full negative speech-act, outcome pending.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 3,4,6,7
- **Why**: 本体后两轴 + 实用中两轴 (跳过名实与因果)。"用+声+非+行" 完整批评行为已起, 而语义层与后果层都未变。

### `ooxxoxxx` · 55

**Subtitle**: 3 阳侧 · 阳 · 有 · 名

- **(X, X)**: (ooxx, oxxx)
- **分解**: 阳 · 有 · 用 · 声 · 名 · 非 · 行 · 果
- **对偶**: `xxooxooo` · 200
- **古文**: **誉** — 《说文》"誉, 称也"; 阳 + 有 + 名 三阳 = 誉 (名誉; 论语"无求生以害仁")
- **现代汉语**: 唯阴阳·有无·名实 三轴留阳, 体用形声及是非知行因果全阴。
- **英语**: Three yang axes: yin-yang, being-nonbeing, name-reality. The remaining five axes are yin.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,2,5 / d(⊤⁸)=5
- **Why**: 仅最基础的两轴 (阴阳·有无) 加名实 3 轴留阳, 其余 5 轴皆翻。即"根本极性 + 语义命名"守源, 而本体上层 + 实用三末轴全沉。命名仍清明, 但其它一切已经显化。

### `ooxxxooo` · 56

**Subtitle**: 3 阴侧 · 用 · 声 · 实

- **(X, X)**: (ooxx, xooo)
- **分解**: 阳 · 有 · 用 · 声 · 实 · 是 · 知 · 因
- **对偶**: `xxoooxxx` · 199
- **古文**: **制** — 《说文》"制, 裁也"; 用 + 声 + 实 = 制 (荀子"制礼义"; 法家"立制"; 《大学》"絜矩之道")
- **现代汉语**: 体用+形声+名实 三翻 (用+声+实)。本体后两轴 + 实用首轴, "派生 + 表达 + 现实"三联。
- **英语**: Three yin axes: function, sound, reality. Latter ontology plus first pragmatic — the "function-voice-thing" triad.
- **形式逻辑**: |y|₁ = 3 / e₅₆ / yin 在 bit 3,4,5
- **Why**: bit 3,4,5 — 连续三轴入阴, 跨越本体-实用界。即"用·声·实"三连, 这三轴形式上"派生 → 表达 → 实出", 是从体到事的一条连续流。

### `ooxxxoox` · 57

**Subtitle**: 4 阴侧 · 用 · 声 · 实 · 果

- **(X, X)**: (ooxx, xoox)
- **分解**: 阳 · 有 · 用 · 声 · 实 · 是 · 知 · 果
- **对偶**: `xxoooxxo` · 198
- **古文**: **建** — 《说文》"建, 立朝律也"; 用 + 声 + 实 + 果 = 建 (建立; 法家"立制")
- **现代汉语**: 体用+形声+名实+因果 四翻, 唯是非·知行 留阳。"用·声·实·果", 心仍守是与知。
- **英语**: Four yin axes: function, sound, reality, effect. Right-wrong and know-act stay yang — judgment is and knowing holds.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 3,4,5,8
- **Why**: 本体后两轴 + 实用首尾 (名实+因果)。"用·声·实·果" 派生-表达-语义-后果四联, 而中间的判断与知行未动 — 一种"事到果而心未变"的状况。

### `ooxxxoxo` · 58

**Subtitle**: 4 阴侧 · 用 · 声 · 实 · 行

- **(X, X)**: (ooxx, xoxo)
- **分解**: 阳 · 有 · 用 · 声 · 实 · 是 · 行 · 因
- **对偶**: `xxoooxox` · 197
- **古文**: **作** — 《周易》"作易者其有忧患乎"; 用 + 声 + 实 + 行 = 作 (作为; 论语"述而不作")
- **现代汉语**: 体用+形声+名实+知行 四翻, 唯是非·因果 留阳。"用·声·实·行", 不到判断与后果。
- **英语**: Four yin axes: function, sound, reality, acting. Judgment and outcome held — full practical engagement without resolution.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 3,4,5,7
- **Why**: 本体后两轴 + 实用奇位 (5,7)。"用·声·实·行" 四联 — 派生·表达·现实·行动俱起, 而是非判断与因果闭合都留源。一种 "事在做, 心未表态" 的执行态。

### `ooxxxoxx` · 59

**Subtitle**: 3 阳侧 · 阳 · 有 · 是

- **(X, X)**: (ooxx, xoxx)
- **分解**: 阳 · 有 · 用 · 声 · 实 · 是 · 行 · 果
- **对偶**: `xxoooxoo` · 196
- **古文**: **承** — 《说文》"承, 奉也"; 阳 + 有 + 是 三阳 = 承 (承认·承顺; 《尚书》"承天景命")
- **现代汉语**: 唯阴阳·有无·是非 三轴留阳, 余 5 轴皆阴。
- **英语**: Three yang axes: yin-yang, being-nonbeing, right-wrong. The remaining five are yin.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,2,6
- **Why**: 基础极性 + 肯定判断 守源, 其余皆已显化。"心是, 而事尽显"。

### `ooxxxxoo` · 60  *[palindrome]*

**Subtitle**: 4 阴侧 · 用 · 声 · 实 · 非

- **(X, X)**: (ooxx, xxoo)
- **分解**: 阳 · 有 · 用 · 声 · 实 · 非 · 知 · 因
- **对偶**: `xxooooxx` · 195
- **古文**: **央** — 《诗·小雅》"夜如何其? 夜未央"; palindrome 内核 4 阴外缘 4 阳; 庄子"枢始得其环中"; 与 #195 边 内/外极对
- **现代汉语**: **央** — 内核 4 阴 (用·声·实·非) + 外缘 4 阳 (阴阳·有无·知行·因果)。被四阳包裹的中心 (palindrome 镜对内核); 与 #195 边 形成 中/外 二元。
- **英语**: Yin-core, yang-shell. The middle four axes flip; the outer two pairs hold. Palindromic symmetry.
- **形式逻辑**: |y|₁ = 4 / palindrome (8 位反序 = 自身) / 高低半 = (ooxx, xxoo) = 互补 / yin 在 bit 3,4,5,6
- **Why**: palindrome 的"内对外"对称版 — 内核 4 轴 (体用·形声·名实·是非) 全阴, 外壳 4 轴 (阴阳·有无·知行·因果) 全阳。即"派生-表达-语义-判断" 四个 中层 轴全部翻, 而最根本与最末梢的两端守源。哲学上, 这是一种"中层全变, 边缘未动"的格局。对偶 #195 反之 (中阳边阴)。

### `ooxxxxox` · 61

**Subtitle**: 3 阳侧 · 阳 · 有 · 知

- **(X, X)**: (ooxx, xxox)
- **分解**: 阳 · 有 · 用 · 声 · 实 · 非 · 知 · 果
- **对偶**: `xxooooxo` · 194
- **古文**: **彻** — 《说文》"彻, 通也"; 阳 + 有 + 知 三阳 = 彻 (通彻; 《孟子》"反身而诚")
- **现代汉语**: 唯阴阳·有无·知行 三轴留阳。
- **英语**: Three yang axes: yin-yang, being-nonbeing, know-act. The rest yin.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,2,7
- **Why**: 基础极性 + 知守源, 其余皆已显化为 用·声·实·非·果。心知, 而身/言/事尽变。

### `ooxxxxxo` · 62

**Subtitle**: 3 阳侧 · 阳 · 有 · 因

- **(X, X)**: (ooxx, xxxo)
- **分解**: 阳 · 有 · 用 · 声 · 实 · 非 · 行 · 因
- **对偶**: `xxooooox` · 193
- **古文**: **起** — 《说文》"起, 能立也"; 阳 + 有 + 因 三阳 = 起 (起源·兴起)
- **现代汉语**: 唯阴阳·有无·因果 三轴留阳。
- **英语**: Three yang axes: yin-yang, being-nonbeing, cause-effect. The rest yin.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,2,8
- **Why**: 基础极性 + 因 守源, 其余 5 轴已沉。即"因 未现 (即未到果), 余皆已显" — 一种"事在动而果未临"的近极阴态, 同时根极性仍守。

### `ooxxxxxx` · 63

**Subtitle**: 2 阳侧 · 阳 · 有

- **(X, X)**: (ooxx, xxxx)
- **分解**: 阳 · 有 · 用 · 声 · 实 · 非 · 行 · 果
- **对偶**: `xxoooooo` · 192
- **古文**: **生** — 《周易·系辞》"生生之谓易"; 阳 + 有 双阳 (近极阳余 6 阴) = 生 (《孟子》"人之所以异于禽兽者几希")
- **现代汉语**: 唯阴阳·有无 两轴留阳, 其余 6 轴皆阴。极阴附近, 仅最根的两轴守住。
- **英语**: Only yin-yang and being-nonbeing hold yang; six axes yin. Near maximum yin — only the two deepest polarities resist.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 1,2 / d(⊤⁸)=6, d(⊥⁸)=2
- **Why**: 两轴 (阴阳·有无) 这是 8 轴中最形上的两轴 — "存在论" 维 (阳/有 = 生成的两层) 守住, 其余 6 轴皆沉到阴。哲学上, 这是"道之大者犹存, 万象皆显" 的近极阴。对偶 #192 是 (xxoooooo): 仅阴/无两轴翻, 即近极阳。

### `oxoooooo` · 64

**Subtitle**: 1 阴侧 · 无

- **(X, X)**: (oxoo, oooo)
- **分解**: 阳 · 无 · 体 · 形 · 名 · 是 · 知 · 因
- **对偶**: `xoxxxxxx` · 191
- **古文**: **无** — 《道德经》"无名天地之始" / "天下万物生于有, 有生于无"; 道家本体
- **现代汉语**: 有无一轴入无。无从有中浮现, 道家"无生于有"的第一次显化。
- **英语**: Single perturbation on being-nonbeing (→ non-being). Absence emerges within presence — the first ontological withdrawal.
- **形式逻辑**: F₂⁸ 单位向量 e₆₄ / |y|₁ = 1 / yin ⊂ 本体类
- **Why**: 仅 bit 2 (有无轴) 翻。这是道家根本范畴的第一次启动: 有依旧, 而无开始浮现。《道德经》"有无相生", 此码捕捉"无"刚从"有"中分化的瞬间。X² 回声 (bit 6 = 是非) 与 palindrome 镜像 (bit 7 = 知行) 都留阳, 这一扰动孤立。对偶 #191 仅有 留阳。

### `oxooooox` · 65

**Subtitle**: 2 阴侧 · 无 · 果

- **(X, X)**: (oxoo, ooox)
- **分解**: 阳 · 无 · 体 · 形 · 名 · 是 · 知 · 果
- **对偶**: `xoxxxxxo` · 190
- **古文**: **空** — 佛家"五蕴皆空"; 无 + 果 = 空 (无所有之果, 即空); 般若学根本
- **现代汉语**: 有无+因果 双翻 (无+果)。"无"显化, 同时果显 — 缺席本身有后果。
- **英语**: Two-axis yin: non-being and effect. Absence has its consequence — non-presence registers an outcome.
- **形式逻辑**: |y|₁ = 2 / e₆₅ / yin 在 bit 2, 8 (本体次轴 + 实用末尾)
- **Why**: 有无翻无, 因果翻果 — 中间 5 轴留阳。即"无的出现"与"果的显现"耦合: 不在场也是一种结果。这与"无之以为用"的辩证有共鸣。

### `oxooooxo` · 66  *[palindrome]*

**Subtitle**: 2 阴侧 · 无 · 行

- **(X, X)**: (oxoo, ooxo)
- **分解**: 阳 · 无 · 体 · 形 · 名 · 是 · 行 · 因
- **对偶**: `xoxxxxox` · 189
- **古文**: **静** — 《道德经》"致虚极, 守静笃; 万物并作, 吾以观复"; 无 + 行 = 静 [palindrome 2↔7]
- **现代汉语**: 有无+知行 双阴 (无+行)。palindrome 第 2 配对同侧入阴 — 无之行, 缺席的实践。
- **英语**: Being-nonbeing and know-act both flip — the 2nd palindrome pair self-resonates. "Acting absence" — practice without presence.
- **形式逻辑**: |y|₁ = 2 / palindrome (bit 2 ↔ bit 7 同侧入阴) / yin ⊂ {bit 2, 7}
- **Why**: palindrome 第 2 配对 (有无 ↔ 知行) 单独翻 — 有 与 知 两个"安顿轴"同时退场, 显化为 无 与 行。即"在没有具体存在感支撑下的实践" — 庄子《养生主》"为善无近名"的味道。配对的另两组 (1↔8, 3↔6, 4↔5) 都留阳。

### `oxooooxx` · 67

**Subtitle**: 3 阴侧 · 无 · 行 · 果

- **(X, X)**: (oxoo, ooxx)
- **分解**: 阳 · 无 · 体 · 形 · 名 · 是 · 行 · 果
- **对偶**: `xoxxxxoo` · 188
- **古文**: **灭** — 《说文》"灭, 尽也"; 无 + 行 + 果 = 灭 (佛家"寂灭"; 庄子"灭迹") 
- **现代汉语**: 有无+知行+因果 三翻 (无+行+果)。无之行得无之果, 缺席的实践链。
- **英语**: Three yin axes: non-being, acting, effect. Absent-grounded action yields absent-grounded result.
- **形式逻辑**: |y|₁ = 3 / e₆₇ / yin 在 bit 2,7,8
- **Why**: 有无·知行·因果 三轴入阴 — 本体的"无"与实用末两轴的"行·果"同步显化。形声·体用·名实·是非 留阳。即"在无的境况下的完整实践链 (行→果)" — 它把 66 的 palindrome 对 (无·行) 又加上了"果"的末梢。

### `oxoooxoo` · 68  *[true X²]*

**Subtitle**: 2 阴侧 · 无 · 非

- **(X, X)**: (oxoo, oxoo)  ← true X² (左右半相等)
- **分解**: 阳 · 无 · 体 · 形 · 名 · 非 · 知 · 因
- **对偶**: `xoxxxoxx` · 187
- **古文**: **塞** — 《说文》"塞, 隔也"; 《孟子》"塞乎天地之间"; 无 + 非 = 双否之阻塞; X² 配对 2↔6 双否同步 (#240 接收"否" 卦名后此 cell 承接 X² 算子层)
- **现代汉语**: **塞** — X² 双否阻塞 (有无 + 是非 X² 配对 2↔6 共振)。"无从有出" 与 "非从是出" 同步, 阻隔之态 — 孟子"塞乎天地之间"。( "否" 已迁 #240 接卦名)
- **英语**: Being-nonbeing and right-wrong both flip — the 2nd X² pair self-resonates. Non-being mirrors negation: two parallel negativities.
- **形式逻辑**: |y|₁ = 2 / true X² (high=low=oxoo) / 68 = 17 × 4 (X² 对角元) / yin 在 bit 2, 6
- **Why**: bit 2 (有无) 与 bit 6 (是非) 同步入阴。X² 配对 (1↔5, **2↔6**, 3↔7, 4↔8) 第 2 对单独共振。哲学意涵: "无"是存在论的否定, "非"是判断的否定 — 两者结构同源, 此码捕捉它们的同步发生。"不在 = 不是" 的 X² 对应。

### `oxoooxox` · 69

**Subtitle**: 3 阴侧 · 无 · 非 · 果

- **(X, X)**: (oxoo, oxox)
- **分解**: 阳 · 无 · 体 · 形 · 名 · 非 · 知 · 果
- **对偶**: `xoxxxoxo` · 186
- **古文**: **断** — 《说文》"断, 截也"; 无 + 非 + 果 = 断 / 绝灭 (《庄子·齐物论》"道恶乎隐而有真伪")
- **现代汉语**: 有无+是非+因果 三翻 (无+非+果)。两种否定 + 果, 否定生果。
- **英语**: Three yin axes: non-being, wrong-judgment, effect. Twofold negation yields its outcome.
- **形式逻辑**: |y|₁ = 3 / e₆₉ / yin 在 bit 2,6,8
- **Why**: 有无·是非·因果 三轴入阴 — 本体的"无"+ 实用的"非·果"。两种否定 (无/非) 加上后果, 知行·名实 留阳 — 无具体行动或语言变化, 只是抽象的否定性后果。68 的 X² 对 (无·非) 加上"果"末梢。

### `oxoooxxo` · 70

**Subtitle**: 3 阴侧 · 无 · 非 · 行

- **(X, X)**: (oxoo, oxxo)
- **分解**: 阳 · 无 · 体 · 形 · 名 · 非 · 行 · 因
- **对偶**: `xoxxxoox` · 185
- **古文**: **反** — 《道德经》"反者道之动"; 无 + 非 + 行 = 反 (返其本; 庄子"反衍")
- **现代汉语**: 有无+是非+知行 三翻 (无+非+行)。无 + 非 + 行 — 否定性行动, 果未到。
- **英语**: Three yin axes: non-being, wrong-judgment, acting. Negative action grounded in absence — outcome pending.
- **形式逻辑**: |y|₁ = 3 / e₇₀ / yin 在 bit 2,6,7
- **Why**: 有无·是非·知行 三轴入阴, 因果·名实·体用·形声·阴阳 留阳。"无·非·行" — 缺席之根上的否定性行动, 其后果尚未闭环。是 68 (无·非 X² 对) 加上"行"的临界态。

### `oxoooxxx` · 71

**Subtitle**: 4 阴侧 · 无 · 非 · 行 · 果

- **(X, X)**: (oxoo, oxxx)
- **分解**: 阳 · 无 · 体 · 形 · 名 · 非 · 行 · 果
- **对偶**: `xoxxxooo` · 184
- **古文**: **亡** — 《孟子》"逆天者亡"; 无 + 非 + 行 + 果 = 亡 (灭亡)
- **现代汉语**: 有无+是非+知行+因果 四翻, 唯阴阳·体用·形声·名实 留阳。"无·非·行·果"完整否定链。
- **英语**: Four yin axes: non-being, wrong-judgment, acting, effect. The full negative cascade — absence, dissent, action, consequence.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,6,7,8 / d(⊤⁸)=4, d(⊥⁸)=4
- **Why**: 实用类三尾 (非·行·果) + 本体的有无 (无) — "无·非·行·果" 完整的"否定性实践"轨迹。仅最深的极性 (阴阳)·体用·形声·名实 保留生成侧 — 形上基础与语义命名都未动, 但存在论根 (有→无) 与全部实用底色都已翻负。

### `oxooxooo` · 72

**Subtitle**: 2 阴侧 · 无 · 实

- **(X, X)**: (oxoo, xooo)
- **分解**: 阳 · 无 · 体 · 形 · 实 · 是 · 知 · 因
- **对偶**: `xoxxoxxx` · 183
- **古文**: **虚** — 《道德经》"致虚极"; 无 + 实 = 虚 (虚实相生); 庄子"唯道集虚"
- **现代汉语**: 有无+名实 双阴 (无+实)。存在与命名两端松动 — 无中之实, 不可言之事。
- **英语**: Two-axis yin: non-being and reality. Ontology's "absent presence" meets semantic's "thing-beyond-name".
- **形式逻辑**: |y|₁ = 2 / e₇₂ / yin 在 bit 2, 5 (本体与实用首位)
- **Why**: 有无·名实 同时入阴。两者都是"承载/显化"维: 有出无 (本体侧), 名出实 (语义侧)。这是"虚无中冒出现象"的最简结构: 无言之实, 不在之在。X² 配对中是 (2↔6) 与 (1↔5) 的"半边"启动 — 不构成 X² 共振但触及两对回声。

### `oxooxoox` · 73

**Subtitle**: 3 阴侧 · 无 · 实 · 果

- **(X, X)**: (oxoo, xoox)
- **分解**: 阳 · 无 · 体 · 形 · 实 · 是 · 知 · 果
- **对偶**: `xoxxoxxo` · 182
- **古文**: **化** — 《说文》"化, 教行也"; 无 + 实 + 果 = 化育 (《周易》"化而裁之谓之变"; 《中庸》"赞天地之化育")
- **现代汉语**: 有无+名实+因果 三翻 (无+实+果)。无言之事产生了后果, 而是非·知行未动。
- **英语**: Three yin axes: non-being, reality, effect. Unnameable thing bears outcome — judgment and action untouched.
- **形式逻辑**: |y|₁ = 3 / e₇₃ / yin 在 bit 2,5,8
- **Why**: 有无·名实·因果 三轴入阴。"无·实·果" — 三个轴都是"显化"链上的: 无 (本体出), 实 (语义出), 果 (因出)。它们同步翻意味着系统的显化维全部启动, 而判断、行动、表达维都未动。一种"暗中显化并结果"的纯派生态。

### `oxooxoxo` · 74

**Subtitle**: 3 阴侧 · 无 · 实 · 行

- **(X, X)**: (oxoo, xoxo)
- **分解**: 阳 · 无 · 体 · 形 · 实 · 是 · 行 · 因
- **对偶**: `xoxxoxox` · 181
- **古文**: **易** — 《周易》之名; 《系辞》"生生之谓易"; 无 + 实 + 行 = 易 (变易)
- **现代汉语**: 有无+名实+知行 三翻 (无+实+行)。无中之实之行 — 缺席之事在做。
- **英语**: Three yin axes: non-being, reality, acting. The "doing of the unnameable in absence" — concrete action without ontic/linguistic grounding.
- **形式逻辑**: |y|₁ = 3 / e₇₄ / yin 在 bit 2,5,7
- **Why**: 有无·名实·知行 — 全是奇/中位 (bit 2, 5, 7)。是非·因果 (bit 6, 8) 留阳。即"无中之实之行", 但判断仍是, 后果未来。一种纯行动而无伦理评判的实践态。

### `oxooxoxx` · 75

**Subtitle**: 4 阴侧 · 无 · 实 · 行 · 果

- **(X, X)**: (oxoo, xoxx)
- **分解**: 阳 · 无 · 体 · 形 · 实 · 是 · 行 · 果
- **对偶**: `xoxxoxoo` · 180
- **古文**: **造** — 《说文》"造, 就也"; 无 + 实 + 行 + 果 = 造 (从无生有之造化)
- **现代汉语**: 有无+名实+知行+因果 四翻, 唯是非留是。"无·实·行·果", 判断仍肯定。
- **英语**: Four yin axes: non-being, reality, acting, effect. Right-wrong alone holds at "is" — full positive engagement in the void.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,5,7,8 / d(⊤⁸)=d(⊥⁸)=4
- **Why**: 实用类除是非外全翻 + 本体的有无。"无·实·行·果" — 自我肯定地在虚无中实事求行结果。判断始终是, 形声·体用·阴阳留阳: 即心始终肯定, 而事事在虚无中展开。

### `oxooxxoo` · 76

**Subtitle**: 3 阴侧 · 无 · 实 · 非

- **(X, X)**: (oxoo, xxoo)
- **分解**: 阳 · 无 · 体 · 形 · 实 · 非 · 知 · 因
- **对偶**: `xoxxooxx` · 179
- **古文**: **妙** — 《道德经》"故常无, 欲以观其妙"; 无 + 实 + 非 = 妙 (玄妙不可说)
- **现代汉语**: 有无+名实+是非 三翻 (无+实+非)。无中冒出现象, 现象即错 — 形上批判态。
- **英语**: Three yin axes: non-being, reality, wrong-judgment. Absence-rooted reality joined with negative judgment — pure metaphysical critique.
- **形式逻辑**: |y|₁ = 3 / e₇₆ / yin 在 bit 2,5,6 (本体次轴 + 实用前两位)
- **Why**: 有无·名实·是非 三轴入阴, 知行·因果留阳。"无中生实, 实即非" — 无中冒出现象, 然现象被判断为否。一种纯意识批判, 身未动果未临。

### `oxooxxox` · 77  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 无 · 实 · 非 · 果

- **(X, X)**: (oxoo, xxox)
- **分解**: 阳 · 无 · 体 · 形 · 实 · 非 · 知 · 果
- **对偶**: `xoxxooxo` · 178
- **古文**: **幻** — 佛家"如梦如幻"; 无 + 实 + 非 + 果 = 幻 (虚妄之果); 《金刚经》"一切有为法, 如梦幻泡影"; comp-palindrome
- **现代汉语**: 有无+名实+是非+因果 四翻, 唯阴阳·体用·形声·知行 留阳。comp-palindrome: 配对轴各取相反侧。
- **英语**: Four yin axes: non-being, reality, wrong-judgment, effect. Anti-palindrome: each palindrome pair holds opposite sides.
- **形式逻辑**: |y|₁ = 4 / comp-palindrome (反序后取补 = 自身) / yin 在 bit 2,5,6,8 / d(⊤⁸)=d(⊥⁸)=4
- **Why**: comp-palindrome 16 元之一。配对 (1↔8): 阳·果, (2↔7): 无·知, (3↔6): 体·非, (4↔5): 形·实 — 每对一阳一阴。即"在每个 palindrome 配对中都分裂"。哲学上, 它是类泰 (#15) 在有无轴上扰动的版本 — 本体的"有"被替换为"无", 加全部实用层翻。

### `oxooxxxo` · 78

**Subtitle**: 4 阴侧 · 无 · 实 · 非 · 行

- **(X, X)**: (oxoo, xxxo)
- **分解**: 阳 · 无 · 体 · 形 · 实 · 非 · 行 · 因
- **对偶**: `xoxxooox` · 177
- **古文**: **罔** — 《论语·为政》"学而不思则罔"; 无 + 实 + 非 + 行 = 罔 (迷惘)
- **现代汉语**: 有无+名实+是非+知行 四翻, 唯因果留因。"无·实·非·行" 完整批评性行动, 果未临。
- **英语**: Four yin axes: non-being, reality, wrong-judgment, acting. Cause-effect holds — full negative practical engagement, outcome pending.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,5,6,7 / yang 仅 bit 1,3,4,8
- **Why**: 实用类除因果外全翻 + 本体有无。"无·实·非·行" — 在虚无之根上展开的完整否定性实践, 后果尚未闭环。革命前夕, 根是"无"。

### `oxooxxxx` · 79

**Subtitle**: 3 阳侧 · 阳 · 体 · 形

- **(X, X)**: (oxoo, xxxx)
- **分解**: 阳 · 无 · 体 · 形 · 实 · 非 · 行 · 果
- **对偶**: `xoxxoooo` · 176
- **古文**: **质** — 《说文》"质, 以物相赘"; 阳 + 体 + 形 三阳 = 质 (体质·实质; 《论语》"质胜文则野")
- **现代汉语**: 唯阴阳·体用·形声 三轴留阳, 余 5 轴皆阴。本体壳留 (形+体), 而存在论"有"已沉, 实用全开。
- **英语**: Three yang axes: yin-yang, substance-function, form-sound. Being-nonbeing flips along with all pragmatics.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,3,4 / d(⊤⁸)=5
- **Why**: 阴阳·体用·形声 守源 — 本体的"极性+派生+表达"三轴; 而本体核心 (有无) + 实用 4 轴全翻。象征"形上骨架存而中柱崩 (无), 实用全显"。

### `oxoxoooo` · 80

**Subtitle**: 2 阴侧 · 无 · 声

- **(X, X)**: (oxox, oooo)
- **分解**: 阳 · 无 · 体 · 声 · 名 · 是 · 知 · 因
- **对偶**: `xoxoxxxx` · 175
- **古文**: **默** — 《说文》"默, 犬暂逐人也" (引申无声); 无 + 声 = 寂默; 论语"默而识之"
- **现代汉语**: 有无 + 形声 双阴 (无+声)。本体的两个"显化轴"同步翻 — 无之声, 缺席中的发声。
- **英语**: Two-axis yin: non-being and sound. Two ontological "emergence" axes flip — voice from absence.
- **形式逻辑**: |y|₁ = 2 / e₈₀ / yin ⊂ 本体类 (bit 2, 4)
- **Why**: 有无 (bit 2) 与形声 (bit 4) 入阴, 体用 (bit 3) 留阳 — 本体的奇数偶数交替模式。即"无的声音", 一种从虚空中冒出来的发声。实用 4 轴皆留阳, 故这是纯本体内的扰动。

### `oxoxooox` · 81

**Subtitle**: 3 阴侧 · 无 · 声 · 果

- **(X, X)**: (oxox, ooox)
- **分解**: 阳 · 无 · 体 · 声 · 名 · 是 · 知 · 果
- **对偶**: `xoxoxxxo` · 174
- **古文**: **响** — 《说文》"响, 声也"; 无 + 声 + 果 = 响 (《周易》"同声相应"; 空谷之响)
- **现代汉语**: 有无+形声+因果 三翻 (无+声+果)。无之声引发后果, 而判断行动未动。
- **英语**: Three yin axes: non-being, sound, effect. Voice-from-absence bears outcome — pure resonance without action or judgment.
- **形式逻辑**: |y|₁ = 3 / e₈₁ / yin 在 bit 2,4,8
- **Why**: 有无·形声·因果 三轴入阴。"无·声·果" — 一种从虚空里发出的声音, 直接产生后果。是非·知行·名实·体用·阴阳 留阳。象征"无声之声引发因果"的形上奇态。

### `oxoxooxo` · 82

**Subtitle**: 3 阴侧 · 无 · 声 · 行

- **(X, X)**: (oxox, ooxo)
- **分解**: 阳 · 无 · 体 · 声 · 名 · 是 · 行 · 因
- **对偶**: `xoxoxxox` · 173
- **古文**: **冥** — 《庄子·大宗师》"冥伯之丘"; 无 + 声 + 行 = 冥行 (暗中独行)
- **现代汉语**: 有无+形声+知行 三翻 (无+声+行)。"无的声"伴随"行" — 言行起于虚无。
- **英语**: Three yin axes: non-being, sound, acting. The voiced act from absence — speech and action from the void.
- **形式逻辑**: |y|₁ = 3 / e₈₂ / yin 在 bit 2,4,7
- **Why**: 有无·形声·知行 — 无之声之行。Plato 的 "speech is action" 模式叠加在虚无的本体上。是非·因果留阳: 不评判, 不计后果, 仅是"无中发声而动"。

### `oxoxooxx` · 83

**Subtitle**: 4 阴侧 · 无 · 声 · 行 · 果

- **(X, X)**: (oxox, ooxx)
- **分解**: 阳 · 无 · 体 · 声 · 名 · 是 · 行 · 果
- **对偶**: `xoxoxxoo` · 172
- **古文**: **昧** — 《左传》"昧者无知"; 无 + 声 + 行 + 果 = 昧 (《尚书》"明明上天")
- **现代汉语**: 有无+形声+知行+因果 四翻, 唯阴阳·体用·名实·是非 留阳。"无·声·行·果"四联。
- **英语**: Four yin axes: non-being, sound, acting, effect. The void speaks, acts, and bears outcome — judgment and substance hold yang.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,4,7,8 / d(⊤⁸)=d(⊥⁸)=4
- **Why**: 4 个轴 (无·声·行·果) 入阴 — 本体的有无·形声 + 实用的知行·因果。"无声行果" 完整链 — 从虚空发出声音, 引发行动, 结成果。体用·名实·是非·阴阳留阳, 故根基与判断仍守。

### `oxoxoxoo` · 84

**Subtitle**: 3 阴侧 · 无 · 声 · 非

- **(X, X)**: (oxox, oxoo)
- **分解**: 阳 · 无 · 体 · 声 · 名 · 非 · 知 · 因
- **对偶**: `xoxoxoxx` · 171
- **古文**: **缄** — 《说文》"缄, 束箧也" (引申封口); 无 + 声 + 非 = 缄默之否
- **现代汉语**: 有无+形声+是非 三翻 (无+声+非)。无之声 + 非, 否定性发声。
- **英语**: Three yin axes: non-being, sound, wrong-judgment. Negative voicing from the void.
- **形式逻辑**: |y|₁ = 3 / e₈₄ / yin 在 bit 2,4,6 / 偶位三连
- **Why**: 有无·形声·是非 — 全是偶位轴 (bit 2,4,6)。一种"从虚无中发出否定之声"的模式。知行·因果·阴阳·体用·名实 (奇位) 留阳。这是 Walsh-Hadamard 上"偶位扰动"的子类。

### `oxoxoxox` · 85  *[true X² · comp-palindrome]*

**Subtitle**: 4 阴侧 · 无 · 声 · 非 · 果

- **(X, X)**: (oxox, oxox)  ← true X² (左右半相等)
- **分解**: 阳 · 无 · 体 · 声 · 名 · 非 · 知 · 果
- **对偶**: `xoxoxoxo` · 170
- **古文**: 阴阳错位 · 奇位阴 (Walsh W₁)
- **现代汉语**: 偶位阳 · 奇位阴 (棋盘 W₁)。8 轴交错, 一阳一阴, 高低半完全自方。
- **英语**: Walsh W₁ checkerboard — yang on even positions, yin on odd. Full self-square + anti-palindrome.
- **形式逻辑**: |y|₁ = 4 / true X² (high=low=oxox) / comp-palindrome / Walsh W₁ 基函数 / d(⊤⁸)=d(⊥⁸)=4
- **Why**: 偶位 (bit 1,3,5,7 即 阴阳·体用·名实·知行) 留阳, 奇位 (bit 2,4,6,8 即 有无·形声·是非·因果) 入阴。这是 F₂⁸ 上最低频的偶函数模式, 在 Hadamard 变换中作为 W₁ 基。哲学上: 8 轴交替地"守"与"显" — 极性、派生、命名、知 留源, 而存在、表达、判断、因果 全显。对偶 #170 反之。

### `oxoxoxxo` · 86

**Subtitle**: 4 阴侧 · 无 · 声 · 非 · 行

- **(X, X)**: (oxox, oxxo)
- **分解**: 阳 · 无 · 体 · 声 · 名 · 非 · 行 · 因
- **对偶**: `xoxoxoox` · 169
- **古文**: **拒** — 《说文》"拒, 扞也"; 无 + 声 + 非 + 行 = 拒 (无言之拒动)
- **现代汉语**: 有无+形声+是非+知行 四翻, 唯阴阳·体用·名实·因果 留阳。"无·声·非·行"中段偏离。
- **英语**: Four yin axes: non-being, sound, wrong-judgment, acting. Outcome stays at "cause" — full critical voice-act, outcome pending.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,4,6,7 / d=4
- **Why**: 与 #85 相比, 因果轴还原阳 (因), 而知行翻成行。即"在 Walsh W₁ 模式上把因果换为行"。"无·声·非·行"完整批评行动, 唯果未临。

### `oxoxoxxx` · 87

**Subtitle**: 3 阳侧 · 阳 · 体 · 名

- **(X, X)**: (oxox, oxxx)
- **分解**: 阳 · 无 · 体 · 声 · 名 · 非 · 行 · 果
- **对偶**: `xoxoxooo` · 168
- **古文**: **章** — 《说文》"章, 乐竟为一章"; 阳 + 体 + 名 三阳 = 章 (彰显之体名; 论语"焕乎其有文章")
- **现代汉语**: 唯阴阳·体用·名实 三轴留阳。极性 + 派生 + 命名 守源, 余 5 轴皆显化。
- **英语**: Three yang axes: yin-yang, substance-function, name-reality. Polarity, derivation, naming hold; the rest five flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,3,5 (奇位三轴) / d(⊤⁸)=5
- **Why**: 奇位三轴 (1,3,5) 留阳, 其余 5 轴入阴。即 X² 配对 (1↔5) 整对留阳, 加 bit 3 (体用) 留阳; 其余皆翻。这种"奇位部分守, 偶位全失"接近 Walsh 反相。

### `oxoxxooo` · 88

**Subtitle**: 3 阴侧 · 无 · 声 · 实

- **(X, X)**: (oxox, xooo)
- **分解**: 阳 · 无 · 体 · 声 · 实 · 是 · 知 · 因
- **对偶**: `xoxooxxx` · 167
- **古文**: **隐** — 《周易·系辞》"君子藏器于身, 待时而动"; 无 + 声 + 实 = 隐 (大学"莫见乎隐")
- **现代汉语**: 有无+形声+名实 三翻 (无+声+实)。本体两轴 (无·声) + 实用首 (实) — 形上下三阶联翻。
- **英语**: Three yin axes: non-being, sound, reality. Two ontological emanations couple with name-overflow — pure expressive cascade.
- **形式逻辑**: |y|₁ = 3 / e₈₈ / yin 在 bit 2,4,5
- **Why**: 有无·形声·名实 — bit 2,4,5 (跳过 3)。"无·声·实" — 从虚无中冒出的声响实事化。体用·是非·知行·因果·阴阳留阳, 故是非·知行·因果的判断/行动/后果维都未启动 — 纯"表达性涌现"。

### `oxoxxoox` · 89

**Subtitle**: 4 阴侧 · 无 · 声 · 实 · 果

- **(X, X)**: (oxox, xoox)
- **分解**: 阳 · 无 · 体 · 声 · 实 · 是 · 知 · 果
- **对偶**: `xoxooxxo` · 166
- **古文**: **谋** — 《说文》"谋, 虑难曰谋"; 无 + 声 + 实 + 果 = 谋 (《孙子》"上兵伐谋")
- **现代汉语**: 有无+形声+名实+因果 四翻, 唯阴阳·体用·是非·知行 留阳。"无·声·实·果"涌现得果。
- **英语**: Four yin axes: non-being, sound, reality, effect. Expressive emergence completes — judgment and action hold yang.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,4,5,8 / d=4
- **Why**: 4 个"显化/表达"轴 (无·声·实·果) 入阴。即 Walsh W₃ (#15) 的本体扰动版 + 因果尾。意味"从虚空冒出声、化为实、结成果", 而判断与行动维都未动。

### `oxoxxoxo` · 90  *[palindrome]*

**Subtitle**: 4 阴侧 · 无 · 声 · 实 · 行

- **(X, X)**: (oxox, xoxo)
- **分解**: 阳 · 无 · 体 · 声 · 实 · 是 · 行 · 因
- **对偶**: `xoxooxox` · 165
- **古文**: **沉** — 《说文》"沉, 没也"; 无 + 声 + 实 + 行 = 沉 (沉默之实行; 《楚辞》"沉郁顿挫"); palindrome
- **现代汉语**: 有无+形声+名实+知行 四翻, 唯阴阳·体用·是非·因果 留阳。palindrome 形 — 配对轴 (1↔8, 2↔7, 3↔6, 4↔5) 各取同侧。
- **英语**: Four yin axes: non-being, sound, reality, acting. Palindrome — each mirror pair takes a consistent side.
- **形式逻辑**: |y|₁ = 4 / palindrome (bit i = bit 7-i) / yin 在 bit 2,4,5,7
- **Why**: palindrome 第 1 配对 (1↔8): 阳·因 同阳; 第 2 (2↔7): 无·行 同阴; 第 3 (3↔6): 体·是 同阳; 第 4 (4↔5): 声·实 同阴。即四配对中两对阴两对阳, 镜像对称。

### `oxoxxoxx` · 91

**Subtitle**: 3 阳侧 · 阳 · 体 · 是

- **(X, X)**: (oxox, xoxx)
- **分解**: 阳 · 无 · 体 · 声 · 实 · 是 · 行 · 果
- **对偶**: `xoxooxoo` · 164
- **古文**: **真** — 《说文》"真, 仙人变形而登天也"; 阳 + 体 + 是 三阳 = 真 (本体之是, 庄子"真人")
- **现代汉语**: 唯阴阳·体用·是非 三轴留阳。极性 + 派生 + 肯定判断 守源。
- **英语**: Three yang axes: yin-yang, substance-function, right-wrong. The remaining five flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,3,6
- **Why**: 5 轴入阴: 无·声·实·行·果。阳轴只剩极性、派生、判断 — 心仍肯定且根仍极性, 而事尽显化。

### `oxoxxxoo` · 92

**Subtitle**: 4 阴侧 · 无 · 声 · 实 · 非

- **(X, X)**: (oxox, xxoo)
- **分解**: 阳 · 无 · 体 · 声 · 实 · 非 · 知 · 因
- **对偶**: `xoxoooxx` · 163
- **古文**: **疑** — 《说文》"疑, 惑也"; 无 + 声 + 实 + 非 = 疑 (《大学》"格物致知"前之疑惑)
- **现代汉语**: 有无+形声+名实+是非 四翻, 唯阴阳·体用·知行·因果 留阳。"无·声·实·非"四联意识批判。
- **英语**: Four yin axes: non-being, sound, reality, wrong-judgment. Conscious critique fully developed — body and outcome unmoved.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,4,5,6 / d=4
- **Why**: 4 个"表达-判断"维轴 (无·声·实·非) 入阴, 即 #15 (类泰) 的本体扰动 + 中段连续。"虚空发声成实成非" — 一种从无中生出的批判性涌现, 但身未动 (知行=知), 果未临 (因果=因)。

### `oxoxxxox` · 93

**Subtitle**: 3 阳侧 · 阳 · 体 · 知

- **(X, X)**: (oxox, xxox)
- **分解**: 阳 · 无 · 体 · 声 · 实 · 非 · 知 · 果
- **对偶**: `xoxoooxo` · 162
- **古文**: **达** — 《论语》"己欲达而达人"; 阳 + 体 + 知 三阳 = 达 (通达; 《周易》"知至至之")
- **现代汉语**: 唯阴阳·体用·知行 三轴留阳。
- **英语**: Three yang axes: yin-yang, substance-function, know-act. Polarity + derivation + knowing hold.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,3,7
- **Why**: 知行守"知", 体用守体, 阴阳守阳, 其它皆翻。即"心知, 形体未动, 而无·声·实·非·果 五种显化已发生"。一种被动观察者的状态。

### `oxoxxxxo` · 94

**Subtitle**: 3 阳侧 · 阳 · 体 · 因

- **(X, X)**: (oxox, xxxo)
- **分解**: 阳 · 无 · 体 · 声 · 实 · 非 · 行 · 因
- **对偶**: `xoxoooox` · 161
- **古文**: **基** — 《说文》"基, 墙始也"; 阳 + 体 + 因 三阳 = 基 (基础; 《大学》"君子先慎乎德")
- **现代汉语**: 唯阴阳·体用·因果 三轴留阳。
- **英语**: Three yang axes: yin-yang, substance-function, cause-effect. Cause holds, effect not yet.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,3,8
- **Why**: 极性·派生·因 守源; 无·声·实·非·行 已动。"事在动而果未来", 而本体的"体"与"阳"仍守。一种近极阴而根仍存的状态。

### `oxoxxxxx` · 95

**Subtitle**: 2 阳侧 · 阳 · 体

- **(X, X)**: (oxox, xxxx)
- **分解**: 阳 · 无 · 体 · 声 · 实 · 非 · 行 · 果
- **对偶**: `xoxooooo` · 160
- **古文**: **立** — 《论语》"三十而立"; 阳 + 体 双阳 = 立 (本体之确立; 《大学》"修身齐家治国平天下"之根本)
- **现代汉语**: 唯阴阳·体用 两轴留阳, 余 6 轴皆阴。"阳"与"体"两个最根本的本体轴守源, 其余尽显。
- **英语**: Only two yang axes: yin-yang and substance-function. Polarity and substance hold; everything else manifests.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 1,3 / d(⊤⁸)=6
- **Why**: 极性 + 本体核心 (体) 两轴留, 其余 6 轴尽翻。哲学上, 这是"道体仍存而万象皆显"的近极阴形态。

### `oxxooooo` · 96

**Subtitle**: 2 阴侧 · 无 · 用

- **(X, X)**: (oxxo, oooo)
- **分解**: 阳 · 无 · 用 · 形 · 名 · 是 · 知 · 因
- **对偶**: `xooxxxxx` · 159
- **古文**: **玄** — 《道德经》"玄之又玄, 众妙之门"; 无 + 用 = 玄 (无之以为用即玄之妙)
- **现代汉语**: 有无+体用 双阴 (无+用)。本体中两轴翻, 而极性 (阳) 与表达 (形) 守源 — 道家"无之用"的形式化。
- **英语**: Two-axis yin: non-being and function. The Daoist "function of non-being" — bit-encoded.
- **形式逻辑**: |y|₁ = 2 / e₉₆ / yin 在 bit 2, 3 (本体中两轴)
- **Why**: 有无·体用 同步入阴。《道德经》"三十辐共一毂, 当其无, 有车之用" — 此码即"无"与"用"两轴的同步翻转, 是道家"以无为用"的最简结构。X² 回声 (bit 6 是非 + bit 7 知行) 都留阳, 故判断与行动未动。

### `oxxoooox` · 97

**Subtitle**: 3 阴侧 · 无 · 用 · 果

- **(X, X)**: (oxxo, ooox)
- **分解**: 阳 · 无 · 用 · 形 · 名 · 是 · 知 · 果
- **对偶**: `xooxxxxo` · 158
- **古文**: **道** — 《道德经》"道可道, 非常道"; 无 + 用 + 果 = 道 (无之以为用而成果, 即道之运行)
- **现代汉语**: 有无+体用+因果 三翻 (无+用+果)。无之用得果, 道家辩证的具体后果。
- **英语**: Three yin axes: non-being, function, effect. "Non-being-as-function" bears outcome — Daoist dialectic concretized.
- **形式逻辑**: |y|₁ = 3 / e₉₇ / yin 在 bit 2,3,8
- **Why**: 有无·体用·因果 三轴 — "无·用·果"。以无为用而有果, 即"无之用"具体显化为后果。形声·名实·是非·知行 留阳, 故仍是抽象层面的因果。

### `oxxoooxo` · 98

**Subtitle**: 3 阴侧 · 无 · 用 · 行

- **(X, X)**: (oxxo, ooxo)
- **分解**: 阳 · 无 · 用 · 形 · 名 · 是 · 行 · 因
- **对偶**: `xooxxxox` · 157
- **古文**: **机** — 《庄子·至乐》"万物皆出于机, 皆入于机"; 无 + 用 + 行 = 机 (玄机)
- **现代汉语**: 有无+体用+知行 三翻 (无+用+行)。"无·用·行" — 以无为用的实际行动。
- **英语**: Three yin axes: non-being, function, acting. Practicing the function of non-being.
- **形式逻辑**: |y|₁ = 3 / e₉₈ / yin 在 bit 2,3,7
- **Why**: 有无·体用·知行 — 三个相邻 (bit 2,3,7) 入阴。"无·用·行" — 既以无为用又付诸行动。是非·因果 (bit 6,8) 留阳: 不评判、不计后果, 纯 Daoist 实践。

### `oxxoooxx` · 99

**Subtitle**: 4 阴侧 · 无 · 用 · 行 · 果

- **(X, X)**: (oxxo, ooxx)
- **分解**: 阳 · 无 · 用 · 形 · 名 · 是 · 行 · 果
- **对偶**: `xooxxxoo` · 156
- **古文**: **就** — 《说文》"就, 高也" (引申成就); 无 + 用 + 行 + 果 = 就 (无之以为用而成)
- **现代汉语**: 有无+体用+知行+因果 四翻, 唯阴阳·形声·名实·是非 留阳。"无·用·行·果"完整 Daoist 链。
- **英语**: Four yin axes: non-being, function, acting, effect. The full Daoist "non-being-as-function" cascade with judgment intact.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,3,7,8 / d=4
- **Why**: 本体的"无·用" + 实用末两轴"行·果" — 完整的"以无为用-行-果"链。是非留是 (心始终肯定), 形声留形, 名实留名, 阴阳留阳 — 即语言和判断维都未动, 只在本体-实用的"派生与显化"通道里完成。

### `oxxooxoo` · 100

**Subtitle**: 3 阴侧 · 无 · 用 · 非

- **(X, X)**: (oxxo, oxoo)
- **分解**: 阳 · 无 · 用 · 形 · 名 · 非 · 知 · 因
- **对偶**: `xooxxoxx` · 155
- **古文**: **微** — 《中庸》"莫见乎隐, 莫显乎微"; 无 + 用 + 非 = 微 (《道德经》"听之不闻名曰希")
- **现代汉语**: 有无+体用+是非 三翻 (无+用+非)。无之用伴否定判断 — 道家批判态。
- **英语**: Three yin axes: non-being, function, wrong-judgment. The "non-being-as-function" with critical judgment.
- **形式逻辑**: |y|₁ = 3 / e₁₀₀ / yin 在 bit 2,3,6
- **Why**: 有无·体用·是非 三轴入阴。形声·名实·知行·因果·阴阳 留阳。"无·用·非" — 以无为用而判断为否。一种 Daoist 的批判: 不只以无为用, 还判定现状为非。

### `oxxooxox` · 101

**Subtitle**: 4 阴侧 · 无 · 用 · 非 · 果

- **(X, X)**: (oxxo, oxox)
- **分解**: 阳 · 无 · 用 · 形 · 名 · 非 · 知 · 果
- **对偶**: `xooxxoxo` · 154
- **古文**: **病** — 《周易》"凡益之道, 与时偕行"; 无 + 用 + 非 + 果 = 病 (无用之非果即病弊)
- **现代汉语**: 有无+体用+是非+因果 四翻, 唯阴阳·形声·名实·知行 留阳。"无·用·非·果"否定批判得果。
- **英语**: Four yin axes: non-being, function, wrong-judgment, effect. Non-being-as-function under critique bears its outcome.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,3,6,8 / d=4
- **Why**: 本体两轴 (无·用) + 实用两隔轴 (非·果)。即"无之用-非-果", 而身未动 (知行留知)。心知有非果, 而形为之"用"。

### `oxxooxxo` · 102  *[true X² · palindrome]*

**Subtitle**: 4 阴侧 · 无 · 用 · 非 · 行

- **(X, X)**: (oxxo, oxxo)  ← true X² (左右半相等)
- **分解**: 阳 · 无 · 用 · 形 · 名 · 非 · 行 · 因
- **对偶**: `xooxxoox` · 153
- **古文**: **方** — 《周髀》"地方"; X² self-square 算子 (σ₂ 不动点); palindrome ∩ X² 内对; 与 #153 圆 形成"天圆地方"经典对 [K.4 双重身份]
- **现代汉语**: **方** — X² self-square 算子 (σ₂ 不动点)。高低半皆 oxxo 同时镜像不变 (palindrome ∩ X² 内对); 与 #153 圆 形成"天圆地方"经典对; 最高对称 4 元之一。
- **英语**: Inner-symmetric self-square. Palindrome ∩ true X² — one of the four maximally symmetric codes (0, 102, 153, 255).
- **形式逻辑**: |y|₁ = 4 / true X² (high=low=oxxo) / palindrome / 102 = 17×6 (X² 对角元) / d(⊤⁸)=d(⊥⁸)=4
- **Why**: palindrome ∩ true X² 4 元 {0, 102, 153, 255} 之一。其结构: bit 2,3,6,7 入阴 — 即 X² 配对的 (2↔6) 与 (3↔7) 双对共振, 同时 palindrome 配对 (2↔7) 与 (3↔6) 同侧。本体的"无·用" + 实用的"非·行" — 道家的"无用"与实用的"非行"在两层对称中同步翻。最深的对称性意味着这是"以无为用且否定行动"的最纯净结构。

### `oxxooxxx` · 103

**Subtitle**: 3 阳侧 · 阳 · 形 · 名

- **(X, X)**: (oxxo, oxxx)
- **分解**: 阳 · 无 · 用 · 形 · 名 · 非 · 行 · 果
- **对偶**: `xooxxooo` · 152
- **古文**: **晳** — 《说文》"晳, 人色白也" (引申清晰); 阳 + 形 + 名 三阳 = 晳 (形名清晳)
- **现代汉语**: 唯阴阳·形声·名实 三轴留阳。表达-命名维守源, 余 5 轴皆显化。
- **英语**: Three yang axes: yin-yang, form-sound, name-reality. The "expression-naming" axes hold; the rest five flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,4,5
- **Why**: 阴阳·形声·名实 守源 — 三个"表达-命名"相关的轴 (形和名都关乎语言/符号)。其余 5 轴入阴。一种"语言形式仍稳, 而事态尽变"的近极阴。

### `oxxoxooo` · 104

**Subtitle**: 3 阴侧 · 无 · 用 · 实

- **(X, X)**: (oxxo, xooo)
- **分解**: 阳 · 无 · 用 · 形 · 实 · 是 · 知 · 因
- **对偶**: `xooxoxxx` · 151
- **古文**: **朴** — 《道德经》"复归于朴" / "敦兮其若朴"; 无 + 用 + 实 = 朴 (未雕之木)
- **现代汉语**: 有无+体用+名实 三翻 (无+用+实)。"无·用·实" — 以无为用而实现于事。
- **英语**: Three yin axes: non-being, function, reality. Non-being-as-function actualizes in reality.
- **形式逻辑**: |y|₁ = 3 / e₁₀₄ / yin 在 bit 2,3,5
- **Why**: 有无·体用·名实 — 道家的"无之用"加上语义的"实出名外"。三轴皆"显化"维。形声·是非·知行·因果·阴阳留阳。

### `oxxoxoox` · 105  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 无 · 用 · 实 · 果

- **(X, X)**: (oxxo, xoox)
- **分解**: 阳 · 无 · 用 · 形 · 实 · 是 · 知 · 果
- **对偶**: `xooxoxxo` · 150
- **古文**: **生** — 《道德经》"道生一, 一生二, 二生三"; 无 + 用 + 实 + 果 = 生 (无之以为用而生实生果); comp-palindrome
- **现代汉语**: 有无+体用+名实+因果 四翻, 唯阴阳·形声·是非·知行 留阳。comp-palindrome: 配对轴反侧。
- **英语**: Four yin axes: non-being, function, reality, effect. Anti-palindrome: each mirror pair holds opposite sides.
- **形式逻辑**: |y|₁ = 4 / comp-palindrome / yin 在 bit 2,3,5,8 / d=4
- **Why**: comp-palindrome 16 元之一。配对 (1↔8): 阳·果 (反), (2↔7): 无·知 (反), (3↔6): 用·是 (反), (4↔5): 形·实 (反)。即"无·用·实·果"在 anti-mirror 上重组。

### `oxxoxoxo` · 106

**Subtitle**: 4 阴侧 · 无 · 用 · 实 · 行

- **(X, X)**: (oxxo, xoxo)
- **分解**: 阳 · 无 · 用 · 形 · 实 · 是 · 行 · 因
- **对偶**: `xooxoxox` · 149
- **古文**: **修** — 《大学》"修身齐家治国"; 无 + 用 + 实 + 行 = 修 (《中庸》"修身以道, 修道以仁")
- **现代汉语**: 有无+体用+名实+知行 四翻, 唯阴阳·形声·是非·因果 留阳。"无·用·实·行"派生四联。
- **英语**: Four yin axes: non-being, function, reality, acting. Four derivative axes synchronize; polarity, form, judgment, cause hold.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,3,5,7 / d=4
- **Why**: yin 在 2,3,5,7 — 派生维 (无·用·实·行) 全开。表达 (形)、判断 (是)、根 (阳)、因 守。一种纯"以无生用化实行" 的进展态, 心仍肯定。

### `oxxoxoxx` · 107

**Subtitle**: 3 阳侧 · 阳 · 形 · 是

- **(X, X)**: (oxxo, xoxx)
- **分解**: 阳 · 无 · 用 · 形 · 实 · 是 · 行 · 果
- **对偶**: `xooxoxoo` · 148
- **古文**: **直** — 《说文》"直, 正见也"; 阳 + 形 + 是 三阳 = 直 (《论语》"以直报怨"; 《孟子》"养浩然之气")
- **现代汉语**: 唯阴阳·形声·是非 三轴留阳。
- **英语**: Three yang axes: yin-yang, form-sound, right-wrong.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,4,6
- **Why**: 极性·形·是 守源, 即"根仍极性, 形仍可见, 心仍肯定"。其余 5 轴 (无·用·实·行·果) 已显化。

### `oxxoxxoo` · 108

**Subtitle**: 4 阴侧 · 无 · 用 · 实 · 非

- **(X, X)**: (oxxo, xxoo)
- **分解**: 阳 · 无 · 用 · 形 · 实 · 非 · 知 · 因
- **对偶**: `xooxooxx` · 147
- **古文**: **驳** — 《说文》"驳, 马色不纯" (引申辩驳); 无 + 用 + 实 + 非 = 驳 (反驳)
- **现代汉语**: 有无+体用+名实+是非 四翻, 唯阴阳·形声·知行·因果 留阳。"无·用·实·非"四联意识批判。
- **英语**: Four yin axes: non-being, function, reality, wrong-judgment. Critical metaphysical cascade — body and outcome hold.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,3,5,6 / d=4
- **Why**: 本体两轴 (无·用) + 实用前两轴 (实·非)。即"以无为用化实判非", 但行动与因果都未启动。一种纯意识的批判性 Daoist 形而上学。

### `oxxoxxox` · 109

**Subtitle**: 3 阳侧 · 阳 · 形 · 知

- **(X, X)**: (oxxo, xxox)
- **分解**: 阳 · 无 · 用 · 形 · 实 · 非 · 知 · 果
- **对偶**: `xooxooxo` · 146
- **古文**: **察** — 《说文》"察, 覆也"; 阳 + 形 + 知 三阳 = 察 (察知; 《大学》"致知格物")
- **现代汉语**: 唯阴阳·形声·知行 三轴留阳。
- **英语**: Three yang axes: yin-yang, form-sound, know-act.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,4,7
- **Why**: 极性·形·知 守, 余 5 轴翻。"形可见, 心知, 而其余皆变" — 一种纯观照状态。

### `oxxoxxxo` · 110

**Subtitle**: 3 阳侧 · 阳 · 形 · 因

- **(X, X)**: (oxxo, xxxo)
- **分解**: 阳 · 无 · 用 · 形 · 实 · 非 · 行 · 因
- **对偶**: `xooxooox` · 145
- **古文**: **源** — 《说文》"源, 水泉本也"; 阳 + 形 + 因 三阳 = 源 (本源)
- **现代汉语**: 唯阴阳·形声·因果 三轴留阳。
- **英语**: Three yang axes: yin-yang, form-sound, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,4,8
- **Why**: 形·因 守, 极性留阳, 余 5 轴翻。"事在动而果未临, 形仍清晰" 的近极阴。

### `oxxoxxxx` · 111

**Subtitle**: 2 阳侧 · 阳 · 形

- **(X, X)**: (oxxo, xxxx)
- **分解**: 阳 · 无 · 用 · 形 · 实 · 非 · 行 · 果
- **对偶**: `xooxoooo` · 144
- **古文**: **显** — 《周易·系辞》"显诸仁, 藏诸用"; 阳 + 形 双阳 = 显 (《中庸》"莫显乎微")
- **现代汉语**: 唯阴阳·形声 两轴留阳, 余 6 轴皆阴。极性 + 形 守, 其余尽显。
- **英语**: Two yang axes: yin-yang and form-sound. Polarity and visible form hold; six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 1,4 / d(⊤⁸)=6
- **Why**: 仅 阴阳 与 形声 守源, 其余 6 轴尽翻。形象 + 极性两个最"可见"的本体轴留, 而存在论 + 派生 + 全实用都已显化。

### `oxxxoooo` · 112

**Subtitle**: 3 阴侧 · 无 · 用 · 声

- **(X, X)**: (oxxx, oooo)
- **分解**: 阳 · 无 · 用 · 声 · 名 · 是 · 知 · 因
- **对偶**: `xoooxxxx` · 143
- **古文**: **音** — 《道德经》"大音希声"; 无 + 用 + 声 = 玄音 (《礼记·乐记》"凡音之起, 由人心生也")
- **现代汉语**: 有无+体用+形声 三翻 (无+用+声)。本体除阴阳外全翻, 即本体三轴沉。
- **英语**: Three yin axes: non-being, function, sound. Three of four ontological axes flip; only yin-yang holds.
- **形式逻辑**: |y|₁ = 3 / e₁₁₂ / yin 在 bit 2,3,4 (本体后三轴) / yang 在 bit 1,5,6,7,8
- **Why**: 本体类除最深的阴阳轴外, 其余三轴 (有无·体用·形声) 全部入阴。"无·用·声"三联 — 道家"无之用 + 形之声", 而实用 4 轴皆留阳。即"本体全开而实用未动"的奇异态: 形上动而形下静。

### `oxxxooox` · 113  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 无 · 用 · 声 · 果

- **(X, X)**: (oxxx, ooox)
- **分解**: 阳 · 无 · 用 · 声 · 名 · 是 · 知 · 果
- **对偶**: `xoooxxxo` · 142
- **古文**: **鸣** — 《庄子·齐物论》"夫大块噫气, 其名为风"; 无 + 用 + 声 + 果 = 鸣 (大音无声而有鸣); comp-palindrome
- **现代汉语**: 有无+体用+形声+因果 四翻, 唯阴阳·名实·是非·知行 留阳。comp-palindrome 之一。
- **英语**: Four yin axes: non-being, function, sound, effect. Anti-palindrome — each mirror pair holds opposite sides.
- **形式逻辑**: |y|₁ = 4 / comp-palindrome / yin 在 bit 2,3,4,8 / d=4
- **Why**: comp-palindrome 16 元之一。本体后三轴 (无·用·声) 全翻 + 实用末轴 (果)。配对 (1↔8) 阳·果反; (2↔7) 无·知反; (3↔6) 用·是反; (4↔5) 声·名反 — 四对皆 anti-mirror。哲学上: 本体显化而仅果回响, 中间实用三轴 (名·是·知) 反而守。

### `oxxxooxo` · 114

**Subtitle**: 4 阴侧 · 无 · 用 · 声 · 行

- **(X, X)**: (oxxx, ooxo)
- **分解**: 阳 · 无 · 用 · 声 · 名 · 是 · 行 · 因
- **对偶**: `xoooxxox` · 141
- **古文**: **奏** — 《说文》"奏, 进也"; 无 + 用 + 声 + 行 = 奏 (上奏; 《礼记》"奏之以乐")
- **现代汉语**: 有无+体用+形声+知行 四翻, 唯阴阳·名实·是非·因果 留阳。"无·用·声·行"本体全显加行。
- **英语**: Four yin axes: non-being, function, sound, acting. Three latter-ontological axes plus action — outcome and judgment hold.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,3,4,7 / d=4
- **Why**: 本体后三轴入阴 + 实用的知行。"无·用·声·行" — 道家本体全开化为行动。名实·是非·因果·阴阳 留阳。

### `oxxxooxx` · 115

**Subtitle**: 3 阳侧 · 阳 · 名 · 是

- **(X, X)**: (oxxx, ooxx)
- **分解**: 阳 · 无 · 用 · 声 · 名 · 是 · 行 · 果
- **对偶**: `xoooxxoo` · 140
- **古文**: **确** — 《说文》"确, 磬石也" (引申确实); 阳 + 名 + 是 三阳 = 确 (名实之确)
- **现代汉语**: 唯阴阳·名实·是非 三轴留阳。
- **英语**: Three yang axes: yin-yang, name-reality, right-wrong.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,5,6
- **Why**: 极性 + 名 + 是 守, 即"根仍极性, 言仍精确, 心仍肯定", 余 5 轴 (无·用·声·行·果) 皆显化。一种"心言守正而事尽变"的近极阴。

### `oxxxoxoo` · 116

**Subtitle**: 4 阴侧 · 无 · 用 · 声 · 非

- **(X, X)**: (oxxx, oxoo)
- **分解**: 阳 · 无 · 用 · 声 · 名 · 非 · 知 · 因
- **对偶**: `xoooxoxx` · 139
- **古文**: **辟** — 《孟子》"辟邪说"; 无 + 用 + 声 + 非 = 辟 (排辟; 邪辞之否定性发声)
- **现代汉语**: 有无+体用+形声+是非 四翻, 唯阴阳·名实·知行·因果 留阳。本体后三+ 实用否定判断。
- **英语**: Four yin axes: non-being, function, sound, wrong-judgment. Three latter-ontological axes plus negation.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,3,4,6 / d=4
- **Why**: 本体三轴 (无·用·声) + 实用的是非。"无·用·声·非" — 道家本体全开伴否定判断。

### `oxxxoxox` · 117

**Subtitle**: 3 阳侧 · 阳 · 名 · 知

- **(X, X)**: (oxxx, oxox)
- **分解**: 阳 · 无 · 用 · 声 · 名 · 非 · 知 · 果
- **对偶**: `xoooxoxo` · 138
- **古文**: **辨** — 《说文》"辨, 判也"; 阳 + 名 + 知 三阳 = 辨 (名辨; 荀子《非相》)
- **现代汉语**: 唯阴阳·名实·知行 三轴留阳。
- **英语**: Three yang axes: yin-yang, name-reality, know-act.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,5,7
- **Why**: 极性 + 名 + 知 守, 即"根仍极性, 言仍精, 心仍知", 其余 5 轴皆翻。

### `oxxxoxxo` · 118

**Subtitle**: 3 阳侧 · 阳 · 名 · 因

- **(X, X)**: (oxxx, oxxo)
- **分解**: 阳 · 无 · 用 · 声 · 名 · 非 · 行 · 因
- **对偶**: `xoooxoox` · 137
- **古文**: **号** — 《说文》"号, 呼也" (引申名号); 阳 + 名 + 因 三阳 = 号 (名号·称号)
- **现代汉语**: 唯阴阳·名实·因果 三轴留阳。
- **英语**: Three yang axes: yin-yang, name-reality, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,5,8
- **Why**: 极性 + 名 + 因 守, 其余 5 轴翻。"事在动而果未临, 言仍清, 根仍极性"。

### `oxxxoxxx` · 119  *[true X²]*

**Subtitle**: 2 阳侧 · 阳 · 名

- **(X, X)**: (oxxx, oxxx)  ← true X² (左右半相等)
- **分解**: 阳 · 无 · 用 · 声 · 名 · 非 · 行 · 果
- **对偶**: `xoooxooo` · 136
- **古文**: **称** — 《论语》"必也正名乎"; 阴阳 + 名实 双阳 = 称 (称谓: 极性与命名的同侧守); [X² 1↔5 阳守]
- **现代汉语**: 高低半皆 oxxx — bit 1 与 5 (阴阳·名实) 同步留阳, 其余 6 轴皆阴。X² 配对第 1 对单留。
- **英语**: Two yang axes: yin-yang and name-reality. The 1st X² pair (yin-yang ↔ name-reality) self-resonates on the yang side; six other axes are yin.
- **形式逻辑**: |y|₁ = 6 / true X² (high=low=oxxx) / 119 = 17×7 (X² 对角元) / d(⊤⁸)=6, d(⊥⁸)=2
- **Why**: 16 个 X² 对角元的第 8 个 (h=7)。bit 1 (阴阳) 与 bit 5 (名实) 同步留阳 — X² 配对 (**1↔5**, 2↔6, 3↔7, 4↔8) 第 1 对单独"守住"。哲学意涵: 阴阳 (最根本极性) 与名实 (语义命名) 是 X² 同源回声; 此码即唯这一对守在阳侧, 其余 6 轴皆沉。对偶 #136 反之 (两轴单阴, 余阳)。

### `oxxxxooo` · 120

**Subtitle**: 4 阴侧 · 无 · 用 · 声 · 实

- **(X, X)**: (oxxx, xooo)
- **分解**: 阳 · 无 · 用 · 声 · 实 · 是 · 知 · 因
- **对偶**: `xooooxxx` · 135
- **古文**: **传** — 《说文》"传, 遽也"; 无 + 用 + 声 + 实 = 传 (传授; 论语"传不习乎")
- **现代汉语**: 有无+体用+形声+名实 四翻, 唯阴阳·是非·知行·因果 留阳。"无·用·声·实"本体全开 + 实出名。
- **英语**: Four yin axes: non-being, function, sound, reality. Ontology fully manifest plus name-overflow.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 2,3,4,5 / d=4
- **Why**: bit 2,3,4,5 连续四轴 — 本体后三 + 实用首 — 入阴。即"本体类除阴阳外全翻 + 名实最末守不住"。一种"形上之根仍稳, 但本体三轴 + 语义首轴皆已显化"。

### `oxxxxoox` · 121

**Subtitle**: 3 阳侧 · 阳 · 是 · 知

- **(X, X)**: (oxxx, xoox)
- **分解**: 阳 · 无 · 用 · 声 · 实 · 是 · 知 · 果
- **对偶**: `xooooxxo` · 134
- **古文**: **诚** — 《大学》"诚意"; 《中庸》"诚者天之道也"; 阳 + 是 + 知 三阳 = 诚
- **现代汉语**: 唯阴阳·是非·知行 三轴留阳。
- **英语**: Three yang axes: yin-yang, right-wrong, know-act. Polarity + judgment + knowing hold.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,6,7
- **Why**: 阴阳·是非·知行 守 — 即"根仍极性, 心仍是仍知", 而其余 5 轴 (无·用·声·实·果) 皆显化。

### `oxxxxoxo` · 122

**Subtitle**: 3 阳侧 · 阳 · 是 · 因

- **(X, X)**: (oxxx, xoxo)
- **分解**: 阳 · 无 · 用 · 声 · 实 · 是 · 行 · 因
- **对偶**: `xooooxox` · 133
- **古文**: **据** — 《说文》"据, 杖持也"; 阳 + 是 + 因 三阳 = 据 (凭据; 论语"君子据于德")
- **现代汉语**: 唯阴阳·是非·因果 三轴留阳。
- **英语**: Three yang axes: yin-yang, right-wrong, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,6,8
- **Why**: 极性 + 是 + 因 守, 其余 5 轴翻。"心是, 因尚未到果, 而事尽变"。

### `oxxxxoxx` · 123

**Subtitle**: 2 阳侧 · 阳 · 是

- **(X, X)**: (oxxx, xoxx)
- **分解**: 阳 · 无 · 用 · 声 · 实 · 是 · 行 · 果
- **对偶**: `xooooxoo` · 132
- **古文**: **诺** — 《说文》"诺, 应也"; 阳 + 是 双阳 = 诺 (《老子》"信不足焉, 有不信焉"; 韩非"轻诺寡信")
- **现代汉语**: 唯阴阳·是非 两轴留阳, 余 6 轴阴。
- **英语**: Two yang axes: yin-yang and right-wrong. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 1,6 / d(⊤⁸)=6
- **Why**: 极性 + 是 守, 即"根极性 + 心始终肯定", 其余 6 轴 (本体三 + 实用三) 皆显化。"自我肯定地处在万事皆变中"。

### `oxxxxxoo` · 124

**Subtitle**: 3 阳侧 · 阳 · 知 · 因

- **(X, X)**: (oxxx, xxoo)
- **分解**: 阳 · 无 · 用 · 声 · 实 · 非 · 知 · 因
- **对偶**: `xoooooxx` · 131
- **古文**: **慧** — 佛家"般若智慧"; 阳 + 知 + 因 三阳 = 慧 (《中庸》"诚则明矣")
- **现代汉语**: 唯阴阳·知行·因果 三轴留阳。
- **英语**: Three yang axes: yin-yang, know-act, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 1,7,8
- **Why**: 极性 + 知 + 因 守, 余 5 轴翻。"心知, 因尚未到果, 而其余皆显化" — 近极阴而 X² 配对 (3↔7) 中 7 还守。

### `oxxxxxox` · 125

**Subtitle**: 2 阳侧 · 阳 · 知

- **(X, X)**: (oxxx, xxox)
- **分解**: 阳 · 无 · 用 · 声 · 实 · 非 · 知 · 果
- **对偶**: `xoooooxo` · 130
- **古文**: **明** — 《大学》"在明明德"; 阳 + 知 双阳 = 明 (《论语》"知者不惑"; 王阳明"明明德")
- **现代汉语**: 唯阴阳·知行 两轴留阳, 余 6 轴阴。"根仍极性, 心仍知行 (知)", 其余尽显。
- **英语**: Two yang axes: yin-yang and know-act (at "knowing"). Six axes manifest.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 1,7 / d(⊤⁸)=6
- **Why**: 极性 + 知 守, 余 6 轴皆翻。"知而无行, 知而万象皆显"。

### `oxxxxxxo` · 126  *[palindrome]*

**Subtitle**: 2 阳侧 · 阳 · 因

- **(X, X)**: (oxxx, xxxo)
- **分解**: 阳 · 无 · 用 · 声 · 实 · 非 · 行 · 因
- **对偶**: `xoooooox` · 129
- **古文**: **创** — 《说文》"创, 始也"; 阳 + 因 双阳 (palindrome 极对) = 创 (元始之极对); 《易》"乾元资始"; [palindrome 1↔8 阳守]
- **现代汉语**: 唯阴阳·因果 两轴留阳, 余 6 轴皆阴。palindrome — 极对 (1↔8) 同侧留阳, 其余三 palindrome 对皆同侧入阴。
- **英语**: Two yang axes: yin-yang and cause-effect. Palindrome — extremal pair holds on yang side; the other three palindrome pairs fall to yin.
- **形式逻辑**: |y|₁ = 6 / palindrome (bit i = bit 7-i) / yang 仅 bit 1,8 / d=6
- **Why**: 极性 + 因 守, 其余 6 轴翻。palindrome 配对 (1↔8): 阳·因 同阳 (这一对单守); (2↔7): 无·行 同阴; (3↔6): 用·非 同阴; (4↔5): 声·实 同阴。即最外的"极性-因果"对单独守住, 其余三对皆同陷阴侧。对偶 #129 反之, 极对同陷阴侧, 其余皆阳。

### `oxxxxxxx` · 127

**Subtitle**: 1 阳侧 · 阳

- **(X, X)**: (oxxx, xxxx)
- **分解**: 阳 · 无 · 用 · 声 · 实 · 非 · 行 · 果
- **对偶**: `xooooooo` · 128
- **古文**: **阳** — 《说文》"阳, 高明也"; 易经乾元之质; 《老子》"万物负阴而抱阳"
- **现代汉语**: 唯阴阳一轴留阳, 余 7 轴皆阴。最深的极性 (阳) 是阴海中唯一留住的灯。
- **英语**: Single yang remnant on yin-yang axis. Only the deepest polarity holds; everything else manifests.
- **形式逻辑**: |y|₁ = 7 / yang 仅 bit 1 / d(⊤⁸)=7, d(⊥⁸)=1 / 单点阳留存 8 元之一
- **Why**: Hamming weight = 7 中唯一一个保留 bit 1 (阴阳) 阳的码。这是 8 个"单点阳留存"中"最根本"的一个: 在万象皆显化的近极阴中, 仅 极性"阳" 还守住。对偶 #128 是 weight 1 单点阴扰动 (仅阴阳翻为阴)。两者构成 8 个"首位/末位 8 ↔ 阴极/阳极" 对偶之首。

### `xooooooo` · 128

**Subtitle**: 1 阴侧 · 阴

- **(X, X)**: (xooo, oooo)
- **分解**: 阴 · 有 · 体 · 形 · 名 · 是 · 知 · 因
- **对偶**: `oxxxxxxx` · 127
- **古文**: **阴** — 《说文》"阴, 闇也"; 易经坤元之始; 《老子》"万物负阴而抱阳"
- **现代汉语**: 阴阳一轴入阴。最根本极性的第一次下沉。
- **英语**: Single perturbation on yin-yang axis (→ yin). The deepest polarity makes its first descent.
- **形式逻辑**: F₂⁸ 单位向量 e₁₂₈ (MSB) / |y|₁ = 1 / yin ⊂ 本体类首位
- **Why**: 仅 bit 1 (阴阳轴) 翻。这是从纯阳出发的 8 个邻居中"最根本"的一个: 阴阳极性首次下沉, 其它 7 轴皆留阳。哲学上, 这是道家"道生一, 一生二"中的"二"的第一次显化 — 阴阳的双 face 出现, 而其它对偶尚未分化。对偶 #127 是仅 bit 1 留阳。

### `xoooooox` · 129  *[palindrome]*

**Subtitle**: 2 阴侧 · 阴 · 果

- **(X, X)**: (xooo, ooox)
- **分解**: 阴 · 有 · 体 · 形 · 名 · 是 · 知 · 果
- **对偶**: `oxxxxxxo` · 126
- **古文**: **报** — 《诗·大雅》"投我以桃, 报之以李"; 阴 + 果 = 阴报 (因果报应); [palindrome 1↔8]
- **现代汉语**: 阴阳+因果 双阴 (阴+果)。palindrome 第 1 配对 (最外极对) 同步入阴 — 极性下沉与后果显化同步。
- **英语**: Yin-yang and cause-effect both flip — the 1st palindrome pair (extremal) self-resonates. The deepest polarity descends and its furthest outcome surfaces.
- **形式逻辑**: |y|₁ = 2 / palindrome (bit 1 ↔ bit 8 同侧入阴) / yin ⊂ {bit 1, 8}
- **Why**: palindrome 配对的最外对 (1↔8) — 阴阳与因果 — 同侧入阴。这是 8-bit 字符串两个端点同步翻转。哲学意涵: "极性"(本体最深) 与"因果"(实用最末) 是最远的一对; 它们的同步意味着系统两端同时崩到承载侧, 而中间六轴仍守。对偶 #126 反之, 仅这一对守阳。

### `xoooooxo` · 130

**Subtitle**: 2 阴侧 · 阴 · 行

- **(X, X)**: (xooo, ooxo)
- **分解**: 阴 · 有 · 体 · 形 · 名 · 是 · 行 · 因
- **对偶**: `oxxxxxox` · 125
- **古文**: **潜** — 《说文》"潜, 涉水也"; 易经乾卦"潜龙勿用"; 阴 + 行 = 潜 (暗中之行)
- **现代汉语**: 阴阳+知行 双阴 (阴+行)。极性下沉伴具体行动。
- **英语**: Two-axis yin: yin-yang and acting. Polarity descends and bodily action commences.
- **形式逻辑**: |y|₁ = 2 / e₁₃₀ / yin 在 bit 1, 7
- **Why**: 阴阳翻阴, 知行翻行。"阴+行" — 阴的极性首次显化的同时, 实践开始; 但因果尾尚留因, 故果未成。X² 配对: bit 1 ↔ bit 5 (名实), 这里只 bit 1 翻; bit 3 ↔ bit 7 (知行), 只 bit 7 翻 — 两对都"半启动"。

### `xoooooxx` · 131

**Subtitle**: 3 阴侧 · 阴 · 行 · 果

- **(X, X)**: (xooo, ooxx)
- **分解**: 阴 · 有 · 体 · 形 · 名 · 是 · 行 · 果
- **对偶**: `oxxxxxoo` · 124
- **古文**: **酬** — 《诗·小雅》"以酬大宗"; 阴 + 行 + 果 = 酬报 (因果回应)
- **现代汉语**: 阴阳+知行+因果 三翻 (阴+行+果)。极性下沉, 行而结果。
- **英语**: Three yin axes: yin-yang, acting, effect. Polarity descends, action issues, outcome bears.
- **形式逻辑**: |y|₁ = 3 / e₁₃₁ / yin 在 bit 1, 7, 8
- **Why**: 阴阳·知行·因果 — 最深极性下沉, 末两轴 (行·果) 同步显化。即在"阴极性"上完成行动→后果的链。本体的 有无·体用·形声 与实用的 名实·是非 留阳。

### `xooooxoo` · 132

**Subtitle**: 2 阴侧 · 阴 · 非

- **(X, X)**: (xooo, oxoo)
- **分解**: 阴 · 有 · 体 · 形 · 名 · 非 · 知 · 因
- **对偶**: `oxxxxoxx` · 123
- **古文**: **邪** — 《说文》"邪, 邪琅郡也" (引申为不正); 阴 + 非 = 邪 (《尚书》"无偏无党, 王道荡荡")
- **现代汉语**: 阴阳+是非 双阴 (阴+非)。极性下沉伴否定判断。
- **英语**: Two-axis yin: yin-yang and wrong-judgment. The deepest polarity meets the first negation.
- **形式逻辑**: |y|₁ = 2 / e₁₃₂ / yin 在 bit 1, 6
- **Why**: 阴阳·是非 同步翻。"阴+非" — 最深极性下沉与判断否定同步。哲学意涵: 当本体下沉到阴, 心也判断出"非" — 这是悲观主义形上学的最简结构。

### `xooooxox` · 133

**Subtitle**: 3 阴侧 · 阴 · 非 · 果

- **(X, X)**: (xooo, oxox)
- **分解**: 阴 · 有 · 体 · 形 · 名 · 非 · 知 · 果
- **对偶**: `oxxxxoxo` · 122
- **古文**: **灾** — 《说文》"灾, 天火也"; 阴 + 非 + 果 = 灾 (《左传》"灾不假设其类")
- **现代汉语**: 阴阳+是非+因果 三翻 (阴+非+果)。阴+否定+后果, 即"悲观结果"。
- **英语**: Three yin axes: yin-yang, wrong-judgment, effect. Pessimistic conclusion: yin-rooted, negative, with outcome.
- **形式逻辑**: |y|₁ = 3 / e₁₃₃ / yin 在 bit 1, 6, 8
- **Why**: 阴阳·是非·因果 三轴入阴。"阴+非+果" — 极性下沉、判断否定、后果显现 三联。知行·名实 等留阳。一种"被动地观察到否定性结果"的状态: 心不动, 但形上、判断、因果维都已转阴。

### `xooooxxo` · 134

**Subtitle**: 3 阴侧 · 阴 · 非 · 行

- **(X, X)**: (xooo, oxxo)
- **分解**: 阴 · 有 · 体 · 形 · 名 · 非 · 行 · 因
- **对偶**: `oxxxxoox` · 121
- **古文**: **逆** — 《说文》"逆, 迎也" (引申反向); 阴 + 非 + 行 = 逆 (《孟子》"逆天者亡")
- **现代汉语**: 阴阳+是非+知行 三翻 (阴+非+行)。"阴+非+行" — 否定性行动的极性下沉版。
- **英语**: Three yin axes: yin-yang, wrong-judgment, acting. The "negative action from yin" — the deepest descent activates dissent and action.
- **形式逻辑**: |y|₁ = 3 / e₁₃₄ / yin 在 bit 1, 6, 7
- **Why**: 阴阳·是非·知行 三轴。"阴+非+行" — 极性沉, 心非, 身行。因果留因 (果未成), 名实·体用·形声·有无 留阳。

### `xooooxxx` · 135

**Subtitle**: 4 阴侧 · 阴 · 非 · 行 · 果

- **(X, X)**: (xooo, oxxx)
- **分解**: 阴 · 有 · 体 · 形 · 名 · 非 · 行 · 果
- **对偶**: `oxxxxooo` · 120
- **古文**: **凶** — 《周易》"吉凶悔吝"; 阴 + 非 + 行 + 果 = 凶 (易经卦辞之凶)
- **现代汉语**: 阴阳+是非+知行+因果 四翻, 唯有无·体用·形声·名实 留阳。"阴+非+行+果"完整否定链。
- **英语**: Four yin axes: yin-yang, wrong-judgment, acting, effect. Full negative cascade rooted in yin polarity.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 6, 7, 8 / d(⊤⁸)=d(⊥⁸)=4
- **Why**: 阴阳 + 实用末三轴 (非·行·果) — 极性下沉, 判断否定, 行动, 后果, 四联。有无·体用·形声·名实 留阳 — 即存在论、本体派生、表达、命名都未动, 仅极性 + 末段实用层全翻。

### `xoooxooo` · 136  *[true X²]*

**Subtitle**: 2 阴侧 · 阴 · 实

- **(X, X)**: (xooo, xooo)  ← true X² (左右半相等)
- **分解**: 阴 · 有 · 体 · 形 · 实 · 是 · 知 · 因
- **对偶**: `oxxxoxxx` · 119
- **古文**: **物** — 《说文》"物, 万物也"; 阴 + 实 = 物 (《周易》"乾道变化, 各正性命"; 朱熹"物者, 事也") [X² 1↔5]
- **现代汉语**: 阴阳 + 名实 双阴, 高低半皆 xooo。X² 第 1 配对 (极性 ↔ 命名) 在阴侧共振。
- **英语**: Yin-yang and name-reality both flip — the 1st X² pair (extremal/semantic) self-resonates on the yin side.
- **形式逻辑**: |y|₁ = 2 / true X² (high=low=xooo) / 136 = 17×8 (X² 对角元第 9 个) / yin 在 bit 1, 5
- **Why**: bit 1 (阴阳) 与 bit 5 (名实) 同步入阴 — X² 配对 (**1↔5**, 2↔6, 3↔7, 4↔8) 第 1 对单独共振。哲学意涵: 阴阳 (本体最深极性) 与 名实 (语义最深命名) 是 X² 同源回声; 此码即两者同时翻至阴侧 — 道之根与语之根同步沉。这是 119 (两者同守阳) 的对偶。

### `xoooxoox` · 137

**Subtitle**: 3 阴侧 · 阴 · 实 · 果

- **(X, X)**: (xooo, xoox)
- **分解**: 阴 · 有 · 体 · 形 · 实 · 是 · 知 · 果
- **对偶**: `oxxxoxxo` · 118
- **古文**: **证** — 《说文》"证, 告也"; 阴 + 实 + 果 = 证 (因果之证; 佛家"证果")
- **现代汉语**: 阴阳+名实+因果 三翻 (阴+实+果)。极性下沉 + 实出 + 后果, 一种 X² 共振的延伸。
- **英语**: Three yin axes: yin-yang, name-reality, effect. The 1st X² pair (yin+reality) extended with effect.
- **形式逻辑**: |y|₁ = 3 / e₁₃₇ / yin 在 bit 1, 5, 8
- **Why**: 136 (阴+实 X²) 加上"果"末梢。即极性已沉、语义已出、果已成 — 三个"显化链"的高阶完成态。是非·知行·体用·形声·有无 留阳。

### `xoooxoxo` · 138

**Subtitle**: 3 阴侧 · 阴 · 实 · 行

- **(X, X)**: (xooo, xoxo)
- **分解**: 阴 · 有 · 体 · 形 · 实 · 是 · 行 · 因
- **对偶**: `oxxxoxox` · 117
- **古文**: **慎** — 《大学》"君子必慎其独"; 阴 + 实 + 行 = 慎 (《尚书》"惟刑之恤")
- **现代汉语**: 阴阳+名实+知行 三翻 (阴+实+行)。极性下沉 + 实 + 行 — 但判断与果未到。
- **英语**: Three yin axes: yin-yang, name-reality, acting. Polarity, reality, action — without judgment or outcome.
- **形式逻辑**: |y|₁ = 3 / e₁₃₈ / yin 在 bit 1, 5, 7
- **Why**: bit 1, 5, 7 — 全奇位三轴。"阴+实+行" — 在阴的极性中, 实际地行动。是非·因果·有无·体用·形声 留阳。

### `xoooxoxx` · 139

**Subtitle**: 4 阴侧 · 阴 · 实 · 行 · 果

- **(X, X)**: (xooo, xoxx)
- **分解**: 阴 · 有 · 体 · 形 · 实 · 是 · 行 · 果
- **对偶**: `oxxxoxoo` · 116
- **古文**: **运** — 《周易》"日月运行"; 阴 + 实 + 行 + 果 = 运 (命运; 阴中实事运转)
- **现代汉语**: 阴阳+名实+知行+因果 四翻, 唯有无·体用·形声·是非 留阳。"阴+实+行+果"完整 X² 链 + 实用末。
- **英语**: Four yin axes: yin-yang, name-reality, acting, effect. The 1st X² pair extended with full action-outcome.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 5, 7, 8 / d=4
- **Why**: 阴阳 + 名实 (X² 第 1 对) + 知行 + 因果 (X² 第 3·4 对的 yin 侧)。是非留是 — 心始终肯定。即在阴的根上肯定地完成实践链。

### `xoooxxoo` · 140

**Subtitle**: 3 阴侧 · 阴 · 实 · 非

- **(X, X)**: (xooo, xxoo)
- **分解**: 阴 · 有 · 体 · 形 · 实 · 非 · 知 · 因
- **对偶**: `oxxxooxx` · 115
- **古文**: **失** — 《论语》"过则勿惮改"; 阴 + 实 + 非 = 失 (《孟子》"失其本心")
- **现代汉语**: 阴阳+名实+是非 三翻 (阴+实+非)。极性下沉 + 实出名 + 否定 — 形上语义批判。
- **英语**: Three yin axes: yin-yang, name-reality, wrong-judgment. Yin grounding + reality overflow + negative judgment — metaphysico-semantic critique.
- **形式逻辑**: |y|₁ = 3 / e₁₄₀ / yin 在 bit 1, 5, 6
- **Why**: 阴阳·名实·是非 三轴。"阴+实+非" — 极性沉, 语义松, 心否定。知行·因果·有无·体用·形声 留阳: 即"心知有非而身未动, 果未来"。

### `xoooxxox` · 141

**Subtitle**: 4 阴侧 · 阴 · 实 · 非 · 果

- **(X, X)**: (xooo, xxox)
- **分解**: 阴 · 有 · 体 · 形 · 实 · 非 · 知 · 果
- **对偶**: `oxxxooxo` · 114
- **古文**: **悔** — 《周易》"悔吝"; 阴 + 实 + 非 + 果 = 悔 (《论语》"过则勿惮改")
- **现代汉语**: 阴阳+名实+是非+因果 四翻, 唯有无·体用·形声·知行 留阳。"阴+实+非+果", 心未行身未动而事已成。
- **英语**: Four yin axes: yin-yang, name-reality, wrong-judgment, effect. Outcome arrives without bodily action — knowledge holds at "knowing".
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 5, 6, 8 / d=4
- **Why**: 极性 + 语义 + 否定 + 后果 — 4 轴入阴, 而知行留知。"阴根、实出、非判、果显" — 一种心知腹诽而果自来的态。

### `xoooxxxo` · 142  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 实 · 非 · 行

- **(X, X)**: (xooo, xxxo)
- **分解**: 阴 · 有 · 体 · 形 · 实 · 非 · 行 · 因
- **对偶**: `oxxxooox` · 113
- **古文**: **殁** — 《说文》"殁, 终也"; 阴 + 无 + 声 + 行 = 殁 (寂灭之行; 《左传》"殁齿不忘"); comp-palindrome
- **现代汉语**: 阴阳+名实+是非+知行 四翻, 唯有无·体用·形声·因果 留阳。comp-palindrome: 配对各取反侧。
- **英语**: Four yin axes: yin-yang, name-reality, wrong-judgment, acting. Anti-palindrome — each mirror pair takes opposite sides.
- **形式逻辑**: |y|₁ = 4 / comp-palindrome / yin 在 bit 1, 5, 6, 7 / d=4
- **Why**: comp-palindrome 16 元之一。配对 (1↔8): 阴·因 反, (2↔7): 有·行 反, (3↔6): 体·非 反, (4↔5): 形·实 反 — 四对皆 anti-mirror。哲学上: 阴极性 + 实用三个"批评维" (实·非·行) 全翻, 而其镜像端 (因·形·体·有) 全守阳。

### `xoooxxxx` · 143

**Subtitle**: 3 阳侧 · 有 · 体 · 形

- **(X, X)**: (xooo, xxxx)
- **分解**: 阴 · 有 · 体 · 形 · 实 · 非 · 行 · 果
- **对偶**: `oxxxoooo` · 112
- **古文**: **居** — 《论语》"君子居之"; 有 + 体 + 形 三阳 = 居 (存居; 《周易》"安土敦乎仁")
- **现代汉语**: 唯有无·体用·形声 三轴留阳, 阴阳+实用 4 轴全翻。即"本体后三守, 阴阳沉, 实用全显"。
- **英语**: Three yang axes: being-nonbeing, substance-function, form-sound. Yin-yang descends along with all four pragmatics.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,3,4 / d(⊤⁸)=5
- **Why**: 有无·体用·形声 (本体后三轴) 留阳, 阴阳 + 实用 4 轴全翻。哲学上: 极性已沉到阴, 但本体的"存在"、"派生"、"表达"维都还在; 而实用层完全显化。一种"形上骨架尚立, 但极性已沉, 实用全开"的态。

### `xooxoooo` · 144

**Subtitle**: 2 阴侧 · 阴 · 声

- **(X, X)**: (xoox, oooo)
- **分解**: 阴 · 有 · 体 · 声 · 名 · 是 · 知 · 因
- **对偶**: `oxxoxxxx` · 111
- **古文**: **谣** — 《尔雅》"徒歌曰谣"; 阴 + 声 = 谣 (暗中流传之声); 《诗·魏风》"心之忧矣, 我歌且谣"
- **现代汉语**: 阴阳+形声 双阴 (阴+声)。极性下沉伴发声 — 阴中之声。
- **英语**: Two-axis yin: yin-yang and sound. Voice from yin grounding — the descent that speaks.
- **形式逻辑**: |y|₁ = 2 / e₁₄₄ / yin 在 bit 1, 4 (本体首尾两端)
- **Why**: 阴阳·形声 同步翻 — 本体的首 (极性) 与本体的末 (表达) 同步入阴。"阴+声" — 一种从最深极性中传出的声音。bit 2 (有无) 与 bit 3 (体用) 留阳, 故存在论与本体派生未动 — 仅极性与表达维触发。

### `xooxooox` · 145

**Subtitle**: 3 阴侧 · 阴 · 声 · 果

- **(X, X)**: (xoox, ooox)
- **分解**: 阴 · 有 · 体 · 声 · 名 · 是 · 知 · 果
- **对偶**: `oxxoxxxo` · 110
- **古文**: **哀** — 《说文》"哀, 闵也"; 阴 + 声 + 果 = 哀 (《礼记·乐记》"哀以伤其外, 而中以伤其内")
- **现代汉语**: 阴阳+形声+因果 三翻 (阴+声+果)。阴+声+果 — 阴中之声引发后果。
- **英语**: Three yin axes: yin-yang, sound, effect. Voice from yin yields outcome.
- **形式逻辑**: |y|₁ = 3 / e₁₄₅ / yin 在 bit 1, 4, 8
- **Why**: 阴阳·形声·因果 三轴。"阴+声+果" — 极性沉, 发声, 后果显。是非·知行·名实·体用·有无 留阳。即"从深处发声而果自来"的纯派生模式。

### `xooxooxo` · 146

**Subtitle**: 3 阴侧 · 阴 · 声 · 行

- **(X, X)**: (xoox, ooxo)
- **分解**: 阴 · 有 · 体 · 声 · 名 · 是 · 行 · 因
- **对偶**: `oxxoxxox` · 109
- **古文**: **哭** — 《说文》"哭, 哀声也"; 阴 + 声 + 行 = 哭 (《礼记》"丧礼以哀")
- **现代汉语**: 阴阳+形声+知行 三翻 (阴+声+行)。阴中之声伴行动。
- **英语**: Three yin axes: yin-yang, sound, acting. Voice from yin coupled with action.
- **形式逻辑**: |y|₁ = 3 / e₁₄₆ / yin 在 bit 1, 4, 7
- **Why**: 阴阳·形声·知行 入阴。"阴+声+行" — 在阴的根上发声并行动。是非·因果 留阳: 不评判, 不计后果, 仅是"阴中言行"。

### `xooxooxx` · 147

**Subtitle**: 4 阴侧 · 阴 · 声 · 行 · 果

- **(X, X)**: (xoox, ooxx)
- **分解**: 阴 · 有 · 体 · 声 · 名 · 是 · 行 · 果
- **对偶**: `oxxoxxoo` · 108
- **古文**: **诵** — 《说文》"诵, 讽也"; 阴 + 声 + 行 + 果 = 诵 (诵读·诵咏; 《诗·小雅》)
- **现代汉语**: 阴阳+形声+知行+因果 四翻, 唯有无·体用·名实·是非 留阳。"阴+声+行+果"四联肯定实践。
- **英语**: Four yin axes: yin-yang, sound, acting, effect. Four-axis cascade under positive judgment — voice-action-result in yin.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 4, 7, 8 / d=4
- **Why**: 阴阳 + 形声 + 实用末两 — "阴+声+行+果"。是非留是 (心肯定), 有无·体用·名实 留阳。即"从阴中肯定地发声·行·得果"的链 — 心始终是, 而事尽显。

### `xooxoxoo` · 148

**Subtitle**: 3 阴侧 · 阴 · 声 · 非

- **(X, X)**: (xoox, oxoo)
- **分解**: 阴 · 有 · 体 · 声 · 名 · 非 · 知 · 因
- **对偶**: `oxxoxoxx` · 107
- **古文**: **怨** — 《论语·里仁》"放于利而行, 多怨"; 阴 + 声 + 非 = 怨 (《诗·小雅》"怨怒之声")
- **现代汉语**: 阴阳+形声+是非 三翻 (阴+声+非)。阴中之声 + 否定判断 — 悲观的发声。
- **英语**: Three yin axes: yin-yang, sound, wrong-judgment. Voice of pessimism — yin-rooted, vocalized, negative.
- **形式逻辑**: |y|₁ = 3 / e₁₄₈ / yin 在 bit 1, 4, 6
- **Why**: 阴阳·形声·是非 — bit 1,4,6 (跳过 2,3,5,7,8)。"阴+声+非" — 极性沉、发声、判否, 而行动与后果未起, 语义未变。一种"批判性发声但未实践"的态。

### `xooxoxox` · 149

**Subtitle**: 4 阴侧 · 阴 · 声 · 非 · 果

- **(X, X)**: (xoox, oxox)
- **分解**: 阴 · 有 · 体 · 声 · 名 · 非 · 知 · 果
- **对偶**: `oxxoxoxo` · 106
- **古文**: **悲** — 《说文》"悲, 痛也"; 阴 + 声 + 非 + 果 = 悲 (阴声否定有果)
- **现代汉语**: 阴阳+形声+是非+因果 四翻, 唯有无·体用·名实·知行 留阳。"阴+声+非+果", 心未行身未动而果至。
- **英语**: Four yin axes: yin-yang, sound, wrong-judgment, effect. Outcome arrives without acting — knowledge holds.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 4, 6, 8 / d=4
- **Why**: 4 轴 (阴·声·非·果) 入阴 — 跳过偶数 bit 2 与奇数 bit 3,5,7。"在阴的根上发声、否定、而果已来", 然心 (知行=知) 仍守。

### `xooxoxxo` · 150  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 声 · 非 · 行

- **(X, X)**: (xoox, oxxo)
- **分解**: 阴 · 有 · 体 · 声 · 名 · 非 · 行 · 因
- **对偶**: `oxxoxoox` · 105
- **古文**: **愤** — 《论语》"不愤不启"; 阴 + 声 + 非 + 行 = 愤 (《说文》"愤, 懑也"; 怨怒之行); comp-palindrome
- **现代汉语**: 阴阳+形声+是非+知行 四翻, 唯有无·体用·名实·因果 留阳。comp-palindrome。
- **英语**: Four yin axes: yin-yang, sound, wrong-judgment, acting. Anti-palindrome — each mirror pair opposite sides.
- **形式逻辑**: |y|₁ = 4 / comp-palindrome / yin 在 bit 1, 4, 6, 7 / d=4
- **Why**: comp-palindrome 16 元之一。配对 (1↔8): 阴·因 反, (2↔7): 有·行 反, (3↔6): 体·非 反, (4↔5): 声·名 反 — 四对皆 anti-mirror。"阴+声+非+行"完整批判性发声-行动, 而果未临、根本存在论与命名守源。

### `xooxoxxx` · 151

**Subtitle**: 3 阳侧 · 有 · 体 · 名

- **(X, X)**: (xoox, oxxx)
- **分解**: 阴 · 有 · 体 · 声 · 名 · 非 · 行 · 果
- **对偶**: `oxxoxooo` · 104
- **古文**: **类** — 《荀子·正名》"类不悖"; 有 + 体 + 名 三阳 = 类 (类别; 《周易》"方以类聚")
- **现代汉语**: 唯有无·体用·名实 三轴留阳, 余 5 轴 (阴·声·非·行·果) 皆显化。
- **英语**: Three yang axes: being-nonbeing, substance-function, name-reality. The remaining five flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,3,5 / d(⊤⁸)=5
- **Why**: 5 轴 (阴·声·非·行·果) 入阴, 仅有无·体用·名实 守。即"存在 + 本体派生 + 命名"守源, 而极性、表达、判断、行动、后果皆显化。一种"存在-命名-派生"骨架尚在的近极阴。

### `xooxxooo` · 152

**Subtitle**: 3 阴侧 · 阴 · 声 · 实

- **(X, X)**: (xoox, xooo)
- **分解**: 阴 · 有 · 体 · 声 · 实 · 是 · 知 · 因
- **对偶**: `oxxooxxx` · 103
- **古文**: **谶** — 《说文》"谶, 验也"; 阴 + 声 + 实 = 谶 (谶纬之学; 阴中之语预兆)
- **现代汉语**: 阴阳+形声+名实 三翻 (阴+声+实)。极性下沉 + 发声 + 实出 — 阴中之声化为实事。
- **英语**: Three yin axes: yin-yang, sound, reality. Yin-rooted voice manifests as reality.
- **形式逻辑**: |y|₁ = 3 / e₁₅₂ / yin 在 bit 1, 4, 5
- **Why**: 阴阳·形声·名实 — bit 1,4,5 连续 (跳 2,3,6,7,8)。"阴+声+实" — 从最深阴极性中发出的声音化作具体的实。一种"形上发声实现"的纯涌现态。

### `xooxxoox` · 153  *[true X² · palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 声 · 实 · 果

- **(X, X)**: (xoox, xoox)  ← true X² (左右半相等)
- **分解**: 阴 · 有 · 体 · 声 · 实 · 是 · 知 · 果
- **对偶**: `oxxooxxo` · 102
- **古文**: **圆** — 《周髀》"天圆"; palindrome 周回闭合 (σ₄ 不动点); 与 #102 方 形成"天圆地方"经典对; 周流响满 [K.4 双重身份]
- **现代汉语**: **圆** — palindrome 周回算子 (σ₄ 不动点)。高低半皆 xoox 同时镜像不变; 与 #102 方 形成"天圆地方"经典对; 周流响满, 闭合无端。
- **英语**: Outer-symmetric self-square. Palindrome ∩ true X² — one of the four maximally symmetric codes (0, 102, 153, 255).
- **形式逻辑**: |y|₁ = 4 / true X² (high=low=xoox) / palindrome / 153 = 17×9 (X² 对角元) / d=4
- **Why**: palindrome ∩ true X² 4 元 {0, 102, 153, 255} 之一, 与 102 互为对偶。结构: bit 1, 4, 5, 8 入阴 — X² 配对 (1↔5) 与 (4↔8) 双对共振, 同时 palindrome 配对 (1↔8) 与 (4↔5) 同侧。即"阴极性+形声+名实+因果"四端对应。是 102 (内对) 的镜像 — 外对版本: 端缘 (阴·因) 与 中心 (声·实) 双双沉。

### `xooxxoxo` · 154

**Subtitle**: 4 阴侧 · 阴 · 声 · 实 · 行

- **(X, X)**: (xoox, xoxo)
- **分解**: 阴 · 有 · 体 · 声 · 实 · 是 · 行 · 因
- **对偶**: `oxxooxox` · 101
- **古文**: **讳** — 《说文》"讳, 誋也"; 阴 + 声 + 实 + 行 = 讳 (避讳·隐讳; 《礼记》"入境而问禁")
- **现代汉语**: 阴阳+形声+名实+知行 四翻, 唯有无·体用·是非·因果 留阳。"阴+声+实+行"四联实事化。
- **英语**: Four yin axes: yin-yang, sound, reality, acting. Yin-rooted voice-reality-action triplet; judgment and cause hold.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 4, 5, 7 / d=4
- **Why**: 4 个"显化/实践"维轴入阴。"阴+声+实+行" — 极性沉, 发声, 实出, 行动。是非留是, 因果留因 — 心仍肯定, 后果尚未来。

### `xooxxoxx` · 155

**Subtitle**: 3 阳侧 · 有 · 体 · 是

- **(X, X)**: (xoox, xoxx)
- **分解**: 阴 · 有 · 体 · 声 · 实 · 是 · 行 · 果
- **对偶**: `oxxooxoo` · 100
- **古文**: **常** — 《中庸》"庸德之行"; 有 + 体 + 是 三阳 = 常 (常道; 《老子》"复命曰常")
- **现代汉语**: 唯有无·体用·是非 三轴留阳, 余 5 轴 (阴·声·实·行·果) 皆显化。
- **英语**: Three yang axes: being-nonbeing, substance-function, right-wrong. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,3,6 / d(⊤⁸)=5
- **Why**: 存在·派生·肯定判断 守, 其余 5 轴翻。即"本体的存在-派生骨架与心的肯定守住, 而极性已沉, 表达-语义-行动-后果全显"。

### `xooxxxoo` · 156

**Subtitle**: 4 阴侧 · 阴 · 声 · 实 · 非

- **(X, X)**: (xoox, xxoo)
- **分解**: 阴 · 有 · 体 · 声 · 实 · 非 · 知 · 因
- **对偶**: `oxxoooxx` · 99
- **古文**: **诽** — 《说文》"诽, 谤也"; 阴 + 声 + 实 + 非 = 诽 (《礼记》"诽政")
- **现代汉语**: 阴阳+形声+名实+是非 四翻, 唯有无·体用·知行·因果 留阳。"阴+声+实+非"四联意识批判。
- **英语**: Four yin axes: yin-yang, sound, reality, wrong-judgment. Conscious critique fully realized — body and outcome unmoved.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 4, 5, 6 / d=4
- **Why**: 阴阳 + 本体末 (形声) + 实用前两 (名实·是非)。即"阴根+形上发声+实出+判否" — 一种心 (知行=知) 未动而四轴皆已沉的纯意识批判。

### `xooxxxox` · 157

**Subtitle**: 3 阳侧 · 有 · 体 · 知

- **(X, X)**: (xoox, xxox)
- **分解**: 阴 · 有 · 体 · 声 · 实 · 非 · 知 · 果
- **对偶**: `oxxoooxo` · 98
- **古文**: **晓** — 《说文》"晓, 明也"; 有 + 体 + 知 三阳 = 晓 (通晓·了悟)
- **现代汉语**: 唯有无·体用·知行 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, substance-function, know-act. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,3,7 / d(⊤⁸)=5
- **Why**: 存在·本体派生·知 守, 其余 5 轴 (阴·声·实·非·果) 皆翻。心知, 而形上极性已沉, 实用层全显。

### `xooxxxxo` · 158

**Subtitle**: 3 阳侧 · 有 · 体 · 因

- **(X, X)**: (xoox, xxxo)
- **分解**: 阴 · 有 · 体 · 声 · 实 · 非 · 行 · 因
- **对偶**: `oxxoooox` · 97
- **古文**: **根** — 《说文》"根, 木株也"; 有 + 体 + 因 三阳 = 根 (根本; 《道德经》"归根曰静")
- **现代汉语**: 唯有无·体用·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, substance-function, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,3,8 / d(⊤⁸)=5
- **Why**: 存在·派生·因 守, 余 5 轴翻。"因 留住未到果, 而事尽显, 极性已沉"。

### `xooxxxxx` · 159

**Subtitle**: 2 阳侧 · 有 · 体

- **(X, X)**: (xoox, xxxx)
- **分解**: 阴 · 有 · 体 · 声 · 实 · 非 · 行 · 果
- **对偶**: `oxxooooo` · 96
- **古文**: **存** — 《论语·先进》"存而不论"; 有 + 体 双阳 = 存 (《周易》"存乎其人"; 存而养之)
- **现代汉语**: 唯有无·体用 两轴留阳, 余 6 轴皆阴。本体最核心两轴 (存在·派生) 守源, 其余尽显。
- **英语**: Two yang axes: being-nonbeing and substance-function. The core ontological pair (existence and derivation) holds; six axes manifest.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 2,3 / d(⊤⁸)=6
- **Why**: 有无 + 体用 守 — 两个本体最核心的轴。极性 (阳) 已沉, 形声 (表达) 已沉, 实用 4 轴全沉。即"本体存在与派生骨架仍立, 而极性 + 表达 + 全实用皆已显化"的近极阴。

### `xoxooooo` · 160

**Subtitle**: 2 阴侧 · 阴 · 用

- **(X, X)**: (xoxo, oooo)
- **分解**: 阴 · 有 · 用 · 形 · 名 · 是 · 知 · 因
- **对偶**: `oxoxxxxx` · 95
- **古文**: **柔** — 《道德经》"柔弱胜刚强"; 阴 + 用 = 柔 (《易·系辞》"刚柔相摩, 八卦相荡")
- **现代汉语**: 阴阳+体用 双阴 (阴+用)。极性下沉伴本体派生 — 阴中之用。
- **英语**: Two-axis yin: yin-yang and function. Polarity descends and function emerges — "use rooted in yin".
- **形式逻辑**: |y|₁ = 2 / e₁₆₀ / yin 在 bit 1, 3 (本体首与本体派生)
- **Why**: 阴阳·体用 同步翻 — 极性沉而本体派生启动。"阴+用" — 与 #32 (单独用) 的差别是: 这里极性已沉, 所以"用"是从阴的根上派生的。

### `xoxoooox` · 161

**Subtitle**: 3 阴侧 · 阴 · 用 · 果

- **(X, X)**: (xoxo, ooox)
- **分解**: 阴 · 有 · 用 · 形 · 名 · 是 · 知 · 果
- **对偶**: `oxoxxxxo` · 94
- **古文**: **致** — 《大学》"致知在格物"; 阴 + 用 + 果 = 致 (柔之用致其果)
- **现代汉语**: 阴阳+体用+因果 三翻 (阴+用+果)。阴根之用得果。
- **英语**: Three yin axes: yin-yang, function, effect. Yin-rooted function bears outcome.
- **形式逻辑**: |y|₁ = 3 / e₁₆₁ / yin 在 bit 1, 3, 8
- **Why**: 阴阳·体用·因果 — 阴极性下沉, 派生功用, 结成果。形声·名实·是非·知行·有无 留阳。即"以阴为体的用产生因果"。

### `xoxoooxo` · 162

**Subtitle**: 3 阴侧 · 阴 · 用 · 行

- **(X, X)**: (xoxo, ooxo)
- **分解**: 阴 · 有 · 用 · 形 · 名 · 是 · 行 · 因
- **对偶**: `oxoxxxox` · 93
- **古文**: **顺** — 《说文》"顺, 理也"; 阴 + 用 + 行 = 顺 (《周易》"坤为顺"; 孟子"顺天者存")
- **现代汉语**: 阴阳+体用+知行 三翻 (阴+用+行)。阴根之用化为行。
- **英语**: Three yin axes: yin-yang, function, acting. Yin-rooted function becomes action.
- **形式逻辑**: |y|₁ = 3 / e₁₆₂ / yin 在 bit 1, 3, 7
- **Why**: 阴阳·体用·知行 — 三个 X² 配对中 (1↔5)、(3↔7) 的本体一侧。"阴+用+行" — 极性沉、派生用、化为行。是非·因果留阳: 不评判, 不结果。

### `xoxoooxx` · 163

**Subtitle**: 4 阴侧 · 阴 · 用 · 行 · 果

- **(X, X)**: (xoxo, ooxx)
- **分解**: 阴 · 有 · 用 · 形 · 名 · 是 · 行 · 果
- **对偶**: `oxoxxxoo` · 92
- **古文**: **守** — 《道德经》"守雌"; 阴 + 用 + 行 + 果 = 守 (柔守; 法家"守法")
- **现代汉语**: 阴阳+体用+知行+因果 四翻, 唯有无·形声·名实·是非 留阳。"阴+用+行+果"完整链。
- **英语**: Four yin axes: yin-yang, function, acting, effect. Yin-rooted full action-outcome cascade.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 3, 7, 8 / d=4
- **Why**: 极性 + 体用 + 实用末两 — "阴+用+行+果"。是非留是, 有无留有, 形声留形, 名实留名 — 心肯定且语言、存在论、表达三守, 而极性 + 派生 + 行动 + 后果全开。

### `xoxooxoo` · 164

**Subtitle**: 3 阴侧 · 阴 · 用 · 非

- **(X, X)**: (xoxo, oxoo)
- **分解**: 阴 · 有 · 用 · 形 · 名 · 非 · 知 · 因
- **对偶**: `oxoxxoxx` · 91
- **古文**: **弱** — 《道德经》"弱者道之用"; 阴 + 用 + 非 = 弱 (柔用之非力)
- **现代汉语**: 阴阳+体用+是非 三翻 (阴+用+非)。阴根之用伴否定。
- **英语**: Three yin axes: yin-yang, function, wrong-judgment. Yin-rooted function under negative judgment.
- **形式逻辑**: |y|₁ = 3 / e₁₆₄ / yin 在 bit 1, 3, 6
- **Why**: 阴阳·体用·是非 — bit 1,3,6 (跳 2,4,5,7,8)。"阴+用+非" — 极性沉, 用现, 心否。一种"形上批判的派生" — 用是发生的, 但被判定为非。

### `xoxooxox` · 165  *[palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 用 · 非 · 果

- **(X, X)**: (xoxo, oxox)
- **分解**: 阴 · 有 · 用 · 形 · 名 · 非 · 知 · 果
- **对偶**: `oxoxxoxo` · 90
- **古文**: **衰** — 《说文》"衰, 草雨衣"; 阴 + 用 + 非 + 果 = 衰 (柔之非用得果; 《论语》"凤鸟不至, 河不出图, 吾已矣夫"); palindrome
- **现代汉语**: 阴阳+体用+是非+因果 四翻, 唯有无·形声·名实·知行 留阳。palindrome — 镜像不变。
- **英语**: Four yin axes: yin-yang, function, wrong-judgment, effect. Palindrome — each mirror pair holds a consistent side.
- **形式逻辑**: |y|₁ = 4 / palindrome / yin 在 bit 1, 3, 6, 8 / d=4
- **Why**: palindrome 16 元之一。配对: (1↔8) 阴·果 同阴, (2↔7) 有·知 同阳, (3↔6) 用·非 同阴, (4↔5) 形·名 同阳。即四对中两对阴两对阳, 交错对称。

### `xoxooxxo` · 166

**Subtitle**: 4 阴侧 · 阴 · 用 · 非 · 行

- **(X, X)**: (xoxo, oxxo)
- **分解**: 阴 · 有 · 用 · 形 · 名 · 非 · 行 · 因
- **对偶**: `oxoxxoox` · 89
- **古文**: **抗** — 《说文》"抗, 扦也"; 阴 + 用 + 非 + 行 = 抗 (抗拒; 《孟子》"威武不能屈")
- **现代汉语**: 阴阳+体用+是非+知行 四翻, 唯有无·形声·名实·因果 留阳。"阴+用+非+行"完整批判行动。
- **英语**: Four yin axes: yin-yang, function, wrong-judgment, acting. Full critical action grounded in yin; outcome pending.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 3, 6, 7 / d=4
- **Why**: 极性 + 派生 + 否定 + 行动 — 4 轴入阴, 而因果留因。即"阴根的批判性派生与行动" 完整发动, 但后果尚未临。

### `xoxooxxx` · 167

**Subtitle**: 3 阳侧 · 有 · 形 · 名

- **(X, X)**: (xoxo, oxxx)
- **分解**: 阴 · 有 · 用 · 形 · 名 · 非 · 行 · 果
- **对偶**: `oxoxxooo` · 88
- **古文**: **像** — 《说文》"像, 似也"; 有 + 形 + 名 三阳 = 像 (形像; 《周易》"圣人立象以尽意")
- **现代汉语**: 唯有无·形声·名实 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, form-sound, name-reality. Existence + expression + naming hold; five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,4,5 / d(⊤⁸)=5
- **Why**: 有 · 形 · 名 守 — 存在 + 视觉表达 + 命名, 即"语言-视觉-存在"骨架。其余 5 轴 (阴·用·非·行·果) 皆显化。

### `xoxoxooo` · 168

**Subtitle**: 3 阴侧 · 阴 · 用 · 实

- **(X, X)**: (xoxo, xooo)
- **分解**: 阴 · 有 · 用 · 形 · 实 · 是 · 知 · 因
- **对偶**: `oxoxoxxx` · 87
- **古文**: **雌** — 《道德经》"知其雄, 守其雌, 为天下溪"; 阴 + 用 + 实 = 雌 (柔牝之实)
- **现代汉语**: 阴阳+体用+名实 三翻 (阴+用+实)。阴根之用化为实。
- **英语**: Three yin axes: yin-yang, function, reality. Yin-rooted function manifests as reality.
- **形式逻辑**: |y|₁ = 3 / e₁₆₈ / yin 在 bit 1, 3, 5
- **Why**: 阴阳·体用·名实 — bit 1,3,5 全奇位 (三个奇 bit)。"阴+用+实" — X² 配对 (1↔5) 双侧 (阴·实) + (3↔7) 单侧 (用), 即一对 X² 共振 + 一对半启动。"极性·派生·语义"三个 X² 链的同侧全开。

### `xoxoxoox` · 169

**Subtitle**: 4 阴侧 · 阴 · 用 · 实 · 果

- **(X, X)**: (xoxo, xoox)
- **分解**: 阴 · 有 · 用 · 形 · 实 · 是 · 知 · 果
- **对偶**: `oxoxoxxo` · 86
- **古文**: **遂** — 《说文》"遂, 亡也" (引申顺成); 阴 + 用 + 实 + 果 = 遂 (《周易》"遂初"; 顺遂)
- **现代汉语**: 阴阳+体用+名实+因果 四翻, 唯有无·形声·是非·知行 留阳。"阴+用+实+果"派生四联。
- **英语**: Four yin axes: yin-yang, function, reality, effect. Yin-rooted derivation completes in outcome.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 3, 5, 8 / d=4
- **Why**: 4 个轴 (阴·用·实·果) 入阴 — 都属"显化链" (极性·派生·语义·后果)。一种"在阴的根上派生-语义-果"的完整暗中演化, 而判断与行动维都未动。

### `xoxoxoxo` · 170  *[true X² · comp-palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 用 · 实 · 行

- **(X, X)**: (xoxo, xoxo)  ← true X² (左右半相等)
- **分解**: 阴 · 有 · 用 · 形 · 实 · 是 · 行 · 因
- **对偶**: `oxoxoxox` · 85
- **古文**: **综** — 《周易·系辞》"参伍以变, 错综其数"; Walsh W₁ 反 scramble (anti-rev σ₅); 与 #85 错 形成经典"错综"对 [K.4 双重身份]
- **现代汉语**: **综** — Walsh W₁ anti-scramble 算子。奇位阴 / 偶位阳 (与 #85 错 互反相); 与 错 形成"错综"经典成语对 — 系辞"错综其数"。
- **英语**: Walsh W₁ checkerboard — yin on odd, yang on even positions. Dual of #85.
- **形式逻辑**: |y|₁ = 4 / true X² (high=low=xoxo) / comp-palindrome / Walsh W₁ ⊕ 1 / d=4
- **Why**: 奇位 (bit 1,3,5,7 即 阴阳·体用·名实·知行) 入阴, 偶位 (bit 2,4,6,8 即 有无·形声·是非·因果) 留阳。85 的对偶, F₂⁸ 上最低频偶函数的反相。哲学上: 极性、派生、命名、知 这四个"派生关系"轴 (它们在 X² 配对中两两同侧, 即 (1↔5)(3↔7)) 全部入阴, 而其它四轴守。

### `xoxoxoxx` · 171

**Subtitle**: 3 阳侧 · 有 · 形 · 是

- **(X, X)**: (xoxo, xoxx)
- **分解**: 阴 · 有 · 用 · 形 · 实 · 是 · 行 · 果
- **对偶**: `oxoxoxoo` · 84
- **古文**: **审** — 《说文》"审, 悉也"; 有 + 形 + 是 三阳 = 审 (《大学》"安而后能虑")
- **现代汉语**: 唯有无·形声·是非 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, form-sound, right-wrong. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,4,6 (全偶位)
- **Why**: 偶位中三轴 (有·形·是) 守, 偶位末 (因) 已翻。即"存在 + 形 + 是"守住, 其余 5 轴 (阴·用·实·行·果) 翻。

### `xoxoxxoo` · 172

**Subtitle**: 4 阴侧 · 阴 · 用 · 实 · 非

- **(X, X)**: (xoxo, xxoo)
- **分解**: 阴 · 有 · 用 · 形 · 实 · 非 · 知 · 因
- **对偶**: `oxoxooxx` · 83
- **古文**: **抑** — 《说文》"抑, 按也"; 阴 + 用 + 实 + 非 = 抑 (压抑; 《诗·小雅》"抑抑威仪")
- **现代汉语**: 阴阳+体用+名实+是非 四翻, 唯有无·形声·知行·因果 留阳。"阴+用+实+非"形上批判。
- **英语**: Four yin axes: yin-yang, function, reality, wrong-judgment. Metaphysical critique grounded in yin.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 3, 5, 6 / d=4
- **Why**: 极性 + 派生 + 实 + 非 — 4 轴入阴。即"阴根·用·实·非", 而身未动 (知行=知)、果未来 (因果=因)、有 + 形 留阳。

### `xoxoxxox` · 173

**Subtitle**: 3 阳侧 · 有 · 形 · 知

- **(X, X)**: (xoxo, xxox)
- **分解**: 阴 · 有 · 用 · 形 · 实 · 非 · 知 · 果
- **对偶**: `oxoxooxo` · 82
- **古文**: **省** — 《论语》"吾日三省吾身"; 有 + 形 + 知 三阳 = 省 (省察)
- **现代汉语**: 唯有无·形声·知行 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, form-sound, know-act.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,4,7
- **Why**: 有·形·知 守, 其余 5 轴翻。即"存在 + 视觉表达 + 知"守源 — 心知, 形可见, 存在仍肯定; 而极性、派生、语义、判断、后果皆翻。

### `xoxoxxxo` · 174

**Subtitle**: 3 阳侧 · 有 · 形 · 因

- **(X, X)**: (xoxo, xxxo)
- **分解**: 阴 · 有 · 用 · 形 · 实 · 非 · 行 · 因
- **对偶**: `oxoxooox` · 81
- **古文**: **现** — 《说文》"现, 出貌"; 有 + 形 + 因 三阳 = 现 (出现·显现)
- **现代汉语**: 唯有无·形声·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, form-sound, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,4,8
- **Why**: 有·形·因 守, 其余 5 轴翻。形 + 存在 + 因 守住, 而极性已沉、派生已起、行动已发、果未临。

### `xoxoxxxx` · 175

**Subtitle**: 2 阳侧 · 有 · 形

- **(X, X)**: (xoxo, xxxx)
- **分解**: 阴 · 有 · 用 · 形 · 实 · 非 · 行 · 果
- **对偶**: `oxoxoooo` · 80
- **古文**: **在** — 《周易》"在天成象, 在地成形"; 有 + 形 双阳 = 在 (存在与形象同守)
- **现代汉语**: 唯有无·形声 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: being-nonbeing and form-sound. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 2,4 / d(⊤⁸)=6
- **Why**: 仅 有 + 形 守。即"存在与视觉表达"两个最具象的本体轴守住, 而极性、派生、全部实用层皆翻。

### `xoxxoooo` · 176

**Subtitle**: 3 阴侧 · 阴 · 用 · 声

- **(X, X)**: (xoxx, oooo)
- **分解**: 阴 · 有 · 用 · 声 · 名 · 是 · 知 · 因
- **对偶**: `oxooxxxx` · 79
- **古文**: **叹** — 《说文》"叹, 吞叹也"; 阴 + 用 + 声 = 叹 (柔用而出声 = 叹息; 《诗经》"维彼哲人, 告之话言")
- **现代汉语**: 阴阳+体用+形声 三翻 (阴+用+声)。本体除"有"外全翻 — 仅存在论守。
- **英语**: Three yin axes: yin-yang, function, sound. Only being-nonbeing holds yang in the ontological half.
- **形式逻辑**: |y|₁ = 3 / e₁₇₆ / yin 在 bit 1, 3, 4 (本体除 bit 2 外全)
- **Why**: 阴阳·体用·形声 — 本体类除有无外三轴入阴。"阴+用+声" — 极性沉, 派生用, 出声。实用 4 轴全留阳, 故仅本体震荡而实用未动。这是 #112 (阴阳留阳, 本体后三翻) 的对偶式扰动: 这里反过来, 阴阳翻而有无留。

### `xoxxooox` · 177

**Subtitle**: 4 阴侧 · 阴 · 用 · 声 · 果

- **(X, X)**: (xoxx, ooox)
- **分解**: 阴 · 有 · 用 · 声 · 名 · 是 · 知 · 果
- **对偶**: `oxooxxxo` · 78
- **古文**: **泣** — 《说文》"泣, 无声出涕也"; 阴 + 用 + 声 + 果 = 泣 (《诗·小雅》"出涕沱若")
- **现代汉语**: 阴阳+体用+形声+因果 四翻, 唯有无·名实·是非·知行 留阳。"阴+用+声+果"四联。
- **英语**: Four yin axes: yin-yang, function, sound, effect. Three latter ontological axes flip plus effect — outcome from yin-derivation-voicing.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 3, 4, 8 / d=4
- **Why**: 本体除有无外 + 实用末。"阴+用+声+果" — 极性·派生·表达 + 后果。心 (知行=知) 与语言 (名实=名) 与判断 (是非=是) 守, 即"形上动而心言守"。

### `xoxxooxo` · 178  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 用 · 声 · 行

- **(X, X)**: (xoxx, ooxo)
- **分解**: 阴 · 有 · 用 · 声 · 名 · 是 · 行 · 因
- **对偶**: `oxooxxox` · 77
- **古文**: **从** — 《论语》"七十而从心所欲不逾矩"; 阴 + 用 + 声 + 行 = 从 (柔顺之行; 《周易》"坤为顺"); comp-palindrome
- **现代汉语**: 阴阳+体用+形声+知行 四翻, 唯有无·名实·是非·因果 留阳。comp-palindrome。
- **英语**: Four yin axes: yin-yang, function, sound, acting. Anti-palindrome.
- **形式逻辑**: |y|₁ = 4 / comp-palindrome / yin 在 bit 1, 3, 4, 7 / d=4
- **Why**: comp-palindrome 之一。配对 (1↔8): 阴·因 反, (2↔7): 有·行 反, (3↔6): 用·是 反, (4↔5): 声·名 反 — 四对皆 anti-mirror。即"本体三 (阴·用·声) + 实用一 (行)"组成 anti-palindrome。

### `xoxxooxx` · 179

**Subtitle**: 3 阳侧 · 有 · 名 · 是

- **(X, X)**: (xoxx, ooxx)
- **分解**: 阴 · 有 · 用 · 声 · 名 · 是 · 行 · 果
- **对偶**: `oxooxxoo` · 76
- **古文**: **谛** — 佛家"四谛"; 有 + 名 + 是 三阳 = 谛 (真谛·审实)
- **现代汉语**: 唯有无·名实·是非 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, name-reality, right-wrong. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,5,6
- **Why**: 存在 + 名 + 是 守 — 即"存在论 + 语义 + 肯定判断"骨架。其余 5 轴 (阴·用·声·行·果) 翻。

### `xoxxoxoo` · 180

**Subtitle**: 4 阴侧 · 阴 · 用 · 声 · 非

- **(X, X)**: (xoxx, oxoo)
- **分解**: 阴 · 有 · 用 · 声 · 名 · 非 · 知 · 因
- **对偶**: `oxooxoxx` · 75
- **古文**: **谗** — 《说文》"谗, 谮也"; 阴 + 用 + 声 + 非 = 谗 (谗言; 《诗·小雅》"听言则对")
- **现代汉语**: 阴阳+体用+形声+是非 四翻, 唯有无·名实·知行·因果 留阳。"阴+用+声+非"形上批判。
- **英语**: Four yin axes: yin-yang, function, sound, wrong-judgment. Metaphysical-critical voicing from yin.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 3, 4, 6 / d=4
- **Why**: 本体后三 + 实用否定。即"阴+用+声+非"完整形上批判性发声, 而身未动果未来。

### `xoxxoxox` · 181

**Subtitle**: 3 阳侧 · 有 · 名 · 知

- **(X, X)**: (xoxx, oxox)
- **分解**: 阴 · 有 · 用 · 声 · 名 · 非 · 知 · 果
- **对偶**: `oxooxoxo` · 74
- **古文**: **认** — 《广韵》"认, 识也"; 有 + 名 + 知 三阳 = 认 (认识·识别)
- **现代汉语**: 唯有无·名实·知行 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, name-reality, know-act. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,5,7
- **Why**: 存在 + 名 + 知 守, 其余 5 轴翻。"心知言明存在守", 而极性 + 派生 + 表达 + 判断 + 后果皆翻。

### `xoxxoxxo` · 182

**Subtitle**: 3 阳侧 · 有 · 名 · 因

- **(X, X)**: (xoxx, oxxo)
- **分解**: 阴 · 有 · 用 · 声 · 名 · 非 · 行 · 因
- **对偶**: `oxooxoox` · 73
- **古文**: **缘** — 佛家"因缘"; 《说文》"缘, 衣纯也" (引申原因); 有 + 名 + 因 三阳 = 缘
- **现代汉语**: 唯有无·名实·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, name-reality, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,5,8
- **Why**: 存在 + 名 + 因 守, 其余 5 轴翻。"因尚未到果, 名仍清, 存在仍肯定", 而极性、派生、表达、判断、行动皆翻。

### `xoxxoxxx` · 183

**Subtitle**: 2 阳侧 · 有 · 名

- **(X, X)**: (xoxx, oxxx)
- **分解**: 阴 · 有 · 用 · 声 · 名 · 非 · 行 · 果
- **对偶**: `oxooxooo` · 72
- **古文**: **谓** — 《说文》"谓, 报也"; 有 + 名 双阳 = 谓 (《周易》"是故易者, 象也"; 称谓之名)
- **现代汉语**: 唯有无·名实 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: being-nonbeing and name-reality. The "existence+naming" pair holds; six axes manifest.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 2,5 / d(⊤⁸)=6
- **Why**: 有 + 名 守 — 存在论与命名两个"基础给定"维守住, 而极性、派生、表达、判断、行动、后果皆已显化。

### `xoxxxooo` · 184

**Subtitle**: 4 阴侧 · 阴 · 用 · 声 · 实

- **(X, X)**: (xoxx, xooo)
- **分解**: 阴 · 有 · 用 · 声 · 实 · 是 · 知 · 因
- **对偶**: `oxoooxxx` · 71
- **古文**: **私** — 《说文》"私, 禾也" (引申私密); 阴 + 用 + 声 + 实 = 私 (《韩非子》"公私之分"; 私语)
- **现代汉语**: 阴阳+体用+形声+名实 四翻, 唯有无·是非·知行·因果 留阳。"阴+用+声+实"本体三 + 实出名。
- **英语**: Four yin axes: yin-yang, function, sound, reality. Ontology mostly flips plus name-overflow.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 3, 4, 5 / d=4
- **Why**: bit 1, 3, 4, 5 连续 (跳过 2)。阴极性 + 本体后两 + 实用首 — "阴+用+声+实"。存在 + 判断 + 心 + 因 守。一种"形上派生显化为实, 而存在论与心、判断、因 都守"的态。

### `xoxxxoox` · 185

**Subtitle**: 3 阳侧 · 有 · 是 · 知

- **(X, X)**: (xoxx, xoox)
- **分解**: 阴 · 有 · 用 · 声 · 实 · 是 · 知 · 果
- **对偶**: `oxoooxxo` · 70
- **古文**: **解** — 《说文》"解, 判也"; 有 + 是 + 知 三阳 = 解 (理解; 庄子《养生主》"庖丁解牛")
- **现代汉语**: 唯有无·是非·知行 三轴留阳。
- **英语**: Three yang axes: being-nonbeing, right-wrong, know-act.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,6,7
- **Why**: 存在 + 心是 + 心知 守, 其余 5 轴翻。一种"心仍是仍知, 存在仍肯定"的近极阴。

### `xoxxxoxo` · 186

**Subtitle**: 3 阳侧 · 有 · 是 · 因

- **(X, X)**: (xoxx, xoxo)
- **分解**: 阴 · 有 · 用 · 声 · 实 · 是 · 行 · 因
- **对偶**: `oxoooxox` · 69
- **古文**: **理** — 《周易》"穷理尽性"; 朱熹"天理"; 有 + 是 + 因 三阳 = 理 (道理)
- **现代汉语**: 唯有无·是非·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, right-wrong, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,6,8
- **Why**: 存在 + 是 + 因 守, 其余 5 轴翻。"事在动而果未到, 心是, 存在肯定", 极性已沉。

### `xoxxxoxx` · 187  *[true X²]*

**Subtitle**: 2 阳侧 · 有 · 是

- **(X, X)**: (xoxx, xoxx)  ← true X² (左右半相等)
- **分解**: 阴 · 有 · 用 · 声 · 实 · 是 · 行 · 果
- **对偶**: `oxoooxoo` · 68
- **古文**: **然** — 《道德经》"道法自然"; 有无 + 是非 双阳 = 然 (存在与肯定的同侧守; 庄子"自然"); [X² 2↔6 阳守]
- **现代汉语**: 高低半皆 xoxx — bit 2 与 6 (有无·是非) 同步留阳, 其余 6 轴皆阴。X² 配对第 2 对单留。
- **英语**: Two yang axes: being-nonbeing and right-wrong. The 2nd X² pair (being ↔ judgment) self-resonates on the yang side; six other axes are yin.
- **形式逻辑**: |y|₁ = 6 / true X² (high=low=xoxx) / 187 = 17×11 (X² 对角元) / d(⊤⁸)=6, d(⊥⁸)=2
- **Why**: 16 个 X² 对角元中第 12 个 (h=11)。bit 2 (有无) 与 bit 6 (是非) 同步留阳 — X² 配对 (1↔5, **2↔6**, 3↔7, 4↔8) 第 2 对单独"守住阳"。哲学意涵: "有"(存在论的肯定) 与 "是"(判断的肯定) 是 X² 同源回声; 此码即唯这两轴守阳, 其余 6 轴全沉。对偶 #68 反之: 这两轴单独翻成 无·非。

### `xoxxxxoo` · 188

**Subtitle**: 3 阳侧 · 有 · 知 · 因

- **(X, X)**: (xoxx, xxoo)
- **分解**: 阴 · 有 · 用 · 声 · 实 · 非 · 知 · 因
- **对偶**: `oxooooxx` · 67
- **古文**: **学** — 《论语》"学而时习之"; 有 + 知 + 因 三阳 = 学 (学问之根)
- **现代汉语**: 唯有无·知行·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: being-nonbeing, know-act, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 2,7,8
- **Why**: 存在 + 知 + 因 守, 其余 5 轴 (阴·用·声·实·非) 翻。心知, 因尚未到果, 而表达·判断·语义·派生·极性皆翻。

### `xoxxxxox` · 189  *[palindrome]*

**Subtitle**: 2 阳侧 · 有 · 知

- **(X, X)**: (xoxx, xxox)
- **分解**: 阴 · 有 · 用 · 声 · 实 · 非 · 知 · 果
- **对偶**: `oxooooxo` · 66
- **古文**: **觉** — 《孟子》"先觉觉后觉"; 有 + 知 双阳 (palindrome 第 2 对守) = 觉 (存在之觉; 王阳明"良知"); [palindrome 2↔7 阳守]
- **现代汉语**: 唯有无·知行 两轴留阳, 余 6 轴阴。palindrome 第 2 配对 (有无 ↔ 知行) 同侧留阳。
- **英语**: Two yang axes: being-nonbeing and know-act. The 2nd palindrome pair (being ↔ knowing) self-resonates on the yang side; six axes are yin.
- **形式逻辑**: |y|₁ = 6 / palindrome / yang 仅 bit 2,7 / d(⊤⁸)=6
- **Why**: palindrome 配对 (2↔7) 单独守阳: 有 + 知 同阳。其它三对 (1↔8, 3↔6, 4↔5) 都同阴。哲学意涵: "存在"与"知"两个安顿轴守住, 这是 66 (无·行 双阴) 的对偶 — 这里反过来 "有·知" 双阳。

### `xoxxxxxo` · 190

**Subtitle**: 2 阳侧 · 有 · 因

- **(X, X)**: (xoxx, xxxo)
- **分解**: 阴 · 有 · 用 · 声 · 实 · 非 · 行 · 因
- **对偶**: `oxooooox` · 65
- **古文**: **始** — 《道德经》"无名天地之始, 有名万物之母"; 有 + 因 双阳 = 始 (存在论之起源)
- **现代汉语**: 唯有无·因果 两轴留阳, 余 6 轴阴。
- **英语**: Two yang axes: being-nonbeing and cause-effect. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 2,8 / d(⊤⁸)=6
- **Why**: 存在 + 因 守, 其余 6 轴翻。"事在动而果未来, 存在仍肯定", 极性已沉, 派生·表达·语义·判断·行动·都已显化。

### `xoxxxxxx` · 191

**Subtitle**: 1 阳侧 · 有

- **(X, X)**: (xoxx, xxxx)
- **分解**: 阴 · 有 · 用 · 声 · 实 · 非 · 行 · 果
- **对偶**: `oxoooooo` · 64
- **古文**: **有** — 道德经"天下万物生于有"; 王弼"有之以为利, 无之以为用"
- **现代汉语**: 唯有无一轴留阳, 余 7 轴皆阴。"有"是阴海中唯一留住的存在论之根。
- **英语**: Single yang remnant on being-nonbeing axis. Only the existential affirmation holds in the near-yin sea.
- **形式逻辑**: |y|₁ = 7 / yang 仅 bit 2 / d(⊤⁸)=7, d(⊥⁸)=1 / 单点阳留存 8 元之一
- **Why**: 8 个"单点阳留存"中"存在论"的一个: 在万象皆显化的近极阴中, 仅 "有" 还守住。对偶 #64 是 weight 1 单点阴扰动 (仅有无翻为无)。这两者构成"存在 vs 非存在"的极对偶。

### `xxoooooo` · 192

**Subtitle**: 2 阴侧 · 阴 · 无

- **(X, X)**: (xxoo, oooo)
- **分解**: 阴 · 无 · 体 · 形 · 名 · 是 · 知 · 因
- **对偶**: `ooxxxxxx` · 63
- **古文**: **寂** — 《说文》"寂, 无人声"; 阴 + 无 = 寂 / 太虚; 道家"虚极静笃"; 佛家"涅槃寂静"
- **现代汉语**: 阴阳+有无 双阴 (阴+无)。本体最深的两轴 (极性 + 存在) 同步下沉。
- **英语**: Two-axis yin: yin-yang and being-nonbeing. The two deepest ontological axes descend together — polarity meets nothingness.
- **形式逻辑**: |y|₁ = 2 / e₁₉₂ / yin 在 bit 1, 2 (本体首两位)
- **Why**: 阴阳·有无 同步翻 — 即极性 (阳→阴) 与存在 (有→无) 同步沉。这是道家形上最深的双重否定。"阴+无" — 在阴的极性中, 一切归于无。其余 6 轴皆留阳, 故是本体最深的扰动。对偶 #63 是 (阳·有) 双留阳的形式 (即最浅的 6 轴皆已翻成阴, 仅最深两轴守阳)。

### `xxooooox` · 193

**Subtitle**: 3 阴侧 · 阴 · 无 · 果

- **(X, X)**: (xxoo, ooox)
- **分解**: 阴 · 无 · 体 · 形 · 名 · 是 · 知 · 果
- **对偶**: `ooxxxxxo` · 62
- **古文**: **死** — 《说文》"死, 凘也, 人所离也"; 阴 + 无 + 果 = 死 (生命之最终归"无")
- **现代汉语**: 阴阳+有无+因果 三翻 (阴+无+果)。本体双沉 + 末果, 一种"虚无生果"。
- **英语**: Three yin axes: yin-yang, being-nonbeing, effect. From yin and nothingness, outcome arises.
- **形式逻辑**: |y|₁ = 3 / e₁₉₃ / yin 在 bit 1, 2, 8
- **Why**: 阴阳·有无·因果 — 本体最深双轴 + 实用最末。"阴+无+果" — 极性沉, 存在沉, 而仍有后果。一种"从绝对的虚无中冒出后果"的诡谲态; 中间 5 轴 (体·形·名·是·知) 留阳。

### `xxooooxo` · 194

**Subtitle**: 3 阴侧 · 阴 · 无 · 行

- **(X, X)**: (xxoo, ooxo)
- **分解**: 阴 · 无 · 体 · 形 · 名 · 是 · 行 · 因
- **对偶**: `ooxxxxox` · 61
- **古文**: **泯** — 《说文》"泯, 灭也"; 阴 + 无 + 行 = 泯灭 (《诗·大雅》"泯然众人")
- **现代汉语**: 阴阳+有无+知行 三翻 (阴+无+行)。深阴根之行。
- **英语**: Three yin axes: yin-yang, being-nonbeing, acting. Action from the deepest yin-grounded nothingness.
- **形式逻辑**: |y|₁ = 3 / e₁₉₄ / yin 在 bit 1, 2, 7
- **Why**: 阴阳·有无·知行 — 本体最深双 + 实用的行。即在阴+无的深处生出行动, 而判断、后果、语义、表达、派生维都未动。

### `xxooooxx` · 195  *[palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 无 · 行 · 果

- **(X, X)**: (xxoo, ooxx)
- **分解**: 阴 · 无 · 体 · 形 · 名 · 是 · 行 · 果
- **对偶**: `ooxxxxoo` · 60
- **古文**: **边** — 《周礼》"在边鄙"; palindrome 外缘 4 阴中央 4 阳 (#60 对偶); 庄子"得其环中"反例; 字图外缘
- **现代汉语**: **边** — palindrome 外缘 4 阴 (阴阳·有无·知行·因果) + 内核 4 阳 (体用·形声·名实·是非)。与 #60 央 形成 内/外 极对; "在边鄙" (周礼)。
- **英语**: Yang-core, yin-shell (palindromic). The middle four axes (体·形·名·是) hold; the outer four (阴·无·行·果) flip. Dual of #60.
- **形式逻辑**: |y|₁ = 4 / palindrome / yin 在 bit 1, 2, 7, 8 / d(⊤⁸)=d(⊥⁸)=4
- **Why**: palindrome 镜对模式: 外两对 (1↔8, 2↔7) 同侧阴, 内两对 (3↔6, 4↔5) 同侧阳。即极对 (阴阳-因果) + 次外对 (有无-知行) 双双沉, 而中两对 (体用-是非, 形声-名实) 守。哲学上: "边缘维全失而中段维守住" — 体派生·形象·名义·判断 四个"中层维"仍稳, 而最外的极性·存在·知行·因果 全沉。对偶 #60 为镜像 (中阴边阳, 央).

### `xxoooxoo` · 196

**Subtitle**: 3 阴侧 · 阴 · 无 · 非

- **(X, X)**: (xxoo, oxoo)
- **分解**: 阴 · 无 · 体 · 形 · 名 · 非 · 知 · 因
- **对偶**: `ooxxxoxx` · 59
- **古文**: **绝** — 《说文》"绝, 断丝也"; 阴 + 无 + 非 = 绝 (《道德经》"绝学无忧")
- **现代汉语**: 阴阳+有无+是非 三翻 (阴+无+非)。三重否定 — 极性、存在、判断都否。
- **英语**: Three yin axes: yin-yang, being-nonbeing, wrong-judgment. Triple negation — polarity, existence, judgment all flip to "no".
- **形式逻辑**: |y|₁ = 3 / e₁₉₆ / yin 在 bit 1, 2, 6
- **Why**: 阴阳·有无·是非 — 三个"否定维"同步入阴: 极性的"阴", 存在论的"无", 判断的"非"。这是三重否定的最简结构 — 从最深处一直到判断层的全否。其余 5 轴留阳。

### `xxoooxox` · 197

**Subtitle**: 4 阴侧 · 阴 · 无 · 非 · 果

- **(X, X)**: (xxoo, oxox)
- **分解**: 阴 · 无 · 体 · 形 · 名 · 非 · 知 · 果
- **对偶**: `ooxxxoxo` · 58
- **古文**: **凋** — 《说文》"凋, 半伤也"; 阴 + 无 + 非 + 果 = 凋 (凋零; 论语"岁寒, 然后知松柏之后凋也")
- **现代汉语**: 阴阳+有无+是非+因果 四翻, 唯体用·形声·名实·知行 留阳。三重否定+果。
- **英语**: Four yin axes: yin-yang, being-nonbeing, wrong-judgment, effect. Triple negation bears outcome — pessimistic conclusion.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 2, 6, 8 / d=4
- **Why**: 196 (三重否定) 加上"果"末梢 — 即"虚无的否定性结果"。体用·形声·名实·知行 守 — 即派生、表达、命名、知 都未动, 但结果已自来。

### `xxoooxxo` · 198

**Subtitle**: 4 阴侧 · 阴 · 无 · 非 · 行

- **(X, X)**: (xxoo, oxxo)
- **分解**: 阴 · 无 · 体 · 形 · 名 · 非 · 行 · 因
- **对偶**: `ooxxxoox` · 57
- **古文**: **悖** — 《说文》"悖, 乱也"; 阴 + 无 + 非 + 行 = 悖 (《左传》"悖入悖出")
- **现代汉语**: 阴阳+有无+是非+知行 四翻, 唯体用·形声·名实·因果 留阳。"阴+无+非+行"批评性行动。
- **英语**: Four yin axes: yin-yang, being-nonbeing, wrong-judgment, acting. Negativity all the way from yin-grounded existence to action — outcome pending.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 2, 6, 7 / d=4
- **Why**: 三重否定 + 行动。即"阴根·无之根·心非·身行" 四联, 但因果留因 (果未临), 体派生·形象·命名 守。一种"从绝对虚无中发出否定性行动"的极端态。

### `xxoooxxx` · 199

**Subtitle**: 3 阳侧 · 体 · 形 · 名

- **(X, X)**: (xxoo, oxxx)
- **分解**: 阴 · 无 · 体 · 形 · 名 · 非 · 行 · 果
- **对偶**: `ooxxxooo` · 56
- **古文**: **范** — 《说文》"范, 法也"; 体 + 形 + 名 三阳 = 范 (模范·规范)
- **现代汉语**: 唯体用·形声·名实 三轴留阳, 余 5 轴皆阴。本体的"派生-表达-命名"三轴守源。
- **英语**: Three yang axes: substance-function, form-sound, name-reality. The "derivation-expression-naming" triple holds; five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 3,4,5 / d(⊤⁸)=5
- **Why**: bit 3,4,5 连续 (本体后两 + 实用首) 留阳, 余 5 轴翻。即"本体派生 + 形象 + 命名"骨架尚存, 而极性、存在、判断、行动、后果皆已显化。

### `xxooxooo` · 200

**Subtitle**: 3 阴侧 · 阴 · 无 · 实

- **(X, X)**: (xxoo, xooo)
- **分解**: 阴 · 无 · 体 · 形 · 实 · 是 · 知 · 因
- **对偶**: `ooxxoxxx` · 55
- **古文**: **幽** — 《说文》"幽, 隐也"; 阴 + 无 + 实 = 幽 (《周易》"探赜索隐"; 幽冥之实)
- **现代汉语**: 阴阳+有无+名实 三翻 (阴+无+实)。深阴双根 + 实出名 — 虚无中之实。
- **英语**: Three yin axes: yin-yang, being-nonbeing, reality. Reality emerges from yin-grounded nothingness — paradoxical concretion.
- **形式逻辑**: |y|₁ = 3 / e₂₀₀ / yin 在 bit 1, 2, 5
- **Why**: 阴阳·有无·名实 — 本体最深双轴 + 实用首。"阴+无+实" — 在最深的虚无中冒出具体的实。一种悖论态: 既无又有, 既空又实。

### `xxooxoox` · 201

**Subtitle**: 4 阴侧 · 阴 · 无 · 实 · 果

- **(X, X)**: (xxoo, xoox)
- **分解**: 阴 · 无 · 体 · 形 · 实 · 是 · 知 · 果
- **对偶**: `ooxxoxxo` · 54
- **古文**: **尽** — 《说文》"尽, 器中空也"; 阴 + 无 + 实 + 果 = 尽 (《孟子》"尽心知性")
- **现代汉语**: 阴阳+有无+名实+因果 四翻, 唯体用·形声·是非·知行 留阳。"阴+无+实+果"虚无生实生果。
- **英语**: Four yin axes: yin-yang, being-nonbeing, reality, effect. From yin-nothingness, reality and outcome emerge.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 2, 5, 8 / d=4
- **Why**: 4 个"显化"维轴 (阴·无·实·果) 入阴。即"从虚无的根生出实, 实生果"。体派生·形象·心·判断 守。是非·知行 守住意味着"心知是, 而事自显化"。

### `xxooxoxo` · 202

**Subtitle**: 4 阴侧 · 阴 · 无 · 实 · 行

- **(X, X)**: (xxoo, xoxo)
- **分解**: 阴 · 无 · 体 · 形 · 实 · 是 · 行 · 因
- **对偶**: `ooxxoxox` · 53
- **古文**: **退** — 《道德经》"功成身退, 天之道也"; 阴 + 无 + 实 + 行 = 退 (《周易》"君子以遯而无闷")
- **现代汉语**: 阴阳+有无+名实+知行 四翻, 唯体用·形声·是非·因果 留阳。"阴+无+实+行"虚无中行实。
- **英语**: Four yin axes: yin-yang, being-nonbeing, reality, acting. Action of reality in yin-grounded nothingness.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 2, 5, 7 / d=4
- **Why**: 4 个奇位轴 (1,2,5,7) — 实际是 bit 1,2 加 5,7。"阴+无+实+行" — 从虚无的根中冒出实, 然后付诸行动。心仍是仍因 (判断与因果守源)。

### `xxooxoxx` · 203

**Subtitle**: 3 阳侧 · 体 · 形 · 是

- **(X, X)**: (xxoo, xoxx)
- **分解**: 阴 · 无 · 体 · 形 · 实 · 是 · 行 · 果
- **对偶**: `ooxxoxoo` · 52
- **古文**: **矩** — 《周易》"方以类聚, 物以群分"; 《大学》"絜矩之道"; 体·形·是 三阳 = 矩 (规矩之器, "方"已迁 #102)
- **现代汉语**: **矩** — 体·形·是 三阳留 + 5 轴入阴。规矩之器 (《大学》"絜矩之道"); "方"已让 #102 (X² 自方算子)。
- **英语**: Three yang axes: substance-function, form-sound, right-wrong. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 3,4,6 / d(⊤⁸)=5
- **Why**: 体派生·形象·心是 守, 其余 5 轴翻。即"派生骨架 + 形象 + 肯定判断"守住, 而极性·存在·语义·行动·后果皆已显化。

### `xxooxxoo` · 204  *[true X² · comp-palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 无 · 实 · 非

- **(X, X)**: (xxoo, xxoo)  ← true X² (左右半相等)
- **分解**: 阴 · 无 · 体 · 形 · 实 · 非 · 知 · 因
- **对偶**: `ooxxooxx` · 51
- **古文**: 反齐响 · 周期 4 自方 (Walsh W₂ 对偶)
- **现代汉语**: 高低半皆 xxoo, 是 true X² ∩ comp-palindrome 4 元之一。2-bit 周期 (11,00) 重复 4 次。
- **英语**: Period-4 self-square (xxoo, xxoo) — dual of #51. Walsh W₂ flipped. One of the four true X² ∩ comp-palindrome codes (51, 85, 170, 204).
- **形式逻辑**: |y|₁ = 4 / true X² (high=low=xxoo) / comp-palindrome / Walsh W₂ ⊕ 1 / 204 = 17×12
- **Why**: 51 的对偶, Walsh W₂ 的另一相。结构: bit 1,2,5,6 入阴 — 即 X² 配对 (1↔5) 与 (2↔6) 双对共振 (阴), 其余两对 (3↔7, 4↔8) 双对共振 (阳)。哲学上: 两个最"根本-语义"的 X² 配对 (极性-命名, 存在-判断) 全部入阴, 而两个"派生-表达-行动-后果"的 X² 配对 (派生-知行, 表达-因果) 全部留阳。

### `xxooxxox` · 205

**Subtitle**: 3 阳侧 · 体 · 形 · 知

- **(X, X)**: (xxoo, xxox)
- **分解**: 阴 · 无 · 体 · 形 · 实 · 非 · 知 · 果
- **对偶**: `ooxxooxo` · 50
- **古文**: **照** — 《说文》"照, 明也"; 体 + 形 + 知 三阳 = 照 (观照; 般若"照见五蕴皆空")
- **现代汉语**: 唯体用·形声·知行 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: substance-function, form-sound, know-act. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 3,4,7
- **Why**: 派生·形·知 守, 其余 5 轴翻。"形可见, 心知, 派生维持", 而极性、存在、语义、判断、行动、后果都已显化。

### `xxooxxxo` · 206

**Subtitle**: 3 阳侧 · 体 · 形 · 因

- **(X, X)**: (xxoo, xxxo)
- **分解**: 阴 · 无 · 体 · 形 · 实 · 非 · 行 · 因
- **对偶**: `ooxxooox` · 49
- **古文**: **构** — 《说文》"构, 盖也" (引申建构); 体 + 形 + 因 三阳 = 构 (构成·结构)
- **现代汉语**: 唯体用·形声·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: substance-function, form-sound, cause-effect. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 3,4,8
- **Why**: 派生·形·因 守, 其余 5 轴翻。"形可见, 因尚未到果, 派生维持", 而事尽显化, 极性已沉。

### `xxooxxxx` · 207

**Subtitle**: 2 阳侧 · 体 · 形

- **(X, X)**: (xxoo, xxxx)
- **分解**: 阴 · 无 · 体 · 形 · 实 · 非 · 行 · 果
- **对偶**: `ooxxoooo` · 48
- **古文**: **象** — 《周易·系辞》"是故易者, 象也"; 体 + 形 双阳 = 象 (本体之形)
- **现代汉语**: 唯体用·形声 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: substance-function and form-sound. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 3,4 / d(⊤⁸)=6
- **Why**: 仅 体 + 形 守 — 本体的"派生 + 表达"两个最具操作性的轴。极性、存在、命名、判断、行动、后果皆已显化。

### `xxoxoooo` · 208

**Subtitle**: 3 阴侧 · 阴 · 无 · 声

- **(X, X)**: (xxox, oooo)
- **分解**: 阴 · 无 · 体 · 声 · 名 · 是 · 知 · 因
- **对偶**: `ooxoxxxx` · 47
- **古文**: **暗** — 《说文》"暗, 日无光也"; 阴 + 无 + 声 = 暗 (《庄子·齐物论》"夫芴漠无形")
- **现代汉语**: 阴阳+有无+形声 三翻 (阴+无+声)。深阴 + 表达, "虚无中之声"。
- **英语**: Three yin axes: yin-yang, being-nonbeing, sound. Voice from the deepest yin-grounded nothingness.
- **形式逻辑**: |y|₁ = 3 / e₂₀₈ / yin 在 bit 1, 2, 4
- **Why**: 阴阳·有无·形声 — 本体最深双 + 表达。"阴+无+声" — 从最深的虚无中传出的声音。体派生·名实·是非·知行·因果 留阳, 故纯本体之声, 无具体实事。

### `xxoxooox` · 209

**Subtitle**: 4 阴侧 · 阴 · 无 · 声 · 果

- **(X, X)**: (xxox, ooox)
- **分解**: 阴 · 无 · 体 · 声 · 名 · 是 · 知 · 果
- **对偶**: `ooxoxxxo` · 46
- **古文**: **没** — 《说文》"没, 沉也"; 阴 + 无 + 声 + 果 = 没 (湮没; 《楚辞》"何时俶傥之心已乎")
- **现代汉语**: 阴阳+有无+形声+因果 四翻, 唯体用·名实·是非·知行 留阳。"阴+无+声+果"虚无之声引发果。
- **英语**: Four yin axes: yin-yang, being-nonbeing, sound, effect. Voice from nothingness yields outcome.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 2, 4, 8 / d=4
- **Why**: 本体最深双 (阴·无) + 本体末 (声) + 实用末 (果)。"阴+无+声+果" — 从虚无传声而得果。体派生·语义·判断·心 守。

### `xxoxooxo` · 210

**Subtitle**: 4 阴侧 · 阴 · 无 · 声 · 行

- **(X, X)**: (xxox, ooxo)
- **分解**: 阴 · 无 · 体 · 声 · 名 · 是 · 行 · 因
- **对偶**: `ooxoxxox` · 45
- **古文**: **匿** — 《说文》"匿, 亡也"; 阴 + 无 + 声 + 行 = 匿 (《周易》"隐而藏之")
- **现代汉语**: 阴阳+有无+形声+知行 四翻, 唯体用·名实·是非·因果 留阳。"阴+无+声+行"虚无之声化行。
- **英语**: Four yin axes: yin-yang, being-nonbeing, sound, acting. Voice from nothingness becomes action.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 2, 4, 7 / d=4
- **Why**: 本体最深双 + 表达 + 行动。"阴+无+声+行" — 虚无中发声转为行动。是非·名实·体用·因果 守。

### `xxoxooxx` · 211

**Subtitle**: 3 阳侧 · 体 · 名 · 是

- **(X, X)**: (xxox, ooxx)
- **分解**: 阴 · 无 · 体 · 声 · 名 · 是 · 行 · 果
- **对偶**: `ooxoxxoo` · 44
- **古文**: **则** — 《说文》"则, 等画物也"; 体 + 名 + 是 三阳 = 则 (规则; 《诗·大雅》"有物有则")
- **现代汉语**: 唯体用·名实·是非 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: substance-function, name-reality, right-wrong. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 3,5,6
- **Why**: 派生 + 名 + 是 守, 其余 5 轴翻。"派生骨架 + 名 + 肯定判断"守住, 极性、存在、表达、行动、后果皆已显化。

### `xxoxoxoo` · 212  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 无 · 声 · 非

- **(X, X)**: (xxox, oxoo)
- **分解**: 阴 · 无 · 体 · 声 · 名 · 非 · 知 · 因
- **对偶**: `ooxoxoxx` · 43
- **古文**: **哑** — 《说文》"哑, 笑也" (后引申无声); 阴 + 无 + 声 + 非 = 哑 (默而否定); comp-palindrome
- **现代汉语**: 阴阳+有无+形声+是非 四翻, 唯体用·名实·知行·因果 留阳。comp-palindrome。
- **英语**: Four yin axes: yin-yang, being-nonbeing, sound, wrong-judgment. Anti-palindrome.
- **形式逻辑**: |y|₁ = 4 / comp-palindrome / yin 在 bit 1, 2, 4, 6 / d=4
- **Why**: comp-palindrome 之一。配对 (1↔8): 阴·因 反, (2↔7): 无·知 反, (3↔6): 体·非 反, (4↔5): 声·名 反 — 四对皆 anti-mirror。即"阴根 + 虚无 + 表达 + 否定" 在 anti-palindrome 结构上同步分裂。

### `xxoxoxox` · 213

**Subtitle**: 3 阳侧 · 体 · 名 · 知

- **(X, X)**: (xxox, oxox)
- **分解**: 阴 · 无 · 体 · 声 · 名 · 非 · 知 · 果
- **对偶**: `ooxoxoxo` · 42
- **古文**: **判** — 《说文》"判, 分也"; 体 + 名 + 知 三阳 = 判 (判断·区分)
- **现代汉语**: 唯体用·名实·知行 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: substance-function, name-reality, know-act. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 3,5,7
- **Why**: 体·名·知 守 — 全奇位三轴 (本体派生·语义命名·心知)。其余 5 轴翻。一种 X² 配对 (3↔7) 单守 + bit 5 加守。

### `xxoxoxxo` · 214

**Subtitle**: 3 阳侧 · 体 · 名 · 因

- **(X, X)**: (xxox, oxxo)
- **分解**: 阴 · 无 · 体 · 声 · 名 · 非 · 行 · 因
- **对偶**: `ooxoxoox` · 41
- **古文**: **族** — 《说文》"族, 矢锋也" (引申聚类); 体 + 名 + 因 三阳 = 族 (族类·宗族)
- **现代汉语**: 唯体用·名实·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: substance-function, name-reality, cause-effect. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 3,5,8
- **Why**: 体·名·因 守, 其余 5 轴翻。"派生 + 名 + 因守住, 而极性、存在、表达、判断、行动、果(已动到因) 皆显化"。

### `xxoxoxxx` · 215

**Subtitle**: 2 阳侧 · 体 · 名

- **(X, X)**: (xxox, oxxx)
- **分解**: 阴 · 无 · 体 · 声 · 名 · 非 · 行 · 果
- **对偶**: `ooxoxooo` · 40
- **古文**: **位** — 《周易》"圣人定位"; 体 + 名 双阳 = 位 (本体与命名同立)
- **现代汉语**: 唯体用·名实 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: substance-function and name-reality. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 3,5 / d(⊤⁸)=6
- **Why**: 体派生 + 名 守。哲学上, 这是"派生关系结构 + 语义命名"两个 X² 配对 ((3↔7)的一半, (1↔5)的一半) 守住, 其余 6 轴皆已显化。

### `xxoxxooo` · 216

**Subtitle**: 4 阴侧 · 阴 · 无 · 声 · 实

- **(X, X)**: (xxox, xooo)
- **分解**: 阴 · 无 · 体 · 声 · 实 · 是 · 知 · 因
- **对偶**: `ooxooxxx` · 39
- **古文**: **晦** — 《说文》"晦, 月尽也"; 阴 + 无 + 声 + 实 = 晦 (晦暗·晦冥)
- **现代汉语**: 阴阳+有无+形声+名实 四翻, 唯体用·是非·知行·因果 留阳。"阴+无+声+实"完整深阴表达链。
- **英语**: Four yin axes: yin-yang, being-nonbeing, sound, reality. Full deep-yin expressive cascade — voice from nothingness becomes thing.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 2, 4, 5 / d=4
- **Why**: bit 1,2 + bit 4,5 (连续 4 中跳过 3)。"阴+无+声+实" — 从最深虚无中, 经声音化为实。体派生 + 心 (是·知) + 因 守。

### `xxoxxoox` · 217

**Subtitle**: 3 阳侧 · 体 · 是 · 知

- **(X, X)**: (xxox, xoox)
- **分解**: 阴 · 无 · 体 · 声 · 实 · 是 · 知 · 果
- **对偶**: `ooxooxxo` · 38
- **古文**: **会** — 《说文》"会, 合也"; 体 + 是 + 知 三阳 = 会 (体会; 《大学》"心领神会")
- **现代汉语**: 唯体用·是非·知行 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: substance-function, right-wrong, know-act. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 3,6,7
- **Why**: 体派生 + 心是 + 心知 守, 其余 5 轴翻。即"派生骨架 + 心知是"守住, 而极性·存在·表达·语义·行动·后果都已显化。

### `xxoxxoxo` · 218

**Subtitle**: 3 阳侧 · 体 · 是 · 因

- **(X, X)**: (xxox, xoxo)
- **分解**: 阴 · 无 · 体 · 声 · 实 · 是 · 行 · 因
- **对偶**: `ooxooxox` · 37
- **古文**: **典** — 《说文》"典, 五帝之书也"; 体 + 是 + 因 三阳 = 典 (经典)
- **现代汉语**: 唯体用·是非·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: substance-function, right-wrong, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 3,6,8
- **Why**: 派生 + 是 + 因 守。"派生骨架持, 心仍肯定, 果未到", 而其余 5 轴 (阴·无·声·实·行) 皆翻。

### `xxoxxoxx` · 219  *[palindrome]*

**Subtitle**: 2 阳侧 · 体 · 是

- **(X, X)**: (xxox, xoxx)
- **分解**: 阴 · 无 · 体 · 声 · 实 · 是 · 行 · 果
- **对偶**: `ooxooxoo` · 36
- **古文**: **正** — 《大学》"欲修其身者, 先正其心"; 体 + 是 双阳 (palindrome 第 3 对守) = 正 (派生与肯定守源); [palindrome 3↔6 阳守]
- **现代汉语**: 唯体用·是非 两轴留阳, 余 6 轴皆阴。palindrome 第 3 配对 (体用 ↔ 是非) 同侧留阳。
- **英语**: Two yang axes: substance-function and right-wrong. The 3rd palindrome pair self-resonates on the yang side; six axes are yin.
- **形式逻辑**: |y|₁ = 6 / palindrome / yang 仅 bit 3,6 / d(⊤⁸)=6
- **Why**: palindrome 配对 (3↔6) 单守阳: 体 + 是 同阳。其它三对 (1↔8, 2↔7, 4↔5) 都同阴。即"派生与判断"两个"内层中段"维守住, 而最深的极性·存在和最末的行·果, 加表达·语义全沉。

### `xxoxxxoo` · 220

**Subtitle**: 3 阳侧 · 体 · 知 · 因

- **(X, X)**: (xxox, xxoo)
- **分解**: 阴 · 无 · 体 · 声 · 实 · 非 · 知 · 因
- **对偶**: `ooxoooxx` · 35
- **古文**: **闻** — 《论语》"朝闻道, 夕死可矣"; 体 + 知 + 因 三阳 = 闻 (见闻·学问)
- **现代汉语**: 唯体用·知行·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: substance-function, know-act, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 3,7,8
- **Why**: 体·知·因 守, 其余 5 轴 (阴·无·声·实·非) 翻。即"派生 + 心知 + 因 (果未到)"守住, 而极性、存在、表达、语义、判断皆显化。

### `xxoxxxox` · 221  *[true X²]*

**Subtitle**: 2 阳侧 · 体 · 知

- **(X, X)**: (xxox, xxox)  ← true X² (左右半相等)
- **分解**: 阴 · 无 · 体 · 声 · 实 · 非 · 知 · 果
- **对偶**: `ooxoooxo` · 34
- **古文**: **悟** — 《说文》"悟, 觉也"; 体用 + 知行 双阳 = 悟 (派生与认知的同侧守; 禅宗"明心见性"); [X² 3↔7 阳守]
- **现代汉语**: 高低半皆 xxox — bit 3 与 7 (体用·知行) 同步留阳, 其余 6 轴皆阴。X² 配对第 3 对单留。
- **英语**: Two yang axes: substance-function and know-act. The 3rd X² pair (substance ↔ knowing) self-resonates on the yang side; six axes are yin.
- **形式逻辑**: |y|₁ = 6 / true X² (high=low=xxox) / 221 = 17×13 (X² 对角元) / d(⊤⁸)=6, d(⊥⁸)=2
- **Why**: 16 个 X² 对角元第 14 个 (h=13)。bit 3 (体用) 与 bit 7 (知行) 同步留阳 — X² 配对 (1↔5, 2↔6, **3↔7**, 4↔8) 第 3 对单独守阳。哲学意涵: "体" (本体派生) 与"知" (实用知识) 是 X² 同源回声; 此码即仅此两轴守源。对偶 #34 反之 (两轴单独翻为用·行)。

### `xxoxxxxo` · 222

**Subtitle**: 2 阳侧 · 体 · 因

- **(X, X)**: (xxox, xxxo)
- **分解**: 阴 · 无 · 体 · 声 · 实 · 非 · 行 · 因
- **对偶**: `ooxoooox` · 33
- **古文**: **本** — 《大学》"物有本末, 事有终始"; 体 + 因 双阳 = 本 (论语"君子务本"; 朱熹"本根")
- **现代汉语**: 唯体用·因果 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: substance-function and cause-effect. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 3,8 / d(⊤⁸)=6
- **Why**: 体派生 + 因 守, 其余 6 轴翻。即"派生骨架立, 因尚未到果", 而极性、存在、表达、命名、判断、行动皆显化。

### `xxoxxxxx` · 223

**Subtitle**: 1 阳侧 · 体

- **(X, X)**: (xxox, xxxx)
- **分解**: 阴 · 无 · 体 · 声 · 实 · 非 · 行 · 果
- **对偶**: `ooxooooo` · 32
- **古文**: **体** — 王弼《周易略例》"体用一源"; 朱熹"理为体, 气为用"; 中国哲学最深范畴之一
- **现代汉语**: 唯体用一轴留阳, 余 7 轴皆阴。"体"是阴海中唯一留住的本体派生之根。
- **英语**: Single yang remnant on substance-function axis. Only the metaphysical "body" / substance holds.
- **形式逻辑**: |y|₁ = 7 / yang 仅 bit 3 / d(⊤⁸)=7, d(⊥⁸)=1 / 单点阳留存 8 元之一
- **Why**: 8 个"单点阳留存"中"派生根本"的一个: 在万象皆显化的近极阴中, 仅 "体" 还守住。对偶 #32 是 weight 1 (仅体用翻为用)。两者构成"体"与"用"的对偶。

### `xxxooooo` · 224

**Subtitle**: 3 阴侧 · 阴 · 无 · 用

- **(X, X)**: (xxxo, oooo)
- **分解**: 阴 · 无 · 用 · 形 · 名 · 是 · 知 · 因
- **对偶**: `oooxxxxx` · 31
- **古文**: **冲** — 《道德经》"道冲而用之或不盈"; 阴 + 无 + 用 = 道之冲虚之用; 张载《正蒙》"太虚即气"之冲; 与 #31 统 形成虚/实对
- **现代汉语**: **冲** — 阴+无+用 (本体前三入阴, 形声留阳)。道德经"道冲而用之或不盈"; 张载"太虚"之冲虚 (单字化 "太虚"); 形上骨架震荡, 实用未动。
- **英语**: Three yin axes: yin-yang, being-nonbeing, function. Three of four ontological axes flip — Daoist "function-of-nothingness" deepened.
- **形式逻辑**: |y|₁ = 3 / e₂₂₄ / yin 在 bit 1, 2, 3 (本体前三轴)
- **Why**: 阴阳·有无·体用 — 本体前三轴连续入阴。"阴+无+用" — 在阴+无 的最深处, 派生"用"。形声 + 实用 4 轴 留阳, 故仅本体核心震荡而表达 + 实用未动。

### `xxxoooox` · 225

**Subtitle**: 4 阴侧 · 阴 · 无 · 用 · 果

- **(X, X)**: (xxxo, ooox)
- **分解**: 阴 · 无 · 用 · 形 · 名 · 是 · 知 · 果
- **对偶**: `oooxxxxo` · 30
- **古文**: **休** — 《道德经》"功遂身退, 天之道"; 阴 + 无 + 用 + 果 = 休 (休止·休歇)
- **现代汉语**: 阴阳+有无+体用+因果 四翻, 唯形声·名实·是非·知行 留阳。"阴+无+用+果"深阴派生果。
- **英语**: Four yin axes: yin-yang, being-nonbeing, function, effect. Deep yin derivation bears outcome — sound, name, judgment, knowing all hold.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 2, 3, 8 / d=4
- **Why**: 本体前三轴 + 实用末。"阴+无+用+果" — 道家深阴的派生有后果。形 + 名 + 是 + 知 守。

### `xxxoooxo` · 226

**Subtitle**: 4 阴侧 · 阴 · 无 · 用 · 行

- **(X, X)**: (xxxo, ooxo)
- **分解**: 阴 · 无 · 用 · 形 · 名 · 是 · 行 · 因
- **对偶**: `oooxxxox` · 29
- **古文**: **遁** — 《周易》"遁"卦; 阴 + 无 + 用 + 行 = 遁 (《周易·遁》"君子以远小人")
- **现代汉语**: 阴阳+有无+体用+知行 四翻, 唯形声·名实·是非·因果 留阳。"阴+无+用+行"深阴派生行。
- **英语**: Four yin axes: yin-yang, being-nonbeing, function, acting. Deep-yin derivation activates as action.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 2, 3, 7 / d=4
- **Why**: 本体前三 + 实用知行。"阴+无+用+行"完整深阴派生-实践链, 但后果未临。形象与心 (是) 守。

### `xxxoooxx` · 227

**Subtitle**: 3 阳侧 · 形 · 名 · 是

- **(X, X)**: (xxxo, ooxx)
- **分解**: 阴 · 无 · 用 · 形 · 名 · 是 · 行 · 果
- **对偶**: `oooxxxoo` · 28
- **古文**: **符** — 《说文》"符, 信也"; 形 + 名 + 是 三阳 = 符 (符合·名实相符)
- **现代汉语**: 唯形声·名实·是非 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: form-sound, name-reality, right-wrong. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 4,5,6 / d(⊤⁸)=5
- **Why**: bit 4,5,6 连续 — 形 + 名 + 是 守。即"表达 + 命名 + 肯定判断"骨架持, 其余 5 轴皆已显化。

### `xxxooxoo` · 228

**Subtitle**: 4 阴侧 · 阴 · 无 · 用 · 非

- **(X, X)**: (xxxo, oxoo)
- **分解**: 阴 · 无 · 用 · 形 · 名 · 非 · 知 · 因
- **对偶**: `oooxxoxx` · 27
- **古文**: **废** — 《说文》"废, 屋顿也"; 阴 + 无 + 用 + 非 = 废 (《尚书》"无遗老成"; 道家"无为而无不为"的反面)
- **现代汉语**: 阴阳+有无+体用+是非 四翻, 唯形声·名实·知行·因果 留阳。"阴+无+用+非"深阴派生伴否定。
- **英语**: Four yin axes: yin-yang, being-nonbeing, function, wrong-judgment. Deep-yin function under critique.
- **形式逻辑**: |y|₁ = 4 / yin 在 bit 1, 2, 3, 6 / d=4
- **Why**: 本体前三 + 实用是非。"阴+无+用+非" — 深阴派生伴否定判断。形 + 名 + 知 + 因 守, 即"形象、命名、心、因"未变。

### `xxxooxox` · 229

**Subtitle**: 3 阳侧 · 形 · 名 · 知

- **(X, X)**: (xxxo, oxox)
- **分解**: 阴 · 无 · 用 · 形 · 名 · 非 · 知 · 果
- **对偶**: `oooxxoxo` · 26
- **古文**: **悉** — 《说文》"悉, 详尽也"; 形 + 名 + 知 三阳 = 悉 (知悉·尽知)
- **现代汉语**: 唯形声·名实·知行 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: form-sound, name-reality, know-act.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 4,5,7
- **Why**: 形 + 名 + 知 守, 其余 5 轴翻。"形可见, 名清, 心知", 而其余 5 轴 (阴·无·用·非·果) 皆显化。

### `xxxooxxo` · 230

**Subtitle**: 3 阳侧 · 形 · 名 · 因

- **(X, X)**: (xxxo, oxxo)
- **分解**: 阴 · 无 · 用 · 形 · 名 · 非 · 行 · 因
- **对偶**: `oooxxoox` · 25
- **古文**: **谱** — 《广韵》"谱, 籍录之书"; 形 + 名 + 因 三阳 = 谱 (谱系·族谱)
- **现代汉语**: 唯形声·名实·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: form-sound, name-reality, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 4,5,8
- **Why**: 形 + 名 + 因 守, 其余 5 轴翻。即"形象 + 命名 + 因 (果未到)"守住, 而极性、存在、派生、判断、行动皆显化。

### `xxxooxxx` · 231  *[palindrome]*

**Subtitle**: 2 阳侧 · 形 · 名

- **(X, X)**: (xxxo, oxxx)
- **分解**: 阴 · 无 · 用 · 形 · 名 · 非 · 行 · 果
- **对偶**: `oooxxooo` · 24
- **古文**: **彰** — 《说文》"彰, 文彰也"; 形 + 名 双阳 (palindrome 中轴守) = 彰 (《大学》"在止于至善"; 《周易》"美言可以市尊"); [palindrome 4↔5 阳守]
- **现代汉语**: 唯形声·名实 两轴留阳, 余 6 轴皆阴。palindrome 第 4 配对 (中心轴) 同侧留阳。
- **英语**: Two yang axes: form-sound and name-reality. The 4th palindrome pair (central) self-resonates on the yang side.
- **形式逻辑**: |y|₁ = 6 / palindrome / yang 仅 bit 4,5 / d=6
- **Why**: palindrome 配对 (4↔5) 单守阳: 形 + 名 同阳。其它三对 (1↔8, 2↔7, 3↔6) 都同阴。即"形象 + 命名"两个最中心的轴 (8 轴中位 4-5) 守住, 而最深 (阴·无) 与最末 (行·果) 加体派生·判断·心都沉。对偶 #24 反之 (形+名 双阴, 余阳)。

### `xxxoxooo` · 232  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 无 · 用 · 实

- **(X, X)**: (xxxo, xooo)
- **分解**: 阴 · 无 · 用 · 形 · 实 · 是 · 知 · 因
- **对偶**: `oooxoxxx` · 23
- **古文**: **素** — 《道德经》"见素抱朴, 少私寡欲"; 阴 + 无 + 用 + 实 = 素 (无为之朴; 庄子"复其初"); comp-palindrome
- **现代汉语**: 阴阳+有无+体用+名实 四翻, 唯形声·是非·知行·因果 留阳。comp-palindrome。
- **英语**: Four yin axes: yin-yang, being-nonbeing, function, reality. Anti-palindrome.
- **形式逻辑**: |y|₁ = 4 / comp-palindrome / yin 在 bit 1, 2, 3, 5 / d=4
- **Why**: comp-palindrome 16 元之一。配对 (1↔8): 阴·因 反, (2↔7): 无·知 反, (3↔6): 用·是 反, (4↔5): 形·实 反 — 四对皆 anti-mirror。即"本体前三 (阴·无·用) + 实用首 (实)"四轴入阴。

### `xxxoxoox` · 233

**Subtitle**: 3 阳侧 · 形 · 是 · 知

- **(X, X)**: (xxxo, xoox)
- **分解**: 阴 · 无 · 用 · 形 · 实 · 是 · 知 · 果
- **对偶**: `oooxoxxo` · 22
- **古文**: **的** — 《广韵》"的, 实也" (后引申确实); 形 + 是 + 知 三阳 = 的 (的确·标的)
- **现代汉语**: 唯形声·是非·知行 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: form-sound, right-wrong, know-act. Five axes flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 4,6,7
- **Why**: 形 + 是 + 知 守, 其余 5 轴翻。"形象 + 心是 + 心知"守住, 其余尽显化。

### `xxxoxoxo` · 234

**Subtitle**: 3 阳侧 · 形 · 是 · 因

- **(X, X)**: (xxxo, xoxo)
- **分解**: 阴 · 无 · 用 · 形 · 实 · 是 · 行 · 因
- **对偶**: `oooxoxox` · 21
- **古文**: **依** — 《说文》"依, 倚也"; 形 + 是 + 因 三阳 = 依 (依据)
- **现代汉语**: 唯形声·是非·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: form-sound, right-wrong, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 4,6,8
- **Why**: 形 + 是 + 因 守, 其余 5 轴翻。即"形仍清, 心仍是, 因尚未到果", 而极性·存在·派生·语义·行动皆已显化。

### `xxxoxoxx` · 235

**Subtitle**: 2 阳侧 · 形 · 是

- **(X, X)**: (xxxo, xoxx)
- **分解**: 阴 · 无 · 用 · 形 · 实 · 是 · 行 · 果
- **对偶**: `oooxoxoo` · 20
- **古文**: **图** — 《说文》"图, 画计难也"; 形 + 是 双阳 = 图 (《周易》"河出图, 洛出书"; 形之肯定即图)
- **现代汉语**: 唯形声·是非 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: form-sound and right-wrong. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 4,6 / d(⊤⁸)=6
- **Why**: 形 + 是 守。"形象 + 心是"两轴守住, 其余 6 轴皆已显化。

### `xxxoxxoo` · 236

**Subtitle**: 3 阳侧 · 形 · 知 · 因

- **(X, X)**: (xxxo, xxoo)
- **分解**: 阴 · 无 · 用 · 形 · 实 · 非 · 知 · 因
- **对偶**: `oooxooxx` · 19
- **古文**: **窥** — 《说文》"窥, 小视也"; 形 + 知 + 因 三阳 = 窥 (窥见·见知)
- **现代汉语**: 唯形声·知行·因果 三轴留阳, 余 5 轴皆显化。
- **英语**: Three yang axes: form-sound, know-act, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 4,7,8
- **Why**: 形 + 知 + 因 守, 其余 5 轴 (阴·无·用·实·非) 翻。"形象仍清, 心仍知, 因尚未到果", 而极性·存在·派生·语义·判断皆翻。

### `xxxoxxox` · 237

**Subtitle**: 2 阳侧 · 形 · 知

- **(X, X)**: (xxxo, xxox)
- **分解**: 阴 · 无 · 用 · 形 · 实 · 非 · 知 · 果
- **对偶**: `oooxooxo` · 18
- **古文**: **观** — 《大学》"观天下莫不有美"; 形 + 知 双阳 = 观 (易经"观"卦: 观天之道, 执天之行)
- **现代汉语**: 唯形声·知行 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: form-sound and know-act. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 4,7 / d(⊤⁸)=6
- **Why**: 形 + 知 守。"形象可见 + 心知"两轴守住, 其余 6 轴皆已显化。

### `xxxoxxxo` · 238  *[true X²]*

**Subtitle**: 2 阳侧 · 形 · 因

- **(X, X)**: (xxxo, xxxo)  ← true X² (左右半相等)
- **分解**: 阴 · 无 · 用 · 形 · 实 · 非 · 行 · 因
- **对偶**: `oooxooox` · 17
- **古文**: **见** — 《周易·系辞》"是故见乃谓之象"; 形声 + 因果 双阳 = 见 (表达与起源的同侧守); [X² 4↔8 阳守]
- **现代汉语**: 高低半皆 xxxo — bit 4 与 8 (形声·因果) 同步留阳, 其余 6 轴皆阴。X² 配对第 4 对单留。
- **英语**: Two yang axes: form-sound and cause-effect. The 4th X² pair (form ↔ cause) self-resonates on the yang side.
- **形式逻辑**: |y|₁ = 6 / true X² (high=low=xxxo) / 238 = 17×14 (X² 对角元) / d(⊤⁸)=6, d(⊥⁸)=2
- **Why**: 16 个 X² 对角元第 15 个 (h=14)。bit 4 (形声) 与 bit 8 (因果) 同步留阳 — X² 配对 (1↔5, 2↔6, 3↔7, **4↔8**) 第 4 对单独守阳。哲学意涵: "形" (本体表达) 与 "因" (实用起源) 是 X² 同源回声; 此码即唯此两轴守源。对偶 #17 反之 (两轴单独翻为声·果)。

### `xxxoxxxx` · 239

**Subtitle**: 1 阳侧 · 形

- **(X, X)**: (xxxo, xxxx)
- **分解**: 阴 · 无 · 用 · 形 · 实 · 非 · 行 · 果
- **对偶**: `oooxoooo` · 16
- **古文**: **形** — 《易·系辞》"形而上者谓之道, 形而下者谓之器"; 六书"形声"之"形"
- **现代汉语**: 唯形声一轴留阳, 余 7 轴皆阴。"形"是阴海中唯一留住的可见根。
- **英语**: Single yang remnant on form-sound axis. Only the visible form holds in the near-yin sea.
- **形式逻辑**: |y|₁ = 7 / yang 仅 bit 4 / d(⊤⁸)=7, d(⊥⁸)=1 / 单点阳留存 8 元之一
- **Why**: 8 个"单点阳留存"中"表达根"的一个: 在万象皆显化的近极阴中, 仅 "形" 还守住。对偶 #16 是 weight 1 (仅形声翻为声)。两者构成"形"与"声"的对偶。

### `xxxxoooo` · 240  *[comp-palindrome]*

**Subtitle**: 4 阴侧 · 阴 · 无 · 用 · 声

- **(X, X)**: (xxxx, oooo)
- **分解**: 阴 · 无 · 用 · 声 · 名 · 是 · 知 · 因
- **对偶**: `ooooxxxx` · 15
- **古文**: **否** — 《周易》否卦"天地不交而万物不通"; 类否系 (本体阴·实用阳); NOT/阻塞算子; 与 #15 泰 形成易经经典对 [K.4 双重身份, 从 #68 迁此]
- **现代汉语**: **否** — 类否卦, 本体类全阴·实用类全阳 (天地不交); NOT/阻塞算子双重身份; 与 #15 泰 形成易经经典对 (泰否相反, 否极泰来)。
- **英语**: Ontology fully yin, pragmatics fully yang — the "theory manifest, practice pristine" cleavage. Inverted step function.
- **形式逻辑**: |y|₁ = 4 / Walsh W₃ ⊕ 1 (反阶跃函数) / comp-palindrome / d(⊤⁸)=d(⊥⁸)=4
- **Why**: 前 4 本体类轴 (阴阳·有无·体用·形声) 全阴, 后 4 实用类轴 (名实·是非·知行·因果) 全阳。15 (类泰) 的对偶, 反向阶跃函数。哲学意涵: 类似《易》否卦 "天地不交而万物不通" — 本体全沉 (天降为地)、实用全升 (地升为天), 二者错位。comp-palindrome: 配对轴 (1↔8, 2↔7, 3↔6, 4↔5) 各取相反侧 — (阴·因), (无·知), (用·是), (声·名), 每对一阴一阳。

### `xxxxooox` · 241

**Subtitle**: 3 阳侧 · 名 · 是 · 知

- **(X, X)**: (xxxx, ooox)
- **分解**: 阴 · 无 · 用 · 声 · 名 · 是 · 知 · 果
- **对偶**: `ooooxxxo` · 14
- **古文**: **决** — 《说文》"决, 行流也" (引申决断); 名 + 是 + 知 三阳 = 决 (决断·判定)
- **现代汉语**: 唯名实·是非·知行 三轴留阳, 余 5 轴 (含本体全沉) 皆阴。
- **英语**: Three yang axes: name-reality, right-wrong, know-act. Ontology fully yin; pragmatics holds three-of-four.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 5,6,7 / d(⊤⁸)=5
- **Why**: bit 5,6,7 连续 (实用前三) 留阳。即"名 + 是 + 知"守, 即实用类除因果外全守; 而本体类全沉到阴 + 因翻为果。一种"形上全失, 心言守, 唯果到来"的态。

### `xxxxooxo` · 242

**Subtitle**: 3 阳侧 · 名 · 是 · 因

- **(X, X)**: (xxxx, ooxo)
- **分解**: 阴 · 无 · 用 · 声 · 名 · 是 · 行 · 因
- **对偶**: `ooooxxox` · 13
- **古文**: **凭** — 《广韵》"凭, 倚也"; 名 + 是 + 因 三阳 = 凭 (凭据)
- **现代汉语**: 唯名实·是非·因果 三轴留阳, 余 5 轴皆阴。
- **英语**: Three yang axes: name-reality, right-wrong, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 5,6,8
- **Why**: 名 + 是 + 因 守, 即"名清、心是、因尚未到果"守住, 而本体类全沉 + 实用的知行已翻成行。一种"言守心是, 而事已动"的态。

### `xxxxooxx` · 243

**Subtitle**: 2 阳侧 · 名 · 是

- **(X, X)**: (xxxx, ooxx)
- **分解**: 阴 · 无 · 用 · 声 · 名 · 是 · 行 · 果
- **对偶**: `ooooxxoo` · 12
- **古文**: **当** — 《荀子·正名》"名当则正"; 名 + 是 双阳 = 当 (名实当, 名家"循名责实")
- **现代汉语**: 唯名实·是非 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: name-reality and right-wrong. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 5,6 / d(⊤⁸)=6
- **Why**: 名 + 是 守 — 即"语言命名 + 肯定判断"两个最稳的实用轴守住, 而本体全沉 + 实用末三 (知行·因果) + 实用首 (名实已合) 等皆翻。"心言守正, 形上全失, 事已动"。

### `xxxxoxoo` · 244

**Subtitle**: 3 阳侧 · 名 · 知 · 因

- **(X, X)**: (xxxx, oxoo)
- **分解**: 阴 · 无 · 用 · 声 · 名 · 非 · 知 · 因
- **对偶**: `ooooxoxx` · 11
- **古文**: **史** — 《说文》"史, 记事者也"; 名 + 知 + 因 三阳 = 史 (历史·名实之因)
- **现代汉语**: 唯名实·知行·因果 三轴留阳, 余 5 轴皆阴。
- **英语**: Three yang axes: name-reality, know-act, cause-effect.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 5,7,8
- **Why**: 名 + 知 + 因 守, 其余 5 轴翻。"名清 + 心知 + 因 (果未到)"守住, 而本体全沉 + 心非 (是非翻非) — 心知言明, 但判断已转否。

### `xxxxoxox` · 245

**Subtitle**: 2 阳侧 · 名 · 知

- **(X, X)**: (xxxx, oxox)
- **分解**: 阴 · 无 · 用 · 声 · 名 · 非 · 知 · 果
- **对偶**: `ooooxoxo` · 10
- **古文**: **识** — 《说文》"识, 知也"; 名 + 知 双阳 = 识 (《大学》"致知"; 名而知之即识)
- **现代汉语**: 唯名实·知行 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: name-reality and know-act. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 5,7 / d(⊤⁸)=6
- **Why**: 名 + 知 守。"言明 + 心知"两轴守住, 其余 6 轴皆已显化, 包括 心非 (是非翻) 与 因果 (翻为果)。"心知言明而其余皆失"。

### `xxxxoxxo` · 246

**Subtitle**: 2 阳侧 · 名 · 因

- **(X, X)**: (xxxx, oxxo)
- **分解**: 阴 · 无 · 用 · 声 · 名 · 非 · 行 · 因
- **对偶**: `ooooxoox` · 9
- **古文**: **故** — 《论语·为政》"温故而知新"; 名 + 因 双阳 = 故 (有名有因即故旧·缘由)
- **现代汉语**: 唯名实·因果 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: name-reality and cause-effect. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 5,8 / d(⊤⁸)=6
- **Why**: 名 + 因 守。"语言命名 + 因 (果未到)"守住, 其余 6 轴皆已显化。一种 X² 配对 (1↔5) 与 (4↔8) 的"半边" — 留住 5 和 8 两端。

### `xxxxoxxx` · 247

**Subtitle**: 1 阳侧 · 名

- **(X, X)**: (xxxx, oxxx)
- **分解**: 阴 · 无 · 用 · 声 · 名 · 非 · 行 · 果
- **对偶**: `ooooxooo` · 8
- **古文**: **名** — 《道德经》"名可名, 非常名"; 公孙龙"白马非马" 之"名"; 名家根本范畴
- **现代汉语**: 唯名实一轴留阳, 余 7 轴皆阴。"名"是阴海中唯一留住的语义之根。
- **英语**: Single yang remnant on name-reality axis. Only naming holds in the near-yin sea.
- **形式逻辑**: |y|₁ = 7 / yang 仅 bit 5 / d(⊤⁸)=7, d(⊥⁸)=1 / 单点阳留存 8 元之一
- **Why**: 8 个"单点阳留存"中"语义命名"的一个: 在万象皆显化的近极阴中, 仅 "名" 还守住。对偶 #8 是 weight 1 (仅名实翻为实)。两者构成"名"与"实"的对偶。

### `xxxxxooo` · 248

**Subtitle**: 3 阳侧 · 是 · 知 · 因

- **(X, X)**: (xxxx, xooo)
- **分解**: 阴 · 无 · 用 · 声 · 实 · 是 · 知 · 因
- **对偶**: `oooooxxx` · 7
- **古文**: **究** — 《说文》"究, 穷也"; 是 + 知 + 因 三阳 = 究 (究因·穷理; 《大学》"格物致知")
- **现代汉语**: 唯是非·知行·因果 三轴留阳, 余 5 轴皆阴。本体全沉 + 实用首 (实) 也已翻, 余末三守。
- **英语**: Three yang axes: right-wrong, know-act, cause-effect. The last three pragmatic axes hold; ontology and name-reality flip.
- **形式逻辑**: |y|₁ = 5 / yang 仅 bit 6,7,8 (实用末三连续)
- **Why**: bit 6,7,8 连续 — 实用末三轴 (是·知·因) 守, 即"判断 + 行为认知 + 起因"三轴持。本体类全沉 + 名实翻 (名→实) — 形上全失, 命名也失, 但心言行心仍守。

### `xxxxxoox` · 249

**Subtitle**: 2 阳侧 · 是 · 知

- **(X, X)**: (xxxx, xoox)
- **分解**: 阴 · 无 · 用 · 声 · 实 · 是 · 知 · 果
- **对偶**: `oooooxxo` · 6
- **古文**: **信** — 《论语·学而》"与朋友交而不信乎"; 是 + 知 双阳 = 信 (心之肯定与确知, 五常之一)
- **现代汉语**: 唯是非·知行 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: right-wrong and know-act. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 6,7 / d(⊤⁸)=6
- **Why**: 是 + 知 守。"心仍是仍知"守住 — 两个最内在的认知/判断维, 而本体全沉 + 名 + 因都已翻。

### `xxxxxoxo` · 250

**Subtitle**: 2 阳侧 · 是 · 因

- **(X, X)**: (xxxx, xoxo)
- **分解**: 阴 · 无 · 用 · 声 · 实 · 是 · 行 · 因
- **对偶**: `oooooxox` · 5
- **古文**: **由** — 《论语》"由也升堂矣"; 是 + 因 双阳 = 由 (有是有因即所由; 大学"君子无所不用其极")
- **现代汉语**: 唯是非·因果 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: right-wrong and cause-effect. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 6,8 / d(⊤⁸)=6
- **Why**: 是 + 因 守。"心是, 因尚未到果"守住, 其余 6 轴皆已显化。

### `xxxxxoxx` · 251

**Subtitle**: 1 阳侧 · 是

- **(X, X)**: (xxxx, xoxx)
- **分解**: 阴 · 无 · 用 · 声 · 实 · 是 · 行 · 果
- **对偶**: `oooooxoo` · 4
- **古文**: **是** — 《说文》"是, 直也"; 庄子《齐物论》"果有彼是乎哉"; 程朱"求是"
- **现代汉语**: 唯是非一轴留阳, 余 7 轴皆阴。"是"是阴海中唯一留住的肯定。
- **英语**: Single yang remnant on right-wrong axis. Only affirmation holds in the near-yin sea.
- **形式逻辑**: |y|₁ = 7 / yang 仅 bit 6 / d(⊤⁸)=7, d(⊥⁸)=1 / 单点阳留存 8 元之一
- **Why**: 8 个"单点阳留存"中"肯定判断"的一个: 在万象皆显化的近极阴中, 仅 "是" 还守住。对偶 #4 是 weight 1 (仅是非翻为非)。两者构成"是"与"非"的对偶。

### `xxxxxxoo` · 252

**Subtitle**: 2 阳侧 · 知 · 因

- **(X, X)**: (xxxx, xxoo)
- **分解**: 阴 · 无 · 用 · 声 · 实 · 非 · 知 · 因
- **对偶**: `ooooooxx` · 3
- **古文**: **智** — 《说文》"智, 识词也"; 知 + 因 双阳 = 智 (《孟子》"是非之心, 智也"; 五常)
- **现代汉语**: 唯知行·因果 两轴留阳, 余 6 轴皆阴。
- **英语**: Two yang axes: know-act and cause-effect. Six axes flip.
- **形式逻辑**: |y|₁ = 6 / yang 仅 bit 7,8 (实用末两轴)
- **Why**: 知 + 因 守 — 实用最末两轴 (心知 + 起因) 守住, 其余 6 轴皆已显化。一种"心知未行, 因未到果, 余皆显"的近极阴。

### `xxxxxxox` · 253

**Subtitle**: 1 阳侧 · 知

- **(X, X)**: (xxxx, xxox)
- **分解**: 阴 · 无 · 用 · 声 · 实 · 非 · 知 · 果
- **对偶**: `ooooooxo` · 2
- **古文**: **知** — 《大学》"致知在格物"; 王阳明"良知"; 论语"知者不惑"
- **现代汉语**: 唯知行一轴留阳, 余 7 轴皆阴。"知"是阴海中唯一留住的认知。
- **英语**: Single yang remnant on know-act axis. Only knowing holds in the near-yin sea.
- **形式逻辑**: |y|₁ = 7 / yang 仅 bit 7 / d(⊤⁸)=7, d(⊥⁸)=1 / 单点阳留存 8 元之一
- **Why**: 8 个"单点阳留存"中"认知"的一个: 在万象皆显化的近极阴中, 仅 "知" 还守住。对偶 #2 是 weight 1 (仅知行翻为行)。两者构成"知"与"行"的对偶 — 王阳明"知行合一"在这一对极端中被拆分。

### `xxxxxxxo` · 254

**Subtitle**: 1 阳侧 · 因

- **(X, X)**: (xxxx, xxxo)
- **分解**: 阴 · 无 · 用 · 声 · 实 · 非 · 行 · 因
- **对偶**: `ooooooox` · 1
- **古文**: **因** — 《说文》"因, 就也"; 佛家"因缘和合"; 因明学之"因"; 起源
- **现代汉语**: 唯因果一轴留阳, 余 7 轴皆阴。"因"是阴海中唯一留住的起源, 果尚未来。
- **英语**: Single yang remnant on cause-effect axis. Only cause holds; effect has not yet arrived.
- **形式逻辑**: |y|₁ = 7 / yang 仅 bit 8 / d(⊤⁸)=7, d(⊥⁸)=1 / 单点阳留存 8 元之一
- **Why**: 8 个"单点阳留存"中"起源"的一个: 在万象皆显化的近极阴中, 仅 "因" 还守住 (果尚未到)。对偶 #1 是 weight 1 (仅因果翻为果)。这是"因显" vs "果显"的最大对偶。

### `xxxxxxxx` · 255  *[true X² · palindrome]*

**Subtitle**: 纯阴极 · 全承载

- **(X, X)**: (xxxx, xxxx)  ← true X² (左右半相等)
- **分解**: 阴 · 无 · 用 · 声 · 实 · 非 · 行 · 果
- **对偶**: `oooooooo` · 0
- **古文**: 坤元 / 纯阴 / 万象尽承
- **现代汉语**: 八轴齐站承载侧, 形下尽显化的极点。
- **英语**: All eight dual axes on the receptive side; full articulation, the absolute negation.
- **形式逻辑**: ⊥⁸ / antipode 1⁸ ∈ F₂⁸ / Hamming 8 / palindrome ∩ true X² 之 trivial 对边
- **Why**: 8 个对偶轴都在承载侧。0 的 bitwise NOT, F₂⁸ 上距 0 最大的点 (Hamming d=8)。亦 palindrome 与 true X²: 它与 0 同属"最对称的四元组" (0, 102, 153, 255), 是 X² 表 (16×16) 的左上角对角元。哲学上: 一切对偶皆已显化承载, 即"道之全开"的极点 — 与 #0 (道之全收) 形成绝对的两极。



