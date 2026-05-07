# 阅读次第

本页给 docs-next 义理区提供几条短路径。读者不必一次读完旧 `义理/` 长文；先确定目的，再沿相应路径进入。所有事实状态以 [../_generated/](../_generated/) 下索引、当前 Lean 源码和信任边界为准。

## 快速路径

适合第一次进入，只想知道整体骨架。

1. [核心框架](core-framework.md)：四级生成、六征、实虚史真、算子。
2. [A-G 映射](map-a-g.md)：看基础段如何分工。
3. [八衍总览](eight-expansions.md)：看同一骨架怎样展开到八个域。
4. [义理到 Lean](bridge-to-lean.md)：理解哪些话能说成已证，哪些只能说成解释。

读完后应能回答：本项目怎样从元、二分、四象、八卦进入算子、义理和形式证明。

## 形式路径

适合要检查证明、模块和 claim 强度的读者。

1. [形式与证明](formal-and-proof.md)。
2. [H-M 映射](map-h-m.md)。
3. [义理到 Lean](bridge-to-lean.md)。
4. [../_generated/lean-index.md](../_generated/lean-index.md)。
5. [../_generated/claim-index.md](../_generated/claim-index.md)。
6. [../_generated/trust-boundary.md](../_generated/trust-boundary.md)。

判断顺序：先找模块，再找 claim，再找边界。不要只凭旧文标题判断“已证明”。

## 传统路径

适合关心儒道佛、先秦和跨文明对照的读者。

1. [传统义理](traditions.md)。
2. [N-T 映射](map-n-t.md)。
3. [A-G 映射](map-a-g.md) 中 A、E、F。
4. [../archive-pointers.md](../archive-pointers.md)。
5. 旧文入口由 [../_generated/markdown-index.md](../_generated/markdown-index.md) 定位。

本路径只做结构对应。史料冻结，不在 docs-next 改写来源。

## 现代与对齐路径

适合关心 AI alignment、政治哲学、非道、经济博弈的读者。

1. [现代与对齐](modern-and-alignment.md)。
2. [N-T 映射](map-n-t.md) 中 O、R、T。
3. [U-Z 映射](map-u-z.md)。
4. [义理到 Lean](bridge-to-lean.md) 中 claim 与信任边界。

本路径的核心问题是：一个系统是否保生、共开、守中、可反身修正；若失败，失败点是目标、指标、权力、制度还是解释。

## 八衍路径

适合关心数学、逻辑、统计、几何、范畴、动力、心智、物理的读者。

1. [八衍总览](eight-expansions.md)。
2. [八衍与专题](extensions.md)。
3. [A-G 映射](map-a-g.md) 中 D、G。
4. [../_generated/lean-index.md](../_generated/lean-index.md) 中 `Foundation/Eight` 与 `Foundation/Modern`。

本路径要分清三种强度：学科直觉、结构同构、Lean 已检查。

## 写作者路径

适合继续扩写 docs-next 的维护者。

1. 先查 [../_generated/markdown-index.md](../_generated/markdown-index.md)，确认旧文入口和标题。
2. 再查 [../_generated/lean-index.md](../_generated/lean-index.md)，确认是否有形式模块。
3. 对强 claim 查 [../_generated/claim-index.md](../_generated/claim-index.md)。
4. 对自指、运行、公理查 [../_generated/trust-boundary.md](../_generated/trust-boundary.md)。
5. 只在 `docs-next/20_theory_义理/*.md` 写短导览，不复制旧文长段，不改史料。

## 推荐顺序总表

| 目标 | 顺序 |
|---|---|
| 快速理解 | `core-framework` → `map-a-g` → `eight-expansions` → `bridge-to-lean` |
| 查证明 | `formal-and-proof` → `map-h-m` → generated indexes |
| 查传统 | `traditions` → `map-n-t` → archive pointers |
| 查现代 | `modern-and-alignment` → `map-u-z` → claim/trust indexes |
| 查八衍 | `eight-expansions` → `extensions` → Lean index |

阅读时遇到“必然、证明、完备、绝对、真道”等强词，立即转到 generated indexes；没有索引支持时，按义理解释处理。
