# 生生不息新文档集

本目录是新的文档集暂存区。旧文档暂不删除；待本目录稳定后，再整体替换根 README、`formal/SSBX/README.md`、`义理/README.md` 与 web 索引入口。

## 两条入口

- [起步](00_start/README.md)：快速选择形式、义理或维护路径。
- [形式层](10_formal_形式/README.md)：从 Lean 代码、构建、信任边界、模块索引与 claim ledger 进入。
- [义理层](20_theory_义理/README.md)：从四级生成、义理分类、传统/现代论证与对齐主题进入。

英文读者先看 [overview.en.md](overview.en.md)。英文只维护总览，不作为第二套规范。

## 当前机器口径

- `lake build` 已恢复通过；当前仍有 unused `simp` argument warnings。
- live trust boundary 以 [trust-boundary](./_generated/trust-boundary.md) 为准。
- claim 状态以 [claim-index](./_generated/claim-index.md) 为准。
- 模块与声明索引以 [lean-index](./_generated/lean-index.md) 为准。

## 读法

1. 先看 [形式层信任边界](10_formal_形式/trust-boundaries.md)，确认哪些是 Lean theorem、ledger claim、模型计算或外推。
2. 再看 [义理索引](20_theory_义理/README.md)，按主题进入旧 `义理/` 的重排版本。
3. 查证时回到 [_generated](./_generated/)，不要从散文段落读取数量、状态或构建事实。
4. 需要追溯旧稿时，看 [archive-pointers.md](archive-pointers.md)；`史料/` 保持 frozen。

## 覆盖面

本目录不是四个顶层文件；主体在各分区内：

- `00_start/`：读者路径与范围。
- `10_formal_形式/`：形式化、模块簇、信任边界、构建。
- `20_theory_义理/`：旧义理文档的分类重排。
- `30_crosswalk_互证/`：Lean 与义理互证。
- `40_reference_参考/`：算子、字根、六表、字文与术语。
- `50_maintenance/`：生成、检查、发布与归档策略。
- `_generated/`：脚本生成的事实索引。

## 维护原则

- 一个事实只保留一个权威来源：Lean/ledger 为形式事实，生成索引为可定位目录，人工文档只做解释和路径。
- 不在 README 里堆长表；长表进入 `_generated` 或 `40_reference_参考/`。
- 不把 `史料/` 改写成现规范；只记录它们被哪里取代。
