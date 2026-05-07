# 形式路径

适合想从 Lean 代码确认项目状态的读者。

## 顺序

1. 读 `../10_formal_形式/trust-boundaries.md`，先确认 axiom、opaque、partial boundary。
2. 读 `../10_formal_形式/build-and-verify.md`，确认构建命令与 warning 口径。
3. 读 `../_generated/lean-index.md`，按模块簇定位文件。
4. 读 `../_generated/claim-index.md`，确认 claim 是 machineChecked、ledgerDependent 还是 modelComputed。
5. 再进入 `Foundation/Wen`、`Foundation/Bagua`、`Truth/Model` 等专题页。

## 不要这样读

- 不要从旧 README 的 job 数或 theorem 数判断当前状态。
- 不要把图谱节点看成已证明 claim。
- 不要把 ledger-dependent claim 当作 Lean theorem。
