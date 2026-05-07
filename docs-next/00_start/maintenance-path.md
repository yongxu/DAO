# 维护路径

适合准备修改代码、生成图谱或继续重写文档的维护者。

## 顺序

1. 先运行 `git status --short`，确认没有误覆盖别人改动。
2. 修改 Lean 后先跑 `/Users/ren/.elan/bin/lake build`。
3. 修改文档源或索引规则后跑 `python3 scripts/docs_next.py build --out docs-next/_generated --clean`。
4. 提交前跑 `python3 scripts/docs_next.py check --out docs-next/_generated --strict`。
5. 按 `../50_maintenance/release-checklist.md` 做最后核对。

## 边界

不要手改 `_generated/` 来掩盖脚本问题；应修脚本或源文件，然后重新生成。
