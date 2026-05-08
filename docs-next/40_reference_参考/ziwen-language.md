# 字文语言

字文语言的完整未来规范在根目录 `ziwen-spec.md`。当前可执行 surface 子集是
`wenyan-surface`，状态账本见 `formal/SSBX/notes/wensurface-roadmap.md`。
本页只给新版文档中的读法和审计入口。

## 定位

字文语言是受控文本与形式结构之间的桥。它服务于：

- 字元、glyph、算子和读法的登记。
- 文言式程序、parser、interpreter 和 self-host 路线。
- 人读义理与 Lean 结构之间的可追踪表达。

它不等于自然语言全自动理解，也不等于传统文言的完整语法学。

## 相关入口

| 主题 | 入口 |
|---|---|
| 规范正文 | `ziwen-spec.md` |
| WenSurface 状态账本 | `formal/SSBX/notes/wensurface-roadmap.md` |
| WenSurface 语法扩展 spec | `formal/SSBX/notes/wensurface-syntax-spec.md` |
| 受控文规范 | `formal/SSBX/notes/baguaWen-spec.md` |
| parse-print 路线 | `formal/SSBX/notes/parse-print-roadmap.md` |
| 文言算子 | `operators.md` |
| 字元名册 | `glyphs-registry.md` |
| Lean 文层模块 | `../_generated/lean-index.md` 中 `Foundation/Wen` 与 `Text` |

## 分层读法

| 层 | 问题 |
|---|---|
| 字元层 | 哪些字或符号被登记 |
| 读法层 | 一个字在何处如何读 |
| 算子层 | 读法如何成为结构操作 |
| 句法层 | 文本如何被 parser 接收 |
| 执行层 | 可执行片段如何求值 |
| 自释层 | 文本、解释器和自描述如何互证 |

## 审计规则

- 先看 `../_generated/operator-index.md` 和 `../_generated/registry-index.md`。
- 再看 `Foundation/Wen` 与 `Text` 相关 Lean 模块。
- 若涉及 quine、自宿主或自解释，保留路线状态，不写成全系统已自证。
- 若涉及旧文「文道一也」，应同时参考 `../30_crosswalk_互证/claim-status.md`。
- 若涉及 `wenyan-surface`，区分完整 Ziwen v0 规范与当前可执行子集；catalogue-only 算子只能写成 `known-not-executable`。
