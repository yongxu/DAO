/-
# RootRuleDemoInterpreter -- minimal Wen surface into RootRuleKernel

This is a deliberately small interpreter skeleton. It maps a few fixed Chinese
example sentences into `CoreForm`; all other text is treated as a named lookup
and therefore carries context loss until a real parser/interpreter is supplied.

## 状态 (Status, 2026-05-17): DEPRECATED — teaching artifact only

本模块是 5 个 evaluator 中唯一无外部用户的真冗余者（91 LOC, 0 external refs,
仅在 `SSBX.lean` 被 import 作 PoC 展示）。其下 8 个 `native_decide` example
作为 demo 价值保留，但**不应用于新代码**。

迁移路径（canonical evaluators）:

| 用途 | 推荐 |
|---|---|
| `Tm → Value` (Lean-level eval) | `SSBX.Foundation.Wen.WenDefEval.denoteHex` (及兄弟 `denoteCell` / `denoteHexFun` 等) |
| `String → R8` (user-facing pipeline) | `SSBX.Foundation.Wen.WenEval.wenEval` (经 YiInstr) |
| `root rule → R8` (projection) | `SSBX.Foundation.Wen.RootRuleKernel.CoreForm.eval` |

本模块仅用于 `RootRuleExamples` 例句的最小 wrapper，新接入请直接走上述
canonical 路径之一。详见 `samples/README.md`.
-/

import SSBX.Foundation.Wen.RootRuleExamples

namespace SSBX.Foundation.Wen.RootRuleDemoInterpreter

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Wen.R8ProjectionCalculus
open SSBX.Foundation.Wen.RootRuleKernel
open SSBX.Foundation.Wen.RootRuleExamples

/-! ## Demo parsing -/

/-- Minimal surface parser for the current example corpus.

DEPRECATED: 见模块头 `## 状态`. -/
@[deprecated "use WenDefEval.denoteHex (Tm→Value), WenEval.wenEval (String→R8),\
  or RootRuleKernel.CoreForm.eval (root rule→R8) instead; this is a teaching demo only"
  (since := "2026-05-17")]
def parseDemoCoreForm (text : String) : CoreForm :=
  if text = "道总归道" then
    daoReturnsDao
  else if text = "真可假假可真" then
    truthToggleTwice
  else if text = "加元" || text = "加爻" then
    .quote truthToggle
  else
    .project (.lookup text)

set_option linter.deprecated false in
/-- Demo rewrite keeps the text but passes through the normal-form boundary.

DEPRECATED: 见模块头 `## 状态`. -/
@[deprecated "use WenDefEval.denoteHex or WenEval.wenEval; see module header"
  (since := "2026-05-17")]
def demoRewrite (s : Sentence) : WenNormalForm :=
  { text := s.source }

set_option linter.deprecated false in
/-- Interpret demo normal forms through the root-rule kernel.

DEPRECATED: 见模块头 `## 状态`. -/
@[deprecated "use WenDefEval.denoteHex or WenEval.wenEval; for root-rule → R8 use RootRuleKernel.CoreForm.eval directly"
  (since := "2026-05-17")]
def demoInterpret (nf : WenNormalForm) : R8Semantics :=
  CoreForm.eval emptyEnv (parseDemoCoreForm nf.text)

set_option linter.deprecated false in
/-- Minimal concrete interpreter for example-corpus alignment.

DEPRECATED: 见模块头 `## 状态`. 推荐用 `WenDefEval.denoteHex` (Tm→Value)
或 `WenEval.wenEval` (String→R8) 作为 user-facing evaluator. -/
@[deprecated "use WenDefEval.denoteHex (Tm→Value) or WenEval.wenEval (String→R8); see RootRuleKernel.CoreForm.eval for root-rule path"
  (since := "2026-05-17")]
def demoInterpreter : WenR8Interpreter where
  rewrite := demoRewrite
  interpret := demoInterpret

/-! ## Checked example sentences

注意: 以下 8 个 theorem / example **保留**, 作为 demo 期 PoC 价值；
但 `demoInterpreter` 本身已 deprecated (见模块头). 故下方一律
`set_option linter.deprecated false in` 抑制 warn — 这只是文档保留, 非鼓励复用. -/

def daoSentence : Sentence := { source := "道总归道" }
def truthSentence : Sentence := { source := "真可假假可真" }
def addAxisSentence : Sentence := { source := "加爻" }
def unknownSentence : Sentence := { source := "未登记句" }

set_option linter.deprecated false in
theorem demo_dao_sentence_projects_origin :
    sentenceProjection demoInterpreter daoSentence = R8.origin := rfl

set_option linter.deprecated false in
theorem demo_truth_sentence_projects_origin :
    sentenceProjection demoInterpreter truthSentence = R8.origin := by
  exact truth_toggle_twice_returns_dao

set_option linter.deprecated false in
theorem demo_add_axis_sentence_reports_higher_operator_loss :
    sentenceProjectionLoss demoInterpreter addAxisSentence = .higherOperator := rfl

set_option linter.deprecated false in
theorem demo_unknown_sentence_reports_context_loss :
    sentenceProjectionLoss demoInterpreter unknownSentence = .context := rfl

set_option linter.deprecated false in
theorem demo_interpreter_has_projection_for_all_sentences :
    ∀ s : Sentence, ∃ c : R8, sentenceProjection demoInterpreter s = c :=
  sentence_has_r8_projection demoInterpreter

set_option linter.deprecated false in
theorem demo_interpreter_has_loss_for_all_sentences :
    ∀ s : Sentence, ∃ loss : ProjectionLoss, sentenceProjectionLoss demoInterpreter s = loss :=
  sentence_has_loss_ledger demoInterpreter

/-! ## Public summary -/

set_option linter.deprecated false in
theorem root_rule_demo_interpreter_summary :
    sentenceProjection demoInterpreter daoSentence = R8.origin
    ∧ sentenceProjection demoInterpreter truthSentence = R8.origin
    ∧ sentenceProjectionLoss demoInterpreter addAxisSentence = .higherOperator
    ∧ sentenceProjectionLoss demoInterpreter unknownSentence = .context
    ∧ (∀ s : Sentence, ∃ c : R8, sentenceProjection demoInterpreter s = c)
    ∧ (∀ s : Sentence, ∃ loss : ProjectionLoss,
        sentenceProjectionLoss demoInterpreter s = loss) := by
  exact
    ⟨ demo_dao_sentence_projects_origin
    , demo_truth_sentence_projects_origin
    , demo_add_axis_sentence_reports_higher_operator_loss
    , demo_unknown_sentence_reports_context_loss
    , demo_interpreter_has_projection_for_all_sentences
    , demo_interpreter_has_loss_for_all_sentences
    ⟩

end SSBX.Foundation.Wen.RootRuleDemoInterpreter
