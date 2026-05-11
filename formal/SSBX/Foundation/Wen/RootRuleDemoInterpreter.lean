/-
# RootRuleDemoInterpreter -- minimal Wen surface into RootRuleKernel

This is a deliberately small interpreter skeleton. It maps a few fixed Chinese
example sentences into `CoreForm`; all other text is treated as a named lookup
and therefore carries context loss until a real parser/interpreter is supplied.
-/

import SSBX.Foundation.Wen.RootRuleExamples

namespace SSBX.Foundation.Wen.RootRuleDemoInterpreter

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Wen.R8ProjectionCalculus
open SSBX.Foundation.Wen.RootRuleKernel
open SSBX.Foundation.Wen.RootRuleExamples

/-! ## Demo parsing -/

/-- Minimal surface parser for the current example corpus. -/
def parseDemoCoreForm (text : String) : CoreForm :=
  if text = "道总归道" then
    daoReturnsDao
  else if text = "真可假假可真" then
    truthToggleTwice
  else if text = "加元" || text = "加爻" then
    .quote truthToggle
  else
    .project (.lookup text)

/-- Demo rewrite keeps the text but passes through the normal-form boundary. -/
def demoRewrite (s : Sentence) : WenNormalForm :=
  { text := s.source }

/-- Interpret demo normal forms through the root-rule kernel. -/
def demoInterpret (nf : WenNormalForm) : R8Semantics :=
  CoreForm.eval emptyEnv (parseDemoCoreForm nf.text)

/-- Minimal concrete interpreter for example-corpus alignment. -/
def demoInterpreter : WenR8Interpreter where
  rewrite := demoRewrite
  interpret := demoInterpret

/-! ## Checked example sentences -/

def daoSentence : Sentence := { source := "道总归道" }
def truthSentence : Sentence := { source := "真可假假可真" }
def addAxisSentence : Sentence := { source := "加爻" }
def unknownSentence : Sentence := { source := "未登记句" }

theorem demo_dao_sentence_projects_origin :
    sentenceProjection demoInterpreter daoSentence = R8.origin := rfl

theorem demo_truth_sentence_projects_origin :
    sentenceProjection demoInterpreter truthSentence = R8.origin := by
  exact truth_toggle_twice_returns_dao

theorem demo_add_axis_sentence_reports_higher_operator_loss :
    sentenceProjectionLoss demoInterpreter addAxisSentence = .higherOperator := rfl

theorem demo_unknown_sentence_reports_context_loss :
    sentenceProjectionLoss demoInterpreter unknownSentence = .context := rfl

theorem demo_interpreter_has_projection_for_all_sentences :
    ∀ s : Sentence, ∃ c : R8, sentenceProjection demoInterpreter s = c :=
  sentence_has_r8_projection demoInterpreter

theorem demo_interpreter_has_loss_for_all_sentences :
    ∀ s : Sentence, ∃ loss : ProjectionLoss, sentenceProjectionLoss demoInterpreter s = loss :=
  sentence_has_loss_ledger demoInterpreter

/-! ## Public summary -/

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
