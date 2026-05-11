/-
# RootRuleExamples -- small checked corpus for the root-language roadmap

These are not parser tests. They are target semantic examples for the later
Wen/Lisp interpreter:

* "Dao returns to Dao" is origin visibility.
* "truth can turn false and false can turn true" is a duplicated toggle.
* missing context and quoting report loss.
* adding an axis needs nonzero, finite-span independence, and projectability.
-/

import SSBX.Foundation.Wen.RootRuleKernel
import SSBX.Foundation.Wen.R8AxisIndependence

namespace SSBX.Foundation.Wen.RootRuleExamples

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Wen.R8ProjectionCalculus
open SSBX.Foundation.Wen.RootRuleKernel
open SSBX.Foundation.Wen.R8AxisIndependence

/-! ## Example forms -/

/-- "Dao returns to Dao": the origin cell. -/
def daoReturnsDao : CoreForm :=
  .atom R8.origin

/-- A representative truth-axis toggle. -/
def truthToggle : CoreForm :=
  .atom R8.imprint_mask

/-- Toggle the same axis twice. -/
def truthToggleTwice : CoreForm :=
  .apply truthToggle truthToggle

/-- A missing name, used to show context loss. -/
def missingContext : CoreForm :=
  .lookup "未定名"

/-! ## Checked readings -/

theorem dao_returns_dao_visible :
    CoreForm.visible emptyEnv daoReturnsDao = R8.origin := rfl

theorem truth_toggle_twice_returns_dao :
    CoreForm.visible emptyEnv truthToggleTwice = R8.origin := by
  exact CoreForm.duplicated_apply_returns_origin emptyEnv R8.imprint_mask

theorem missing_context_reports_loss :
    CoreForm.loss emptyEnv missingContext = .context := rfl

theorem quote_reports_loss :
    CoreForm.loss emptyEnv (.quote truthToggle) = .higherOperator := rfl

theorem projected_extra_axis_reports_loss (c : R8) :
    lossOf (.projected c .extraAxis) = .extraAxis := rfl

/-! ## Axis examples -/

theorem imprint_mask_ne_origin :
    R8.imprint_mask ≠ R8.origin := by
  native_decide

/-- Candidate for adding the R7/R8 past-trace axis in an empty prior frame. -/
def yinAxisCandidate : AxisCandidate where
  mask := R8.imprint_mask
  role := .yin
  prior := []
  projectable := true

theorem yin_axis_candidate_appropriate :
    AxisAppropriateBySpan yinAxisCandidate := by
  exact nonzero_empty_prior_appropriate R8.imprint_mask .yin imprint_mask_ne_origin

theorem yin_axis_candidate_to_old_interface :
    AxisAppropriate yinAxisCandidate.toAxisSpec :=
  axisAppropriateBySpan_to_AxisAppropriate yinAxisCandidate
    yin_axis_candidate_appropriate

/-- Summary for the checked example corpus. -/
theorem root_rule_examples_summary :
    CoreForm.visible emptyEnv daoReturnsDao = R8.origin
    ∧ CoreForm.visible emptyEnv truthToggleTwice = R8.origin
    ∧ CoreForm.loss emptyEnv missingContext = .context
    ∧ CoreForm.loss emptyEnv (.quote truthToggle) = .higherOperator
    ∧ AxisAppropriateBySpan yinAxisCandidate
    ∧ AxisAppropriate yinAxisCandidate.toAxisSpec := by
  exact
    ⟨ dao_returns_dao_visible
    , truth_toggle_twice_returns_dao
    , missing_context_reports_loss
    , quote_reports_loss
    , yin_axis_candidate_appropriate
    , yin_axis_candidate_to_old_interface
    ⟩

end SSBX.Foundation.Wen.RootRuleExamples
