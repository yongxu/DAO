/-
Numbered-sense syntax for compact wenyan expressions.

The internal tree records operator application, but the surface keeps the
unparenthesized wenyan order. This is needed for cases like `生生不息`, where
the two written `生` glyphs take different numbered senses.
-/
import SSBX.Text.Completeness

namespace SSBX.Text.SenseSyntax

open SSBX.Text.Glyph
open SSBX.Text.WenyanOperators
open SSBX.Text.Completeness

inductive SenseExpr where
  | token : GlyphSense -> SenseExpr
  | apply : SenseExpr -> SenseExpr -> SenseExpr
  | juxtapose : SenseExpr -> SenseExpr -> SenseExpr
  deriving DecidableEq, Repr

namespace SenseExpr

def surface : SenseExpr -> String
  | .token s => senseKey s
  | .apply f x => surface f ++ " " ++ surface x
  | .juxtapose x y => surface x ++ " " ++ surface y

end SenseExpr

def IsNegationOperator (s : GlyphSense) : Prop :=
  s ∈ (operatorEntry .N_1).forms

def shengshengBuxiForms : List GlyphSense :=
  [«生2», «生3», «不1», «息1»]

def shengshengBuxiExpr : SenseExpr :=
  .juxtapose
    (.apply (.token «生2») (.token «生3»))
    (.apply (.token «不1») (.token «息1»))

def ValidSenseSyntax (forms : List GlyphSense) : Prop :=
  forms = shengshengBuxiForms ∧
    RegisteredForms forms ∧
    «生2».kind = LexKind.operator ∧
    «生3».kind = LexKind.generated ∧
    «生2» ≠ «生3» ∧
    IsNegationOperator «不1» ∧
    SenseExpr.surface shengshengBuxiExpr = "生2 生3 不1 息1"

theorem sheng2_is_operator : «生2».kind = LexKind.operator := rfl

theorem sheng3_is_generated : «生3».kind = LexKind.generated := rfl

theorem sheng2_ne_sheng3 : «生2» ≠ «生3» := by
  native_decide

theorem bu1_is_negation_operator : IsNegationOperator «不1» := by
  unfold IsNegationOperator
  change «不1» ∈ [«不1»]
  simp

theorem shengsheng_buxi_surface :
    SenseExpr.surface shengshengBuxiExpr = "生2 生3 不1 息1" := by
  rfl

theorem shengsheng_buxi_forms_registered :
    RegisteredForms shengshengBuxiForms := by
  native_decide

theorem shengsheng_buxi_sense_syntax_valid :
    ValidSenseSyntax shengshengBuxiForms := by
  exact ⟨rfl, shengsheng_buxi_forms_registered, sheng2_is_operator,
    sheng3_is_generated, sheng2_ne_sheng3, bu1_is_negation_operator,
    shengsheng_buxi_surface⟩

theorem sheng_polysemy_available :
    RegisteredSense «生1» ∧ RegisteredSense «生2» ∧ RegisteredSense «生3» ∧
      «生1» ≠ «生2» ∧ «生2» ≠ «生3» :=
  sheng_polysemous

end SSBX.Text.SenseSyntax
