/-
Context-sensitive readings for polysemous wenyan glyphs.

This layer sits between raw glyph senses (`GlyphSense`) and catalogue operators
(`OperatorId`). It does not extend the executable baguaWen parser; it records
how a surface glyph such as 之 can expose multiple readings, then lets syntax
and expected type cues select a reading when the context is strong enough.
-/
import SSBX.Text.WenyanOperators

namespace SSBX.Text.OperatorReadings

open SSBX.Text.Glyph
open SSBX.Text.WenyanOperators

inductive Fixity where
  | prefix
  | infix
  | suffix
  | construction
  deriving DecidableEq, Repr

inductive ContextCue where
  | betweenNominals
  | afterVerb
  | beforeMotionVerb
  | beforeYou
  | expectedFunction
  | expectedProp
  | expectedPath
  deriving DecidableEq, Repr

inductive ReadingStatus where
  | catalogue
  | contextual
  | construction
  | pending
  deriving DecidableEq, Repr

structure OperatorReading where
  sense : GlyphSense
  operator? : Option OperatorId
  label : String
  gloss : String
  fixity : Fixity
  cues : List ContextCue
  status : ReadingStatus
  deriving DecidableEq, Repr

def readingMatches (ctx : List ContextCue) (r : OperatorReading) : Bool :=
  ctx.any (fun c => r.cues.contains c)

def «之属格读法» : OperatorReading where
  sense := «之1»
  operator? := some .S_1
  label := "之1"
  gloss := "属格 / 投影 / function application"
  fixity := .infix
  cues := [.betweenNominals, .expectedFunction]
  status := .catalogue

def «之代指读法» : OperatorReading where
  sense := «之2»
  operator? := none
  label := "之2"
  gloss := "代指 / 虚词承接 / discourse anaphora"
  fixity := .suffix
  cues := [.afterVerb]
  status := .contextual

def «之路径读法» : OperatorReading where
  sense := «之3»
  operator? := none
  label := "之3"
  gloss := "生成来源 / 路径所从 / source binding"
  fixity := .infix
  cues := [.beforeMotionVerb, .expectedPath]
  status := .contextual

def «之又构式» : OperatorReading where
  sense := «之1»
  operator? := none
  label := "之又"
  gloss := "迭代构式 marker, as in X 之又 X"
  fixity := .construction
  cues := [.beforeYou]
  status := .construction

def «或存在读法» : OperatorReading where
  sense := «或1»
  operator? := some .Q_5
  label := "或1-Q"
  gloss := "不定 / 存在量化"
  fixity := .prefix
  cues := [.expectedProp]
  status := .catalogue

def «或可能读法» : OperatorReading where
  sense := «或1»
  operator? := some .M_2
  label := "或1-M"
  gloss := "可能模态"
  fixity := .prefix
  cues := [.expectedProp]
  status := .catalogue

def «故因果读法» : OperatorReading where
  sense := «故1»
  operator? := some .K_1
  label := "故1-K"
  gloss := "因果根据 / because-therefore"
  fixity := .infix
  cues := [.expectedProp]
  status := .catalogue

def «故序贯读法» : OperatorReading where
  sense := «故1»
  operator? := some .S_7
  label := "故1-S"
  gloss := "证明步 / therefore connective"
  fixity := .infix
  cues := [.expectedProp]
  status := .catalogue

def «自来源读法» : OperatorReading where
  sense := «自1»
  operator? := some .K_3
  label := "自1-K"
  gloss := "始于 / from"
  fixity := .prefix
  cues := [.expectedPath]
  status := .catalogue

def «自反身读法» : OperatorReading where
  sense := «自1»
  operator? := some .Z_32
  label := "自1-Z"
  gloss := "自身 / reflexive identity"
  fixity := .prefix
  cues := [.expectedFunction]
  status := .catalogue

def readingsForGlyph : Glyph -> List OperatorReading
  | "之" => [«之属格读法», «之代指读法», «之路径读法», «之又构式»]
  | "或" => [«或存在读法», «或可能读法»]
  | "故" => [«故因果读法», «故序贯读法»]
  | "自" => [«自来源读法», «自反身读法»]
  | _ => []

def contextualReadings (glyph : Glyph) (ctx : List ContextCue) : List OperatorReading :=
  let rs := readingsForGlyph glyph
  if ctx.isEmpty then rs else rs.filter (readingMatches ctx)

def uniquelyResolved (glyph : Glyph) (ctx : List ContextCue) : Prop :=
  (contextualReadings glyph ctx).length = 1

instance uniquelyResolvedDecidable (glyph : Glyph) (ctx : List ContextCue) :
    Decidable (uniquelyResolved glyph ctx) := by
  unfold uniquelyResolved
  infer_instance

theorem zhi_between_nominals_unique :
    uniquelyResolved "之" [.betweenNominals] := by
  native_decide

theorem zhi_after_verb_unique :
    uniquelyResolved "之" [.afterVerb] := by
  native_decide

theorem zhi_before_motion_unique :
    uniquelyResolved "之" [.beforeMotionVerb] := by
  native_decide

theorem zhi_before_you_unique :
    uniquelyResolved "之" [.beforeYou] := by
  native_decide

theorem zhi_no_context_ambiguous :
    ¬ uniquelyResolved "之" [] := by
  native_decide

theorem huo_prop_context_still_ambiguous :
    ¬ uniquelyResolved "或" [.expectedProp] := by
  native_decide

end SSBX.Text.OperatorReadings
