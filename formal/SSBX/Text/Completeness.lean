/-
Text completeness theorems connecting the roster and operator catalogue to glyph senses.
-/
import SSBX.Text.WenyanOperators

namespace SSBX.Text.Completeness

open SSBX.Text.Glyph
open SSBX.Text.WenyanOperators
open SSBX.Roster

theorem roster_text_complete (s : SSBX.Roster.Symbol) : CoveredSymbol s := by
  cases s with
  | atom a => cases a <;> native_decide
  | generated g => cases g <;> native_decide
  | primitive p => cases p <;> native_decide
  | recursive r => cases r <;> native_decide
  | pending u => cases u <;> native_decide

theorem primitive_aliases_complete (p : PrimName) : CoveredPrimitiveAlias p := by
  cases p <;> native_decide

theorem primitive_aliases_keep_formal_interfaces :
    symbolGlyphSenses (Symbol.primitive .«域») = [formalSense "域"] ∧
      primitiveGlyphAliases .«域» = textToSenses "域" ∧
      primitiveGlyphAliases .«格» = textToSenses "格" ∧
      primitiveGlyphAliases .«权» = textToSenses "权" ∧
      primitiveGlyphAliases .«生» = textToSenses "生" ∧
      primitiveGlyphAliases .«校» = textToSenses "校" := by
  native_decide

theorem primitive_core_interfaces_are_five :
    primitiveCoreInterface .«域» = PrimitiveCoreInterface.domain ∧
      primitiveCoreInterface .«格» = PrimitiveCoreInterface.structure ∧
      primitiveCoreInterface .«权» = PrimitiveCoreInterface.weight ∧
      primitiveCoreInterface .«生» = PrimitiveCoreInterface.generation ∧
      primitiveCoreInterface .«校» = PrimitiveCoreInterface.audit := by
  native_decide

theorem derived_interfaces_complete (i : DerivedInterface) :
    CoveredDerivedInterface i := by
  cases i <;> native_decide

theorem derived_interfaces_rhs_use_single_glyph_operators (i : DerivedInterface) :
    RhsUsesSingleGlyphOperators i := by
  cases i <;> native_decide

theorem derived_interfaces_use_single_glyph_operator_combinations :
    DerivedInterface.assignment .I_F = "I_F := 域" ∧
      DerivedInterface.assignment .D_KΓ = "D_KΓ := 格权" ∧
      DerivedInterface.assignment .Ω = "Ω := 权" ∧
      DerivedInterface.assignment .«Φ_形» = "Φ_形 := 校形" ∧
      DerivedInterface.assignment .«Φ_因» = "Φ_因 := 校因" ∧
      DerivedInterface.assignment .«Φ_结» = "Φ_结 := 校结" ∧
      DerivedInterface.assignment .«Π_开» = "Π_开 := 校权" ∧
      DerivedInterface.assignment .Attention = "Attention := 权" := by
  native_decide

theorem operator_table_complete (id : OperatorId) : CoveredOperator id :=
  SSBX.Text.WenyanOperators.operator_table_complete id

theorem sheng_polysemous :
    RegisteredSense «生1» ∧ RegisteredSense «生2» ∧ RegisteredSense «生3» ∧
      «生1» ≠ «生2» ∧ «生2» ≠ «生3» := by
  native_decide

theorem zhi_is_operator :
    RegisteredSense «之1» ∧ «之1».kind = LexKind.operator := by
  native_decide

theorem zhi_has_particle_sense :
    RegisteredSense «之2» ∧ «之2».kind = LexKind.particle := by
  native_decide

theorem zhi_operator_entry :
    (operatorEntry .S_1).forms = [«之1»] := by
  native_decide

theorem truth_polysemous :
    RegisteredSense «真1» ∧ RegisteredSense «真2» ∧ «真1» ≠ «真2» := by
  native_decide

theorem core_senses_registered :
    RegisteredSense «自1» ∧ RegisteredSense «由1» ∧ RegisteredSense «似1» ∧
      RegisteredSense «可1» ∧ RegisteredSense «行1» ∧ RegisteredSense «校1» ∧
      RegisteredSense «合1» ∧ RegisteredSense «法1» ∧ RegisteredSense «洽1» ∧
      RegisteredSense «复1» ∧ RegisteredSense «和1» := by
  native_decide

theorem core_particle_senses_registered :
    RegisteredSense «者1» ∧ RegisteredSense «也1» ∧ RegisteredSense «于1» ∧
      RegisteredSense «於1» ∧ RegisteredSense «未1» ∧ RegisteredSense «已1» := by
  native_decide

theorem isness_single_glyph_operators_registered :
    RegisteredSense «是1» ∧ RegisteredSense «系1» ∧ RegisteredSense «之1» ∧
      RegisteredSense «的1» ∧ RegisteredSense «地1» ∧ RegisteredSense «于1» ∧
      RegisteredSense «所1» ∧ RegisteredSense «有1» ∧ RegisteredSense «无1» ∧
      RegisteredSense «为1» ∧ RegisteredSense «然1» ∧ RegisteredSense «者1» ∧
      RegisteredSense «也1» ∧
      «是1».kind = LexKind.operator ∧
      «系1».kind = LexKind.operator ∧
      «之1».kind = LexKind.operator ∧
      «的1».kind = LexKind.operator ∧
      «地1».kind = LexKind.operator ∧
      «然1».kind = LexKind.operator := by
  native_decide

theorem added_particle_operator_entries :
    (operatorEntry .S_13).forms = [«者1»] ∧
      (operatorEntry .S_14).forms = [«也1»] ∧
      (operatorEntry .S_15).forms = [«于1», «於1»] ∧
      (operatorEntry .S_16).forms = [«所1»] ∧
      (operatorEntry .S_17).forms = [«未1»] ∧
      (operatorEntry .S_18).forms = [«已1»] := by
  native_decide

theorem core_operator_entries_use_numbered_senses :
    (operatorEntry .I_4).forms = [«是1»] ∧
      (operatorEntry .I_7).forms = [«合1»] ∧
      (operatorEntry .F_9).forms = [«行1»] ∧
      (operatorEntry .M_5).forms = [«可1»] ∧
      (operatorEntry .M_6).forms = [«能1»] ∧
      (operatorEntry .M_2).forms = [«或1»] ∧
      (operatorEntry .K_2).forms = [«由1»] ∧
      (operatorEntry .K_3).forms = [«自1»] ∧
      (operatorEntry .S_6).forms = [«然1»] ∧
      (operatorEntry .S_7).forms = [«故1»] ∧
      (operatorEntry .H_5).forms = [«法1»] ∧
      (operatorEntry .Y_18).forms = [«和1»] ∧
      (operatorEntry .Z_32).forms = [«自1»] := by
  native_decide

theorem core_generated_sense_formulas :
    senseFormulaOfGenerated .«合法» = "合1 + 法1" ∧
      senseFormulaOfGenerated .«自由» = "自1 + 由1" ∧
      senseFormulaOfGenerated .«自似» = "自1 + 似1" ∧
      senseFormulaOfGenerated .«可校» = "可1 + 校1" ∧
      senseFormulaOfGenerated .«所是» = "所1 + 是1" ∧
      senseFormulaOfGenerated .«自洽» = "自1 + 洽1" ∧
      senseFormulaOfGenerated .«可行» = "可1 + 行1" ∧
      senseFormulaOfGenerated .«复生» = "复1 + 生1" ∧
      senseFormulaOfGenerated .«生生不息» = "生2 生3 不1 息1" ∧
      senseFormulaOfRecursive .«自由» = "自1 + 由1 + 可识 + 可择 + 可达 + 非坏迫" ∧
      senseFormulaOfRecursive .«真» =
        "真1(P,Γ) := P 合于 所是(Γ); 真2 := 度期周 + 审校不败" := by
  native_decide

end SSBX.Text.Completeness
