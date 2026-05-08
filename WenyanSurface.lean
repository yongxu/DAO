/-
# wenyan-surface — CLI for the WenSurface interpreter

Reads a wenyan program from stdin or a single argv argument, runs it through
`SSBX.Foundation.Wen.WenSurface.wenyanInterp`, with Bool and finite carrier
fallbacks, and prints the result.

Examples:
  echo '推 一'         | wenyan-surface
  wenyan-surface '之又 推 乾'
  wenyan-surface '同 一 一'

This binary is parallel to (not a replacement for) the frozen baguaWen
22-token controlled IL parser. WenSurface speaks the surface language:
推/比/不/必/同/凡/損/损/益, hex consts 一/乾/坤/full King-Wen names,
bool 真/假, marker 之, construction 之又, and prefix-only binders 者/凡/令
over Hex variables. Grouping brackets `（ E ）` and `( E )` preserve AST
grouping and elaborate transparently.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd
import SSBX.Foundation.Wen.WenSurface.Coverage

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenSurface
open SSBX.Foundation.Wen.WenDefEval
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Text.OperatorSignatures

/-! ## Pretty-printing -/

private def yaoLine : Yao → String
  | .yang => "▬▬▬▬▬"
  | .yin  => "▬▬   ▬▬"

/-- Render a hexagram as 6 lines, top (y6) → bottom (y1). -/
private def hexDiagram (h : Hexagram) : String :=
  String.intercalate "\n"
    ["  " ++ yaoLine h.y6,
     "  " ++ yaoLine h.y5,
     "  " ++ yaoLine h.y4,
     "  " ++ yaoLine h.y3,
     "  " ++ yaoLine h.y2,
     "  " ++ yaoLine h.y1]

/-- Try to label a Hexagram with a familiar name. -/
private def hexLabel (h : Hexagram) : String :=
  if h = Hexagram.qian then " («乾»)"
  else if h = Hexagram.kun then " («坤»)"
  else if h = «一» then " («一»)"
  else ""

private def hexShow (h : Hexagram) : String :=
  let idx := (Hexagram.toIdx h).val
  s!"hex idx {idx}{hexLabel h}\n{hexDiagram h}"

private def hexBrief (h : Hexagram) : String :=
  s!"idx {(Hexagram.toIdx h).val}{hexLabel h}"

private def hexPairShow (p : Hexagram × Hexagram) : String :=
  s!"pair ({hexBrief p.1}) ({hexBrief p.2})"

private def hexListShow (xs : List Hexagram) : String :=
  "list [" ++ String.intercalate ", " (xs.map hexBrief) ++ "]"

private def readingSupportShow
    (r : SSBX.Text.OperatorReadings.OperatorReading) : String :=
  match r.operator? with
  | some id =>
      let support :=
        if (executableSemanticsFor? id).isSome then "executable"
        else "known-not-executable"
      s!"{r.label} => {id.code} {id.title}; {support}; expected={repr r.expectedTypes}"
  | none =>
      s!"{r.label} => pending; not-executable; expected={repr r.expectedTypes}"

private def readingBlock
    (rs : List SSBX.Text.OperatorReadings.OperatorReading) : String :=
  if rs.isEmpty then ""
  else "\n" ++ String.intercalate "\n" (rs.map fun r => "  - " ++ readingSupportShow r)

private def readingSupportKind
    (r : SSBX.Text.OperatorReadings.OperatorReading) : String :=
  match r.operator? with
  | some id =>
      if (executableSemanticsFor? id).isSome then "executable"
      else "known-not-executable"
  | none => "pending"

private def expectedTypeDiagShow : SSBX.Text.OperatorReadings.ExpectedType → String
  | .unknown => "unknown"
  | .function => "function"
  | .prop => "prop"
  | .path => "path"
  | .object => "object"
  | .operator => "operator"
  | .action => "action"
  | .nominal => "nominal"
  | .predicate => "predicate"
  | .quantifier => "quantifier"
  | .modal => "modal"
  | .aspect => "aspect"
  | .role => "role"
  | .construction => "construction"

private def cueDiagShow : SSBX.Text.OperatorReadings.ContextCue → String
  | .controlledToken => "controlledToken"
  | .instructionContext => "instructionContext"
  | .explicitSense => "explicitSense"
  | .betweenNominals => "betweenNominals"
  | .betweenActions => "betweenActions"
  | .contrastive => "contrastive"
  | .afterVerb => "afterVerb"
  | .beforeMotionVerb => "beforeMotionVerb"
  | .beforeYou => "beforeYou"
  | .wholeConstruction => "wholeConstruction"
  | .asConstruction => "asConstruction"
  | .nominalizerConstruction => "nominalizerConstruction"
  | .finalAssertion => "finalAssertion"
  | .expectedFunction => "expectedFunction"
  | .expectedProp => "expectedProp"
  | .expectedPath => "expectedPath"
  | .expectedObject => "expectedObject"
  | .expectedOperator => "expectedOperator"
  | .expectedAction => "expectedAction"
  | .expectedNominal => "expectedNominal"
  | .expectedPredicate => "expectedPredicate"
  | .quantifierDomain => "quantifierDomain"
  | .modalFrame => "modalFrame"
  | .abilityContext => "abilityContext"
  | .permissionContext => "permissionContext"
  | .normativeContext => "normativeContext"
  | .positionTimeContext => "positionTimeContext"
  | .instrumentalContext => "instrumentalContext"
  | .purposeContext => "purposeContext"
  | .identityContext => "identityContext"
  | .geometryContext => "geometryContext"
  | .innerOuterContext => "innerOuterContext"
  | .emotionContext => "emotionContext"
  | .legalContext => "legalContext"
  | .governanceContext => "governanceContext"
  | .strategyContext => "strategyContext"
  | .militaryContext => "militaryContext"
  | .medicalContext => "medicalContext"
  | .ritualContext => "ritualContext"
  | .mohistContext => "mohistContext"
  | .namesSchoolContext => "namesSchoolContext"
  | .xunziContext => "xunziContext"
  | .zhuangziContext => "zhuangziContext"
  | .chuciContext => "chuciContext"
  | .guanziContext => "guanziContext"
  | .huainanContext => "huainanContext"
  | .aspectContext => "aspectContext"
  | .boundaryMotionContext => "boundaryMotionContext"
  | .qiFlowContext => "qiFlowContext"
  | .roleContext => "roleContext"
  | .argumentContext => "argumentContext"
  | .temporalRange => "temporalRange"
  | .focusAdverb => "focusAdverb"

private def constructionDiagShow : SSBX.Text.OperatorReadings.ConstructionKind → String
  | .none => "none"
  | .genitiveProjection => "genitiveProjection"
  | .anaphora => "anaphora"
  | .sourcePath => "sourcePath"
  | .iteration => "iteration"
  | .quantifier => "quantifier"
  | .modal => "modal"
  | .causal => "causal"
  | .sequential => "sequential"
  | .mohistCondition => "mohistCondition"
  | .reflexive => "reflexive"
  | .wholeConstruction => "wholeConstruction"

private def cueFamiliesForReading
    (r : SSBX.Text.OperatorReadings.OperatorReading) : List String :=
  let direct := r.cues.map cueDiagShow
  let fromTypes := r.expectedTypes.filterMap fun ty =>
    match ty with
    | .function => some "expectedFunction"
    | .prop => some "expectedProp"
    | .path => some "expectedPath"
    | .object => some "expectedObject"
    | .operator => some "expectedOperator"
    | .action => some "expectedAction"
    | .nominal => some "expectedNominal"
    | .predicate => some "expectedPredicate"
    | .quantifier => some "quantifierDomain"
    | .modal => some "modalFrame"
    | .aspect => some "aspectContext"
    | .role => some "roleContext"
    | .construction => some "wholeConstruction"
    | .unknown => none
  let fromConstruction :=
    match r.construction with
    | .quantifier => ["quantifierDomain"]
    | .modal => ["modalFrame"]
    | .mohistCondition => ["mohistContext", "expectedProp"]
    | .reflexive => ["expectedFunction"]
    | .sourcePath => ["expectedPath"]
    | .iteration => ["beforeYou"]
    | .wholeConstruction => ["wholeConstruction"]
    | .causal | .sequential => ["expectedProp"]
    | .none | .genitiveProjection | .anaphora => []
  (direct ++ fromTypes ++ fromConstruction).eraseDups

private def ambiguityAction
    (r : SSBX.Text.OperatorReadings.OperatorReading) : String :=
  let families := cueFamiliesForReading r
  let familyShow := String.intercalate ", " families
  let typeShow := String.intercalate ", " (r.expectedTypes.map expectedTypeDiagShow)
  let constructionShow := constructionDiagShow r.construction
  "choose " ++ r.label ++
    " by adding context for " ++
    (if familyShow.isEmpty then "one of its catalogue cue families" else familyShow) ++
    "; expected=" ++ typeShow ++
    "; construction=" ++ constructionShow

private def ambiguityActionBlock
    (rs : List SSBX.Text.OperatorReadings.OperatorReading) : String :=
  if rs.isEmpty then ""
  else
    "\nWhy ambiguous: multiple catalogue readings share this surface; context has not selected one.\n" ++
    "Suggestions:\n" ++
      String.intercalate "\n" (rs.map fun r => "  - " ++ ambiguityAction r)

private def operatorByCode? (code : String) : Option OperatorId :=
  allOperatorIds.find? (fun id => id.code == code)

private def signatureEvidenceShow : SignatureEvidence → String
  | .seedOverride => "seedOverride"
  | .catalogueShape => "catalogueShape"

private def tyShow : SSBX.Foundation.Wen.WenDef.Ty → String
  | .hex => "Hex"
  | .bool => "Bool"
  | .cell => "Cell"
  | .catalogue kind => "Catalogue[" ++ kind.key ++ "]"
  | .prod a b => "(" ++ tyShow a ++ " * " ++ tyShow b ++ ")"
  | .list a => "List[" ++ tyShow a ++ "]"
  | .arr a b => "(" ++ tyShow a ++ " -> " ++ tyShow b ++ ")"

private def typeDiagShow : TypeDiag → String
  | .unknownVar name => s!"unknown variable \"{name}\""
  | .expectedFunction actual =>
      s!"expected a function in application position, got {tyShow actual}"
  | .argumentMismatch expected actual =>
      s!"expected argument type {tyShow expected}, got {tyShow actual}"

private def operatorOutput (code : String) : String :=
  match operatorByCode? code with
  | none => s!"operator {code}: no such catalogue OperatorId"
  | some id =>
      let entry := operatorRegistryEntryFor id
      let sig := entry.signature
      let glyphForms := operatorForms id |>.map (fun sense => sense.glyph)
      let compoundForms :=
        operatorCompoundSurfaceIds.filterMap (fun row =>
          if row.snd = id then some row.fst else none)
      let formLine :=
        "forms: " ++
          (if glyphForms.isEmpty then "(none)" else String.intercalate " " glyphForms)
      let compoundLine :=
        if compoundForms.isEmpty then []
        else ["compound surfaces: " ++ String.intercalate " " compoundForms]
      let executable :=
        match entry.executable? with
        | some sem =>
            s!"yes\nexecutable note: {sem.note}\nexecutable arity: {sem.arity}"
        | none =>
            "no\nstatus: known but not executable yet"
      String.intercalate "\n"
        ([ s!"operator {id.code} {id.title}"
         , formLine
         , s!"signature kind: {repr sig.kind}"
         , s!"signature arity: {sig.arity}"
         , s!"signature evidence: {signatureEvidenceShow sig.evidence}"
         , s!"signature note: {sig.note}"
         , "executable: " ++ executable
         ] ++ compoundLine)

private def coverageOutput : String :=
  let readingCount :=
    (allSurfaceReadings.map (fun entry => entry.readings.length)).foldl Nat.add 0
  let formBackedCount :=
    (allOperatorIds.filter (fun id => !(operatorForms id).isEmpty)).length
  String.intercalate "\n"
    [ s!"surface readings: {allSurfaceReadings.length} surfaces / {readingCount} readings"
    , s!"operators: {operatorRegistryEntries.length} registered / {executableRegistryEntries.length} executable"
    , s!"operator forms: {formBackedCount} ids with at least one form"
    , s!"operator-cell rows: {SSBX.Text.OperatorCellMap.allOperatorCells.length}"
    , s!"operator-cell semantic rows: {SSBX.Text.OperatorCellSemantics.allOperatorCellSemanticRows.length}"
    ]

private def operatorListFilterValid (filter : String) : Bool :=
  filter == "all"
    || filter == "executable"
    || filter == "known-not-executable"
    || filter == "unsupported"

private def operatorListFilterIsKnownNotExecutable (filter : String) : Bool :=
  filter == "known-not-executable" || filter == "unsupported"

private def operatorListIds (filter : String) : List OperatorId :=
  if filter == "executable" then
    allOperatorIds.filter isExecutableOperator
  else if operatorListFilterIsKnownNotExecutable filter then
    allOperatorIds.filter (fun id => !(isExecutableOperator id))
  else
    allOperatorIds

private def operatorSupportKind (id : OperatorId) : String :=
  if isExecutableOperator id then "executable" else "known-not-executable"

private def operatorSummaryLine (id : OperatorId) : String :=
  let sig := fullSignatureFor id
  let forms := operatorForms id |>.map (fun sense => sense.glyph)
  let formsShow := if forms.isEmpty then "(none)" else String.intercalate " " forms
  s!"{id.code}\t{id.title}\t{operatorSupportKind id}\tarity={sig.arity}\tforms={formsShow}"

private def operatorsOutput (filter : String) : String :=
  if !(operatorListFilterValid filter) then
    s!"operators: unknown filter \"{filter}\"; expected all, executable, known-not-executable, or unsupported"
  else
    let ids := operatorListIds filter
    let header :=
      s!"operators {filter}: {ids.length} shown; {operatorRegistryEntries.length} registered / {executableRegistryEntries.length} executable"
    String.intercalate "\n" (header :: ids.map operatorSummaryLine)

private def errShow : WenSurfaceErr → String
  | .lex (.unexpected col ch) =>
      s!"lex error at col {col}: unexpected character '{ch}'"
  | .lex .fuelExhausted =>
      "lex fuel exhausted (internal: should not occur at sane fuel)"
  | .resolve (.noReading surface col) =>
      s!"resolve error at col {col}: surface \"{surface}\" has no known reading"
  | .resolve (.ambiguous surface col candidates) =>
      s!"resolve error at col {col}: surface \"{surface}\" is ambiguous ({candidates.length} catalogue readings)" ++
        readingBlock candidates ++ ambiguityActionBlock candidates
  | .resolve (.knownButUnsupported surface col readings) =>
      s!"resolve error at col {col}: surface \"{surface}\" is known ({readings.length} readings) but has no executable catalogue reading" ++
        readingBlock readings
  | .resolve (.unpromotedHexagramGap surface col) =>
      s!"resolve error at col {col}: surface \"{surface}\" is a tracked hexagram gap but is not promoted to executable semantics"
  | .parse .empty =>
      "parse error: empty / incomplete expression"
  | .parse .fuelExhausted =>
      "parse error: fuel exhausted (program too deeply nested?)"
  | .parse (.unmatchedOpenBracket surface col) =>
      s!"parse error at col {col}: unmatched open bracket \"{surface}\""
  | .parse (.unmatchedCloseBracket surface col) =>
      s!"parse error at col {col}: unmatched close bracket \"{surface}\""
  | .parse (.expectedCloseBracket openSurface expected openCol col) =>
      s!"parse error at col {col}: expected close bracket \"{expected}\" for \"{openSurface}\" opened at col {openCol}"
  | .parse (.expectedVariable surface col) =>
      s!"parse error at col {col}: \"{surface}\" expects a Hex variable name"
  | .parse (.unexpectedApplicationMarker surface col) =>
      s!"parse error at col {col}: unexpected application marker \"{surface}\""
  | .parse (.unpromotedHexagramGap surface col) =>
      s!"parse error at col {col}: surface \"{surface}\" is a tracked hexagram gap, not an executable operator"
  | .parse (.nonassocInfix surface col) =>
      s!"parse error at col {col}: non-associative infix operator \"{surface}\" must be bracketed"
  | .parse (.typeMismatch expected actual surface col) =>
      s!"type error at col {col}: expected {tyShow expected}, got {tyShow actual} from \"{surface}\""
  | .parse (.leftoverAtoms n surface col) =>
      s!"parse error at col {col}: {n} leftover token(s) past parsed expression; first leftover \"{surface}\""
  | .elab (.unsupportedOp id surface col) =>
      let loc := if surface = "" then "" else s!" at col {col} (\"{surface}\")"
      s!"elab error{loc}: operator {repr id} is known but not executable yet"
  | .elab (.unsupportedConstruction name) =>
      s!"elab error: construction \"{name}\" is not executable yet"
  | .elab .empty =>
      "elab error: empty / incomplete expression"
  | .elab (.leftoverAtoms n) =>
      s!"elab error: {n} leftover atom(s) past parsed expression"
  | .elab .fuelExhausted =>
      "elab error: fuel exhausted (program too deeply nested?)"
  | .elab (.typeMismatch diag) =>
      "type error: " ++ typeDiagShow diag
  | .denoteFailed expected actual =>
      s!"denote failed: expected {tyShow expected} result, got {tyShow actual}"

private def errPhase : WenSurfaceErr → String
  | .lex _ => "lex"
  | .resolve (.knownButUnsupported _ _ _) => "unsupported"
  | .resolve (.unpromotedHexagramGap _ _) => "unsupported"
  | .resolve _ => "resolve"
  | .parse (.unpromotedHexagramGap _ _) => "unsupported"
  | .parse (.typeMismatch _ _ _ _) => "type"
  | .parse _ => "parse"
  | .elab (.unsupportedOp _ _ _) => "unsupported"
  | .elab (.unsupportedConstruction _) => "unsupported"
  | .elab (.typeMismatch _) => "type"
  | .elab _ => "elab"
  | .denoteFailed _ _ => "denote"

private def errCode : WenSurfaceErr → String
  | .lex (.unexpected _ _) => "lex_unexpected_char"
  | .lex .fuelExhausted => "lex_fuel_exhausted"
  | .resolve (.noReading _ _) => "no_reading"
  | .resolve (.ambiguous _ _ _) => "ambiguous_reading"
  | .resolve (.knownButUnsupported _ _ _) => "known_but_unsupported"
  | .resolve (.unpromotedHexagramGap _ _) => "unpromoted_hexagram_gap"
  | .parse .empty => "empty_expression"
  | .parse .fuelExhausted => "parse_fuel_exhausted"
  | .parse (.unmatchedOpenBracket _ _) => "unmatched_open_bracket"
  | .parse (.unmatchedCloseBracket _ _) => "unmatched_close_bracket"
  | .parse (.expectedCloseBracket _ _ _ _) => "expected_close_bracket"
  | .parse (.expectedVariable _ _) => "expected_variable"
  | .parse (.unexpectedApplicationMarker _ _) => "unexpected_application_marker"
  | .parse (.unpromotedHexagramGap _ _) => "unpromoted_hexagram_gap"
  | .parse (.nonassocInfix _ _) => "nonassoc_infix"
  | .parse (.typeMismatch _ _ _ _) => "type_mismatch"
  | .parse (.leftoverAtoms _ _ _) => "leftover_tokens"
  | .elab (.unsupportedOp _ _ _) => "unsupported_operator"
  | .elab (.unsupportedConstruction _) => "unsupported_construction"
  | .elab .empty => "empty_expression"
  | .elab (.leftoverAtoms _) => "leftover_atoms"
  | .elab .fuelExhausted => "elab_fuel_exhausted"
  | .elab (.typeMismatch _) => "type_mismatch"
  | .denoteFailed _ _ => "denote_failed"

private def lexErrShow : LexErr → String
  | .unexpected col ch => s!"lex error at col {col}: unexpected character '{ch}'"
  | .fuelExhausted => "lex fuel exhausted"

private def resolveErrShow : ResolveErr → String
  | .noReading surface col =>
      s!"resolve error at col {col}: surface \"{surface}\" has no known reading"
  | .ambiguous surface col candidates =>
      s!"resolve error at col {col}: surface \"{surface}\" is ambiguous ({candidates.length} catalogue readings)" ++
        readingBlock candidates ++ ambiguityActionBlock candidates
  | .knownButUnsupported surface col readings =>
      s!"resolve error at col {col}: surface \"{surface}\" is known ({readings.length} readings) but has no executable catalogue reading" ++
        readingBlock readings
  | .unpromotedHexagramGap surface col =>
      s!"resolve error at col {col}: surface \"{surface}\" is a tracked hexagram gap but is not promoted to executable semantics"

private def parseErrShow : ParseErr → String
  | .empty => "parse error: empty / incomplete expression"
  | .fuelExhausted => "parse error: fuel exhausted"
  | .unmatchedOpenBracket surface col =>
      s!"parse error at col {col}: unmatched open bracket \"{surface}\""
  | .unmatchedCloseBracket surface col =>
      s!"parse error at col {col}: unmatched close bracket \"{surface}\""
  | .expectedCloseBracket openSurface expected openCol col =>
      s!"parse error at col {col}: expected close bracket \"{expected}\" for \"{openSurface}\" opened at col {openCol}"
  | .expectedVariable surface col =>
      s!"parse error at col {col}: \"{surface}\" expects a Hex variable name"
  | .unexpectedApplicationMarker surface col =>
      s!"parse error at col {col}: unexpected application marker \"{surface}\""
  | .unpromotedHexagramGap surface col =>
      s!"parse error at col {col}: surface \"{surface}\" is a tracked hexagram gap, not an executable operator"
  | .nonassocInfix surface col =>
      s!"parse error at col {col}: non-associative infix operator \"{surface}\" must be bracketed"
  | .typeMismatch expected actual surface col =>
      s!"type error at col {col}: expected {tyShow expected}, got {tyShow actual} from \"{surface}\""
  | .leftoverAtoms n surface col =>
      s!"parse error at col {col}: {n} leftover token(s) past parsed expression; first leftover \"{surface}\""

private def atomShow : ResolvedAtom → String
  | .hexConst h => s!"hex[{(Hexagram.toIdx h).val}]"
  | .boolConst b => s!"bool[{b}]"
  | .varName n => s!"var[{n}]"
  | .catalogueOp r =>
      match r.operator? with
      | some id => s!"op[{id.code}:{id.title}]"
      | none => s!"op[pending:{r.label}]"
  | .hexOrOp h r =>
      match r.operator? with
      | some id => s!"hex-or-op[hex={(Hexagram.toIdx h).val};op={id.code}:{id.title}]"
      | none => s!"hex-or-op[hex={(Hexagram.toIdx h).val};pending={r.label}]"
  | .syntax .zhe => "syntax[者]"
  | .syntax .ling => "syntax[令]"
  | .appMarker => "marker[之]"
  | .iterate => "construction[之又]"
  | .openBracket => "open-bracket"
  | .closeBracket => "close-bracket"

private def tokShow (t : GlyphTok) : String :=
  s!"{t.startCol}:{t.surface}/w{t.width}"

private def resolvedShow (t : ResolvedTok) : String :=
  s!"{tokShow t.tok} => {atomShow t.atom}"

private def tokensOutput (src : String) : String :=
  match lexWen src with
  | .ok toks => String.intercalate "\n" (toks.map tokShow)
  | .error e => lexErrShow e

private def resolveOutput (src : String) : String :=
  match lexWen src with
  | .error e => lexErrShow e
  | .ok toks =>
      match resolveWithCues toks with
      | .ok rs => String.intercalate "\n" (rs.map resolvedShow)
      | .error e => resolveErrShow e

private def astOutput (src : String) : String :=
  match parseSurface src with
  | .ok ast => reprStr ast
  | .error (.inl e) => lexErrShow e
  | .error (.inr (.inl e)) => resolveErrShow e
  | .error (.inr (.inr e)) => parseErrShow e

private def typeOutput (src : String) : String :=
  match wenyanCompile src with
  | .ok typed => s!"type {tyShow typed.ty}\nterm {repr typed.tm}"
  | .error e => errShow e

private def catalogueRun? (src : String) : Option (OperatorId × SignatureKind × Nat) :=
  match wenyanCompile src with
  | .error _ => none
  | .ok typed =>
      match denoteCatalogue typed.tm with
      | some (id, kind, args) => some (id, kind, args.length)
      | none => none

private def catalogueRunShow (id : OperatorId) (kind : SignatureKind) (arity : Nat) : String :=
  s!"catalogue {id.code} {id.title} kind {kind.key} args {arity}"

private def jsonEscape (s : String) : String :=
  String.join <| s.toList.map fun c =>
    if c == '"' then "\\\""
    else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n"
    else c.toString

private def jsonString (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def jsonArray (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

private def jsonObject (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (k, v) => jsonString k ++ ":" ++ v) ++ "}"

private def jsonFieldString (key value : String) : String × String :=
  (key, jsonString value)

private def jsonFieldNat (key : String) (value : Nat) : String × String :=
  (key, toString value)

private def jsonFieldBool (key : String) (value : Bool) : String × String :=
  (key, toString value)

private def jsonFieldRaw (key value : String) : String × String :=
  (key, value)

private def hexJson (h : Hexagram) : String :=
  jsonObject
    [ jsonFieldNat "idx" (Hexagram.toIdx h).val
    , jsonFieldString "label" (hexLabel h)
    ]

private def hexPairJson (p : Hexagram × Hexagram) : String :=
  jsonArray [hexJson p.1, hexJson p.2]

private def hexListJson (xs : List Hexagram) : String :=
  jsonArray (xs.map hexJson)

private def endColOfSurface (startCol : Nat) (surface : String) : Nat :=
  startCol + surface.toList.length

private def expectedTypeShow : SSBX.Text.OperatorReadings.ExpectedType → String
  | .unknown => "unknown"
  | .function => "function"
  | .prop => "prop"
  | .path => "path"
  | .object => "object"
  | .operator => "operator"
  | .action => "action"
  | .nominal => "nominal"
  | .predicate => "predicate"
  | .quantifier => "quantifier"
  | .modal => "modal"
  | .aspect => "aspect"
  | .role => "role"
  | .construction => "construction"

private def fixityShow : SSBX.Text.OperatorReadings.Fixity → String
  | .prefix => "prefix"
  | .infix => "infix"
  | .suffix => "suffix"
  | .construction => "construction"

private def readingStatusShow : SSBX.Text.OperatorReadings.ReadingStatus → String
  | .catalogue => "catalogue"
  | .contextual => "contextual"
  | .construction => "construction"
  | .pending => "pending"

private def constructionKindShow : SSBX.Text.OperatorReadings.ConstructionKind → String
  | .none => "none"
  | .genitiveProjection => "genitiveProjection"
  | .anaphora => "anaphora"
  | .sourcePath => "sourcePath"
  | .iteration => "iteration"
  | .quantifier => "quantifier"
  | .modal => "modal"
  | .causal => "causal"
  | .sequential => "sequential"
  | .mohistCondition => "mohistCondition"
  | .reflexive => "reflexive"
  | .wholeConstruction => "wholeConstruction"

private def operatorIdJsonFields (id : OperatorId) : List (String × String) :=
  [ jsonFieldString "operatorCode" id.code
  , jsonFieldString "operatorTitle" id.title
  ]

private def optMin (a b : Option Nat) : Option Nat :=
  match a, b with
  | some x, some y => some (Nat.min x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

private def optMax (a b : Option Nat) : Option Nat :=
  match a, b with
  | some x, some y => some (Nat.max x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

private def resolvedTokEndCol (t : ResolvedTok) : Nat :=
  t.tok.startCol + t.tok.width

mutual
  private def surfaceExprStartCol? : SurfaceExpr → Option Nat
    | .atom tok => some tok.tok.startCol
    | .app f x => optMin (surfaceExprStartCol? f) (surfaceExprStartCol? x)
    | .seq items => surfaceExprListStartCol? items
    | .marker tok body => optMin (some tok.tok.startCol) (surfaceExprStartCol? body)
    | .binder _ _ body => surfaceExprStartCol? body
    | .letBind _ value body => optMin (surfaceExprStartCol? value) (surfaceExprStartCol? body)
    | .construction _ items => surfaceExprListStartCol? items
    | .grouped openTok _ _ => some openTok.tok.startCol

  private def surfaceExprListStartCol? : List SurfaceExpr → Option Nat
    | [] => none
    | item :: rest => optMin (surfaceExprStartCol? item) (surfaceExprListStartCol? rest)
end

mutual
  private def surfaceExprEndCol? : SurfaceExpr → Option Nat
    | .atom tok => some (resolvedTokEndCol tok)
    | .app f x => optMax (surfaceExprEndCol? f) (surfaceExprEndCol? x)
    | .seq items => surfaceExprListEndCol? items
    | .marker tok body => optMax (some (resolvedTokEndCol tok)) (surfaceExprEndCol? body)
    | .binder _ _ body => surfaceExprEndCol? body
    | .letBind _ value body => optMax (surfaceExprEndCol? value) (surfaceExprEndCol? body)
    | .construction _ items => surfaceExprListEndCol? items
    | .grouped _ closeTok _ => some (resolvedTokEndCol closeTok)

  private def surfaceExprListEndCol? : List SurfaceExpr → Option Nat
    | [] => none
    | item :: rest => optMax (surfaceExprEndCol? item) (surfaceExprListEndCol? rest)
end

private def surfaceExprJson (expr : SurfaceExpr) : String :=
  let spanFields :=
    match surfaceExprStartCol? expr, surfaceExprEndCol? expr with
    | some startCol, some endCol =>
        [ jsonFieldNat "startCol" startCol
        , jsonFieldNat "endCol" endCol
        ]
    | _, _ => []
  jsonObject <| spanFields ++ [jsonFieldString "ast" (reprStr expr)]

private def relationInfixSyntaxJson? (expr : SurfaceExpr) : Option String :=
  match expr with
  | .app (.app (.atom opTok) lhs) rhs =>
      match relationInfixTok? opTok with
      | none => none
      | some normalizedOp =>
          match normalizedOp.atom.operatorId?, surfaceExprEndCol? lhs, surfaceExprStartCol? rhs with
          | some id, some lhsEndCol, some rhsStartCol =>
              if decide (lhsEndCol <= opTok.tok.startCol ∧ opTok.tok.startCol < rhsStartCol) then
                let spanFields :=
                  match surfaceExprStartCol? expr, surfaceExprEndCol? expr with
                  | some startCol, some endCol =>
                      [ jsonFieldNat "startCol" startCol
                      , jsonFieldNat "endCol" endCol
                      ]
                  | _, _ => []
                some <| jsonObject <|
                  [ jsonFieldString "node" "operatorForm"
                  , jsonFieldString "surface" normalizedOp.tok.surface
                  , jsonFieldString "syntaxForm" "infix"
                  , jsonFieldString "fixity" "infix"
                  , jsonFieldNat "precedence" 40
                  , jsonFieldString "assoc" "nonassoc"
                  , jsonFieldString "desugaredTo" "curriedApplication"
                  , jsonFieldNat "operatorStartCol" opTok.tok.startCol
                  , jsonFieldNat "operatorEndCol" (resolvedTokEndCol opTok)
                  , jsonFieldRaw "args" (jsonArray [surfaceExprJson lhs, surfaceExprJson rhs])
                  ] ++ operatorIdJsonFields id ++ spanFields
              else
                none
          | _, _, _ => none
  | _ => none

mutual
  private def syntaxFormsJsonFuel : Nat → SurfaceExpr → List String
    | 0, _ => []
    | fuel+1, expr =>
        let children :=
          match expr with
          | .atom _ => []
          | .app f x => syntaxFormsJsonFuel fuel f ++ syntaxFormsJsonFuel fuel x
          | .seq items => syntaxFormsListJsonFuel fuel items
          | .marker _ body => syntaxFormsJsonFuel fuel body
          | .binder _ _ body => syntaxFormsJsonFuel fuel body
          | .letBind _ value body =>
              syntaxFormsJsonFuel fuel value ++ syntaxFormsJsonFuel fuel body
          | .construction _ items => syntaxFormsListJsonFuel fuel items
          | .grouped _ _ body => syntaxFormsJsonFuel fuel body
        match relationInfixSyntaxJson? expr with
        | some form => form :: children
        | none => children

  private def syntaxFormsListJsonFuel : Nat → List SurfaceExpr → List String
    | 0, _ => []
    | _+1, [] => []
    | fuel+1, item :: rest =>
        syntaxFormsJsonFuel fuel item ++ syntaxFormsListJsonFuel fuel rest
end

private def syntaxFormsJson (fuel : Nat) (expr : SurfaceExpr) : List String :=
  syntaxFormsJsonFuel fuel expr

private def readingJson
    (r : SSBX.Text.OperatorReadings.OperatorReading) : String :=
  let opFields :=
    match r.operator? with
    | some id => operatorIdJsonFields id
    | none => [jsonFieldRaw "operatorCode" "null", jsonFieldRaw "operatorTitle" "null"]
  jsonObject <|
    [ jsonFieldString "label" r.label
    , jsonFieldString "gloss" r.gloss
    , jsonFieldString "support" (readingSupportKind r)
    , jsonFieldString "status" (readingStatusShow r.status)
    , jsonFieldString "fixity" (fixityShow r.fixity)
    , jsonFieldRaw "cues" (jsonArray (r.cues.map (jsonString ∘ cueDiagShow)))
    , jsonFieldRaw "expectedTypes" (jsonArray (r.expectedTypes.map (jsonString ∘ expectedTypeShow)))
    , jsonFieldString "construction" (constructionKindShow r.construction)
    ] ++ opFields

private def readingsJson (rs : List SSBX.Text.OperatorReadings.OperatorReading) : String :=
  jsonArray (rs.map readingJson)

private def ambiguitySuggestionJson
    (r : SSBX.Text.OperatorReadings.OperatorReading) : String :=
  let fields :=
    match r.operator? with
    | some id => operatorIdJsonFields id
    | none => [jsonFieldRaw "operatorCode" "null", jsonFieldRaw "operatorTitle" "null"]
  jsonObject <|
    [ jsonFieldString "label" r.label
    , jsonFieldString "gloss" r.gloss
    , jsonFieldRaw "cueFamilies" (jsonArray ((cueFamiliesForReading r).map jsonString))
    , jsonFieldRaw "expectedTypes" (jsonArray (r.expectedTypes.map (jsonString ∘ expectedTypeShow)))
    , jsonFieldString "construction" (constructionKindShow r.construction)
    , jsonFieldString "action" (ambiguityAction r)
    ] ++ fields

private def ambiguitySuggestionsJson
    (rs : List SSBX.Text.OperatorReadings.OperatorReading) : String :=
  jsonArray (rs.map ambiguitySuggestionJson)

private def errLocationFields (surface : String) (col : Nat) : List (String × String) :=
  [ jsonFieldString "surface" surface
  , jsonFieldNat "startCol" col
  , jsonFieldNat "endCol" (endColOfSurface col surface)
  ]

private def errExtraFields : WenSurfaceErr → List (String × String)
  | .lex (.unexpected col ch) =>
      [ jsonFieldString "char" ch.toString
      , jsonFieldNat "startCol" col
      , jsonFieldNat "endCol" (col + 1)
      ]
  | .lex .fuelExhausted => []
  | .resolve (.noReading surface col) => errLocationFields surface col
  | .resolve (.ambiguous surface col candidates) =>
      errLocationFields surface col ++
        [ jsonFieldNat "candidateCount" candidates.length
        , jsonFieldRaw "candidates" (readingsJson candidates)
        , jsonFieldRaw "suggestions" (ambiguitySuggestionsJson candidates)
        , jsonFieldString "hint" "Surface is ambiguous because multiple catalogue readings remain viable; add a contextual cue family to select one."
        ]
  | .resolve (.knownButUnsupported surface col readings) =>
      errLocationFields surface col ++
        [ jsonFieldNat "candidateCount" readings.length
        , jsonFieldRaw "candidates" (readingsJson readings)
        ]
  | .resolve (.unpromotedHexagramGap surface col) => errLocationFields surface col
  | .parse (.expectedVariable surface col) => errLocationFields surface col
  | .parse (.unmatchedOpenBracket surface col) => errLocationFields surface col
  | .parse (.unmatchedCloseBracket surface col) => errLocationFields surface col
  | .parse (.expectedCloseBracket openSurface expected openCol col) =>
      [ jsonFieldString "surface" openSurface
      , jsonFieldString "expected" expected
      , jsonFieldNat "openCol" openCol
      , jsonFieldNat "startCol" col
      , jsonFieldNat "endCol" (col + expected.toList.length)
      ]
  | .parse (.unexpectedApplicationMarker surface col) => errLocationFields surface col
  | .parse (.unpromotedHexagramGap surface col) => errLocationFields surface col
  | .parse (.nonassocInfix surface col) => errLocationFields surface col
  | .parse (.typeMismatch expected actual surface col) =>
      errLocationFields surface col ++
        [ jsonFieldString "expectedType" (tyShow expected)
        , jsonFieldString "actualType" (tyShow actual)
        ]
  | .parse (.leftoverAtoms count surface col) =>
      errLocationFields surface col ++ [jsonFieldNat "leftoverCount" count]
  | .parse _ => []
  | .elab (.unsupportedOp id surface col) =>
      operatorIdJsonFields id ++
        (if surface = "" then [] else errLocationFields surface col) ++
        [jsonFieldString "support" "known-not-executable"]
  | .elab (.unsupportedConstruction name) =>
      [jsonFieldString "construction" name, jsonFieldString "support" "known-not-executable"]
  | .elab (.leftoverAtoms count) => [jsonFieldNat "leftoverCount" count]
  | .elab (.typeMismatch (.unknownVar name)) =>
      [jsonFieldString "variable" name]
  | .elab (.typeMismatch (.expectedFunction actual)) =>
      [ jsonFieldString "expectedType" "function"
      , jsonFieldString "actualType" (tyShow actual)
      ]
  | .elab (.typeMismatch (.argumentMismatch expected actual)) =>
      [ jsonFieldString "expectedType" (tyShow expected)
      , jsonFieldString "actualType" (tyShow actual)
      ]
  | .elab _ => []
  | .denoteFailed expected actual =>
      [ jsonFieldString "expectedType" (tyShow expected)
      , jsonFieldString "actualType" (tyShow actual)
      ]

private def errJson (e : WenSurfaceErr) : String :=
  jsonObject <|
    [ jsonFieldBool "ok" false
    , jsonFieldString "phase" (errPhase e)
    , jsonFieldString "code" (errCode e)
    , jsonFieldString "message" (errShow e)
    , jsonFieldString "error" (errShow e)
    ] ++ errExtraFields e

private def tokenJson (t : GlyphTok) : String :=
  jsonObject
    [ jsonFieldString "surface" t.surface
    , jsonFieldNat "startCol" t.startCol
    , jsonFieldNat "endCol" (t.startCol + t.width)
    , jsonFieldNat "width" t.width
    , jsonFieldBool "isMulti" t.isMulti
    ]

private def atomJson : ResolvedAtom → String
  | .hexConst h =>
      jsonObject
        [ jsonFieldString "kind" "hex"
        , jsonFieldNat "idx" (Hexagram.toIdx h).val
        ]
  | .boolConst b =>
      jsonObject
        [ jsonFieldString "kind" "bool"
        , jsonFieldBool "value" b
        ]
  | .varName name =>
      jsonObject
        [ jsonFieldString "kind" "var"
        , jsonFieldString "name" name
        ]
  | .catalogueOp r =>
      jsonObject
        [ jsonFieldString "kind" "operator"
        , jsonFieldRaw "reading" (readingJson r)
        ]
  | .hexOrOp h r =>
      jsonObject
        [ jsonFieldString "kind" "hexOrOp"
        , jsonFieldNat "hexIdx" (Hexagram.toIdx h).val
        , jsonFieldRaw "reading" (readingJson r)
        ]
  | .syntax .zhe =>
      jsonObject [jsonFieldString "kind" "syntax", jsonFieldString "marker" "者"]
  | .syntax .ling =>
      jsonObject [jsonFieldString "kind" "syntax", jsonFieldString "marker" "令"]
  | .appMarker =>
      jsonObject [jsonFieldString "kind" "applicationMarker", jsonFieldString "surface" "之"]
  | .iterate =>
      jsonObject [jsonFieldString "kind" "construction", jsonFieldString "surface" "之又"]
  | .openBracket =>
      jsonObject [jsonFieldString "kind" "openBracket"]
  | .closeBracket =>
      jsonObject [jsonFieldString "kind" "closeBracket"]

private def resolvedTokJson (t : ResolvedTok) : String :=
  jsonObject
    [ jsonFieldString "surface" t.tok.surface
    , jsonFieldNat "startCol" t.tok.startCol
    , jsonFieldNat "endCol" (t.tok.startCol + t.tok.width)
    , jsonFieldNat "width" t.tok.width
    , jsonFieldRaw "atom" (atomJson t.atom)
    ]

private def tokensJsonOutput (src : String) : String :=
  match lexWen src with
  | .ok toks =>
      jsonObject
        [ jsonFieldBool "ok" true
        , jsonFieldString "mode" "tokens"
        , jsonFieldRaw "tokens" (jsonArray (toks.map tokenJson))
        ]
  | .error e => errJson (.lex e)

private def resolveJsonOutput (src : String) : String :=
  match lexWen src with
  | .error e => errJson (.lex e)
  | .ok toks =>
      match resolveWithCues toks with
      | .ok rs =>
          jsonObject
            [ jsonFieldBool "ok" true
            , jsonFieldString "mode" "resolve"
            , jsonFieldRaw "tokens" (jsonArray (rs.map resolvedTokJson))
            ]
      | .error e => errJson (.resolve e)

private def astJsonOutput (src : String) : String :=
  match parseSurface src with
  | .ok ast =>
      let syntaxForms := syntaxFormsJson (src.toList.length + 10) ast
      jsonObject
        [ jsonFieldBool "ok" true
        , jsonFieldString "mode" "ast"
        , jsonFieldString "ast" (reprStr ast)
        , jsonFieldNat "syntaxFormCount" syntaxForms.length
        , jsonFieldRaw "syntaxForms" (jsonArray syntaxForms)
        ]
  | .error (.inl e) => errJson (.lex e)
  | .error (.inr (.inl e)) => errJson (.resolve e)
  | .error (.inr (.inr e)) => errJson (.parse e)

private def typeJsonOutput (src : String) : String :=
  match wenyanCompile src with
  | .ok typed =>
      jsonObject
        [ jsonFieldBool "ok" true
        , jsonFieldString "mode" "typecheck"
        , jsonFieldString "type" (tyShow typed.ty)
        , jsonFieldString "term" (reprStr typed.tm)
        ]
  | .error e => errJson e

private def jsonOutput (src : String) : String :=
  match wenyanInterp src with
  | .ok h =>
      "{\"ok\":true,\"kind\":\"hex\",\"idx\":" ++ toString (Hexagram.toIdx h).val ++ "}"
  | .error eHex =>
    match wenyanInterpBool src with
    | .ok b => "{\"ok\":true,\"kind\":\"bool\",\"value\":" ++ toString b ++ "}"
    | .error _ =>
      match wenyanInterpHexPair src with
      | .ok p =>
          jsonObject
            [ jsonFieldBool "ok" true
            , jsonFieldString "kind" "hexPair"
            , jsonFieldRaw "values" (hexPairJson p)
            ]
      | .error _ =>
        match wenyanInterpHexList src with
        | .ok xs =>
            jsonObject
              [ jsonFieldBool "ok" true
              , jsonFieldString "kind" "hexList"
              , jsonFieldRaw "values" (hexListJson xs)
              ]
        | .error _ =>
            match catalogueRun? src with
            | some (id, kind, arity) =>
                jsonObject
                  [ jsonFieldBool "ok" true
                  , jsonFieldString "kind" "catalogue"
                  , jsonFieldString "operatorCode" id.code
                  , jsonFieldString "operatorTitle" id.title
                  , jsonFieldString "signatureKind" kind.key
                  , jsonFieldNat "arity" arity
                  ]
            | none => errJson eHex

private def programOk (src : String) : Bool :=
  match wenyanInterp src with
  | .ok _ => true
  | .error _ =>
      match wenyanInterpBool src with
      | .ok _ => true
      | .error _ =>
          match wenyanInterpHexPair src with
          | .ok _ => true
          | .error _ =>
              match wenyanInterpHexList src with
              | .ok _ => true
              | .error _ => (catalogueRun? src).isSome

private def tokensOk (src : String) : Bool :=
  match lexWen src with
  | .ok _ => true
  | .error _ => false

private def resolveOk (src : String) : Bool :=
  match lexWen src with
  | .error _ => false
  | .ok toks =>
      match resolveWithCues toks with
      | .ok _ => true
      | .error _ => false

private def astOk (src : String) : Bool :=
  match parseSurface src with
  | .ok _ => true
  | .error _ => false

private def typecheckOk (src : String) : Bool :=
  match wenyanCompile src with
  | .ok _ => true
  | .error _ => false

private def exitCode (ok : Bool) : UInt32 :=
  if ok then 0 else 1

/-! ## Run a single program -/

private def runProgram (src : String) : String :=
  -- Try concrete exact values first; if those fail, fall back to catalogue form.
  match wenyanInterp src with
  | .ok h => hexShow h
  | .error eHex =>
    match wenyanInterpBool src with
    | .ok b => s!"bool {b}"
    | .error _ =>
      match wenyanInterpHexPair src with
      | .ok p => hexPairShow p
      | .error _ =>
        match wenyanInterpHexList src with
        | .ok xs => hexListShow xs
        | .error _ =>
            match catalogueRun? src with
            | some (id, kind, arity) => catalogueRunShow id kind arity
            | none => errShow eHex   -- show the original (Hex-attempt) error

private def explainOutput (src : String) : String :=
  String.intercalate "\n\n"
    [ "TOKENS\n" ++ tokensOutput src
    , "RESOLVE\n" ++ resolveOutput src
    , "AST\n" ++ astOutput src
    , "TYPECHECK\n" ++ typeOutput src
    , "RUN\n" ++ runProgram src
    ]

private def explainJsonOutput (src : String) : String :=
  jsonObject
    [ jsonFieldBool "ok" (programOk src)
    , jsonFieldString "mode" "explain"
    , jsonFieldRaw "tokens" (tokensJsonOutput src)
    , jsonFieldRaw "resolve" (resolveJsonOutput src)
    , jsonFieldRaw "ast" (astJsonOutput src)
    , jsonFieldRaw "typecheck" (typeJsonOutput src)
    , jsonFieldRaw "run" (jsonOutput src)
    ]

private def operatorJsonOutput (code : String) : String :=
  match operatorByCode? code with
  | none =>
      jsonObject
        [ jsonFieldBool "ok" false
        , jsonFieldString "phase" "operator"
        , jsonFieldString "code" "unknown_operator"
        , jsonFieldString "message" s!"operator {code}: no such catalogue OperatorId"
        , jsonFieldString "operatorCode" code
        ]
  | some id =>
      let entry := operatorRegistryEntryFor id
      let sig := entry.signature
      let glyphForms := operatorForms id |>.map (fun sense => sense.glyph)
      let compoundForms :=
        operatorCompoundSurfaceIds.filterMap (fun row =>
          if row.snd = id then some row.fst else none)
      let executableJson :=
        match entry.executable? with
        | some sem =>
            jsonObject
              [ jsonFieldNat "arity" sem.arity
              , jsonFieldString "note" sem.note
              ]
        | none => "null"
      jsonObject
        [ jsonFieldBool "ok" true
        , jsonFieldString "mode" "operator"
        , jsonFieldString "operatorCode" id.code
        , jsonFieldString "operatorTitle" id.title
        , jsonFieldRaw "forms" (jsonArray (glyphForms.map jsonString))
        , jsonFieldRaw "compoundSurfaces" (jsonArray (compoundForms.map jsonString))
        , jsonFieldRaw "signature"
            (jsonObject
              [ jsonFieldString "kind" (reprStr sig.kind)
              , jsonFieldNat "arity" sig.arity
              , jsonFieldString "evidence" (signatureEvidenceShow sig.evidence)
              , jsonFieldString "note" sig.note
              ])
        , jsonFieldBool "executable" entry.executable?.isSome
        , jsonFieldString "support"
            (if entry.executable?.isSome then "executable" else "known-not-executable")
        , jsonFieldRaw "executableSemantics" executableJson
        ]

private def operatorSummaryJson (id : OperatorId) : String :=
  let sig := fullSignatureFor id
  let glyphForms := operatorForms id |>.map (fun sense => sense.glyph)
  let compoundForms :=
    operatorCompoundSurfaceIds.filterMap (fun row =>
      if row.snd = id then some row.fst else none)
  jsonObject
    [ jsonFieldString "operatorCode" id.code
    , jsonFieldString "operatorTitle" id.title
    , jsonFieldBool "executable" (isExecutableOperator id)
    , jsonFieldString "support" (operatorSupportKind id)
    , jsonFieldRaw "forms" (jsonArray (glyphForms.map jsonString))
    , jsonFieldRaw "compoundSurfaces" (jsonArray (compoundForms.map jsonString))
    , jsonFieldNat "signatureArity" sig.arity
    , jsonFieldString "signatureEvidence" (signatureEvidenceShow sig.evidence)
    ]

private def operatorsJsonOutput (filter : String) : String :=
  if !(operatorListFilterValid filter) then
    jsonObject
      [ jsonFieldBool "ok" false
      , jsonFieldString "phase" "operators"
      , jsonFieldString "code" "unknown_operator_filter"
      , jsonFieldString "message" s!"operators: unknown filter \"{filter}\"; expected all, executable, known-not-executable, or unsupported"
      , jsonFieldString "filter" filter
      ]
  else
    let ids := operatorListIds filter
    jsonObject
      [ jsonFieldBool "ok" true
      , jsonFieldString "mode" "operators"
      , jsonFieldString "filter" filter
      , jsonFieldNat "count" ids.length
      , jsonFieldNat "operatorsRegistered" operatorRegistryEntries.length
      , jsonFieldNat "executableOperators" executableRegistryEntries.length
      , jsonFieldNat "knownNotExecutableOperators" (operatorRegistryEntries.length - executableRegistryEntries.length)
      , jsonFieldRaw "operators" (jsonArray (ids.map operatorSummaryJson))
      ]

private def coverageJsonOutput : String :=
  let readingCount :=
    (allSurfaceReadings.map (fun entry => entry.readings.length)).foldl Nat.add 0
  let formBackedCount :=
    (allOperatorIds.filter (fun id => !(operatorForms id).isEmpty)).length
  jsonObject
    [ jsonFieldBool "ok" true
    , jsonFieldString "mode" "coverage"
    , jsonFieldNat "surfaceCount" allSurfaceReadings.length
    , jsonFieldNat "readingCount" readingCount
    , jsonFieldNat "operatorsRegistered" operatorRegistryEntries.length
    , jsonFieldNat "executableOperators" executableRegistryEntries.length
    , jsonFieldNat "operatorFormBackedCount" formBackedCount
    , jsonFieldNat "operatorCellRows" (SSBX.Text.OperatorCellMap.allOperatorCells.length)
    , jsonFieldNat "operatorCellSemanticRows" (SSBX.Text.OperatorCellSemantics.allOperatorCellSemanticRows.length)
    ]

/-! ## CLI -/

private def usage : String :=
  String.intercalate "\n"
    ["Usage: wenyan-surface <PROGRAM>",
     "       echo <PROGRAM> | wenyan-surface",
     "       wenyan-surface --tokens <PROGRAM>",
     "       wenyan-surface --resolve <PROGRAM>",
     "       wenyan-surface --ast <PROGRAM>",
     "       wenyan-surface --typecheck <PROGRAM>",
     "       wenyan-surface --json <PROGRAM>",
     "       wenyan-surface --json --tokens <PROGRAM>",
     "       wenyan-surface --json --resolve <PROGRAM>",
     "       wenyan-surface --json --ast <PROGRAM>",
     "       wenyan-surface --json --typecheck <PROGRAM>",
     "       wenyan-surface --json --explain <PROGRAM>",
     "       wenyan-surface --json --operator <OP-ID>",
     "       wenyan-surface --json --operators [all|executable|known-not-executable|unsupported]",
     "       wenyan-surface --json --coverage",
     "       wenyan-surface --explain <PROGRAM>",
     "       wenyan-surface --operator <OP-ID>",
     "       wenyan-surface --operators [all|executable|known-not-executable|unsupported]",
     "       wenyan-surface --coverage",
     "       wenyan-surface --help",
     "",
     "Surface vocabulary:",
     "  Executable operators: 371 rows (317 exact/theorem-backed; 54 structural catalogue normal forms)",
     "  Examples include: 推 比 不 必 同 凡 損 损 益 错 錯 综 綜 互 反 則 且 非 或 莫",
     "  Hex consts: 一 乾 坤 plus canonical 64 hexagram names",
     "  Bool consts: 真 假",
     "  Grouping: （ E ） and ( E )",
     "  Marker: 之 (explicit application/projection marker)",
     "  Construction: 之又 (iterate F twice over the next argument)",
     "  Binders: 者 甲 E, 凡 甲 E, 令 甲 V E (Hex variables only)",
     "",
     "Examples:",
     "  wenyan-surface '推 一'        # «生» «一»  (idx 2)",
     "  wenyan-surface '之又 推 乾'    # «生生» 2 «乾»",
     "  wenyan-surface '損 乾'         # «乾» − 1 = «坤»",
     "  wenyan-surface '同 一 一'      # bool true",
     "  wenyan-surface '不 同 一 乾'   # bool true",
     "  wenyan-surface '之又 不 真'    # bool true (双重否定)"]

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] =>
    IO.println usage
    return 0
  | ["--tokens", src] =>
    IO.println (tokensOutput src)
    return exitCode (tokensOk src)
  | ["--resolve", src] =>
    IO.println (resolveOutput src)
    return exitCode (resolveOk src)
  | ["--ast", src] =>
    IO.println (astOutput src)
    return exitCode (astOk src)
  | ["--typecheck", src] =>
    IO.println (typeOutput src)
    return exitCode (typecheckOk src)
  | ["--json", "--tokens", src] | ["--tokens", "--json", src] =>
    IO.println (tokensJsonOutput src)
    return exitCode (tokensOk src)
  | ["--json", "--resolve", src] | ["--resolve", "--json", src] =>
    IO.println (resolveJsonOutput src)
    return exitCode (resolveOk src)
  | ["--json", "--ast", src] | ["--ast", "--json", src] =>
    IO.println (astJsonOutput src)
    return exitCode (astOk src)
  | ["--json", "--typecheck", src] | ["--typecheck", "--json", src] =>
    IO.println (typeJsonOutput src)
    return exitCode (typecheckOk src)
  | ["--json", "--explain", src] | ["--explain", "--json", src] =>
    IO.println (explainJsonOutput src)
    return exitCode (programOk src)
  | ["--json", "--operator", code] | ["--operator", "--json", code] =>
    IO.println (operatorJsonOutput code)
    return exitCode ((operatorByCode? code).isSome)
  | ["--json", "--operators"] | ["--operators", "--json"] =>
    IO.println (operatorsJsonOutput "all")
    return 0
  | ["--json", "--operators", filter] | ["--operators", "--json", filter] =>
    IO.println (operatorsJsonOutput filter)
    return exitCode (operatorListFilterValid filter)
  | ["--json", "--coverage"] | ["--coverage", "--json"] =>
    IO.println coverageJsonOutput
    return 0
  | ["--json", src] =>
    IO.println (jsonOutput src)
    return exitCode (programOk src)
  | ["--explain", src] =>
    IO.println (explainOutput src)
    return exitCode (programOk src)
  | ["--operator", code] =>
    IO.println (operatorOutput code)
    return exitCode ((operatorByCode? code).isSome)
  | ["--operators"] =>
    IO.println (operatorsOutput "all")
    return 0
  | ["--operators", filter] =>
    IO.println (operatorsOutput filter)
    return exitCode (operatorListFilterValid filter)
  | ["--coverage"] =>
    IO.println coverageOutput
    return 0
  | [] =>
    let raw ← (← IO.getStdin).readToEnd
    let src := raw.trimAscii.toString
    if src.isEmpty then
      IO.println usage
      return 1
    else
      IO.println (runProgram src)
      return exitCode (programOk src)
  | [src] =>
    IO.println (runProgram src)
    return exitCode (programOk src)
  | _ =>
    IO.eprintln "wenyan-surface: expected 0 or 1 argument"
    IO.eprintln usage
    return 1
