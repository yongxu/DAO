/-
# wen-lisp -- CLI for the 64-word V4 Lisp kernel

This executable is intentionally thin: it reads one or more S-expression top
forms from a `.wen` file, elaborates 64-word surface names through the V4-native
Lisp reader, and runs the fuelled evaluator.

Line comments start with `;`. Multiple top-level forms may be written on one
line or across lines as ordinary S-expressions.
-/

import SSBX.Foundation.Wen.V4Kernel.LispProgram
import SSBX.Foundation.Wen.V4Kernel.WenScript

open SSBX.Foundation.Lang
open SSBX.Foundation.Wen.V4Kernel
open SSBX.Foundation.Wen.V4Kernel.LispProgram

namespace WenLisp

structure RunOpts where
  fuel : Nat := 256
  trace : Bool := false
  strict : Bool := false
  strictProved : Bool := false

def parseRunFlags : List String → Option RunOpts
  | [] => some {}
  | "--fuel" :: n :: rest => do
      let f ← n.toNat?
      let opts ← parseRunFlags rest
      some { opts with fuel := f }
  | "--trace" :: rest => do
      let opts ← parseRunFlags rest
      some { opts with trace := true }
  | "--strict" :: rest => do
      let opts ← parseRunFlags rest
      some { opts with strict := true }
  | "--strict-proved" :: rest => do
      let opts ← parseRunFlags rest
      some { opts with strictProved := true }
  | _ => none

def stripLineComment (line : String) : String :=
  String.ofList (line.toList.takeWhile (fun c => c != ';'))

def stripComments (source : String) : String :=
  String.intercalate "\n" ((source.splitOn "\n").map stripLineComment)

partial def parseManySexpAux
    (chars : List Char) (acc : List Sexp) : Except ParseErr (List Sexp) :=
  let chars := Parser.skipWS chars
  match chars with
  | [] => .ok acc.reverse
  | _ =>
      match Parser.parseOne chars with
      | .ok (sexp, rest) => parseManySexpAux rest (sexp :: acc)
      | .error err => .error err

def parseManySexp (source : String) : Except ParseErr (List Sexp) :=
  parseManySexpAux (stripComments source).toList []

def readTopFormsSource (source : String) : Option (List SurfaceTopForm) := do
  let sexps ←
    match parseManySexp source with
    | .ok forms => some forms
    | .error _ => none
  readTopSexpList sexps
where
  readTopSexpList : List Sexp → Option (List SurfaceTopForm)
    | [] => some []
    | sexp :: rest => do
        let form ← LispReader.readTop sexp
        let forms ← readTopSexpList rest
        some (form :: forms)

def bitChar (b : Bool) : Char :=
  if b then 'x' else 'o'

def wordBits (word : Word64) : String :=
  String.ofList
    [ bitChar word.first.contentBit
    , bitChar word.first.frameBit
    , bitChar word.second.contentBit
    , bitChar word.second.frameBit
    , bitChar word.third.contentBit
    , bitChar word.third.frameBit
    ]

def wordShow (word : Word64) : String :=
  let bits := wordBits word
  match SSBX.Foundation.Lang.Lexicon.hexagram.find? (fun entry => entry.bits == bits) with
  | some entry => s!"{entry.chinese}/{entry.english}/{bits}"
  | none => bits

def valueShow : Value → String
  | .atom .dao => "dao"
  | .atom .cuo => "cuo"
  | .atom .zong => "zong"
  | .atom .cuoZong => "cuoZong"
  | .symbol name => s!"symbol({wordShow name})"
  | .num n => toString n
  | .nil => "nil"
  | .cons head tail => s!"({valueShow head} . {valueShow tail})"
  | .closure _ _ _ => "<closure>"
  | .prim p => s!"<prim {repr p}>"

def v4Show : SSBX.Foundation.Hierarchy.Operators.V4 → String
  | .dao => "道"
  | .cuo => "错"
  | .zong => "综"
  | .cuoZong => "错综"

def r5Show (value : WenScript.R5Word) : String :=
  let view := value.toView
  s!"{value.chinese}  r4={value.base.chinese}  v4=({v4Show view.first}, {v4Show view.second})  extension={value.extension.chinese}"

def semanticKindShow : WenScript.SemanticCertificateKind → String
  | .cyclicPersistence => "cyclicPersistence"
  | .rootActionImplication => "rootActionImplication"
  | .aliasIdentity => "aliasIdentity"
  | .copulaAlias => "copulaAlias"
  | .aliasInseparability => "aliasInseparability"
  | .certificateAvailability => "certificateAvailability"
  | .stateImplication => "stateImplication"
  | .universalSchema => "universalSchema"
  | .universalInstantiation => "universalInstantiation"
  | .readThenVerifyAvailable => "readThenVerifyAvailable"
  | .v4ActionTrace => "v4ActionTrace"
  | .rootActionTrace => "rootActionTrace"
  | .openObligationAvailability => "openObligationAvailability"
  | .frontierClean => "frontierClean"
  | .calculationAvailability => "calculationAvailability"
  | .openCalculationAvailability => "openCalculationAvailability"
  | .nameAvailability => "nameAvailability"
  | .pendingNameAvailability => "pendingNameAvailability"
  | .wenCapability => "wenCapability"
  | .nameResolutionRule => "nameResolutionRule"
  | .v4OperatorTopic => "v4OperatorTopic"
  | .wenBoundary => "wenBoundary"
  | .nameValueLaw => "nameValueLaw"
  | .v4DualityLaw => "v4DualityLaw"
  | .rootStructureLaw => "rootStructureLaw"
  | .textSchemaInstantiation => "textSchemaInstantiation"
  | .topicRegistration => "topicRegistration"
  | .implicationRegistration => "implicationRegistration"
  | .operatorRegistration => "operatorRegistration"

def diagnosticKindShow : WenScript.DiagnosticKind → String
  | .unsupportedTopicTheorem => "unsupportedTopicTheorem"
  | .unsupportedImplicationProof => "unsupportedImplicationProof"
  | .unsupportedUniversalInstantiation => "unsupportedUniversalInstantiation"
  | .unsupportedReadThenVerify => "unsupportedReadThenVerify"
  | .unsupportedTextLayerOperator => "unsupportedTextLayerOperator"
  | .unsupportedApplicationGrammar => "unsupportedApplicationGrammar"
  | .unknownActionArgument => "unknownActionArgument"
  | .claimStub => "claimStub"

def readingKindShow : Root512.ReadingKind → String
  | .cell => "cell"
  | .operator => "operator"

def rootReadingShow (reading : Root512.RootReading) : String :=
  s!"{wordShow reading.cell.word}@{v4Show reading.cell.temporal}/{readingKindShow reading.kind}"

def parseErrorShow : WenScript.ParseError → String
  | .missingZeroStart => "missing required first line: 零起"
  | .emptyDocument => "empty document"

def frontierSummaryShow (summary : WenScript.FrontierSummary) : String :=
  s!"frontier topic={summary.unsupportedTopicTheorems} implication={summary.unsupportedImplicationProofs} universal={summary.unsupportedUniversalInstantiations} readThen={summary.unsupportedReadThenVerifications} textLayer={summary.unsupportedTextLayerOperators} application={summary.unsupportedApplicationGrammars} unknownArg={summary.unknownActionArguments} claimStub={summary.claimStubDiagnostics}"

def readSrc (path : String) : IO (Option String) := do
  try
    let s ← IO.FS.readFile path
    pure (some s)
  catch e =>
    IO.eprintln s!"error reading {path}: {e}"
    pure none

def cmdParse (path : String) : IO UInt32 := do
  match (← readSrc path) with
  | none => pure 4
  | some src =>
      match parseManySexp src with
      | .error err =>
          IO.eprintln s!"parse error in {path}: {repr err}"
          pure 2
      | .ok sexps =>
          match readTopFormsSource src with
          | none =>
              IO.eprintln s!"reader error in {path}: unknown word, primitive, or malformed top form"
              pure 3
          | some forms =>
              IO.println s!"-- parsed {forms.length} top forms --"
              for (sexp, i) in sexps.zipIdx do
                IO.println s!"form {i}: {sexp}"
              pure 0

def cmdRun (path : String) (flags : List String) : IO UInt32 := do
  match parseRunFlags flags with
  | none =>
      IO.eprintln "error: bad flags (expected --fuel <nat> and optional --trace)"
      pure 1
  | some opts =>
      match (← readSrc path) with
      | none => pure 4
      | some src =>
          match readTopFormsSource src with
          | none =>
              IO.eprintln s!"parse/reader error in {path}"
              pure 2
          | some forms =>
              match evalSurfaceFormsFuel opts.fuel [] forms with
              | none =>
                  IO.eprintln s!"evaluation failed in {path} with fuel={opts.fuel}"
                  pure 3
              | some (global, values) =>
                  IO.println s!"forms={forms.length}  fuel={opts.fuel}  globals={global.length}"
                  if opts.trace then
                    for (value, i) in values.zipIdx do
                      IO.println s!"[{i}] {valueShow value}"
                  match values.reverse with
                  | [] => IO.println "=> nil"
                  | final :: _ => IO.println s!"=> {valueShow final}"
                  pure 0

def cmdProve (path : String) (flags : List String) : IO UInt32 := do
  match parseRunFlags flags with
  | none =>
      IO.eprintln "error: bad flags (expected optional --trace, --strict, or --strict-proved)"
      pure 1
  | some opts =>
      match (← readSrc path) with
      | none => pure 4
      | some src =>
          match WenScript.parseDocument src with
          | .error err =>
              IO.eprintln s!"wenscript parse error in {path}: {parseErrorShow err}"
              pure 2
          | .ok doc =>
              let report := WenScript.proveDocument doc
              let frontier := report.frontierSummary
              IO.println s!"sentences={doc.sentences.length}  definitions={report.definitions.length}  certificates={report.certificates.length}  claimStubs={report.claimStubs.length}"
              IO.println s!"semanticCertificates={report.semanticCertificates.length}  checked={report.semanticCheckedCount}  registrations={report.semanticRegistrationCount}  diagnostics={report.diagnostics.length}"
              IO.println s!"certificateKinds executable={report.semanticExecutableCount}  status={report.semanticStatusCount}  evidence={report.semanticEvidenceCount}"
              IO.println s!"registrations topic={report.semanticKindCount .topicRegistration}  implication={report.semanticKindCount .implicationRegistration}  operator={report.semanticKindCount .operatorRegistration}  universalSchema={report.semanticKindCount .universalSchema}"
              IO.println (frontierSummaryShow frontier)
              IO.println s!"aliases={report.aliasCount}  enums={report.enumCount}  readThenVerify={report.readVerifyCount}"
              IO.println s!"topicComments={report.topicComments.length}  implications={report.implications.length}  universals={report.universals.length}"
              IO.println s!"operatorApps={report.operatorApps.length}  v4Actions={report.v4Actions.length}  rootApplications={report.rootApplications.length}"
              IO.println s!"assertions={report.assertions.length}  barePhrases={report.barePhrases.length}"
              if opts.trace then
                for ((name, value), i) in report.definitions.reverse.zipIdx do
                  IO.println s!"def[{i}] {name} := {r5Show value}"
                for (cert, i) in report.semanticCertificates.reverse.zipIdx do
                  IO.println s!"semanticCert[{i}] {cert.subject} 者 {cert.body} :: {semanticKindShow cert.kind} wellFormed={cert.wellFormed}"
                for ((subject, body), i) in report.topicComments.reverse.zipIdx do
                  IO.println s!"topic[{i}] {subject} 者 {body}"
                for ((condition, conclusion), i) in report.implications.reverse.zipIdx do
                  IO.println s!"implication[{i}] 若 {condition} 则 {conclusion}"
                for ((domain, predicate), i) in report.universals.reverse.zipIdx do
                  IO.println s!"universal[{i}] 凡 {domain} 皆 {predicate}"
                for (app, i) in report.operatorApps.reverse.zipIdx do
                  IO.println s!"operatorApp[{i}] {WenScript.OperatorApplication.summary app}"
                for (trace, i) in report.v4Actions.reverse.zipIdx do
                  IO.println s!"v4Action[{i}] {trace.operatorSurface} 之 {trace.argumentSurface} => {wordShow trace.result}"
                for (trace, i) in report.rootApplications.reverse.zipIdx do
                  IO.println s!"rootApplication[{i}] {trace.operatorSurface} 之 {trace.argumentSurface} :: {rootReadingShow trace.operator} applied to {rootReadingShow trace.argument} => {rootReadingShow trace.result}"
                for (body, i) in report.assertions.reverse.zipIdx do
                  IO.println s!"assertion[{i}] {body}也"
                for ((text, tokens), i) in report.barePhrases.reverse.zipIdx do
                  IO.println s!"bare[{i}] {text}  tokens={tokens}"
                for ((text, tokens), i) in report.claimStubs.reverse.zipIdx do
                  IO.println s!"stub[{i}] {text}  tokens={tokens}"
                for (diag, i) in report.diagnostics.reverse.zipIdx do
                  IO.println s!"diagnostic[{i}] span={diag.span.line}:{diag.span.startColumn}-{diag.span.endColumn} {diagnosticKindShow diag.kind}: {diag.message} :: {diag.text}"
              let hasOpenSyntax := !report.strictClean
              let hasRegistrations := report.semanticRegistrationCount > 0
              if opts.strict && hasOpenSyntax then
                IO.eprintln s!"strict prove failed: diagnostics={report.diagnostics.length} claimStubs={report.claimStubs.length}"
                pure 3
              else if opts.strictProved && (hasOpenSyntax || hasRegistrations) then
                IO.eprintln s!"strict-proved failed: diagnostics={report.diagnostics.length} claimStubs={report.claimStubs.length} registrations={report.semanticRegistrationCount}"
                pure 3
              else
                pure 0

def usage : String :=
"usage:
  wen-lisp run <program.wen> [--fuel <nat>] [--trace]
        Parse and run a 64-word V4 Lisp program.
  wen-lisp parse <program.wen>
        Parse only and print top-level forms.
  wen-lisp prove <program.wen> [--trace] [--strict] [--strict-proved]
        Parse a 零起 controlled-wen proof script and emit structural certificates.
        Add --strict to return nonzero if diagnostics or claim stubs remain.
        Add --strict-proved to also fail while registration-only certificates remain.

File format:
  One or more S-expression top forms. Line comments start with ';'.
  Examples:
    (define 乾 10)
    (define 坤 (add 乾 32))
    坤"

def main : List String → IO UInt32
  | "run" :: path :: flags => cmdRun path flags
  | "parse" :: [path] => cmdParse path
  | "prove" :: path :: flags => cmdProve path flags
  | "--help" :: _ | "-h" :: _ | [] => do
      IO.println usage
      pure 0
  | args => do
      IO.eprintln s!"unknown command: {args}"
      IO.eprintln usage
      pure 1

end WenLisp

def main (args : List String) : IO UInt32 :=
  WenLisp.main args
