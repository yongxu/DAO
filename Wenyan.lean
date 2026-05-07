/-
# Wenyan — CLI runtime for the wenyan/YiInstr language

  `wenyan run <prog.wen> [--init <hex>] [--fuel N]`
      Parse the .wen source, run on BaguaTuring, print final state.
  `wenyan print microKernel`
      Print 微核源 之 wenyan 源 to stdout (for piping into a .wen file).
  `wenyan print daoJudge`
      Print daoJudgeProg 之 wenyan 源.
  `wenyan parse <prog.wen>`
      Parse only — show resulting List YiInstr 之 Repr.
  `wenyan signatures`
      Dump the 14 exact-signature seed rows from Text/OperatorSignatures.lean.
  `wenyan readings <char>`
      Look up surface readings for a single CJK glyph (e.g. `wenyan readings 之`).

  Hex literal: 6 chars, each 0/1 (low → high), e.g. `111111` for 乾,
  `000000` for 坤. Default 乾.
-/
import SSBX.Foundation.Wen.WenyanParser
import SSBX.Foundation.Wen.WenyanSelfHost
import SSBX.Foundation.Bagua.BaguaTuring
import SSBX.Text.OperatorSignatures
import SSBX.Text.OperatorReadings

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanParser
open SSBX.Foundation.Wen.WenyanSelfHost
open SSBX.Text.OperatorSignatures
open SSBX.Text.OperatorReadings

/-! ## § 1 Hex literal parsing -/

/-- Parse a 6-char "010101" string (low → high) into a Hexagram.
    `1` = 阳 (yang), `0` = 阴 (yin). -/
def parseHexLit (s : String) : Option Hexagram :=
  match s.toList with
  | [c1, c2, c3, c4, c5, c6] => do
      let y1 ← bitToYao c1
      let y2 ← bitToYao c2
      let y3 ← bitToYao c3
      let y4 ← bitToYao c4
      let y5 ← bitToYao c5
      let y6 ← bitToYao c6
      pure ⟨y1, y2, y3, y4, y5, y6⟩
  | _ => none
where
  bitToYao : Char → Option Yao
    | '1' => some .yang
    | '0' => some .yin
    | _   => none

def hexToBits : Hexagram → String
  | ⟨y1, y2, y3, y4, y5, y6⟩ =>
    String.ofList [yaoBit y1, yaoBit y2, yaoBit y3, yaoBit y4, yaoBit y5, yaoBit y6]
where
  yaoBit : Yao → Char
    | .yang => '1'
    | .yin  => '0'

/-! ## § 2 Pretty state -/

def shiToString : SSBX.Foundation.Bagua.Cell192.Shi → String
  | .ji  => "已"
  | .jin => "今"
  | .wei => "未"

def showState (s : YiState) : String :=
  let (h, sh) := s.cur
  s!"halted={s.halted}  pc={s.pc}  cur=({hexToBits h}, {shiToString sh})  history.length={s.history.length}"

/-! ## § 3 Argument parsing (minimal flag handler) -/

structure RunOpts where
  init : Hexagram := Hexagram.qian
  fuel : Nat := 10000

/-- Parse `--init <hex>` and `--fuel <nat>` flags. Returns `none` on bad input. -/
def parseRunFlags : List String → Option RunOpts
  | [] => some {}
  | "--init" :: h :: rest => do
      let hex ← parseHexLit h
      let opts ← parseRunFlags rest
      pure { opts with init := hex }
  | "--fuel" :: n :: rest => do
      let f ← n.toNat?
      let opts ← parseRunFlags rest
      pure { opts with fuel := f }
  | _ => none

/-! ## § 4 Subcommands -/

def readSrc (path : String) : IO (Option String) := do
  try
    let s ← IO.FS.readFile path
    pure (some s)
  catch e =>
    IO.eprintln s!"error reading {path}: {e}"
    pure none

def cmdRun (path : String) (flags : List String) : IO UInt32 := do
  match (← readSrc path) with
  | none => pure 4
  | some src =>
  match parseRunFlags flags with
  | none =>
      IO.eprintln "error: bad flags (expected --init <6-bit-hex> or --fuel <nat>)"
      pure 1
  | some opts =>
      match «解程» src with
      | none =>
          IO.eprintln s!"parse error in {path}: source could not be tokenized/parsed"
          IO.eprintln s!"first 80 chars: {src.take 80}"
          pure 2
      | some prog =>
          let final := (YiState.init opts.init prog).runFuel opts.fuel
          IO.println s!"prog.length={prog.length}  init={hexToBits opts.init}  fuel={opts.fuel}"
          IO.println (showState final)
          if final.halted then pure 0 else
            IO.eprintln s!"warning: did not halt within fuel={opts.fuel}"
            pure 3

def cmdParse (path : String) : IO UInt32 := do
  match (← readSrc path) with
  | none => pure 4
  | some src =>
  match «解程» src with
  | none =>
      IO.eprintln s!"parse error in {path}"
      pure 2
  | some prog =>
      IO.println s!"-- parsed {prog.length} instructions --"
      for (instr, i) in prog.zipIdx do
        IO.println s!"pc {i}: {repr instr}"
      pure 0

def cmdPrint : String → IO UInt32
  | "microKernel" => do
      IO.println («印程» «微核源»)
      pure 0
  | "daoJudge" => do
      IO.println («印程» daoJudgeProg)
      pure 0
  | name => do
      IO.eprintln s!"unknown program: {name}  (available: microKernel, daoJudge)"
      pure 1

/-! ## § 4b Operator metadata subcommands (c27901d layer) -/

def signatureKindStr : SignatureKind → String
  | .app        => "app"
  | .endoComp   => "endoComp"
  | .propImp    => "propImp"
  | .instrument => "instrument"
  | .objectEndo => "objectEndo"
  | .propUnary  => "propUnary"
  | .opUnary    => "opUnary"
  | k           => ((repr k).pretty.takeWhile (· != ' ')).toString   -- a369867+ added many more kinds

def cmdSignatures : IO UInt32 := do
  IO.println s!"-- {exactSignatureSeed.length} exact signature seeds (Text/OperatorSignatures.lean) --"
  for sig in exactSignatureSeed do
    IO.println s!"{repr sig.id}  kind={signatureKindStr sig.kind}  arity={sig.arity}  -- {sig.note}"
  pure 0

def expectedTypeStr : ExpectedType → String
  | .unknown => "unknown"     | .function => "function"  | .prop => "prop"
  | .path => "path"           | .object => "object"      | .operator => "operator"
  | .action => "action"       | .nominal => "nominal"    | .predicate => "predicate"
  | .quantifier => "quantifier" | .modal => "modal"      | .aspect => "aspect"
  | .role => "role"           | .construction => "construction"

def constructionKindStr : ConstructionKind → String
  | .none                => "none"
  | .genitiveProjection  => "genitiveProjection"
  | .anaphora            => "anaphora"
  | .sourcePath          => "sourcePath"
  | .iteration           => "iteration"
  | .quantifier          => "quantifier"
  | .modal               => "modal"
  | .causal              => "causal"
  | .sequential          => "sequential"
  | .mohistCondition     => "mohistCondition"
  | .reflexive           => "reflexive"
  | .wholeConstruction   => "wholeConstruction"

def cmdReadings (char : String) : IO UInt32 := do
  let hits := allSurfaceReadings.filter (fun e => e.surface == char)
  if hits.isEmpty then
    IO.eprintln s!"no readings registered for «{char}»"
    IO.eprintln s!"(allSurfaceReadings has {allSurfaceReadings.length} surface entries; try a single CJK glyph like 之, 而, 故, 反, 或, 以, 自)"
    pure 1
  else do
    for entry in hits do
      IO.println s!"-- «{entry.surface}»: {entry.readings.length} reading(s) --"
      for r in entry.readings do
        let opStr := match r.operator? with
          | some id => s!"{repr id}"
          | none    => "(no catalogue id)"
        let etStr := String.intercalate "," (r.expectedTypes.map expectedTypeStr)
        IO.println s!"  {r.label}  prec={r.precedence}  expects=[{etStr}]  ctor={constructionKindStr r.construction}  op={opStr}"
        IO.println s!"    gloss: {r.gloss}"
    pure 0

/-! ## § 5 main -/

def usage : String :=
"usage:
  wenyan run <prog.wen> [--init <6-bit-hex>] [--fuel <nat>]
        Parse + run a wenyan program on BaguaTuring.
        --init: 6 chars of 0/1, low → high yao. Default 111111 (乾).
        --fuel: max steps. Default 10000.
  wenyan parse <prog.wen>
        Tokenize and show parsed instructions.
  wenyan print <microKernel|daoJudge>
        Print one of the embedded sample programs as wenyan source.
  wenyan signatures
        Dump the 14 exact-signature seed rows.
  wenyan readings <char>
        Look up surface readings for a single CJK glyph (try 之/而/故/反/或/以/自)."

def main : List String → IO UInt32
  | "run"   :: path :: flags => cmdRun path flags
  | "parse" :: [path]        => cmdParse path
  | "print" :: [name]        => cmdPrint name
  | ["signatures"]           => cmdSignatures
  | "readings" :: [char]     => cmdReadings char
  | "--help" :: _ | "-h" :: _ | [] => do
      IO.println usage; pure 0
  | args => do
      IO.eprintln s!"unknown command: {args}"
      IO.eprintln usage
      pure 1
