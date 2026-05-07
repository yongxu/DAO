/-
# wenyan-surface — minimal CLI for the WenSurface interpreter

Reads a wenyan program from stdin or a single argv argument, runs it through
`SSBX.Foundation.Wen.WenSurface.wenyanInterp` (and `wenyanInterpBool` as a
fallback for Bool-typed programs), and prints the result.

Examples:
  echo '推 一'         | wenyan-surface
  wenyan-surface '之又 推 乾'
  wenyan-surface '同 一 一'

This binary is parallel to (not a replacement for) the baguaWen CLI on the
`claude/pensive-meitner-c79a1f` branch, which speaks the 22-token controlled IL
syntax. WenyanSurface speaks the surface language: 推/比/不/必/同/凡/損/损/益,
hex consts 一/乾/坤, bool 真/假, marker 之, construction 之又.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenSurface

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

private def errShow : WenSurfaceErr → String
  | .lex (.unexpected col ch) =>
      s!"lex error at col {col}: unexpected character '{ch}'"
  | .lex .fuelExhausted =>
      "lex fuel exhausted (internal: should not occur at sane fuel)"
  | .resolve (.noReading surface col) =>
      s!"resolve error at col {col}: surface \"{surface}\" has no known reading"
  | .elab (.unsupportedOp id) =>
      s!"elab error: operator {repr id} not yet supported in v1"
  | .elab .empty =>
      "elab error: empty / incomplete expression"
  | .elab (.leftoverAtoms n) =>
      s!"elab error: {n} leftover atom(s) past parsed expression"
  | .elab .fuelExhausted =>
      "elab error: fuel exhausted (program too deeply nested?)"
  | .denoteFailed =>
      "denote failed (likely a type mismatch — Tm did not reduce to Hex/Bool)"

/-! ## Run a single program -/

private def runProgram (src : String) : String :=
  -- Try Hex first; if that fails for a denote reason, try Bool.
  match wenyanInterp src with
  | .ok h => hexShow h
  | .error eHex =>
    match wenyanInterpBool src with
    | .ok b => s!"bool {b}"
    | .error _ => errShow eHex   -- show the original (Hex-attempt) error

/-! ## CLI -/

private def usage : String :=
  String.intercalate "\n"
    ["Usage: wenyan-surface <PROGRAM>",
     "       echo <PROGRAM> | wenyan-surface",
     "       wenyan-surface --help",
     "",
     "Surface vocabulary (v1):",
     "  Operators: 推 比 不 必 同 凡 損 损 益",
     "  Hex consts: 一 乾 坤",
     "  Bool consts: 真 假",
     "  Marker: 之 (function-application; treated as noop juxtaposition)",
     "  Construction: 之又 (iterate F twice over the next argument)",
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
  | [] =>
    let raw ← (← IO.getStdin).readToEnd
    let src := raw.trimAscii.toString
    if src.isEmpty then
      IO.println usage
      return 0
    else
      IO.println (runProgram src)
      return 0
  | [src] =>
    IO.println (runProgram src)
    return 0
  | _ =>
    IO.eprintln "wenyan-surface: expected 0 or 1 argument"
    IO.eprintln usage
    return 1
