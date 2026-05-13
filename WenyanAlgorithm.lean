/-
# wenyan-algorithm -- runner for pure-wenyan algorithm files

This executable is intentionally narrow.  It parses the pure wenyan algorithm
files in `examples/wenyan-native/`, lowers them to native Wen top forms through
`SSBX.Foundation.Wen.WenyanAlgorithms`, and runs them with the native evaluator;
it does not use the Lisp reader.
-/

import SSBX.Foundation.Wen.WenyanAlgorithms

namespace WenyanAlgorithm

open SSBX.Foundation.Wen.WenyanAlgorithms

def parseNatArgs : List String → Option (List Nat)
  | [] => some []
  | arg :: rest => do
      let n ← parseWenNat arg
      let ns ← parseNatArgs rest
      some (n :: ns)

def readSrc (path : String) : IO (Option String) := do
  try
    let source ← IO.FS.readFile path
    pure (some source)
  catch e =>
    IO.eprintln s!"error reading {path}: {e}"
    pure none

def runPath (path : String) (rawInput : List String) : IO UInt32 := do
  let inputOverride? ←
    if rawInput.isEmpty then
      pure (some none)
    else
      match parseNatArgs rawInput with
      | some input => pure (some (some input))
      | none =>
          IO.eprintln "bad input list; use Arabic numerals or simple wenyan numerals"
          pure none
  match inputOverride? with
  | none => pure 1
  | some inputOverride =>
      match (← readSrc path) with
      | none => pure 4
      | some source =>
          match runSource? source inputOverride with
          | none =>
              IO.eprintln "not runnable: parse failed, evaluation failed, or no sample input was found"
              IO.eprintln "supported grammar: 法曰/受/若...空，归/取...之首余/令...为/归/试以"
              pure 2
          | some result =>
              IO.println (runResultShow result)
              pure 0

def usage : String :=
  String.intercalate "\n"
    [ "usage:"
    , "  wenyan-algorithm <file.wen> [N...]"
    , "  wenyan-algorithm run <file.wen> [N...]"
    , ""
    , "examples:"
    , "  wenyan-algorithm examples/wenyan-native/quicksort.wen"
    , "  wenyan-algorithm examples/wenyan-native/quicksort.wen 9 4 1 4"
    ]

def main : List String → IO UInt32
  | [] => do
      IO.println usage
      pure 1
  | ["--help"] | ["-h"] => do
      IO.println usage
      pure 0
  | "run" :: path :: input => runPath path input
  | path :: input => runPath path input

end WenyanAlgorithm

def main (args : List String) : IO UInt32 :=
  WenyanAlgorithm.main args
