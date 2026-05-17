/-
# wen — interactive 文言 read-eval-print loop

Wraps the existing
[wenyanCompile / wenyanInterp / wenyanInterpBool](formal/SSBX/Foundation/Wen/WenSurface/EndToEnd.lean)
pipeline behind a tiny REPL.

Commands:
  - `:help`           -- list commands
  - `:quit`           -- exit (Ctrl-D / EOF same effect)
  - `:type <expr>`    -- show the elaborated type of `<expr>`
  - `<expr>`          -- compile + evaluate + show result

Implementation: [`Foundation.Wen.REPL`](formal/SSBX/Foundation/Wen/REPL.lean).
-/

import SSBX.Foundation.Wen.REPL

def main : IO Unit :=
  SSBX.Foundation.Wen.REPL.main
