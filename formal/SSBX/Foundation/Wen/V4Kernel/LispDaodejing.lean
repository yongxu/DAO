/-
# Wen.V4Kernel.LispDaodejing -- two small Daodejing smoke interpretations

These are executable 64-word Lisp readings of two Daodejing fragments.  They do
not claim that the reader parses raw classical Chinese prose; the surface here
is the current S-expression Wen Lisp over the R6/King Wen 64-word set.
-/

import SSBX.Foundation.Wen.V4Kernel.LispReader

namespace SSBX.Foundation.Wen.V4Kernel

namespace LispDaodejing

/-!
Fragment 1, Daodejing 2: 有无相生.

Executable reading: 乾 as origin/identity and 坤 as receptive full-dual are
composed as 64-word symbols.  Identity leaves the other pole visible.
-/

def mutualArisingSource : String :=
  "(wordCompose (quote 乾) (quote 坤))"

def mutualArisingExpr : Expr :=
  .app (.prim .wordCompose) (Expr.list [.quote (.symbol .qian), .quote (.symbol .kun)])

theorem mutualArising_eval :
    evalFuel 8 [] mutualArisingExpr = some (.symbol .kun) := by
  change some (Value.symbol (Word64.compose Word64.qian Word64.kun)) =
    some (Value.symbol Word64.kun)
  rfl

/-!
Fragment 2, Daodejing 40: 反者道之动.

Executable reading: the full-dual word composed with itself returns to origin.
This tests the V4-native involutive law at the 64-word level.
-/

def returningMotionSource : String :=
  "(wordCompose (quote 坤) (quote 坤))"

def returningMotionExpr : Expr :=
  .app (.prim .wordCompose) (Expr.list [.quote (.symbol .kun), .quote (.symbol .kun)])

theorem returningMotion_eval :
    evalFuel 8 [] returningMotionExpr = some (.symbol .qian) := by
  change some (Value.symbol (Word64.compose Word64.kun Word64.kun)) =
    some (Value.symbol Word64.qian)
  rfl

#eval LispReader.readEvalTopString 8 [] mutualArisingSource
#eval LispReader.readEvalTopString 8 [] returningMotionSource

theorem daodejing_smoke_summary :
    evalFuel 8 [] mutualArisingExpr = some (.symbol .kun)
    ∧ evalFuel 8 [] returningMotionExpr = some (.symbol .qian) :=
  ⟨mutualArising_eval, returningMotion_eval⟩

end LispDaodejing

end SSBX.Foundation.Wen.V4Kernel
