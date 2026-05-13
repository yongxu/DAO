/-
# Wen.V4Kernel -- V4-based interpreter and action-trace kernel

V4 is the alphabet.  Programs are free syntax over V4, quoted as V4 trees, and
interpreted by a universal evaluator for this kernel fragment.  The structural
core is `Mode16 = V4 x V4` acting above Word64/R8 as a trace calculus; Lisp is
one runnable surface over that kernel, not the ontology itself.
-/

import SSBX.Foundation.Wen.V4Kernel.Syntax
import SSBX.Foundation.Wen.V4Kernel.Semantics
import SSBX.Foundation.Wen.V4Kernel.Encode
import SSBX.Foundation.Wen.V4Kernel.Universal
import SSBX.Foundation.Wen.V4Kernel.SelfHost
import SSBX.Foundation.Wen.V4Kernel.Data
import SSBX.Foundation.Wen.V4Kernel.Combinator
import SSBX.Foundation.Wen.V4Kernel.Binding
import SSBX.Foundation.Wen.V4Kernel.RBackend
import SSBX.Foundation.Wen.V4Kernel.Word64
import SSBX.Foundation.Wen.V4Kernel.Mode16
import SSBX.Foundation.Wen.V4Kernel.Root512
import SSBX.Foundation.Wen.V4Kernel.ActionSemantics
import SSBX.Foundation.Wen.V4Kernel.WenAction
import SSBX.Foundation.Wen.V4Kernel.WenTrace
import SSBX.Foundation.Wen.V4Kernel.WenRecursion
import SSBX.Foundation.Wen.V4Kernel.WenR5
import SSBX.Foundation.Wen.V4Kernel.WenR6
import SSBX.Foundation.Wen.V4Kernel.WenScript
import SSBX.Foundation.Wen.V4Kernel.LispSyntax
import SSBX.Foundation.Wen.V4Kernel.LispPrim
import SSBX.Foundation.Wen.V4Kernel.LispEval
import SSBX.Foundation.Wen.V4Kernel.LispQuote
import SSBX.Foundation.Wen.V4Kernel.LispUniversal
import SSBX.Foundation.Wen.V4Kernel.LispRBackend
import SSBX.Foundation.Wen.V4Kernel.LispRSpacePlan
import SSBX.Foundation.Wen.V4Kernel.LispSurface
import SSBX.Foundation.Wen.Layered.Bridges.Word64
import SSBX.Foundation.Wen.V4Kernel.LispReader
import SSBX.Foundation.Wen.V4Kernel.LispDaodejing
import SSBX.Foundation.Wen.V4Kernel.LispProgram
import SSBX.Foundation.Wen.V4Kernel.LispTrace
import SSBX.Foundation.Wen.V4Kernel.LispAlgorithms
import SSBX.Foundation.Wen.V4Kernel.LispCompile
import SSBX.Foundation.Wen.V4Kernel.LispMetaInterp
