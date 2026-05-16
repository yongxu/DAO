/-
# Wen.RKernel — Lisp-style interpreter over the V4 alphabet (= R 2)

Per `wen-substrate.md` v1.4 §3.7.8 (distinction monism), R-family is the
**one mathematical core**.  This kernel uses `V4` (the constructor-style
presentation of `R 2`, with bridge `V4 ≃ R 2` proven at
`Foundation/Hierarchy/Operators/V4/Core.lean`) as the program alphabet.
Programs are free syntax over V4, quoted as V4 trees, interpreted by a
universal evaluator.  The structural types ascend through the R-tower
(also explicitly bridged):

* `Mode16 = V4 × V4 ≃ R 4` (action-mode space) — see `Mode16.equivR4`
* `Word64 = V4³ ≃ R 6` (word coordinate) — see `Word64.equivR6`
* `RootCell256 ⊂ Root512 ≅ R 8` (R8-cell reading) — see `RootCell256.equivR8`

Lisp is one runnable surface over this kernel, not the ontology itself.
The ontology is R-family.
-/

import SSBX.Foundation.Wen.RKernel.Syntax
import SSBX.Foundation.Wen.RKernel.Semantics
import SSBX.Foundation.Wen.RKernel.Encode
import SSBX.Foundation.Wen.RKernel.Universal
import SSBX.Foundation.Wen.RKernel.SelfHost
import SSBX.Foundation.Wen.RKernel.Data
import SSBX.Foundation.Wen.RKernel.Combinator
import SSBX.Foundation.Wen.RKernel.Binding
import SSBX.Foundation.Wen.RKernel.RBackend
import SSBX.Foundation.Wen.RKernel.Word64
import SSBX.Foundation.Wen.RKernel.Mode16
import SSBX.Foundation.Wen.RKernel.Root512
import SSBX.Foundation.Wen.RKernel.ActionSemantics
import SSBX.Foundation.Wen.RKernel.WenAction
import SSBX.Foundation.Wen.RKernel.WenTrace
import SSBX.Foundation.Wen.RKernel.WenRecursion
import SSBX.Foundation.Wen.RKernel.WenR5
import SSBX.Foundation.Wen.RKernel.WenR6
import SSBX.Foundation.Wen.RKernel.WenScript
import SSBX.Foundation.Wen.RKernel.LispSyntax
import SSBX.Foundation.Wen.RKernel.LispPrim
import SSBX.Foundation.Wen.RKernel.LispEval
import SSBX.Foundation.Wen.RKernel.LispQuote
import SSBX.Foundation.Wen.RKernel.LispUniversal
import SSBX.Foundation.Wen.RKernel.LispRBackend
import SSBX.Foundation.Wen.RKernel.LispRSpacePlan
import SSBX.Foundation.Wen.RKernel.LispSurface
import SSBX.Foundation.Wen.Layered.Bridges.Word64
import SSBX.Foundation.Wen.RKernel.LispReader
import SSBX.Foundation.Wen.RKernel.LispDaodejing
import SSBX.Foundation.Wen.RKernel.LispProgram
import SSBX.Foundation.Wen.RKernel.LispTrace
import SSBX.Foundation.Wen.RKernel.LispAlgorithms
import SSBX.Foundation.Wen.RKernel.LispCompile
import SSBX.Foundation.Wen.RKernel.LispMetaInterp
