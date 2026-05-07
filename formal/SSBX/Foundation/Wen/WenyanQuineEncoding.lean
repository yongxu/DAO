import SSBX.Foundation.Wen.WenyanSelfInterp

namespace SSBX.Foundation.Wen.WenyanQuineEncoding

open WenyanSelfInterp
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.Cell192

/-!
Raw program-encoding boundary lemmas for the quine work.

This file intentionally stops at `ProgEnc.encProg/decInstrs` facts; it does
not state or prove the final quine theorem.
-/

/-- `ProgEnc.encProg` is exactly raw flattening of per-instruction encodings. -/
theorem encProg_eq_flatten (p : List YiInstr) :
    ProgEnc.encProg p = (p.map YiInstrEnc.encInstr).flatten := by
  rfl

/-- Raw program encoding is concatenative. -/
theorem encProg_append (p q : List YiInstr) :
    ProgEnc.encProg (p ++ q) = ProgEnc.encProg p ++ ProgEnc.encProg q := by
  simp [ProgEnc.encProg, List.map_append]

/-- A program made only of `push` instructions is fully encodable. -/
theorem allEncodable_replicate_push (n : Nat) :
    ProgEnc.AllEncodable (List.replicate n YiInstr.push) := by
  intro i hi
  have hi_push : i = YiInstr.push := List.eq_of_mem_replicate hi
  rw [hi_push]
  trivial

/-- Program-level decoder witness for a raw replicated-`push` program. -/
theorem decInstrs_encProg_replicate_push (n : Nat) (rest : List Cell192) :
    ProgEnc.decInstrs (List.replicate n YiInstr.push).length
      (ProgEnc.encProg (List.replicate n YiInstr.push) ++ rest) =
        some (List.replicate n YiInstr.push, rest) := by
  exact ProgEnc.decInstrs_encProg
    (List.replicate n YiInstr.push)
    (allEncodable_replicate_push n)
    rest

/-- Closed-stream decoder witness for a raw replicated-`push` program. -/
theorem decInstrs_encProg_replicate_push_nil (n : Nat) :
    ProgEnc.decInstrs (List.replicate n YiInstr.push).length
      (ProgEnc.encProg (List.replicate n YiInstr.push)) =
        some (List.replicate n YiInstr.push, []) := by
  simpa using decInstrs_encProg_replicate_push n []

end SSBX.Foundation.Wen.WenyanQuineEncoding
