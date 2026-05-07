import SSBX.Foundation.Wen.WenyanSelfInterp
import SSBX.Foundation.Bagua.KleeneInternal

namespace SSBX.Foundation.Wen.WenyanFramedProg

open WenyanSelfInterp
open SSBX.Foundation.Bagua
open SSBX.Foundation.Bagua.BaguaTuring

/-- Framed Wen program input: a length-delimited YiInstr program. -/
def encFramedProg := KleeneInternal.LenProgInput

/-- Decode a framed Wen program input. -/
def decFramedProg := KleeneInternal.decLenProgInput

/-- Framed Wen program inputs round-trip through the length-delimited decoder. -/
theorem decFramedProg_encFramedProg_self (P)
    (h_len : KleeneInternal.ProgLenBounded P)
    (h_enc : ProgEnc.AllEncodable P) :
    decFramedProg (encFramedProg P) = some (P, []) :=
  KleeneInternal.decLenProgInput_self P h_len h_enc

/-- Concrete framed-program round-trip witness for the Dao judge. -/
theorem daoJudgeProg_framed_roundtrip :
    decFramedProg (encFramedProg daoJudgeProg) = some (daoJudgeProg, []) :=
  decFramedProg_encFramedProg_self daoJudgeProg
    (by
      unfold KleeneInternal.ProgLenBounded
      native_decide)
    (by
      intro i hi
      simp [daoJudgeProg] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        simp [YiInstrEnc.Encodable] <;> native_decide)

end SSBX.Foundation.Wen.WenyanFramedProg
