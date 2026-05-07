import SSBX.Foundation.Wen.WenyanSelfInterp

namespace SSBX.Foundation.Wen.WenyanQuineMeta

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring

/-- A tiny optional-handler lane witness: write `未`, then halt. -/
def setShiHandler : List YiInstr :=
  [YiInstr.setShi Shi.wei, YiInstr.halt]

theorem setShiHandler_runFuel2 (h : Hexagram) :
    let st := (YiState.init h setShiHandler).runFuel 2
    st.halted = true ∧ st.cur.2 = Shi.wei := by
  constructor <;> rfl

end SSBX.Foundation.Wen.WenyanQuineMeta
