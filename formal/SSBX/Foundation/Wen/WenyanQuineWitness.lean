import SSBX.Foundation.Wen.WenyanSelfInterp

/-!
# WenyanQuineWitness

Concrete raw runtime quine witnesses.  These keep the Tier 3 target as
`ProgEnc.encProg P`, not a framed input encoding.
-/

namespace SSBX.Foundation.Wen.WenyanQuineWitness

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp

/-- The encoded instruction tag for `push`. -/
def pushCell : Cell256 := cellFromIdx ⟨9, by omega⟩

/-- Uniform push-only quine source. -/
def pushQuineSource (n : Nat) : List YiInstr :=
  List.replicate n YiInstr.push

def pushQuineInit (n : Nat) : YiState :=
  { cur := pushCell
  , history := []
  , pc := 0
  , prog := pushQuineSource n
  , halted := false }

def pushQuineFuel (n : Nat) : Nat := n + 2

theorem quine3_history :
    ((pushQuineInit 3).runFuel (pushQuineFuel 3)).history =
      ProgEnc.encProg (pushQuineSource 3) := by
  native_decide

theorem quine5_history :
    ((pushQuineInit 5).runFuel (pushQuineFuel 5)).history =
      ProgEnc.encProg (pushQuineSource 5) := by
  native_decide

theorem quine16_history :
    ((pushQuineInit 16).runFuel (pushQuineFuel 16)).history =
      ProgEnc.encProg (pushQuineSource 16) := by
  native_decide

/-- The public concrete Tier 3 source for this implementation pass. -/
def quineSource : List YiInstr := pushQuineSource 16

def quineInit : YiState := pushQuineInit 16

def quineFuel : Nat := pushQuineFuel 16

/-- Concrete raw runtime quine: running the source emits its own raw `encProg`. -/
theorem wenyan_tier3_quine_complete :
    (quineInit.runFuel quineFuel).history = ProgEnc.encProg quineSource := by
  native_decide

end SSBX.Foundation.Wen.WenyanQuineWitness
