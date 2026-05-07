import SSBX.Foundation.Wen.WenyanQuineSpec
import SSBX.Foundation.Wen.WenyanQuineEncoding
import SSBX.Foundation.Wen.WenyanQuineEmitter
import SSBX.Foundation.Wen.WenyanQuineHistory
import SSBX.Foundation.Wen.WenyanQuineWitness
import SSBX.Foundation.Wen.WenyanQuineConcreteSearch
import SSBX.Foundation.Wen.WenyanQuineKleene
import SSBX.Foundation.Wen.WenyanFramedProg
import SSBX.Foundation.Wen.WenyanQuineMeta

/-!
# WenyanQuine

Aggregate module for the Tier 3 raw runtime quine lane.
-/

namespace SSBX.Foundation.Wen.WenyanQuine

open SSBX.Foundation.Wen.WenyanQuineWitness

export SSBX.Foundation.Wen.WenyanQuineEmitter
  (emitCellFrom emitCellFrom_length_le)

export SSBX.Foundation.Wen.WenyanQuineHistory
  (emitCellsFrom emitCellsFrom_history_three)

export SSBX.Foundation.Wen.WenyanQuineWitness
  (quineSource quineInit quineFuel quine3_history quine5_history quine16_history
   wenyan_tier3_quine_complete)

export SSBX.Foundation.Wen.WenyanQuineSpec
  (QuineRunSpec RawTargetTheoremStatement literal_diagonal_gate)

export SSBX.Foundation.Wen.WenyanQuineEncoding
  (encProg_eq_flatten allEncodable_replicate_push decInstrs_encProg_replicate_push_nil)

export SSBX.Foundation.Wen.WenyanQuineConcreteSearch
  (generated_emits_seed_encoding generated_not_self_encoding
   literal_emitter_fixed_point_obstruction)

export SSBX.Foundation.Wen.WenyanQuineKleene
  (QuoterSpec SelfApplicationSpec KleeneQuinePayload HistoryEqualityFixedPointExists
   wenyanQuineKleene_summary)

end SSBX.Foundation.Wen.WenyanQuine
