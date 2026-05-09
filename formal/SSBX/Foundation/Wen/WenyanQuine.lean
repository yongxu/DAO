import SSBX.Foundation.Wen.WenyanQuineSpec
import SSBX.Foundation.Wen.WenyanQuineEncoding
import SSBX.Foundation.Wen.WenyanQuineEmitter
import SSBX.Foundation.Wen.WenyanQuineHistory
import SSBX.Foundation.Wen.WenyanQuineWitness
import SSBX.Foundation.Wen.WenyanQuineConcreteSearch
import SSBX.Foundation.Wen.WenyanQuineKleene
import SSBX.Foundation.Wen.WenyanLambdaBridge
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

export SSBX.Foundation.Wen.WenyanLambdaRoute
  (Tier3QuineExists LambdaHistoryFixedPointExists LambdaHistoryBackend LambdaQuotationBackend
   lambdaHistoryFixedPointExists_to_tier3QuineExists
   lambda_history_backend_finishes_tier3 lambda_history_backend_gives_tier3_quine
   lambda_backend_finishes_tier3)

export SSBX.Foundation.Wen.WenyanLambdaBridge.LamRoute
  (quoteInstr quoteProg beta_step_simulates_wen
   JianLambdaHistoryBackend JianLambdaQuotationBackend)

export SSBX.Foundation.Wen.WenyanLambdaBridge.LamRoute.JianLambdaHistoryBackend
  (finishes_tier3 gives_tier3_quine)

export SSBX.Foundation.Wen.WenyanLambdaBridge.LamRoute.JianLambdaQuotationBackend
  (finishes_tier3 gives_tier3_quine)

export SSBX.Foundation.Wen.WenyanLambdaBridge.LamRoute
  (constJianLambdaHistoryBackend
   constJianLambdaHistoryBackend_gives_tier3_quine
   constJianLambdaHistoryBackend_finishes_tier3)

end SSBX.Foundation.Wen.WenyanQuine
