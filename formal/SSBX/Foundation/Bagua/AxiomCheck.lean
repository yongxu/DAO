/-
# AxiomCheck — 验证 KleeneCarrier 之公理依赖

仅用于诊断 / CI：列印 `kleene_recursion` 派生定理之公理依赖，
确认它依赖的是单一 bundled boundary axiom `kleeneBoundary`，而非原
monolithic `kleene_recursion_axiom`。
-/
import SSBX.Foundation.Bagua.KleeneCarrier

namespace SSBX.Foundation.Bagua.AxiomCheck

open SSBX.Foundation.Bagua.KleeneCarrier

#print axioms kleene_recursion
#print axioms halts_undecidable_internally
#print axioms rice_four_images

end SSBX.Foundation.Bagua.AxiomCheck
