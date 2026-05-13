/-
# Wen.Native.Bridges -- native adapters for concrete carriers

These modules keep V4, Word64/R6, R8, and RootCell256 as adapters over the
generic native API.  They do not introduce separate interpreter roots.
-/

import SSBX.Foundation.Wen.Native.Bridges.V4
import SSBX.Foundation.Wen.Native.Bridges.Word64
import SSBX.Foundation.Wen.Native.Bridges.R8
import SSBX.Foundation.Wen.Native.Bridges.RootCell256

namespace SSBX.Foundation.Wen.Native.Bridges

theorem concrete_bridge_laws :
    Nonempty V4.Carrier
    ∧ Nonempty Word64.Carrier
    ∧ Nonempty R8.Carrier
    ∧ Nonempty RootCell256.Carrier :=
  ⟨⟨SSBX.Foundation.Hierarchy.Operators.V4.dao⟩,
   ⟨SSBX.Foundation.Wen.V4Kernel.Word64.origin⟩,
   ⟨SSBX.Foundation.Bagua.R8.R8.origin⟩,
   ⟨SSBX.Foundation.Wen.V4Kernel.Root512.originCell⟩⟩

end SSBX.Foundation.Wen.Native.Bridges
