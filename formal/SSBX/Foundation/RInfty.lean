/-
# `SSBX.Foundation.RInfty` — umbrella for the profinite limit over `R 8`

Per `wen-algebra.md` v0.6 §1.4 (beyond R 8) and `r8.md` v0.2 §12.5
(R 8 ceiling, R 16+ derived), the squaring tower above `R 8` extends to
infinity:

    R 8 → R 16 = R 8 ⊕ R 8 → R 32 = R 16 ⊕ R 16 → … → R_{2^k · 8} → …

The inverse system of "first-half projections" admits a profinite limit
isomorphic to `Stream' (R 8)` — the trajectory carrier from
`R8/Dynamics.lean`.

This subtree captures that limit doctrine.  Everything is parametric in
`R N`; no Yi / Bagua / Pauli / Hexagram names appear.

This umbrella pulls the whole subtree in one import.
-/

import SSBX.Foundation.RInfty.Profinite
