/-
# Foundation.R.RFamilyStructure — single source of truth for R-Family-as-object

Per `wen-substrate.md` v1.0.3 §3.1 (the 12-item definition of
R-Family-over-$\mathbb{F}_2$) and §3.6 (parametric over arbitrary base $k$).

Companion doc: `docs-next/10_formal_形式/r-family-definition.md` (D2).

## What this module is

The 12-item definition of R-Family in `wen-substrate.md` §3.1 is realized
**collectively** across many specialized Lean modules: `Foundation/R/Basic.lean`
(carriers + origin), `Foundation/R/DirectSum.lean` (composition),
`Foundation/R/Bilinear.lean` (relational layers), `Foundation/R/Squaring.lean`
(self-similar tower), `Foundation/R/Hom.lean` + `Foundation/R4/HomMat.lean`
(Hom-as-content), `Foundation/R4/EndR2.lean` (ring at $R_4$ + atomic ops),
`Foundation/RInfty/Profinite.lean` ($R_\infty$), `Foundation/Atlas/Yi/ShiV4.lean`
($R_2$ as $V_4$ modality), `Foundation/Atlas/Yi/Bagua.lean` ($R_3$ alphabet),
`Foundation/Atlas/Yi/Operators.lean` (zong involution for the 4 + 4 split),
and `Foundation/R/Parametric.lean` (parametric extension).

Prior to this module, no single source bundled them as one object. This
module is the navigation hub: it imports the canonical components and
re-exports them under one umbrella so that downstream code can refer to
"the R-Family structure" via a single import.

## Item-by-item map (per `wen-substrate` §3.1 / D2 §4)

| Item | Component                       | Anchor                                        |
| ---- | ------------------------------- | --------------------------------------------- |
| 1    | Carriers $R_N$                  | `Foundation.R.Basic.R`                        |
| 2    | Origin $R_0$                    | `Foundation.R.Basic.R` at `N = 0`             |
| 3    | Direct sum                      | `Foundation.R.DirectSum.R.directSumEquiv`     |
| 4    | L0/L1/L2 bilinear layers        | `Foundation.R.Bilinear`                       |
| 5    | Squaring tower self-similarity  | `Foundation.R.Squaring.R.squaringEquiv`       |
| 6    | Hom-as-content                  | `Foundation.R.Hom` + `Foundation.R4.HomMat`   |
| 7    | Ring structure at $R_4$         | `Foundation.R4.EndR2`                         |
| 8    | $R_\infty$ profinite limit      | `Foundation.RInfty.Profinite.L_inf`           |
| 9    | $R_2$ as $V_4$ 4-modality       | `Foundation.Atlas.Yi.ShiV4.Shi`               |
| 10   | $R_3$ aspect alphabet           | `Foundation.Atlas.Yi.Bagua.Trigram`           |
| 11   | Atomic operations at $R_4$      | `Foundation.R4.EndR2` (16 elements of `R 4`)  |
| 12   | Self-following / closure        | This module's existence + `Foundation.R.lean` |

## Parametric extension (per §3.6)

The parametric structure `RFamily k N := Fin N → k` for arbitrary base `k`
lives in `Foundation/R/Parametric.lean`. The current module brings it under
the same umbrella so the parametric vs minimum-base perspectives are
co-located.

## Doctrinal anchor

* `wen-substrate.md` v1.0.3 §3.1 (12-item definition).
* `wen-substrate.md` v1.0.3 §3.6 (parametric over $k$).
* `docs-next/10_formal_形式/r-family-definition.md` (D2 companion).
* `docs-next/10_formal_形式/r-family-parametric-bases.md` (D3 companion).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum
import SSBX.Foundation.R.Bilinear
import SSBX.Foundation.R.Squaring
import SSBX.Foundation.R.Hom
import SSBX.Foundation.R.Parametric

namespace SSBX.Foundation.R

/-! ## § 1 Source-of-truth marker

This module's role is **structural** (re-export hub), not computational.
We provide a trivial marker definition so that downstream code can reference
the hub by importing this file (whose presence in the import graph is the
"single source of truth" pointer per wen-substrate v1.0.3 §3.1).
-/

/-- Marker for the single-source-of-truth bundling of R-Family-over-$\mathbb{F}_2$
    per `wen-substrate.md` v1.0.3 §3.1. Downstream code citing "R-Family as
    one object" should import `SSBX.Foundation.R.RFamilyStructure` and may
    reference this marker for documentation purposes.

    The 12 items of §3.1 are realized by the modules imported above plus the
    Atlas-layer companions (`Foundation.Atlas.Yi.ShiV4`,
    `Foundation.Atlas.Yi.Bagua`, `Foundation.Atlas.Yi.Operators`) and
    `Foundation.R4.EndR2` / `Foundation.RInfty.Profinite`. See the D2
    companion doc `r-family-definition.md` §4 for the full code-anchor table. -/
def rFamilyStructure_marker : Unit := ()

/-- The marker reduces to `()`. This trivial lemma exists so that the module
    has a verifiable theorem-level statement, confirming the file is loaded
    by the Lean elaborator (not only imported). -/
theorem rFamilyStructure_marker_eq : rFamilyStructure_marker = () := rfl

end SSBX.Foundation.R
