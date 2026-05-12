/-
# RHierarchy — umbrella entry for the strict (Z/2)ⁿ R₀..R₈ R-hierarchy

One-stop import for the entire R-index navigation surface:

  R₀ Taiji      — Unit, |·| = 1
  R₁ Yao        — yin/yang, |·| = 2 = (Z/2)¹
  R₂ SiXiang    — Yao², |·| = 4 = (Z/2)²
  R₃ Trigram    — Yao³, |·| = 8 = (Z/2)³
  R₄ Mian       — Ben × Zheng, |·| = 16 = (Z/2)⁴
  R₅ Wuyao      — Mian × Bool, |·| = 32 = (Z/2)⁵
  R₆ Hexagram   — Yao⁶, |·| = 64 = (Z/2)⁶
  R₇ YinHex     — Hexagram × YinBit (R7), |·| = 128 = (Z/2)⁷
  R₈ GuoHex     — Hexagram × Shi (R8), |·| = 256 = (Z/2)⁸

Plus the cross-cutting Lift/Project pairs, root-language-tree bookkeeping,
and atomic / V₄-outer operators.

Each R_n_*.lean file is a thin re-export shim providing R-index naming
(no new logic).  Modules that already live in `Hierarchy/` (R5_Wuyao,
LiftProject, Operators/) are also pulled in here.
-/

-- R-index alias shims (R₀..R₈)
import SSBX.Foundation.Hierarchy.R0_Taiji
import SSBX.Foundation.Hierarchy.R1_Yao
import SSBX.Foundation.Hierarchy.R2_SiXiang
import SSBX.Foundation.Hierarchy.R3_Trigram
import SSBX.Foundation.Hierarchy.R4_Mian
import SSBX.Foundation.Hierarchy.R5_Wuyao
import SSBX.Foundation.Hierarchy.R6_Hexagram
import SSBX.Foundation.Hierarchy.R7_YinHex
import SSBX.Foundation.Hierarchy.R8_GuoHex

-- Cross-cutting structure
import SSBX.Foundation.Hierarchy.LiftProject
import SSBX.Foundation.Hierarchy.R432Conversion
import SSBX.Foundation.Hierarchy.RootLanguageTree
import SSBX.Foundation.Hierarchy.Operators.Atomic
import SSBX.Foundation.Hierarchy.Operators.V4Core
import SSBX.Foundation.Hierarchy.Operators.V4Outer
import SSBX.Foundation.Hierarchy.Operators.V4LogicTuring
