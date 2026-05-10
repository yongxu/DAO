/-
# R₀ Taiji — Unit wrapper (R-index alias)

Strict-uniform R₀..R₈ enumeration entry for R₀ = 太极.

R₀ = Unit (the trivial 1-point carrier; «太极» 的形式化).

|Taiji| = 1.

This file is a thin alias: it provides the R-index name `R0.Taiji`
for navigability. No new logic; pure naming convention.
-/

namespace SSBX.Foundation.Hierarchy.R0

/-- R₀ (太极) carrier: Unit (1-point). -/
abbrev Taiji : Type := Unit

/-- All 1 taiji element. -/
def all : List Taiji := [()]

theorem all_length : all.length = 1 := rfl

end SSBX.Foundation.Hierarchy.R0
