import Lake
open Lake DSL

package ssbx where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "ea11ccc0c5c7c4c562742e918fe2e0b2814a58aa"

lean_lib SSBX where
  srcDir := "formal"

@[default_target]
lean_lib SSBXCore where
  srcDir := "formal"
  roots := #[`SSBX.Core]
  globs := #[`SSBX.Core]

lean_exe «wenyan-surface» where
  root := `WenyanSurface
  supportInterpreter := true

lean_exe wenyan where
  root := `Wenyan
  supportInterpreter := true

lean_exe «wen-lisp» where
  root := `WenLisp
  supportInterpreter := true
