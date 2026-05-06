import Lake
open Lake DSL

package ssbx where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib SSBX where
  srcDir := "formal"
