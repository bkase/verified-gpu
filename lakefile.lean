import Lake

open Lake DSL

package VerifiedGPU

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib LanguageQuantale

lean_lib Effects

lean_lib Kernel

lean_lib WGSL

lean_lib Tests where
  roots := #[`Tests.GradeEval]

@[default_target]
lean_exe emitWGSL where
  root := `WGSL.EmitMain
