import Lake

open System Lake DSL

package «sp1-poc» where version := v!"1.0.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.18.0"

lean_lib Sp1Poc

@[default_target]
lean_exe genTemplate where
  root := `Main
