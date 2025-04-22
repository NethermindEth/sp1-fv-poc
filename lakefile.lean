import Lake

open System Lake DSL

package «sp1-poc» where version := v!"1.0.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.18.0"

private def v4_18_0 := "663759405cce4cd6d672913c715b1f4cea4d2ac7"

require Cli from git "https://github.com/leanprover/lean4-cli"@v4_18_0

lean_lib Sp1Poc
lean_lib Generated

@[default_target]
lean_exe genTemplate where
  root := `Main
  supportInterpreter := true
