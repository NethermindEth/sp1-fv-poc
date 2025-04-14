import Lake

open System Lake DSL

package «sp1-poc» where version := v!"1.0.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.17.0"

private def v4_17_0 := "e7fd1a415c80985ade02a021172834ca2139b0ca"

require Cli from git "https://github.com/leanprover/lean4-cli"@v4_17_0

lean_lib Sp1Poc
lean_lib Generated

@[default_target]
lean_exe genTemplate where
  root := `Main
  supportInterpreter := true
