import Lake

open System Lake DSL

package «sp1-poc» where version := v!"0.1.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.17.0"

@[default_target]
lean_lib Sp1Poc
