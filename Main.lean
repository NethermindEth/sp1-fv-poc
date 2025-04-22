import Sp1Poc.Cli
import Lake
import Lean.Util.Path

open Lean

open Sp1 in
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  cli.validate args
