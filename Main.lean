import Sp1Poc
import Lake
import Lean

open Lean

open Sp1 in
unsafe def main (args : List String) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  enableInitializersExecution
  cli.validate args
