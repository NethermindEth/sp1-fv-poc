import Cli
import Lake
import Sp1Poc.Templater

namespace Sp1

def GeneratedFolderRoot : System.FilePath := "./Generated"

section

open Cli

/--
  This is the top level function that implements what is described in `genTemplate -h`.
-/
unsafe def run (p : Parsed) : IO UInt32 := do
  let path_to_constraints := p.positionalArg! "path-to-constraints" |>.as! String
  let circuit := p.positionalArg! "output-circuit-name" |>.as! String
  let genRoot := GeneratedFolderRoot / circuit
  let file := genRoot / "main" |>.addExtension "lean"

  if (←System.FilePath.pathExists file) && !p.hasFlag "force"
  then IO.println s!"{file} exists. Aborting. Use -f to override."
       return 1

  IO.println s!"Target directory: {genRoot}"

  unless ←System.FilePath.pathExists genRoot do IO.FS.createDirAll genRoot

  let lem ← runTemplater ∘
            Function.uncurry defsOfConstraints =<<
            liftM ∘ translateConstraints =<<
            IO.FS.readFile path_to_constraints

  IO.FS.writeFile file (Function.uncurry fileOfLemma lem)
  IO.FS.withFile "Generated.lean" .append (·.write s!"import Generated.{circuit}.main\n".toUTF8)

  return 0

unsafe def cli : Cmd := `[Cli|
  genTemplate VIA run; ["1.0.0"]
  "Lean SP1 constraint processor."

  FLAGS:
    f, force; "Force overwrite the existing circuit."

  ARGS:
    "path-to-constraints" : String; "Path to the file containing circut constraints."
    "output-circuit-name" : String; "Circuit name."
]

end

end Sp1
