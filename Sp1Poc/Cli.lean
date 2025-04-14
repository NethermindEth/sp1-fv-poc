import Cli
import Lake
import Sp1Poc.Templater

namespace Sp1

def RustFolderRoot : System.FilePath := "./RustExtractor"

def GeneratedFolderRoot : System.FilePath := "./Generated"

open Lake in
def cloneWithCache (dirname url : String) : LogIO Unit := do
  let repoDir : GitRepo := ⟨dirname⟩
  if !(← repoDir.dir.pathExists) then IO.println s!"Cloning: {url} into: {repoDir}"; GitRepo.clone url repoDir

def rustOutput (root : System.FilePath := RustFolderRoot) : IO String := do
  IO.println "Extracting constraints..."
  IO.Process.run {
    cwd := root / "air",
    cmd := "cargo",
    args := #["test", "--", "--nocapture"]
  }

section

open Cli

/--
  This is the top level function that implements what is described in `genTemplate -h`.
-/
unsafe def run (p : Parsed) : IO UInt32 := do
  let circuit := p.positionalArg! "circuit-name" |>.as! String
  let genRoot := GeneratedFolderRoot / circuit
  let file := genRoot / "main" |>.addExtension "lean"

  if (←System.FilePath.pathExists file) && !p.hasFlag "force"
  then IO.println s!"{file} exists. Aborting. Use -f to override."
       return 1
  
  IO.println s!"Target directory: {genRoot}"

  unless ←System.FilePath.pathExists genRoot do IO.FS.createDirAll genRoot

  let path := p.flag! "path" |>.as! String
  if let .some url := p.flag? "url" then cloneRust path url.value
  
  let lem ← runTemplater ∘
            Function.uncurry defsOfConstraints =<<
            liftM ∘ translateConstraints =<<
            rustOutput s!"{path}"

  IO.FS.writeFile file (Function.uncurry fileOfLemma lem)
  IO.FS.withFile "Generated.lean" .append (·.write s!"import Generated.{circuit}.main".toUTF8)
  
  return 0

  where cloneRust (to : System.FilePath) (url : String) : IO Unit :=
          discard (cloneWithCache s!"{to}" url).toBaseIO

unsafe def cli : Cmd := `[Cli|
  genTemplate VIA run; ["1.0.0"]
  "Lean synthesizer dependent on the associated rust extractor. Assumed to be in `./RustExtractor` unless specified otherwise. POC Note: you can use `lake build Generated` to separately build (proof check) all Lean circuits."

  FLAGS:
    f, force     ; "Force overwrite the existing circuit."
    path : String; "Overrides the path to the root of the rust extractor."
    url  : String; "Git repository of the rust extractor to be cloned."

  ARGS:
    "circuit-name" : String; "Circuit name."

  EXTENSIONS:
    defaultValues! #[("path", s!"{RustFolderRoot}")]
]

end

end Sp1
