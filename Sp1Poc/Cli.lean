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
  let genRoot := GeneratedFolderRoot / (p.positionalArg! "circuit-name" |>.as! String)
  let file := genRoot / "main" |>.addExtension "lean"

  if (←System.FilePath.pathExists file) && !p.hasFlag "force"
  then IO.println s!"{file} exists. Aborting. Use -f to override."
       return 1
  
  IO.println s!"Target directory: {genRoot}"

  unless ←System.FilePath.pathExists genRoot do IO.FS.createDirAll genRoot

  let rustPath ←
    match p.flag? "url", p.flag? "path" with
    | .none    , .none      => pure (f := IO) RustFolderRoot
    | .none    , .some path => pure <| path.as! String
    | .some url, .some path => do cloneRust path.value url.value
                                  pure <| path.as! String
    | _        , _          => IO.eprintln "Unreachable, `path` must be .some."; return 1

  
  let lem ← runTemplater ∘
            Function.uncurry defsOfConstraints =<<
            liftM ∘ translateConstraints =<<
            rustOutput s!"{rustPath}"

  IO.FS.writeFile file (Function.uncurry fileOfLemma lem)
  return 0

  where cloneRust (to : System.FilePath) (url : String) : IO Unit :=
          discard (cloneWithCache s!"{to}" url).toBaseIO

unsafe def cli : Cmd := `[Cli|
  genTemplate VIA run; ["1.0.0"]
  "Lean synthesizer dependent on the associated rust extractor. Assumed to be in `./RustExtractor` unless specified otherwise."

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
