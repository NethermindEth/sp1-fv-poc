import Sp1Poc
import Lake

namespace Sp1


-- set_option maxHeartbeats 1000000
-- lemma sp1_addOperation
--   -- main local variables
--   (V00 V01 V02 V03 V04 V05 V06 V07 V08 V09 V10 V11 V12 V13 V14 : BabyBear)
--   -- extracted Babybear constraints
--   (C01: 1 * ((V00 + V04 - V08)       * (V00 + V04 - V08       - 256)) = 0)
--   (C02: 1 * ((V01 + V05 - V09 + V12) * (V01 + V05 - V09 + V12 - 256)) = 0)
--   (C03: 1 * ((V02 + V06 - V10 + V13) * (V02 + V06 - V10 + V13 - 256)) = 0)
--   (C04: 1 * ((V03 + V07 - V11 + V14) * (V03 + V07 - V11 + V14 - 256)) = 0)
--   (C05: 1 * (V12 * (V00 + V04 - V08       - 256)) = 0)
--   (C06: 1 * (V13 * (V01 + V05 - V09 + V12 - 256)) = 0)
--   (C07: 1 * (V14 * (V02 + V06 - V10 + V13 - 256)) = 0)
--   (C08: 1 * ((V12 - 1) * (V00 + V04 - V08))       = 0)
--   (C09: 1 * ((V13 - 1) * (V01 + V05 - V09 + V12)) = 0)
--   (C10: 1 * ((V14 - 1) * (V02 + V06 - V10 + V13)) = 0)
--   (C11: 1 * (V12 * (V12 - 1)) = 0)
--   (C12: 1 * (V13 * (V13 - 1)) = 0)
--   (C13: 1 * (V14 * (V14 - 1)) = 0)
--   (C14: 1 * (1 - 1) = 0)
--   -- extracted lookup/permutation argument constraints
--   (C15: V00.val < 256) (C16: V01.val < 256) (C17: V02.val < 256) (C18: V03.val < 256)
--   (C19: V04.val < 256) (C20: V05.val < 256) (C21: V06.val < 256) (C22: V07.val < 256)
--   (C23: V08.val < 256) (C24: V09.val < 256) (C25: V10.val < 256) (C26: V11.val < 256) :
--     -- human-readable specification of wrap-around byte-by-byte 32-bit addition
--     ( ( V00.val + 256 * V01.val + 65536 * V02.val + 16777216 * V03.val ) +
--       ( V04.val + 256 * V05.val + 65536 * V06.val + 16777216 * V07.val ) ) % 4294967296 =
--     ( V08.val + 256 * V09.val + 65536 * V10.val + 16777216 * V11.val )
--      := by sorry
-- --   simp [sub_eq_zero (b := (1 : BabyBear))] at *
-- --   rcases C11 <;> rcases C12 <;> rcases C13 <;> subst_eqs <;>
-- --   simp [BabyBearPrime, Fin.add_def, Fin.sub_def] at * <;>
-- --   omega

end Sp1

namespace Sp1

def RustFolder : System.FilePath := "./RustExtractor"

open Lake in
def cloneWithCache (dirname url : String) : LogIO Unit := do
  let repoDir : GitRepo := ⟨(←IO.currentDir) / dirname⟩
  if !(← repoDir.dir.pathExists) then IO.println s!"Cloning: {url}"; GitRepo.clone url repoDir

def rustOutput : IO String := do
  IO.println "Extracting constraints..."
  IO.Process.run {
    cwd := RustFolder / "air",
    cmd := "cargo",
    args := #["test", "--", "--nocapture"]
  }

protected def HelpMessage :=
s!"Usage:
If no arguments are given, we assume the rust extractor is located in {RustFolder}.

We then run the extractor to obtain constraints and create a Lean file ready to specify and verify the circuit.

Arguments:
help  : Displays this message.
<URL> : Clones the extractor from the Git repository at <URL> into {RustFolder}.
           If the folder exists, acts as if no arguments were given.
"
end Sp1

open Sp1 in
def main : List String → IO Unit
  | []    => rustOutput >>= λ output ↦ let x := templateOfRustOutput output; dbg_trace s!"{x}"; pure ()
  | [arg] => if arg == "help"
             then IO.println Sp1.HelpMessage
             else (cloneWithCache "RustExtractor" arg).toBaseIO >>= λ _ ↦ main []
  | _     => IO.println Sp1.HelpMessage
