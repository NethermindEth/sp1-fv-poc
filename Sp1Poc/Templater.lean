import Lean

namespace Sp1

def templateOfRustOutput (output : String) : String := Id.run do
  let constraints := output.splitOn "\n" |>.dropWhile (·!=ConstraintsBegin)
                                         |>.tail
                                         |>.takeWhile (·!=ConstraintsEnd)

  let prettyZeroes (current : Nat) : String :=
    ⟨List.replicate (log10 constraints.length - log10 current) '0'⟩

  let mut idxHyp     := 1
  let mut hypotheses := ""
  
  for constraint in constraints do
    hypotheses := hypotheses.append s!"(C{prettyZeroes idxHyp}{idxHyp} : {attachType constraint})\n"
    idxHyp     := idxHyp + 1 

  return hypotheses

  where ConstraintsBegin := "running 1 test"
        ConstraintsEnd   := "test tests::test_add ... ok"

        log10 (n : Nat) := s!"{n}".length
        attachType (c : String) := c.replace "= 0" "= (0 : BabyBear)"

end Sp1
