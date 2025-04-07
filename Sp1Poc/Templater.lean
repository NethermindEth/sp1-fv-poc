import Sp1Poc.Wheels
import Lean
import Mathlib.Lean.CoreM
import Std.Data.HashSet.Basic

namespace Sp1

open Lean Elab Term

declare_syntax_cat constraint

section Syntax

syntax "Lookup(" term "," "[" term,* "]" ")" : constraint
syntax "Permutation(" ("FirstRow(" <|> "TransitionRow(" <|> "LastRow(") term:min ")" ")" : constraint
syntax "Constraint(" term:min ")" : constraint

end Syntax

section Elaborator

/--
  POC note.

  Bound variables only supported in cases where we support decoding.
  Viz. the branch `(constraint| Constraint($t:term))` for the implementation.
-/
private def translateConstraint (c : TSyntax `constraint) : Except String (String × Array String) :=
  match c with
  -- "Lookup(" term "," "[" term,* "]" ")"
  | `(constraint| Lookup($selector:term, [$terms:term,*])) => do
    let some 1 := selector.raw.isNatLit? | throw "Unsupported Lookup format - selector."
    let ⟨[a, b, c, d, e, f]⟩ := terms.getElems.map TSyntax.raw | throw "Unsupported Lookup format - expected 6 elements."
    match a.isNatLit?, b.isNatLit?, c.isNatLit?, c.isNatLit?, e.isIdent, f.isIdent with
    | some 5, some 4, some 0, some 0, true, true =>
      /-
        POC note.
        
        One can extend this trivially with an extra `if` to check for `= -1`.
      -/
      let constraint := s!"if {strOfTerm selector} = 1 then ({strOfIdent e} < 256 ∧ {strOfIdent f} < 256) else True"
      pure (constraint, #[strOfIdent e, strOfIdent f])
    | _     , _     , _     , _     , _   , _    =>
      throw s!"Unsupported Lookup format - [{a}, {b}, {c}, {d}, {e}, {f}]."

  -- "Permutation(" ("FirstRow(" <|> "TransitionRow(" <|> "LastRow(") term:min ")" ")"
  | `(constraint| Permutation(FirstRow($_))     ) 
  | `(constraint| Permutation(TransitionRow($_)))
  | `(constraint| Permutation(LastRow($_))      ) => pure ("True", #[])

  -- "Constraint(" term:min ")"
  | `(constraint| Constraint($t:term)) => do
    let mut res : Array String := #[]
    for node in t.raw.topDown do
      if node.isIdent then res := res.push (strOfIdent node)
    pure (strOfTerm t, res)
  | stx => throw s!"Unrecognised constraint syntax: {stx}."
  where strOfTerm  (t : Term)   : String := t.raw.prettyPrint.pretty
        strOfIdent (i : Syntax) : String := i.getId.toString

instance : MonadLift IO (EIO String) := ⟨IO.toEIO (s!"{·}")⟩
instance : MonadLift (EIO String) IO := ⟨EIO.toIO (s!"{·}")⟩

def translateConstraints (input : String) : EIO String (Array String × Array String) :=
  let constraints := input.splitOn "\n"
  /-
    Run the parser on each individual constraint.
    - `hyppotheses` is the set of hypotheses representing the set of polynomial constraints.
    - `bvars` is the set of bound variables in these hypothses.
  -/
  CoreM.withImportModules #[`Sp1Poc] do
    let mut bvars      := #[]
    let mut hypotheses := #[]
    for constraint in constraints do
      if let .ok stx := Parser.runParserCategory (←getEnv) `constraint constraint then
      if let .ok (term, bvs) := translateConstraint ⟨stx⟩ then
      bvars      := bvars.append bvs 
      hypotheses := hypotheses.push term
    pure (bvars, hypotheses)

end Elaborator

def defsOfConstraints (bvars : Array String) (constraints : Array String) : StateM Nat (String × String) := do
  let n ← getModify (·+1)
  pure (
    s!"{options}\ntheorem {lemName n}\n{Indent}\{{typedBvars}}\n{hypotheses} : {specName n} {bvs} := PROOF",
    s!"def {specName n}\n{Indent}({typedBvars}) : Prop := True"
  )
  where Indent : String := ⟨List.replicate 2 ' '⟩
        log10 (n : Nat) := s!"{n}".length
        prettyHypName (current : Nat) : String :=
          ⟨List.replicate (log10 constraints.size - log10 current) '0'⟩
        cmpNames := λ a b ↦ let nA := a.takeRightWhile Char.isDigit |>.toNat!
                            let nB := b.takeRightWhile Char.isDigit |>.toNat!
                            decide (nA < nB)
        sortedBvs  := (Std.HashSet.ofArray bvars).toArray.qsort (lt := cmpNames)

        bvs        := s!"{sortedBvs.foldl (·++s!"{·} ") "" |>.pop}"
        options    := ""
        lemName n  := s!"lemma_{n}"
        specName n := s!"spec_{n}"
        typedBvars := s!"{bvs} : BabyBear"
        hypotheses := (·.pop) <| constraints.zipIdx.foldl (init := "") λ acc (hyp, i) ↦
                        acc++Indent++s!"(C{prettyHypName i}{i} : {hyp})\n"

def fileOfLemma (lem spec : String) : String :=
  s!"{imports} \nnamespace {namespc} \n\n{spec}\n\n{lem}\n\nend {namespc}"
  where namespc := "Sp1"
        imports := "import Sp1Poc"

def runTemplater {m : Type → Type v} [Monad m] (templater : StateM Nat (String × String)) : m (String × String) :=
  pure (templater.run' 0)

end Sp1
