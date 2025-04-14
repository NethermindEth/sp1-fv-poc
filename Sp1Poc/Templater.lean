import Sp1Poc.Wheels
import Lean
import Mathlib.Lean.CoreM
import Std.Data.HashSet.Basic
import Sp1Poc.Basic

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
  Note the syntax is parsed implicitly, as we are 'invoking' Lean's parser via description
  in the `section Syntax`. Thus, we allow a broad range of expressions.

  `translateConstraint` then post-processes this information and rejects currently unsupported
  formats.

  Returns the underlying term as well as an array of bound variables occurring in the term.

  POC note.

  Bound variables only supported in cases where we support decoding.
  Viz. the branch `(constraint| Constraint($t:term))` for the implementation.
-/
private def translateConstraint (c : TSyntax `constraint) : Except String (String × Array String) :=
  match c with
  -- "Lookup(" term "," "[" term,* "]" ")"
  | `(constraint| Lookup($multiplicity:term, [$terms:term,*])) => do
    let all_vars := terms.getElems.foldl (·++bvsOfStx ·) #[]
    rejectUnsupportedLookupVars all_vars
    let mut isTrue : Bool := true
    isTrue := match multiplicity.raw.isNatLit? with
      | none => true
      | some x => x ∈ [0, 1, BabyBearPrime - 1]
    if !isTrue then throw s!"Unsupported multiplicity: {strOfTerm multiplicity}"
    let .some interactionKind := terms.getElems[0]? | throw "Lookup without interaction kind."
    match interactionKind.raw.isNatLit? with
    | .some 3 => if terms.elemsAndSeps.size ≠ 39 then throw "Instruction-related lookup does not have 20 parameters."
                 else let term := s!"if {strOfTerm multiplicity} = 0 || {strOfTerm multiplicity} = BabyBearPrime - 1 then True else sorry"
                      return (term, all_vars)
    | .some 5 => if terms.elemsAndSeps.size ≠ 11 then throw "Byte-related lookup does not have 6 parameters."
                 let ⟨[_, opcode, a, _, b, c]⟩ := terms.getElems | throw "Byte-related lookup does not have 6 parameters."
                 let term := s!"if {strOfTerm multiplicity} = 0 then True else
         if {strOfTerm multiplicity} = 1 then
         match {strOfTerm opcode} with
         | 4 => if {strOfTerm multiplicity} = 1
                then {strOfTerm b} < 256 ∧ {strOfTerm c} < 256
                else if {strOfTerm multiplicity} = 0 then True else sorry
         | _ => sorry
         else sorry"
                 return (term, all_vars)
    | _ => throw s!"Unsupported lookup interaction kind: {strOfTerm interactionKind}"

  -- "Permutation(" ("FirstRow(" <|> "TransitionRow(" <|> "LastRow(") term:min ")" ")"
  | `(constraint| Permutation(FirstRow($_))     )
  | `(constraint| Permutation(TransitionRow($_)))
  | `(constraint| Permutation(LastRow($_))      ) => pure ("True", #[])

  -- "Constraint(" term:min ")"
  | `(constraint| Constraint($t:term)) =>
    pure (strOfTerm t, bvsOfStx t)
  | stx => throw s!"Unrecognised constraint syntax: {stx}."
  where strOfTerm  (t : Term)     : String       := t.raw.prettyPrint.pretty
        strOfIdent (stx : Syntax) : String       := stx.getId.toString
        bvsOfStx   (stx : Syntax) : Array String := Id.run do
          let mut res : Array String := #[]
          for node in stx.topDown do
            if node.isIdent then res := res.push (strOfIdent node)
          return res

        rejectUnsupportedLookupVars (bvs : Array String) : Except String Unit :=
          if bvs.all (·.startsWith "ML") then return () else throw "Unsupported lookup variables."

section

/-
  In `Sp1`, we canonically translate between `Except.error` and `IO.Error`.
-/
scoped instance : MonadLift IO (EIO String) := ⟨IO.toEIO (s!"{·}")⟩
scoped instance : MonadLift (EIO String) IO := ⟨EIO.toIO (s!"{·}")⟩

end

/--
  Rust output parser frontend.

  We run the constraiint parser on each individual constraint and return:
  - `hyppotheses` is the set of hypotheses representing the set of polynomial constraints.
  - `bvars` is the set of bound variables in these hypothses.
-/
def translateConstraints (input : String) : EIO String (Array String × Array String) :=
  let constraints := input.splitOn "\n"
  CoreM.withImportModules #[`Sp1Poc] do
    let mut bvars      := #[]
    let mut hypotheses := #[]
    for constraint in constraints do
      if let .ok stx := Parser.runParserCategory (←getEnv) `constraint constraint then
      match translateConstraint ⟨stx⟩ with
      | .ok (term, bvs) =>
        bvars      := bvars.append bvs
        hypotheses := hypotheses.push term
      | .error err_msg => panic err_msg
    pure (bvars, hypotheses)

end Elaborator

/--
  Returns a pair of:
  - Lean theorem representing the ZK circuit as extracted by the rust module.
  - Lean definition representing a specification of the circuit; set to `True`.

  Runs in `StateM Nat` to uniquely identify lemmas we produce.
  I am not exceedingly partial to this, we could conceivably simply name all of them the same
  and then use a namespace that matches a given circuit's name.
-/
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

/--
  Formats the target Lean file:
  `imports`

  `namespace Sp1`

  `<Definition with the spec.>`

  `<Theorem referring to the spec.>`

  `end Sp1`
-/
def fileOfLemma (lem spec : String) : String :=
  s!"{imports} \nnamespace {namespc} \n\n{spec}\n\n{lem}\n\nend {namespc}"
  where namespc := "Sp1"
        imports := "import Sp1Poc"

/--
  Plumbing.
-/
def runTemplater {m : Type → Type v} [Monad m] (templater : StateM Nat (String × String)) : m (String × String) :=
  pure (templater.run' 0)

end Sp1
