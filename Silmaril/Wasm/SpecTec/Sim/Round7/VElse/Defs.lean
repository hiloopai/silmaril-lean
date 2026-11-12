module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.Defs

/-!
# Round 7, memory SIMD: the `otherwise` rules of `Step_read` and rule 43 (definitions)

The `$vbytes_` transfer for `OpenRMRest.rest` has to show that, at `withVBytes B`, the
`otherwise` premises of `Step_read` read the same as at `B`. An `otherwise` premise of rule `i`
reads every earlier rule `j < i` on the same left-hand side, so after rule 43 (`vload-num-val`,
the one `Step_read` rule that calls `$vbytes_`) it reads rule 43. Round 3 found the `otherwise`
rules by a parse of `specs/spectec/wasm-3.0.ast` outside Lean. The definitions below let the
kernel compute them on the fixed script, and compare the last instruction of each left-hand side
with rule 43's:

* `elseIdx rules`: the indices of the rules with a top-level `otherwise` premise;
* `ruleAtom r`: for a rule whose conclusion is `(z; instr*) ~> _`, the mixop of the last
  instruction of `instr*` when `instr*` is a list or a concatenation ending in a list whose last
  element is a `case` expression;
* `elseOk rules`: rule 43 has such an atom, and every `otherwise` rule after it has one that
  differs from it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

/-- The indices of the rules with a top-level `otherwise` premise. -/
def elseIdx (rules : List Rule) : List Nat :=
  (List.range rules.length).filter fun i =>
    match rules[i]? with
    | some (.ruleD _ _ _ _ prems) => prems.any fun p => match p with | .elsePr => true | _ => false
    | none => false

/-- The mixop of the last instruction of a code expression: the last element of a list, or of
the right operand of a concatenation, when it is a `case` expression. -/
def lastAtom : Exp → Option MixopS
  | .listE es => match es.getLast? with | some (.caseE op _) => some op | _ => none
  | .catE _ e₂ => lastAtom e₂
  | _ => none

/-- The code expression `instr*` of a conclusion `(z; instr*) ~> _`. -/
def readCode : Rule → Option Exp
  | .ruleD _ _ _ (.tupE [.caseE _ (.tupE [_, code]), _]) _ => some code
  | _ => none

/-- The mixop of the last instruction of a `Step_read` rule's left-hand side. -/
def ruleAtom (r : Rule) : Option MixopS := (readCode r).bind lastAtom

/-- Rule 43 has a last-instruction atom, and every `otherwise` rule after it has a different
one. -/
def elseOk (rules : List Rule) : Bool :=
  match rules[43]?.bind ruleAtom with
  | none => false
  | some a => (elseIdx rules).all fun j => j ≤ 43 ||
      match rules[j]?.bind ruleAtom with
      | some b => b != a
      | none => false

/-- `f` on the rules of the relation `x` of the fixed wasm-3.0 script. -/
noncomputable def onRel {α : Type} (x : String) (f : List Rule → α) : Option α :=
  (Scripts.Wasm30.envFixed.findRel? x).map fun v => f v.2.2.2

end Silmaril.Wasm.SpecTec.Sim.Round7.VElse
