module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.VElse.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs

/-!
# Round 7, memory SIMD: the declarative `$vbytes_` transfer (definitions)

`Round7.VAgree` compares the fuelled evaluators of `simEnv B₁` and `simEnv B₂` for builtins that
agree off `$vbytes_` (`AgreeOff`). The declarative readings (`DDerives`, `DDerivesB`, `Fires`,
`TypedD`) also read the typing block `hasTyp` and the `otherwise` premises. The definitions below
are the invariants and kernel checks of that transfer.

* `RefOk r`, `RG l`: a reference reachable from `Step` that is neither `$vbytes_` nor the relation
  `Step` or `Step_read`; every reference of `l` is one. Unlike `VAgree.GoodEvs`, `RG` also asks
  type references to be reachable, so that the type definitions typing unfolds are `RG` too.
* `TypsG ρ`, `ArgTyG w`: type variables and type arguments are bound to `RG` types.
* `elseFree pr`: the premise has no `otherwise` inside it.
* `ruleFactsB r`, `relFactsB m`: the kernel facts about the rules of the relations `Step`
  reaches: no parameters, `RG` quantifier types, and `RG` conclusion alternatives (`conclAlts`).
* `elseFreeIdx rules`: the indices of the rules with an `otherwise` premise at any depth.
* `altAtomOk r a`: every conclusion alternative of `r` ends its left-hand side's code with the
  atom `a` (`VElse.ruleAtom`).
* `lhsAtom v`: the value side of `VElse.ruleAtom`, the mixop of the last instruction of the
  left-hand side `(z; instr*)` of `v = (lhs, rhs)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VDecl

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (Ev evRefs evTyp evExp evRule stepReach)

/-! ## References -/

/-- A reference reachable from `Step`, other than `$vbytes_`, `Step` and `Step_read`. -/
def RefOk (r : Nat × String) : Prop :=
  r ∈ stepReach ∧ r ≠ (1, "vbytes_") ∧ r ≠ (0, "Step") ∧ r ≠ (0, "Step_read")

/-- Every reference of `l` is `RefOk`. -/
def RG (l : List Ev) : Prop := ∀ r ∈ evRefs l, RefOk r

/-- Every type variable of `ρ` is bound to an `RG` type. -/
def TypsG (ρ : VarEnv) : Prop := ∀ p ∈ ρ.typs, RG (evTyp p.2)

/-- A type argument is an `RG` type. -/
def ArgTyG : ArgV → Prop
  | .typ t => RG (evTyp t)
  | _ => True

/-! ## The kernel checks -/

/-- `RefOk`, as a check. -/
def refOkB (r : Nat × String) : Bool :=
  stepReach.contains r && r != (1, "vbytes_") && r != (0, "Step") && r != (0, "Step_read")

/-- `RG`, as a check. -/
def rgB (l : List Ev) : Bool := (evRefs l).all refOkB

/-- Every expression quantifier has an `RG` type. -/
def quantsRgB (qs : List Param) : Bool :=
  qs.all fun q => match q with
    | .expP _ t => rgB (evTyp t)
    | _ => true

/-- A rule's quantifier types and conclusion alternatives are `RG`. -/
def ruleFactsB : Rule → Bool
  | .ruleD _ qs _ e _ => quantsRgB qs && (Round6.Reading.conclAlts e).all fun e' => rgB (evExp e')

/-- **The relations of `m` that `Step` reaches have no parameters, and their rules pass
`ruleFactsB`.** -/
def relFactsB (m : Map RelDef) : Bool :=
  m.all fun p => !stepReach.contains (0, p.1) || (p.2.1.isEmpty && p.2.2.2.2.all ruleFactsB)

/-- A premise without `otherwise` at any depth. -/
def elseFree : Prem → Bool
  | .elsePr => false
  | .iterPr pr _ => elseFree pr
  | _ => true

/-- The indices of the rules with an `otherwise` premise at any depth. -/
def elseFreeIdx (rules : List Rule) : List Nat :=
  (List.range rules.length).filter fun i =>
    match rules[i]? with
    | some (.ruleD _ _ _ _ prems) => !prems.all elseFree
    | none => false

/-- Every conclusion alternative of `r` has the last-instruction atom `a`. -/
def altAtomOk (r : Rule) (a : MixopS) : Bool :=
  match r with
  | .ruleD nm qs op e prems =>
      (Round6.Reading.conclAlts e).all fun e' => VElse.ruleAtom (.ruleD nm qs op e' prems) == some a

/-- **The atoms of the `otherwise` rules of `Step_read` after 43, alternative by alternative**:
rule 43's alternatives end in `VLOAD`, and every later rule with an `otherwise` premise has a
single atom other than `VLOAD` on all its alternatives. -/
def elseAltsOk (rules : List Rule) : Bool :=
  (match rules[43]? with | some r => altAtomOk r "VLOAD" | none => false) &&
    (elseFreeIdx rules).all fun j => j ≤ 43 ||
      match rules[j]? with
      | some r => match VElse.ruleAtom r with
          | some b => b != "VLOAD" && altAtomOk r b
          | none => false
      | none => false

/-- A premise of a context rule of `Step` (1–5): a rule premise of `Step` or `Step_read` whose
arguments and expression are `RG`, or an `RG` premise. -/
def ctxPremOk : Prem → Bool
  | .rulePr y args op e =>
      ((y == "Step" || y == "Step_read") && rgB (Round7.Script.evArgs args ++ evExp e)) ||
        rgB (Round7.Script.evPrem (.rulePr y args op e))
  | pr => rgB (Round7.Script.evPrem pr)

/-- **The premises of `Step` rules 1–5 pass `ctxPremOk`**, and rule 23 ends in `VSTORE` on every
conclusion alternative. -/
def stepCtxOk (rules : List Rule) : Bool :=
  [1, 2, 3, 4, 5].all (fun j => match (rules[j]? : Option Rule) with
    | some (.ruleD _ _ _ _ prems) => prems.all ctxPremOk
    | none => false) &&
  match rules[23]? with
  | some r => altAtomOk r "VSTORE"
  | none => false

/-! ## The value side of `VElse.ruleAtom` -/

/-- The mixop of the last instruction of a left-hand side `(z; instr*)`. -/
def codeAtom : Value → Option MixopS
  | .case _ (.tuple [_, .list cs]) =>
      match cs.getLast? with
      | some (.case a _) => some a
      | _ => none
  | _ => none

/-- The mixop of the last instruction of the left-hand side `(z; instr*)` of `v = (lhs, rhs)`. -/
def lhsAtom : Value → Option MixopS
  | .tuple [l, _] => codeAtom l
  | _ => none

/-! ## A value invariant for the whole step -/

/-- **A value invariant under which the whole step moves across `withVBytes`.** `Step` rules 1–5
call `Step` and `Step_read` on configurations built from their own, so a derivation of `Step`
may reach rules 43 (`Step_read`) and 23 (`Step`), the two rules calling `$vbytes_`. `Q` keeps
them silent and passes from the conclusion of a context rule to its `Step` and `Step_read`
premises:

* `read43`, `step23`: rule 43 of `Step_read` and rule 23 of `Step` derive no `Q` value;
* `ctx`: in an instance of `Step` rule 1–5 whose conclusion is a `Q` value, the value of every
  `Step` or `Step_read` premise is a `Q` value. -/
structure StepInv (Q : Value → Prop) : Prop where
  /-- Rule 43 of `Step_read` derives no `Q` value. -/
  read43 : ∀ (B : Builtins) (D : Interp) (els : Prop) (ps : List Param) (op : MixopS) (t : Typ)
    (rules : List Rule) (r : Rule) (args : List ArgV) (op' : MixopS) (w : Value), Q w →
    (simEnv B).findRel? "Step_read" = some (ps, op, t, rules) → rules[43]? = some r →
    ¬ RuleBody (simEnv B) D els ps args op' r w
  /-- Rule 23 of `Step` derives no `Q` value. -/
  step23 : ∀ (B : Builtins) (D : Interp) (els : Prop) (ps : List Param) (op : MixopS) (t : Typ)
    (rules : List Rule) (r : Rule) (args : List ArgV) (op' : MixopS) (w : Value), Q w →
    (simEnv B).findRel? "Step" = some (ps, op, t, rules) → rules[23]? = some r →
    ¬ RuleBody (simEnv B) D els ps args op' r w
  /-- `Q` passes from a context rule's conclusion to its `Step` and `Step_read` premises. -/
  ctx : ∀ (B : Builtins) (ps : List Param) (op : MixopS) (t : Typ) (rules : List Rule) (j : Nat)
    (nm : IL.Id) (qs : List Param) (op' : MixopS) (e : Exp) (prems : List Prem) (ρ : VarEnv)
    (v : Value) (y : IL.Id) (args : List Arg) (op'' : MixopS) (e' : Exp) (w : Value),
    (simEnv B).findRel? "Step" = some (ps, op, t, rules) → j ∈ [1, 2, 3, 4, 5] →
    rules[j]? = some (.ruleD nm qs op' e prems) → EvalExp (simEnv B) ρ e v → Q v →
    Prem.rulePr y args op'' e' ∈ prems → (y = "Step" ∨ y = "Step_read") →
    EvalExp (simEnv B) ρ e' w → Q w

end Silmaril.Wasm.SpecTec.Sim.Round7.VDecl
