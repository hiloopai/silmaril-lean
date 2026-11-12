module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Type

/-!
# Relation-free syntax: when an environment's relations cannot matter

The evaluator (`Sem.evalExp` and its 28 siblings) and the typing block (`Sem.hasTyp` and its six
siblings) read the relations of an environment in exactly one place: a `rulePr` premise asks
`Sem.derives`. Syntax that never reaches a `rulePr` premise therefore evaluates and types alike in
any two environments that differ only in their relations. This header names that syntax:

* `rfEvB bad`: an event (`Round7.Script.Ev`) is harmless when it is not a relation reference and
  not a reference to a definition in `bad`;
* `GoodEvs bad l`: every event of `l` is harmless;
* `DefsOk bad ρ`, `ArgOk bad w`: definition variables and definition arguments avoid `bad`;
* `DefsGood bad env`, `TypsGood bad env`: the clauses of every definition outside `bad`, and the
  instances of every type, are harmless;
* `withRels env r`: `env` with its relation table replaced by `r`;
* `noElseB`, `ruleOkB bad`: a premise without `otherwise`, and a rule that is harmless and has
  none.

`defsOkB` and `typsOkB` are the Boolean forms of `DefsGood`/`TypsGood` on a table; the kernel
checks them on the fixed wasm-2.0 script with `bad = ["instantiate"]`
(`Sim20.RelFree.defsOkB_fixed20`, `typsOkB_fixed20`): `$instantiate` is the only definition or type
of that script that refers to a relation.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.RelFree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evClause evInst)

/-- A harmless event: not a relation reference, and not a reference to a definition in `bad`. -/
def rfEvB (bad : List String) : Ev → Bool
  | .ref 0 _ => false
  | .ref 1 x => !bad.contains x
  | _ => true

/-- Every event of `l` is harmless. -/
def GoodEvs (bad : List String) (l : List Ev) : Prop := ∀ e ∈ l, rfEvB bad e = true

/-- A definition name outside `bad`. -/
def GoodName (bad : List String) (x : String) : Prop := bad.contains x = false

/-- Every definition variable of `ρ` names a definition outside `bad`. -/
def DefsOk (bad : List String) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.defs, GoodName bad p.2

/-- A definition argument names a definition outside `bad`. -/
def ArgOk (bad : List String) : ArgV → Prop
  | .defName y => GoodName bad y
  | _ => True

/-- Every type variable of `ρ` is bound to a harmless type. -/
def TypsOk (bad : List String) (ρ : VarEnv) : Prop :=
  ∀ p ∈ ρ.typs, GoodEvs bad (Silmaril.Wasm.SpecTec.Sim.Round7.Script.evTyp p.2)

/-- The clauses of every definition of `env` outside `bad` are harmless. -/
def DefsGood (bad : List String) (env : Env) : Prop :=
  ∀ x d, GoodName bad x → env.findDef? x = some d → ∀ c ∈ d.2.2, GoodEvs bad (evClause c)

/-- The instances of every type of `env` are harmless. -/
def TypsGood (bad : List String) (env : Env) : Prop :=
  ∀ x td, env.findTyp? x = some td → ∀ i ∈ td.2, GoodEvs bad (evInst i)

/-- `env` with its relation table replaced by `r`. -/
abbrev withRels (env : Env) (r : Map RelDef) : Env := { env with rels := r }

/-- A premise with no `otherwise` (at top level or under iterations). -/
def noElseB : Prem → Bool
  | .elsePr => false
  | .iterPr pr _ => noElseB pr
  | _ => true

/-- A rule whose events are harmless and whose premises have no `otherwise`. -/
def ruleOkB (bad : List String) (r : Rule) : Bool :=
  (Silmaril.Wasm.SpecTec.Sim.Round7.Script.evRule r).all (rfEvB bad) &&
    match r with
    | .ruleD _ _ _ _ prems => prems.all noElseB

/-- `DefsGood` on a table, as a computation. -/
def defsOkB (bad : List String) (m : Map DefDef) : Bool :=
  m.all fun p => bad.contains p.1 || p.2.2.2.all fun c => (evClause c).all (rfEvB bad)

/-- `TypsGood` on a table, as a computation. -/
def typsOkB (bad : List String) (m : Map TypDef) : Bool :=
  m.all fun p => p.2.2.all fun i => (evInst i).all (rfEvB bad)

end Silmaril.Wasm.SpecTec.Sim20.RelFree
