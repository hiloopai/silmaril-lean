module

public import Silmaril.Wasm.Auto2.VCNorm.Defs

/-!
# The VC stage with memory, callees and normalised conditions

The basic check
(`Silmaril.Wasm.Auto2.VCBridge.vcCheck`) takes contracts without memory and without callees, and
accepts a condition only if it is syntactically a proved one. Here:

* `VcEntryM`: a proved contract that **may use memory `0`** and **may call** functions of the same
  module (`calls`: index, total specification without callees, proved conditions). The callees'
  code is read from the module (`calleesOf?`) and their conditions are checked like the caller's,
  so a contract applies to every module whose callees meet the callee specifications;
* `vcCheckM e m j`: export `j` of `m` has the types of `e.S`, its callees are Wasm functions of
  the same instance with the right arity whose conditions are accepted, and every condition of its
  code is **accepted** (`Silmaril.Wasm.Auto2.VCGen.coveredN`: valid by normalisation, or a renamed normal form
  of a proved condition);
* `ModTSpecM`: the total every-run specification of the export (`fspec`, whose precondition states
  the memory at entry, `MemOk`, and the callees in the store, `Callees`);
* `VcEntry.toM`: the contracts of `VcEntry`; `checkMeetsVCN`: the front end with this check (for
  contracts without memory and callees, where the statement is the front end's `ModMeets`).

Soundness in `Silmaril.Wasm.Auto2.VCCheck.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCCheck

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Auto2.VCBridge (fnCode? VcEntry RefEntry)
open Silmaril.Wasm.Auto.Bridge (scalarInt?)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Game (FnType)

/-- **A proved contract** with memory and callees (see the module docstring). The callees are
given by their index, a total specification without callees and its proved conditions; their code
is read from the module (`calleeOK?`), so the contract applies to every module whose callees meet
these specifications. -/
structure VcEntryM where
  /-- A name (the `wasm-check vc` argument). -/
  name : String
  /-- The specification functions. -/
  F : Fns
  /-- The annotated specification (its `calls` are not used: see `calls`). -/
  S : FnSpec
  /-- The fuel of the generator. -/
  fuel : Nat
  /-- The proved conditions. -/
  conds : List Fm
  valid : AllValid F conds
  total : S.total = true
  /-- The callees: function index, total specification without callees, proved conditions. -/
  calls : List (Nat × FnSpec × List Fm) := []
  callsOK : ∀ c ∈ calls, c.2.1.total = true ∧ c.2.1.calls = [] ∧ AllValid F c.2.2 := by
    intro c hc; cases hc

/-- The contracts of `VcEntry` (no memory, no callees). -/
def _root_.Silmaril.Wasm.Auto2.VCBridge.VcEntry.toM (e : VcEntry) : VcEntryM where
  name := e.name
  F := e.F
  S := e.S
  fuel := e.fuel
  conds := e.conds
  valid := e.valid
  total := e.total

/-- The type, instance and code of function export `j` of `m`'s computed instance. -/
def fnInst? (m : Module) (j : Nat) : Option (FnType × FuncInst Nat × Func) :=
  match instance? m with
  | some (_, I) =>
    match I.exports[j]?, I.store.funcs[I.addrs.getD j 0]? with
    | some ft, some fi =>
      match fi.code with
      | .wasm code => some (ft, fi, code)
      | .host _ => none
    | _, _ => none
  | none => none

/-- The code of function `x` of `fi`'s module in the store `s`, if it is a Wasm function of the
same module instance with `p` parameters and `r` results. -/
def calleeCode? (s : Store Nat) (fi : FuncInst Nat) (x p r : Nat) : Option Func :=
  match fi.module.funcs[x]? with
  | some a' =>
    match s.funcs[a']? with
    | some fi' =>
      match fi'.code, fi'.type.expand? with
      | .wasm code, some (.func ps rs) =>
        if fi'.module = fi.module ∧ p = ps.length ∧ r = rs.length then some code else none
      | _, _ => none
    | none => none
  | none => none

/-- A callee of a contract in the store: its code, if its conditions are accepted. -/
def calleeOK? (e : VcEntryM) (s : Store Nat) (fi : FuncInst Nat) (c : Nat × FnSpec × List Fm) :
    Option (Nat × FnSpec × Func) :=
  match calleeCode? s fi c.1 c.2.1.params.length c.2.1.results.length with
  | some code => if coveredN (genFunc c.2.1 code e.fuel) c.2.2 then some (c.1, c.2.1, code) else none
  | none => none

/-- The callees of a contract in the store (`none`: one is missing or not accepted). -/
def calleesOf? (e : VcEntryM) (s : Store Nat) (fi : FuncInst Nat) :
    Option (List (Nat × FnSpec × Func)) :=
  e.calls.mapM (calleeOK? e s fi)

/-- The specification with the callees `cs`. -/
def specOf (e : VcEntryM) (cs : List (Nat × FnSpec × Func)) : FnSpec := { e.S with calls := cs }

/-- The conditions of export `j` of `m` against the contract `e` (`none`: no code, or a callee
missing or not accepted). -/
def vcCondsM? (e : VcEntryM) (m : Module) (j : Nat) : Option (List Fm) :=
  match fnInst? m j with
  | some (_, fi, code) =>
    (calleesOf? e (instOf m).store fi).map fun cs => genFunc (specOf e cs) code e.fuel
  | none => none

/-- **The check**: export `j` of `m` has the types of `e.S`, its callees are in the module and
meet their specifications, and every condition of its code is accepted. -/
def vcCheckM (e : VcEntryM) (m : Module) (j : Nat) : Bool :=
  match fnInst? m j with
  | some (ft, fi, code) =>
    match calleesOf? e (instOf m).store fi with
    | some cs =>
      decide (ft.params.mapM scalarInt? = some e.S.params) &&
        decide (ft.results.mapM scalarInt? = some e.S.results) &&
        coveredN (genFunc (specOf e cs) code e.fuel) e.conds
    | none => false
  | none => false

/-- The number of conditions of export `j` of `m` that are not accepted (`none`: no code, other
types, or a callee missing or not accepted). -/
def vcMissingM (e : VcEntryM) (m : Module) (j : Nat) : Option Nat :=
  match fnInst? m j with
  | some (ft, fi, code) =>
    match calleesOf? e (instOf m).store fi with
    | some cs =>
      if ft.params.mapM scalarInt? = some e.S.params ∧ ft.results.mapM scalarInt? = some e.S.results
      then some ((genFunc (specOf e cs) code e.fuel).filter fun φ => !accepts e.conds φ).length
      else none
    | none => none
  | none => none

open Silmaril.Wasm.Numerics (Profile) in
open Silmaril.Wasm.Auto.Front (addrOf) in
open Silmaril.Wasm.Verify (instOf) in
/-- **The total every-run specification of a contract at export `j` of `m`** (as
`Silmaril.Wasm.Auto2.VCBridge.ModTSpec`): for the function instance at the export's address and
its callees `cs` in the computed store, every call meeting `e.S`'s precondition (with the memory
at entry, `MemOk`, and the callees in the store, `Callees`) terminates, without a trap, with
results and a final memory meeting its postcondition; and the callees are in the computed
store. -/
def ModTSpecM (P : Profile) (e : VcEntryM) (m : Module) (j : Nat) : Prop :=
  ∀ fi cs, (instOf m).store.funcs[addrOf m j]? = some fi → calleesOf? e (instOf m).store fi = some cs →
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P SingleThreaded.Det.noHost (addrOf m j)
      (fspec e.F (specOf e cs) (addrOf m j) fi) ∧ Callees (specOf e cs) fi (instOf m).store

open Silmaril.Wasm.Auto.Front (Rel Report checkMeets) in
/-- **The front end with the normalising VC stage** for a reference contract `r` (as
`Silmaril.Wasm.Auto2.VCBridge.checkMeetsVC`, with `vcCheckM`). -/
def checkMeetsVCN (R : Rel) (r : RefEntry) (m : Module) (j nRand : Nat) : Report :=
  let base := checkMeets R m j r.f nRand
  match base.verdict with
  | .refuted => base
  | _ => if vcCheckM r.e.toM m j then ⟨.proved, .stage "vcgen"⟩ else ⟨.unknown, base.reason⟩

end Silmaril.Wasm.Auto2.VCCheck
