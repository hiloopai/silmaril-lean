module

public import Silmaril.Wasm.Auto2.VCGen.Defs
public import Silmaril.Wasm.Auto.Bridge.Defs
public import Silmaril.Wasm.Auto.Front.Defs
public import Silmaril.Wasm.Logic.Total.Defs

/-!
# The VC generator at the module level: proved contracts and their check

The link between the VC generator
(`Silmaril.Wasm.Auto2.VCGen`) and the statements of the front end (`ModMeets` of
`Silmaril.Wasm.Auto.Front`), used by `wasm-check`.

* `fnCode? m j`: the scalar type and the code of function export `j` of `m`'s computed instance
  (`Silmaril.Wasm.Verify.instance?`, as the function summaries of `Silmaril.Wasm.Auto.Bridge`);
* `VcEntry`: a **proved contract**: an annotated specification `S` (total correctness, no
  callees, no memory), the specification functions `F`, a fuel, and a list of conditions `conds`
  with a proof that every one is valid. The conditions are proved once (by `vcgen4` and the usual
  tactics) and kept as data;
* `vcCheck e m j`: export `j` of `m` has the parameter and result types of `e.S`, and **every
  condition the generator computes for its code is one of `e.conds`** (syntactic equality of
  formulas, `DecidableEq` derived here). A compiled `vcCheck` is what `wasm-check` runs; the
  kernel evaluates the same function in a certificate (`decide +kernel`).

Soundness (`Silmaril.Wasm.Auto2.VCBridge.Thms`): `vcCheck e m j = true` gives the total every-run
specification of the export (`modTSpec_of_vcCheck`) and, for a reference function the
postcondition determines, `ModMeets` at every profile (`modMeets_of_vcCheck`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCBridge

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Verify (instance?)
open Silmaril.Wasm.Game (FnType)
open Silmaril.Wasm.Auto.Bridge (scalarInt?)

deriving instance DecidableEq for MR
deriving instance DecidableEq for Tm
deriving instance DecidableEq for Fm

/-- The scalar type and the code of function export `j` of `m`'s computed instance. -/
def fnCode? (m : Module) (j : Nat) : Option (FnType × Func) :=
  match instance? m with
  | some (_, I) =>
    match I.exports[j]?, I.store.funcs[I.addrs.getD j 0]? with
    | some ft, some fi =>
      match fi.code with
      | .wasm code => some (ft, code)
      | .host _ => none
    | _, _ => none
  | none => none

/-- **A proved contract** of the VC generator: total correctness, no callees, no memory, no
globals, and the conditions `conds`, each proved valid. -/
structure VcEntry where
  /-- A name (the `wasm-check vc` argument). -/
  name : String
  /-- The specification functions. -/
  F : Fns
  /-- The annotated specification. -/
  S : FnSpec
  /-- The fuel of the generator. -/
  fuel : Nat
  /-- The proved conditions. -/
  conds : List Fm
  valid : AllValid F conds
  total : S.total = true
  calls : S.calls = []
  mem : S.mem = false
  /-- No globals (`FnSpec.globals` is empty). -/
  globals : S.globals = [] := by rfl

/-- Every formula of `l` is one of `conds`. -/
def covered (l conds : List Fm) : Bool := l.all fun φ => decide (φ ∈ conds)

/-- The conditions of export `j` of `m` against the contract `e` (`none`: no code). -/
def vcConds? (e : VcEntry) (m : Module) (j : Nat) : Option (List Fm) :=
  (fnCode? m j).map fun (_, code) => genFunc e.S code e.fuel

/-- **The check**: export `j` of `m` has the types of `e.S` and every condition of its code is a
proved condition of `e`. -/
def vcCheck (e : VcEntry) (m : Module) (j : Nat) : Bool :=
  match fnCode? m j with
  | some (ft, code) =>
    decide (ft.params.mapM scalarInt? = some e.S.params) &&
      decide (ft.results.mapM scalarInt? = some e.S.results) &&
      covered (genFunc e.S code e.fuel) e.conds
  | none => false

/-- The number of conditions of export `j` of `m` that are not proved conditions of `e` (`none`:
no code or other types). -/
def vcMissing (e : VcEntry) (m : Module) (j : Nat) : Option Nat :=
  match fnCode? m j with
  | some (ft, code) =>
    if ft.params.mapM scalarInt? = some e.S.params ∧ ft.results.mapM scalarInt? = some e.S.results
    then some ((genFunc e.S code e.fuel).filter fun φ => !decide (φ ∈ e.conds)).length
    else none
  | none => none

open Silmaril.Wasm.Auto.Equiv (TypedVals) in
/-- The hypothesis on a reference function `f` for a contract: `f` agrees with every result the
postcondition allows on typed arguments (or leaves the result open). -/
def RefOK (e : VcEntry) (f : List Val → Option Result) : Prop :=
  ∀ (vs res : List Val) (B : ByteArray), TypedVals e.S.params vs →
    res.map valTy = e.S.results.map some →
    e.S.post.den e.F (valEnv vs ByteArray.empty) (valEnv res B) →
    f vs = some (.values res) ∨ f vs = none

/-- **A proved reference contract**: a contract, a reference function it determines, and a
precondition that holds for every argument (the front end's reference functions have no
precondition). -/
structure RefEntry where
  /-- The contract. -/
  e : VcEntry
  /-- The reference function. -/
  f : List Val → Option Result
  pre : ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ
  ref : RefOK e f

open Silmaril.Wasm.Auto.Front (Rel Report checkMeets) in
/-- **The front end with the VC stage** for a reference contract `r`: differential testing
against `r.f` (`Silmaril.Wasm.Auto.Front.checkMeets`, which refutes or says unknown), then, if it is
unknown, `vcCheck`: a `proved` verdict (stage `vcgen`) means `ModMeets` at every profile
(`Silmaril.Wasm.Auto2.VCBridge.checkMeetsVC_proved`). -/
def checkMeetsVC (R : Rel) (r : RefEntry) (m : Module) (j nRand : Nat) : Report :=
  let base := checkMeets R m j r.f nRand
  match base.verdict with
  | .refuted => base
  | _ => if vcCheck r.e m j then ⟨.proved, .stage "vcgen"⟩ else ⟨.unknown, base.reason⟩

open Silmaril.Wasm.Numerics (Profile) in
open Silmaril.Wasm.Auto.Front (addrOf) in
open Silmaril.Wasm.Verify (instOf) in
/-- **The total every-run specification of a contract at export `j` of `m`**: for the function
instance at the export's address, every call meeting `e.S`'s precondition terminates, without a
trap, with results meeting its postcondition (`Silmaril.Wasm.Logic.Hoare.TFSpecAt` of
`Silmaril.Wasm.Auto2.VCGen.fspec`). -/
def ModTSpec (P : Profile) (e : VcEntry) (m : Module) (j : Nat) : Prop :=
  ∀ fi, (instOf m).store.funcs[addrOf m j]? = some fi →
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P SingleThreaded.Det.noHost (addrOf m j)
      (fspec e.F e.S (addrOf m j) fi)

end Silmaril.Wasm.Auto2.VCBridge
