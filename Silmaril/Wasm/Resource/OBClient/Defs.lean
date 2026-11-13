module

public import Silmaril.Wasm.Resource.Client.Defs
public import Silmaril.Wasm.Resource.Replay.Defs

@[expose] public section

/-!
# A typestate verifier for borrowing clients (ownership protocol)

`checkOB m ia iu ρ` decides, conservatively, that the Core 3.0 module `m` is a safe client of the
ownership and borrowing protocol `obSpec ρ.toOB` (`Silmaril.Wasm.Resource.Handle`), for roles `ρ`
given by number (`NRoles`): import `ia` allocates (`alloc : [] → [h]`), import `iu` uses
(`use : [h] → …`), exports `j` with `ρ.lend j` borrow their single argument for the call, exports
with `ρ.take j` take ownership of it.

## The analysis

It is the client typestate analysis of `Silmaril.Wasm.Resource.Client`, run with the **held**
handles (owned or borrowed) as the live list, no flag/handle global pairs (`ps = []`, so a handle
lives only in the locals and on the stack of one activation), and these changes:

* **Entry facts (argument identity).** The body of a role export (`roleAddrs`) is checked from the
  fact `loc 0`: its parameter, local `0`, holds a held handle. This is sound because the
  parameter is the handle the environment just lent or handed over, and because a role export is
  entered only by the environment: role exports are outside the reachable set `G` (`reachOB`), so
  no body calls them and no reference to them is held (the reachability check of `G`).
* **No drop, no transfer.** The free import is replaced by the index `noImp I` that no host
  function has: a call of any import other than `ia`/`iu` must be of a function of `G`, which
  avoids the hosts of the imports classified `free` or `give` (`roleOK`). So the program never
  frees or gives a handle; a borrowed handle cannot be dropped.
* **End of call.** Facts are frame-local, so nothing survives the return of an export: the
  protocol's `endCall` ends the borrows with no obligation.

## Frees of owned handles (`checkOF`)

`checkOF m ia iu if_ ρ` also admits the free import `if_ : [h] → …`. It runs the analysis twice
on every body, over the same code:

* the **held** instance (`cfgOf`, live list: the held handles) as above, with `if_` as its free
  import: a use needs a held handle;
* the **owned** instance (`cfgO`, live list: the owned handles), where uses are neutral (`nU`):
  a free needs an owned handle. A role export that takes ownership (`ρ.take`, not `ρ.lend`)
  starts this instance from `loc 0`, a lending one from no fact.

So a program may free the handles it allocated or was handed, but not a borrowed one. The roles
must classify `if_` (only) as `free`; imports classified as `give` must be avoided.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.OBClient

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Resource.Client
open Silmaril.Wasm.Verify (isHost closure rootsB avoidsB exprRF exprCalls instOf storeFuncs)

/-- An import index no host function of the instance has: the stand-in for a free import. -/
def noImp (I : Silmaril.Wasm.Game.ScalarInstance) : Nat := I.imports.length

/-- An export with a handle argument (borrowed or owned). -/
def roleB (ρ : NRoles) (j : Nat) : Bool := ρ.lend j || ρ.take j

/-- The addresses of the role exports. -/
def roleAddrs (I : Silmaril.Wasm.Game.ScalarInstance) (ρ : NRoles) : List Nat :=
  ((List.range I.exports.length).filter (roleB ρ)).map fun j => I.addrs.getD j 0

/-- The reachable functions other than the two imports and the role exports. -/
def reachOB (I : Silmaril.Wasm.Game.ScalarInstance) (ia iu : Nat) (ρ : NRoles) : List Nat :=
  (closure I.store (fsOf I) (storeFuncs I.store ++ I.addrs)).filter fun a =>
    !isBadC I.store ia iu (noImp I) a && !(roleAddrs I ρ).contains a

/-- The body of a role export passes the check from the entry fact `loc 0`. -/
def funcOkE (s : Store Nat) (fs G : List Nat) (ia iu nf : Nat) (a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm code => fi.module.funcs == fs &&
        (exprRF code.body).all (fun x => match fs[x]? with
          | some b => G.contains b
          | none => true) &&
        (exprCalls code.body).all (fun x => match fs[x]? with
          | some b => G.contains b || isBadC s ia iu nf b
          | none => true) &&
        okL (cfgOf s fs ia iu nf []) fi.module.globals [.loc 0] .other code.body
    | .host _ => false
  | none => false

/-- The roles agree with the two imports: only `ia` allocates, only `iu` uses, and the imports
classified as `free` or `give` are avoided by `G` (hence never called). -/
def roleOK (I : Silmaril.Wasm.Game.ScalarInstance) (G : List Nat) (ia iu : Nat) (ρ : NRoles) : Bool :=
  (List.range I.imports.length).all fun i =>
    ρ.alloc i == (i == ia) && ρ.use i == (i == iu) &&
      (!(ρ.free i || ρ.give i) || avoidsB I.store G i)

/-- The role exports take one argument and pass the entry check; the other exports are in `G`. -/
def exportsOK (I : Silmaril.Wasm.Game.ScalarInstance) (G : List Nat) (ia iu : Nat) (ρ : NRoles) :
    Bool :=
  (List.range I.exports.length).all fun j =>
    if roleB ρ j then
      (I.exports[j]?.map (·.params.length)) == some 1 &&
        funcOkE I.store (fsOf I) G ia iu (noImp I) (I.addrs.getD j 0)
    else G.contains (I.addrs.getD j 0)

/-- **The borrowing-client check on an instance.** -/
def checkOBInst (I : Silmaril.Wasm.Game.ScalarInstance) (ia iu : Nat) (ρ : NRoles) : Bool :=
  let s := I.store
  let fs := fsOf I
  let G := reachOB I ia iu ρ
  ia != iu && ia < I.imports.length && iu < I.imports.length &&
    (importArity I ia).map (·.1) == some 0 && (importArity I ia).map (·.2) == some 1 &&
    (importArity I iu).map (·.1) == some 1 &&
    G.all (funcOkC s fs G ia iu (noImp I) []) && rootsB G (storeFuncs s) &&
    avoidsB s G ia && avoidsB s G iu && exportsOK I G ia iu ρ && roleOK I G ia iu ρ

/-- **The borrowing-client check on a module** (its instance `instOf m`). -/
def checkOB (m : Module) (ia iu : Nat) (ρ : NRoles) : Bool :=
  (Silmaril.Wasm.Verify.instance? m).isSome && checkOBInst (instOf m) ia iu ρ

/-! ## Frees of owned handles -/

/-- The configuration of the **owned-handle** instance: uses are neutral. -/
def cfgO (s : Store Nat) (fs : List Nat) (ia iu if_ : Nat) : Cfg :=
  { cfgOf s fs ia iu if_ [] with nU := true }

/-- The reachable functions other than the three imports and the role exports. -/
def reachOF (I : Silmaril.Wasm.Game.ScalarInstance) (ia iu if_ : Nat) (ρ : NRoles) : List Nat :=
  (closure I.store (fsOf I) (storeFuncs I.store ++ I.addrs)).filter fun a =>
    !isBadC I.store ia iu if_ a && !(roleAddrs I ρ).contains a

/-- The body at address `a` passes the owned-handle check from the facts `F`. -/
def funcOkO (s : Store Nat) (fs : List Nat) (ia iu if_ : Nat) (F : List Fact) (a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm code => okL (cfgO s fs ia iu if_) fi.module.globals F .other code.body
    | .host _ => true
  | none => true

/-- The entry facts of the owned-handle instance at export `j`: `loc 0` when it takes
ownership of its argument. -/
def entryO (ρ : NRoles) (j : Nat) : List Fact :=
  if !ρ.lend j && ρ.take j then [.loc 0] else []

/-- The roles agree with the three imports; imports classified as `give` are avoided. -/
def roleOKF (I : Silmaril.Wasm.Game.ScalarInstance) (G : List Nat) (ia iu if_ : Nat) (ρ : NRoles) :
    Bool :=
  (List.range I.imports.length).all fun i =>
    ρ.alloc i == (i == ia) && ρ.use i == (i == iu) && ρ.free i == (i == if_) &&
      (!ρ.give i || avoidsB I.store G i)

/-- The role exports take one argument and pass both entry checks; the other exports are in
`G`. -/
def exportsOKF (I : Silmaril.Wasm.Game.ScalarInstance) (G : List Nat) (ia iu if_ : Nat)
    (ρ : NRoles) : Bool :=
  (List.range I.exports.length).all fun j =>
    if roleB ρ j then
      (I.exports[j]?.map (·.params.length)) == some 1 &&
        funcOkE I.store (fsOf I) G ia iu if_ (I.addrs.getD j 0) &&
        funcOkO I.store (fsOf I) ia iu if_ (entryO ρ j) (I.addrs.getD j 0)
    else G.contains (I.addrs.getD j 0)

/-- **The ownership check with frees, on an instance.** -/
def checkOFInst (I : Silmaril.Wasm.Game.ScalarInstance) (ia iu if_ : Nat) (ρ : NRoles) : Bool :=
  let s := I.store
  let fs := fsOf I
  let G := reachOF I ia iu if_ ρ
  ia != iu && ia != if_ && iu != if_ &&
    ia < I.imports.length && iu < I.imports.length && if_ < I.imports.length &&
    (importArity I ia).map (·.1) == some 0 && (importArity I ia).map (·.2) == some 1 &&
    (importArity I iu).map (·.1) == some 1 && (importArity I if_).map (·.1) == some 1 &&
    G.all (funcOkC s fs G ia iu if_ []) && G.all (funcOkO s fs ia iu if_ []) &&
    rootsB G (storeFuncs s) && avoidsB s G ia && avoidsB s G iu && avoidsB s G if_ &&
    exportsOKF I G ia iu if_ ρ && roleOKF I G ia iu if_ ρ

/-- **The ownership check with frees, on a module**: import `ia` allocates, `iu` uses, `if_`
frees. -/
def checkOF (m : Module) (ia iu if_ : Nat) (ρ : NRoles) : Bool :=
  (Silmaril.Wasm.Verify.instance? m).isSome && checkOFInst (instOf m) ia iu if_ ρ

end Silmaril.Wasm.Resource.OBClient
