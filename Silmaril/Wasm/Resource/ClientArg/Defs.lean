module

public import Silmaril.Wasm.Resource.Client.Defs

@[expose] public section

/-!
# Handles passed to internal callees

`checkClientArg m ia iu if_ ps hs` extends the client check `checkClient` of
`Silmaril.Wasm.Resource.Client` with **helpers**: the module functions with indices `hs`, each
taking exactly one parameter, which is a handle. A call of a helper needs a live handle held by
no flagged pair on top of the stack (`Cfg.isH`), and the helper's body is checked from the entry
fact `loc 0`: its parameter is such a handle. Facts of the caller are dropped at the call, as at
any call (the helper may free its argument).

Helpers lie outside the reachable set `G` (`reachArg`): they are neither exported nor referenced
(`ref.func`, tables), so they are entered only by a direct `call` from checked code, which
requires the handle.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.ClientArg

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Resource.Client
open Silmaril.Wasm.Verify (isHost closure rootsOf rootsB avoidsB exprRF exprCalls instOf)

/-- The configuration of the analysis with the helpers at addresses `H`. -/
def cfgH (s : Store Nat) (fs : List Nat) (ia iu if_ : Nat) (ps : List (Nat × Nat))
    (H : List Nat) : Cfg :=
  { cfgOf s fs ia iu if_ ps with isH := fun a => H.contains a }

/-- The functions a checked body may call without being in `G`: the three imports and the
helpers. -/
def badH (s : Store Nat) (ia iu if_ : Nat) (H : List Nat) (a : Nat) : Bool :=
  isBadC s ia iu if_ a || H.contains a

/-- The helper addresses of the module function indices `hs`. -/
def helpersOf (I : Silmaril.Wasm.Game.ScalarInstance) (hs : List Nat) : List Nat :=
  hs.filterMap fun x => (fsOf I)[x]?

/-- The reachable functions other than the three imports and the helpers. -/
def reachArg (I : Silmaril.Wasm.Game.ScalarInstance) (ia iu if_ : Nat) (H : List Nat) : List Nat :=
  (closure I.store (fsOf I) (rootsOf I.store I.addrs ++ H)).filter
    fun a => !isBadC I.store ia iu if_ a && !H.contains a

/-- The function at address `a` passes the check from the facts `F`. -/
def funcOkH (s : Store Nat) (fs G : List Nat) (ia iu if_ : Nat) (ps : List (Nat × Nat))
    (H : List Nat) (F : List Fact) (a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm code => fi.module.funcs == fs &&
        (exprRF code.body).all (fun x => match fs[x]? with
          | some b => G.contains b
          | none => true) &&
        (exprCalls code.body).all (fun x => match fs[x]? with
          | some b => G.contains b || badH s ia iu if_ H b
          | none => true) &&
        okL (cfgH s fs ia iu if_ ps H) fi.module.globals F .other code.body
    | .host _ => true
  | none => true

/-- A helper is a Wasm function with exactly one parameter. -/
def helperOK (s : Store Nat) (a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    (match fi.code with
      | .wasm _ => true
      | .host _ => false) &&
    (match fi.type.expand? with
      | some (.func ps _) => ps.length == 1
      | _ => false)
  | none => false

/-- **The client check with helpers on an instance.** -/
def checkArgInst (I : Silmaril.Wasm.Game.ScalarInstance) (ia iu if_ : Nat) (ps : List (Nat × Nat))
    (hs : List Nat) : Bool :=
  let s := I.store
  let fs := fsOf I
  let H := helpersOf I hs
  let G := reachArg I ia iu if_ H
  ia != iu && ia != if_ && iu != if_ &&
    (importArity I ia).map (·.1) == some 0 && (importArity I ia).map (·.2) == some 1 &&
    (importArity I iu).map (·.1) == some 1 && (importArity I if_).map (·.1) == some 1 &&
    decide (PairsOK ps) && ps.all (fun p => gval s.globals p.1 == some (Val.i32 0)) &&
    G.all (funcOkH s fs G ia iu if_ ps H []) &&
    H.all (fun b => helperOK s b && funcOkH s fs G ia iu if_ ps H [.loc 0] b) &&
    rootsB G (rootsOf s I.addrs) && avoidsB s G ia && avoidsB s G iu && avoidsB s G if_

/-- **The client check with helpers on a module**: `hs` are the indices of the helpers in the
module's function index space. -/
def checkClientArg (m : Module) (ia iu if_ : Nat) (ps : List (Nat × Nat)) (hs : List Nat) : Bool :=
  (Silmaril.Wasm.Verify.instance? m).isSome && checkArgInst (instOf m) ia iu if_ ps hs

end Silmaril.Wasm.Resource.ClientArg
