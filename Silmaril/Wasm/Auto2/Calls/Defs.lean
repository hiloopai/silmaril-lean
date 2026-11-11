module

public import Silmaril.Wasm.Auto2.Summ.Defs

@[expose] public section

/-!
# Function summaries with calls: symbolic inlining

The summaries of `Silmaril.Wasm.Auto2.Summ` stop at `call`. This module adds calls to the
executor: `xsexecC` runs a body like track equiv's unrolling executor
(`Silmaril.Wasm.Auto.EquivUnroll.xsexecU`) and, at `call x`, runs the **callee's body** symbolically
(inlining) when the callee is a Wasm function of the same module instance (the same function,
global and memory addresses) whose declared locals are integers:

* the callee starts with its parameters bound to the caller's top `n` stack terms (in order) and
  its declared locals at `0`, with the caller's globals, memory term and no guards;
* at its end, the caller continues with the callee's results on its stack, the callee's globals
  and memory, and the callee's guards appended to its own. A callee's guard records the store at
  the trapping instruction with the **caller's** locals: a trap inside the callee leaves the
  callee's frame, and the caller sees the trap in its own frame.

`fuel` bounds instructions, loop iterations and the call depth (a recursive function runs out of
fuel, so there is no summary). The callees are given by a function environment `fe` (function
index to `Callee`); `calleeOf s mi` reads them from the store and module instance.

`sumOfC`, `fnSumC?`, `fnCheckC`, `checkAmongC`, `checkEquivC`: the summaries and checks of
`Silmaril.Wasm.Auto2.Summ` with this executor. The soundness theorems are in
`Silmaril.Wasm.Auto2.Calls.Thms`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Auto2.Calls

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm.Auto.Bridge (scalarInt? intTy?)
open Silmaril.Wasm.Auto.EquivUnroll (whileBody? condConst?)
open Silmaril.Wasm.Auto2.Summ (sumCheckU defFuel)
open Silmaril.Wasm.Game (ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance?)

/-- What the executor needs of a callee. -/
structure Callee where
  /-- The number of parameters. -/
  np : Nat
  /-- The number of results. -/
  nr : Nat
  /-- The integer types of the declared locals. -/
  ls : List IntType
  /-- The body. -/
  body : List Instr

/-- **The callee at function index `x`** of the module instance `mi` in the store `s`: a Wasm
function whose instance has the same function, global and memory addresses as `mi`, and whose
declared locals are integers. -/
def calleeOf {H : Type} (s : Store H) (mi : ModuleInst) (x : Nat) : Option Callee :=
  match mi.funcs[x]? with
  | none => none
  | some a =>
    match s.funcs[a]? with
    | none => none
    | some fi =>
      match fi.code, fi.type.expand? with
      | .wasm code, some (.func ps rs) =>
        if fi.module.funcs = mi.funcs ∧ fi.module.globals = mi.globals ∧ fi.module.mems = mi.mems then
          match code.locals.mapM intTy? with
          | some ls => some ⟨ps.length, rs.length, ls, code.body⟩
          | none => none
        else none
      | _, _ => none

/-- The trap states of a callee's guards, seen from the caller: the caller's locals. -/
def retLocals (L : List (IntType × XT)) (G : List (Guard × XState)) : List (Guard × XState) :=
  G.map fun g => (g.1, { g.2 with locals := L })

/-- The initial state of a callee: parameters from the caller's top `n` stack slots (the top is
the last parameter), declared locals `0`, the caller's globals and memory, no guards. -/
def calleeInit (S : XState) (n : Nat) (ls : List IntType) : XState where
  locals := (S.stack.take n).reverse ++ ls.map fun t => (t, .const 0)
  stack := []
  globs := S.globs
  mem := S.mem
  guards := []

/-- The caller's state after a call: the callee's results on top of the rest of its stack, the
callee's globals and memory, the callee's guards (with the caller's locals) appended. -/
def afterCall (S : XState) (n : Nat) (A : XState) : XState where
  locals := S.locals
  stack := A.stack ++ S.stack.drop n
  globs := A.globs
  mem := A.mem
  guards := S.guards ++ retLocals S.locals A.guards

/-- **Symbolic execution with loop unrolling and inlined calls.** -/
def xsexecC (mem : Bool) (fe : Nat → Option Callee) : Nat → XState → List Instr → Option XState
  | _, S, [] => some S
  | 0, _, _ :: _ => none
  | f + 1, S, i :: is =>
    match i with
    | .loop .empty b =>
      match S.stack, whileBody? b with
      | [], some body =>
        match xsexec mem S body with
        | some S₁ =>
          match S₁.stack with
          | (.i32, e) :: st' =>
            match condConst? e with
            | some 0 => xsexecC mem fe f { S₁ with stack := st' } is
            | some (_ + 1) => xsexecC mem fe f { S₁ with stack := [] } (i :: is)
            | none => none
          | _ => none
        | none => none
      | _, _ => none
    | .call x =>
      match fe x.toNat with
      | some ce =>
        if ce.np ≤ S.stack.length then
          match xsexecC mem fe f (calleeInit S ce.np ce.ls) ce.body with
          | some A =>
            if A.stack.length = ce.nr then xsexecC mem fe f (afterCall S ce.np A) is else none
          | none => none
        else none
      | none => none
    | _ =>
      match xstep mem S i with
      | some S' => xsexecC mem fe f S' is
      | none => none

/-! ## Summaries -/

/-- The summary of a function instance with scalar type `ft` in the store `s`: loops unrolled,
calls to Wasm functions of the same instance inlined. -/
def sumOfC (fuel : Nat) {H : Type} (s : Store H) (ft : FnType) (fi : FuncInst H) :
    Option FnSumX :=
  match fi.code with
  | .wasm code =>
    match ft.params.mapM scalarInt?, ft.results.mapM scalarInt?, code.locals.mapM intTy? with
    | some ps, some rs, some ls =>
      let g := globsUsed s fi.module
      let mo := memOf s fi.module
      match xsexecC mo.isSome (calleeOf s fi.module) fuel (fnInitX ps ls g.2.2) code.body with
      | some A =>
        if A.stack.map (·.1) = rs.reverse then some ⟨ps, rs, g.2.1, bytesOf mo, A⟩ else none
      | none => none
    | _, _, _ => none
  | .host _ => none

/-- The summary of function export `j` of a computed instance. -/
def fnSumCI (fuel : Nat) (I : ScalarInstance) (j : Nat) : Option FnSumX :=
  match I.exports[j]?, I.store.funcs[I.addrs.getD j 0]? with
  | some ft, some fi => sumOfC fuel I.store ft fi
  | _, _ => none

/-- **The summary of function export `j` of `m`'s computed instance**, calls inlined. -/
def fnSumC? (fuel : Nat) (m : Module) (j : Nat) : Option FnSumX :=
  match instance? m with
  | some (_, I) => fnSumCI fuel I j
  | none => none

/-- The check at export `j` of two modules (`Silmaril.Wasm.Auto2.Summ.sumCheckU` on these
summaries). -/
def fnCheckC (fuel : Nat) (m₁ m₂ : Module) (j : Nat) : Bool :=
  sumCheckU (fnSumC? fuel m₁ j) (fnSumC? fuel m₂ j)

/-- **The check on the exports `js`**, each module instantiated once. -/
def checkAmongC (fuel : Nat) (m₁ m₂ : Module) (js : List Nat) : List Bool :=
  match instance? m₁, instance? m₂ with
  | some (_, I₁), some (_, I₂) => js.map fun j => sumCheckU (fnSumCI fuel I₁ j) (fnSumCI fuel I₂ j)
  | _, _ => []

/-! ## The front end -/

/-- Turn a report without a verdict into a proof (stage `equivc`) when `ok` holds. -/
def upgradeC (r : Silmaril.Wasm.Auto.Front.Report) (ok : Bool) : Silmaril.Wasm.Auto.Front.Report :=
  if r.verdict == .unknown && ok then ⟨.proved, .stage "equivc"⟩ else r

/-- **The front end for equivalence**: `Silmaril.Wasm.Auto2.Summ.checkEquivU`, then this check
(stage `equivc`). -/
def checkEquivC (R : Silmaril.Wasm.Auto.Front.Rel) (m₁ m₂ : Module) (j : Nat) (nRand : Nat)
    (identical : Bool) : Silmaril.Wasm.Auto.Front.Report :=
  upgradeC (Silmaril.Wasm.Auto2.Summ.checkEquivU R m₁ m₂ j nRand identical) (fnCheckC defFuel m₁ m₂ j)

/-- **The front end for a refinement**: `checkRefinesU`, then this check. -/
def checkRefinesC (R : Silmaril.Wasm.Auto.Front.Rel) (impl spec : Module) (j : Nat) (nRand : Nat)
    (identical : Bool) : Silmaril.Wasm.Auto.Front.Report :=
  upgradeC (Silmaril.Wasm.Auto2.Summ.checkRefinesU R impl spec j nRand identical)
    (fnCheckC defFuel impl spec j)

/-- The proving stages alone. -/
def proveStageC (m₁ m₂ : Module) (j : Nat) : Silmaril.Wasm.Auto.Front.Report :=
  upgradeC (Silmaril.Wasm.Auto2.Summ.proveStageU m₁ m₂ j) (fnCheckC defFuel m₁ m₂ j)

end Silmaril.Wasm.Auto2.Calls
