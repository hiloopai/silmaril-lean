module

public import Silmaril.Wasm.Jco.Wrap.Thms
public import Silmaril.Wasm.Binaryen.Behaviour

/-!
# A real Core 3.0 module instance as a `CoreInst`

The jco constructions (`wrap`, `wrapE`, `wrapW`, …) are stated over an abstract core instance
`CoreInst`: a state type, a linear memory and the behaviour of each core export. This module
gives the instance of a **real Core 3.0 module instance**, run by silmaril's reference
semantics (`Silmaril.Wasm.Execution.Core.Steps`) at a numerical profile `P` and host `host`:

* the state is the whole Core store `Store H` (globals, tables, memories, functions, GC heap),
  so the instance is **stateful**: a call may change any of it, and later calls see the change;
* the memory is the bytes of the memory instance at store address `ma` (`memBytes`), and a
  store through it replaces those bytes (`putBytes`);
* `coreCall P host mi name xs`: the export `name` of the module instance `mi` (found by name,
  as in `Binaryen.moduleObs`) is invoked with `$invoke` on the arguments `xs`; a run that
  reduces to the values `vs` returns them (as flat values), a run that reduces to a trap traps.

Conventions that are choices of this module (each is stated where it is defined):

* an uncaught exception (`Result.throw`) is a trap, as in the component model, where an
  exception escaping a lifted function traps;
* a missing export, or arguments of the wrong core types (`¬ InvokeOk`), trap (the canonical
  ABI never calls an export with ill-typed arguments; for well-typed calls this case is empty);
* a returned reference or vector value (not a flat value) traps; by type soundness this does
  not happen for an export whose results are number types;
* divergence has no outcome (`RM` relates states to terminating outcomes only).

`realInst P host mi ma` is the `CoreInst`. The initial state of an instance is any store in
which the module was instantiated and its start function ran (`Binaryen.Ready`); `RealStart`
packages this. Theorems in `Silmaril.Wasm.Jco.Real.Inst.Thms`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (exportFunc? Ready)

variable {H : Type}

/-- A flat value as a Core 3.0 value. -/
def toVal (v : Flat) : Val := .num ⟨v.type, v.bits⟩

/-- A Core 3.0 number value as a flat value. -/
def ofVal? : Val → Option Flat
  | .num ⟨t, b⟩ => some ⟨t, b⟩
  | _ => none

/-- The bytes of the memory instance at store address `ma` (empty if there is none). -/
def memBytes (ma : Nat) (s : Store H) : Mem :=
  match s.mems[ma]? with
  | some m => m.bytes.data.toList
  | none => []

/-- Replace the bytes of the memory instance at store address `ma` (no change if there is
none). -/
def putBytes (ma : Nat) (s : Store H) (bs : Mem) : Store H :=
  match s.mems[ma]? with
  | some m => s.setMem ma { m with bytes := ⟨bs.toArray⟩ }
  | none => s

/-- The outcome of a terminated run with result `r` in store `s`: values that are all flat are
returned; a trap, an uncaught exception, or a non-flat value trap. -/
def resultOut (r : Result) (s : Store H) : Out (Store H) (List Flat) :=
  match r with
  | .values vs =>
    match vs.mapM ofVal? with
    | some xs => .ok xs s
    | none => .trap
  | .throw _ => .trap
  | .trap => .trap

/-- **Calling export `name` of the module instance `mi`** with the reference semantics: invoke
its function address on the arguments and run to a result. Ill-typed arguments and a missing
export trap. -/
def coreCall (P : Profile) (host : HostSemantics H) (mi : Silmaril.Wasm.Execution.Core.ModuleInst)
    (name : String) (xs : List Flat) : RM (Store H) (List Flat) := fun s o =>
  match exportFunc? mi name with
  | some a =>
    (InvokeOk s a (xs.map toVal) ∧
      ∃ (c : Config H) (r : Result), Steps P host (invoke s a (xs.map toVal)) c ∧
        c.code = r.toAdmin ∧ o = resultOut r c.store) ∨
    (¬ InvokeOk s a (xs.map toVal) ∧ o = .trap)
  | none => o = .trap

/-- **The `CoreInst` of a real Core 3.0 module instance** `mi` whose (exported) memory is at
store address `ma`, at profile `P` and host `host`. States are Core stores. -/
def realInst (H : Type) (P : Profile) (host : HostSemantics H)
    (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) : CoreInst where
  St := Store H
  mem := memBytes ma
  setMem := putBytes ma
  call := coreCall P host mi

/-- The memory address exported under `x` by `mi`. -/
def exportMem? (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (x : String) : Option Nat :=
  match mi.exports.find? (fun e => e.name == x) with
  | some ⟨_, .mem a⟩ => some a
  | _ => none

/-- **A started instance** of the Core 3.0 module `m`: `m` was instantiated in the empty store
with no imports and its segments and start function ran, giving the store `s0` and module
instance `mi`; it exports its memory under `"memory"` at address `ma`. `s0` is the initial
state of `realInst H P host mi ma`. -/
structure RealStart (P : Profile) (host : HostSemantics H) (m : Silmaril.Wasm.Module) where
  s0 : Store H
  mi : Silmaril.Wasm.Execution.Core.ModuleInst
  ma : Nat
  ready : Ready P host {} m [] s0 mi
  memory : exportMem? mi "memory" = some ma

/-- The core instance of a started module. -/
abbrev RealStart.inst {P : Profile} {host : HostSemantics H} {m : Silmaril.Wasm.Module}
    (r : RealStart P host m) : CoreInst :=
  realInst H P host r.mi r.ma

end Silmaril.Wasm.Jco.Real
