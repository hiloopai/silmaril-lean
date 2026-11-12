module

public import Silmaril.Wasm.Component.FXRes.Engine.Defs
public import Silmaril.Wasm.Component.FXRes.Handle.Defs

/-!
# A WasmFX component engine whose host state holds the continuation table

In the WasmFX component engine with suspension `fxEV P` (`Silmaril.Wasm.Component.FXEngineV`) each
FX thread keeps its continuations in its own store `K`, and a host call passes flat Core values
only, so a continuation can neither reach the host nor outlive the export call that made it.
This module gives the engine `fxCE P`, next to `fxEV P` and without changing it, in which the
**continuation built-ins are host calls of the FX threads** and the engine store holds the
**continuation table** (the representation table of a resource type `cont`):

* `CB`: the built-ins `new` (`[] → [i32]`, with a continuation reference as its operand),
  `take` (`[i32] → []`, leaving a continuation reference) and `drop` (`[i32] → []`). Their flat
  types are nominal: `StepFX'` is untyped and the built-in rules below do not read them.
* `CH H = CB ⊕ H`: the host codes of the engine store are the built-ins and the host functions
  of the component machine (`H`).
* `EStore H`: the FX store over `FXCode (CH H)` and the continuation table `tab : Silmaril.Wasm.Component.Runtime.Table ContFX`
  (`Silmaril.Wasm.Component.Runtime.Table`, the Canonical ABI table). The index of a
  continuation in `tab` is the `i32` representation of a `cont` resource.
* `prepareC?`: instantiation as `prepareFXV?`, then the three built-ins are allocated after the
  FX functions and appended to the function index space of the FX code: for a module whose Core
  instance has `n` functions and `k` FX functions, built-in `b` is function index
  `n + k + b.idx`. Core code does not see them.
* `BStep`: **a built-in call**, at the hole of a context `CtxV` of an FX thread whose code calls
  (`ref.func a; call_ref`) the function `a` with code `.host (.inl b)`:
  * `new`: the live continuation `k` named by the `contRef k` below the call **moves** into
    `tab` at the index `n` returned by `Table.add?` (the store entry `k` is consumed) and the code
    gets `i32 n`;
  * `take`: the entry `n` of `tab` is removed and its continuation gets the fresh store index
    `K.length`, which the code gets as a `contRef`;
  * `drop`: the entry is removed and its continuation discarded;
  * each traps (`trap` at the hole, nothing else changed) when its operand is a consumed
    continuation, the table is full, or the index is not live.
  The event is the table event (`Table.Event ContFX`), `none` for a trap.
* `InternalC`: an internal step of `fxEV`'s relation `InternalV` on the FX store, with the table
  unchanged and **without parking at a built-in**, or a built-in call.
* `statusC`, `fxCE P`: the engine. Callouts of built-ins are never reported (a Core thread
  calling a built-in is `stuck`); callouts of machine host functions are as in `fxEV`.

Theorems: `Silmaril.Wasm.Component.FXRes.ContEngine.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContEngine

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX (FuncFX ContFX AdminFX InstrFX ConfigFX ofCore cvals cthrowing)
open Silmaril.Wasm.Models.FXV (StepFX' CtxV)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Component.FXRes (handleVal)
open Silmaril.Wasm.Component.Engine (CallResult Status)
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Built-ins and stores -/

/-- The continuation built-ins. -/
inductive CB where
  | new
  | take
  | drop
  deriving DecidableEq, Repr

/-- The position of a built-in after the FX functions. -/
def CB.idx : CB → Nat
  | .new => 0
  | .take => 1
  | .drop => 2

/-- The nominal flat type of a built-in. -/
def CB.type : CB → V1.FuncType
  | .new => ⟨[], [.i32]⟩
  | .take => ⟨[.i32], []⟩
  | .drop => ⟨[.i32], []⟩

/-- Host codes: the built-ins and the machine's host functions. -/
abbrev CH (H : Type) := CB ⊕ H

/-- **The engine store**: the FX store and the continuation table. -/
structure EStore (H : Type) where
  core : Store (FXCode (CH H))
  tab : Silmaril.Wasm.Component.Runtime.Table ContFX

/-- Allocate the three built-ins. -/
def allocCB {H : Type} (s : Store (FXCode (CH H))) : Store (FXCode (CH H)) :=
  let s₁ := (SingleThreaded.allocHost s CB.new.type (.host (.inl .new))).1
  let s₂ := (SingleThreaded.allocHost s₁ CB.take.type (.host (.inl .take))).1
  (SingleThreaded.allocHost s₂ CB.drop.type (.host (.inl .drop))).1

/-- **Instantiation**: `prepareFXV?` with the built-ins after the FX functions, in the FX
function index space. The table is kept. -/
def prepareC? {H : Type} (s : EStore H) (m : ModuleFX) (xas : List ExternAddr) :
    Option (EStore H × InstFX × Option Nat) :=
  match Silmaril.Wasm.Component.Engine.Core3.prepareE? s.core m.core xas with
  | some (s₁, i, st) =>
    let q := allocFX (fxInst i s₁.funcs.length (m.fxs.length + 3)) s₁ m.fxs
    some (⟨allocCB q.1, s.tab⟩, ⟨i, q.2⟩, st)
  | none => none

/-! ## Built-in calls -/

variable {H : Type}

/-- Function address `a` is the built-in `b`. -/
def IsCB (s : Store (FXCode (CH H))) (a : Nat) (b : CB) : Prop :=
  ∃ fi, s.funcs[a]? = some fi ∧ fi.code = .host (.host (.inl b))

/-- The call of function address `a` by `call_ref` instruction `c`. -/
def callAt (a : Nat) (c : Admin) : List AdminFX := [.core (.ref (.func a)), .core c]

/-- **A call of a continuation built-in**, with its table event (`none`: a trap). -/
inductive BStep : EStore H × ThreadV (CH H) → EStore H × ThreadV (CH H) →
    Option (Table.Event ContFX) → Prop where
  | new {s : Store (FXCode (CH H))} {t t' : Silmaril.Wasm.Component.Runtime.Table ContFX} {K : List (Option ContFX)} {f : Frame}
      {E : CtxV} {a k n : Nat} {c : Admin} {C : ContFX} (hc : c.IsCallRef) (hb : IsCB s a .new)
      (hk : K[k]? = some (some C)) (ht : t.add? C = some (n, t')) :
      BStep (⟨s, t⟩, .fx K f (E.plug (.contRef k :: callAt a c)))
        (⟨s, t'⟩, .fx (K.set k none) f (E.plug [handleVal n])) (some (.added n C))
  | take {s : Store (FXCode (CH H))} {t t' : Silmaril.Wasm.Component.Runtime.Table ContFX} {K : List (Option ContFX)} {f : Frame}
      {E : CtxV} {a : Nat} {c : Admin} {b : BitVec 32} {C : ContFX} (hc : c.IsCallRef)
      (hb : IsCB s a .take) (ht : t.remove? b.toNat = some (C, t')) :
      BStep (⟨s, t⟩, .fx K f (E.plug (.core (constI32 b) :: callAt a c)))
        (⟨s, t'⟩, .fx (K ++ [some C]) f (E.plug [.contRef K.length])) (some (.removed b.toNat C))
  | drop {s : Store (FXCode (CH H))} {t t' : Silmaril.Wasm.Component.Runtime.Table ContFX} {K : List (Option ContFX)} {f : Frame}
      {E : CtxV} {a : Nat} {c : Admin} {b : BitVec 32} {C : ContFX} (hc : c.IsCallRef)
      (hb : IsCB s a .drop) (ht : t.remove? b.toNat = some (C, t')) :
      BStep (⟨s, t⟩, .fx K f (E.plug (.core (constI32 b) :: callAt a c)))
        (⟨s, t'⟩, .fx K f (E.plug [])) (some (.removed b.toNat C))
  | newUsed {s : Store (FXCode (CH H))} {t : Silmaril.Wasm.Component.Runtime.Table ContFX} {K : List (Option ContFX)} {f : Frame}
      {E : CtxV} {a k : Nat} {c : Admin} (hc : c.IsCallRef) (hb : IsCB s a .new)
      (hk : K[k]? = some none) :
      BStep (⟨s, t⟩, .fx K f (E.plug (.contRef k :: callAt a c)))
        (⟨s, t⟩, .fx K f (E.plug [.core .trap])) none
  | newFull {s : Store (FXCode (CH H))} {t : Silmaril.Wasm.Component.Runtime.Table ContFX} {K : List (Option ContFX)} {f : Frame}
      {E : CtxV} {a k : Nat} {c : Admin} {C : ContFX} (hc : c.IsCallRef) (hb : IsCB s a .new)
      (hk : K[k]? = some (some C)) (ht : t.add? C = none) :
      BStep (⟨s, t⟩, .fx K f (E.plug (.contRef k :: callAt a c)))
        (⟨s, t⟩, .fx K f (E.plug [.core .trap])) none
  | dead {s : Store (FXCode (CH H))} {t : Silmaril.Wasm.Component.Runtime.Table ContFX} {K : List (Option ContFX)} {f : Frame}
      {E : CtxV} {a : Nat} {c : Admin} {b : BitVec 32} {o : CB} (hc : c.IsCallRef)
      (hb : IsCB s a o) (ho : o ≠ .new) (ht : t.remove? b.toNat = none) :
      BStep (⟨s, t⟩, .fx K f (E.plug (.core (constI32 b) :: callAt a c)))
        (⟨s, t⟩, .fx K f (E.plug [.core .trap])) none

/-- A thread parked at a built-in. -/
def ParkedCB : ThreadV (CH H) → Prop
  | .parked _ _ _ _ (.inl _) _ => True
  | _ => False

/-- **The internal step of the engine**: an `InternalV` step with the table unchanged that does
not park at a built-in, or a built-in call. -/
def InternalC (P : Profile) (x y : EStore H × ThreadV (CH H)) : Prop :=
  (y.1.tab = x.1.tab ∧ InternalV P (x.1.core, x.2) (y.1.core, y.2) ∧ ¬ ParkedCB y.2) ∨
    ∃ ev, BStep x y ev

/-- Statuses over `CH H` as statuses over `H`: a callout of a built-in is `stuck`. -/
def mapCB : Status (CH H) → Status H
  | .running => .running
  | .returned r => .returned r
  | .callout (.inr h) args => .callout h args
  | .callout (.inl _) _ => .stuck
  | .stuck => .stuck

open Classical in
/-- **The status of a thread.** -/
noncomputable def statusC (P : Profile) (s : EStore H) : ThreadV (CH H) → Status H
  | .core t => mapCB (liftR (Silmaril.Wasm.Game.statusP P s.core t))
  | .fx K f code => if ∃ y, InternalC P (s, .fx K f code) y then .running else fxResult code
  | .parked _ _ _ _ (.inr h) args =>
    match args.mapM SingleThreaded.toFlat? with
    | some fargs => .callout h fargs
    | none => .stuck
  | .parked _ _ _ _ (.inl _) _ => .stuck

/-! ## The engine -/

/-- **The WasmFX engine with a continuation table** at profile `P`. -/
noncomputable def fxCE (P : Profile) : Engine where
  Module := ModuleFX
  Valid m := (core3P P).Valid m.core
  FuncType := (core3P P).FuncType
  decEqFuncType := (core3P P).decEqFuncType
  ExternType := (core3P P).ExternType
  ExternSub := (core3P P).ExternSub
  ofFlatType := (core3P P).ofFlatType
  flatType? := (core3P P).flatType?
  importTypes m := (core3P P).importTypes m.core
  exportTypes m := (core3P P).exportTypes m.core
  Store H := EStore H
  empty _ := ⟨{}, Table.empty⟩
  FuncAddr := Nat
  MemAddr := Nat
  TableAddr := Nat
  GlobalAddr := Nat
  ExternVal := ExternAddr
  asFunc? := (core3P P).asFunc?
  asMemory? := (core3P P).asMemory?
  asTable? := (core3P P).asTable?
  asGlobal? := (core3P P).asGlobal?
  ofFunc := .func
  Inst := InstFX
  exports i := Silmaril.Wasm.Component.Engine.Core3.instExports i.core ++ i.fx
  externType? s x := (core3P P).externType? s.core x
  prepare? s m xas := prepareC? s m xas
  allocHost s ft h :=
    let q := (core3P P).allocHost s.core ft (.host (.inr h))
    (⟨q.1, s.tab⟩, q.2)
  funcType? s a := (core3P P).funcType? s.core a
  memAddrType? s m := (core3P P).memAddrType? s.core m
  memSize? s m := (core3P P).memSize? s.core m
  memRead? s m st len := (core3P P).memRead? s.core m st len
  memWrite? s m st bs := ((core3P P).memWrite? s.core m st bs).map fun c => ⟨c, s.tab⟩
  tableAddrType? s t := (core3P P).tableAddrType? s.core t
  tableFunc? s t i := (core3P P).tableFunc? s.core t i
  Thread H := ThreadV (CH H)
  invoke a args := .core (SingleThreaded.Thread.invokeFlat a args)
  status s t := statusC P s t
  Internal x y := InternalC P x y
  resume s t r := resumeV s.core t r

/-- Import matching is that of Core 3.0, hence decidable. -/
instance fxCE_decExternSub (P : Profile) (a b : (fxCE P).ExternType) :
    Decidable ((fxCE P).ExternSub a b) :=
  core3P_decExternSub P a b

end Silmaril.Wasm.Component.FXRes.ContEngine
