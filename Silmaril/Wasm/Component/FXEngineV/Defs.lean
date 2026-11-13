module

public import Silmaril.Wasm.Component.FXEngine.Defs
public import Silmaril.Wasm.Models.FXV.Defs

/-!
# A WasmFX component engine whose code can suspend: definitions

The WasmFX engine `fxE P` (`Silmaril.Wasm.Component.FXEngine`) has two properties that together
keep every `suspend` of its modules from completing:

* its FX functions are allocated as host functions **after** the Core part is instantiated, and
  are not added to the module instance's function index space. So `ref.func` names Core
  functions only, `cont.new` makes continuations of Core functions only, and the code a
  `resume` runs under a handler frame is Core code, which has no `suspend`;
* it reduces by `StepFX`, where a continuation reference cannot cross the `br` of an
  `(on x l)` handler clause (`suspend_to_label_stuck`, `Silmaril.Proofs.Wasm.Models.FXLower`).

This module gives a second engine `fxEV P` that fixes both, next to `fxE P` and without changing
it:

* **Function index space.** `prepareFXV?` instantiates the Core part (as `prepareFX?`), then
  appends the addresses the FX functions will get to the instance's `funcs`, so that the FX
  function `j` of the module is function index `|core funcs| + j` for the FX code of the module
  (`ref.func`, hence `cont.new`). Core functions keep the Core instance (their code is validated
  against the Core module only).
* **Reduction.** Threads run by the corrected relation `StepFX'`
  (`Silmaril.Wasm.Models.FXV`), where continuation references are values.
* **Parking.** An FX thread parks at a call of a component host function inside a context
  whose value prefixes are FX values (`CtxV`), so a thread with continuation references on its
  stack can still call out.

Stores, modules (`ModuleFX`), the FX function table `fxOf`, the status of terminated FX code
(`fxResult`) and of Core threads (`liftR`) are those of `fxE P`. `FXNumModule` is the IR module
type of both engines.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXEngineV

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX (FuncFX ContFX AdminFX InstrFX ConfigFX ofCore cvals cthrowing)
open Silmaril.Wasm.Models.FXV (StepFX' CtxV)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Component.Engine (CallResult Status)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Instantiation -/

/-- The module instance seen by the FX functions: the Core instance with the addresses of the
FX functions appended to its functions (allocated from address `n` on). -/
def fxInst (i : ModuleInst) (n k : Nat) : ModuleInst :=
  { i with funcs := i.funcs ++ (List.range k).map (n + ·) }

/-- **Instantiation of an FX module**, with its FX functions in the function index space. -/
def prepareFXV? {H : Type} (s : Store (FXCode H)) (m : ModuleFX) (xas : List ExternAddr) :
    Option (Store (FXCode H) × InstFX × Option Nat) :=
  match Silmaril.Wasm.Component.Engine.Core3.prepareE? s m.core xas with
  | some (s₁, i, st) =>
    let q := allocFX (fxInst i s₁.funcs.length m.fxs.length) s₁ m.fxs
    some (q.1, ⟨i, q.2⟩, st)
  | none => none

/-! ## Threads -/

/-- Threads: Core threads, FX threads, and FX threads parked at a host call (in a context with
FX values). -/
inductive ThreadV (H : Type) where
  | core (t : SingleThreaded.Thread)
  | fx (K : List (Option ContFX)) (f : Frame) (code : List AdminFX)
  | parked (K : List (Option ContFX)) (f : Frame) (E : CtxV)
      (Ec : SingleThreaded.Ctx) (h : H) (args : List Execution.Core.Val)

/-- **The internal step of the engine**: `InternalFX` with `StepFX'` and `CtxV`. -/
def InternalV (P : Profile) {H : Type} (x y : Store (FXCode H) × ThreadV H) : Prop :=
  match x.2 with
  | .core t =>
    (∃ t', y.2 = .core t' ∧ Silmaril.Wasm.Game.InternalP P (x.1, t) (y.1, t')) ∨
      ((∃ F args, Silmaril.Wasm.Game.statusP P x.1 t = .callout (.fx F) args) ∧
        ∃ K f code, y.2 = .fx K f code ∧
          StepFX' P (noHostFX H) fxOf (ofCore (t.config x.1)) ⟨y.1, K, f, code⟩)
  | .fx K f code =>
    (∃ K' f' code', y.2 = .fx K' f' code' ∧
        StepFX' P (noHostFX H) fxOf ⟨x.1, K, f, code⟩ ⟨y.1, K', f', code'⟩) ∨
      (y.1 = x.1 ∧ ∃ (E : CtxV) (cs : List Admin) (Ec : SingleThreaded.Ctx)
        (a : Nat) (h : H) (args : List Execution.Core.Val), code = E.plug (cs.map .core) ∧
        SingleThreaded.decompose? x.1 cs = some (Ec, a, FXCode.host h, args) ∧
        y.2 = .parked K f E Ec h args)
  | .parked .. => False

open Classical in
/-- **The status of a thread.** -/
noncomputable def statusV (P : Profile) {H : Type} (s : Store (FXCode H)) :
    ThreadV H → Status H
  | .core t => liftR (Silmaril.Wasm.Game.statusP P s t)
  | .fx K f code => if ∃ y, InternalV P (s, .fx K f code) y then .running else fxResult code
  | .parked _ _ _ _ h args =>
    match args.mapM SingleThreaded.toFlat? with
    | some fargs => .callout h fargs
    | none => .stuck

/-- **Resumption** of a parked thread with a host result. -/
def resumeV {H : Type} (s : Store (FXCode H)) : ThreadV H → CallResult → ThreadV H
  | .core t, r => .core (SingleThreaded.resume s t (Silmaril.Wasm.Component.Engine.Core3.toCR r))
  | .parked K f E Ec _ _, r =>
    .fx K f (E.plug ((Ec.fill (Silmaril.Wasm.Component.Engine.Core3.toCR r).toAdmin).map .core))
  | t, _ => t

/-! ## The engine -/

/-- **The WasmFX engine with suspension** at profile `P`: `fxE P` with `prepareFXV?`, `StepFX'`
and parking in `CtxV`. -/
noncomputable def fxEV (P : Profile) : Engine where
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
  Store H := Store (FXCode H)
  empty _ := {}
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
  externType? s x := (core3P P).externType? s x
  prepare? s m xas := prepareFXV? s m xas
  allocHost s ft h := (core3P P).allocHost s ft (.host h)
  funcType? s a := (core3P P).funcType? s a
  memAddrType? s m := (core3P P).memAddrType? s m
  memSize? s m := (core3P P).memSize? s m
  memRead? s m st len := (core3P P).memRead? s m st len
  memWrite? s m st bs := (core3P P).memWrite? s m st bs
  tableAddrType? s t := (core3P P).tableAddrType? s t
  tableFunc? s t i := (core3P P).tableFunc? s t i
  Thread H := ThreadV H
  invoke a args := .core (SingleThreaded.Thread.invokeFlat a args)
  status s t := statusV P s t
  Internal x y := InternalV P x y
  resume s t r := resumeV s t r

/-- Import matching is that of Core 3.0, hence decidable. -/
instance fxEV_decExternSub (P : Profile) (a b : (fxEV P).ExternType) :
    Decidable ((fxEV P).ExternSub a b) :=
  core3P_decExternSub P a b

end Silmaril.Wasm.Component.FXEngineV
