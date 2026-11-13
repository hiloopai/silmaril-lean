module

public import Silmaril.Wasm.Component.Core3G.Defs
public import Silmaril.Wasm.Models.FX.Defs

/-!
# A component engine over WasmFX: definitions

The reference component machine is parametric in a core engine (`Silmaril.Wasm.Component.Param`,
`docs/projects/spectec/README.md` §3). This module gives an engine `fxE P` whose threads run **WasmFX**
code (`Silmaril.Wasm.Models.FX`: continuations, handler frames and the stack-switching
instructions, reduced by `StepFX`), and whose modules may define FX functions.

* **Store.** A Core 3.0 store over the host codes `FXCode H`: a host function of the component
  machine (`host h`) or an FX function (`fx F`, its body and module instance). So FX functions
  live in the shared store, have function addresses and flat types, can be exported, called
  through `call_ref` from FX code and turned into continuations by `cont.new`; `fxOf` is the FX
  function table that `StepFX` reads. Every accessor of the canonical ABI (memories, tables,
  function types, instantiation of the Core part) is that of `core3P P` at host type `FXCode H`.
* **Modules** `ModuleFX`: a Core 3.0 module and a list of FX function declarations (`FXDecl`:
  export name, flat type, locals, FX body). Instantiation (`prepareFX?`) prepares the Core module
  and then allocates each FX function as a host function with code `fx F` whose module instance
  is the new instance; the FX functions are exported by name after the Core exports.
* **Threads** `ThreadFX H`:
  * `core t`: a Core 3.0 thread, run by `InternalP P` with status `statusP P` (as `core3P P`);
    a Core thread whose Core status is a call of an FX function (`callout (fx F)`) is running:
    its next step is a `StepFX` step of its FX image, entering the FX function;
  * `fx K f code`: an FX configuration without its store (continuation store `K`, frame,
    FX code), run by `StepFX P` with no host and the FX table `fxOf`;
  * `parked K f E Ec h args`: an FX thread stopped at a call of host function `h` (component
    host code `h`) with arguments `args`; `E` is the FX evaluation context and `Ec` the Core
    context (`decompose?`) of the redex. An FX thread **parks** by an internal step when its
    code is `E.plug (cs.map core)` and `decompose? s cs` finds a call of a component host
    function. `resumeFX` plugs the host's result into `Ec` and `E`.
* **Status** `statusFX P`: a Core thread has its Core status (FX callouts are `running`), an FX
  thread is `running` when it can step and otherwise returned (values, trap, uncaught
  exception) or `stuck`, and a parked thread is a callout.

`fxE P` is a `CoreEngine`; its laws, its game engine and its behaviour are in
`Silmaril.Wasm.Component.FXEngine.Thms`. `ofNum m` is a numeric IR module as an FX module with no
FX functions, and `FXNumModule` is the IR module type whose modules carry FX functions.

Not modelled: static types of FX exports (`exportTypes` lists the Core exports only; the
dynamic type of an FX export, `externType?`, is its flat type), FX imports, and validation of
FX bodies (as in `Silmaril.Wasm.Models.FX`, the reduction is untyped).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXEngine

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX (FuncFX ContFX AdminFX InstrFX StepFX ConfigFX ofCore cvals cthrowing)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Engine (CallResult Status)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Stores and modules -/

/-- Host codes of the FX engine's store: a host function of the component machine, or an FX
function. -/
inductive FXCode (H : Type) where
  | host (h : H)
  | fx (F : FuncFX)

/-- The FX function table of an FX store. -/
def fxOf {H : Type} : FXCode H → Option FuncFX
  | .host _ => none
  | .fx F => some F

/-- The host relation of internal steps: none. -/
abbrev noHostFX (H : Type) : HostSemantics (FXCode H) := fun _ _ _ _ => False

/-- An FX function declaration: its export name, flat type, locals and FX body. -/
structure FXDecl where
  name : String
  type : V1.FuncType
  locals : List ValType
  body : List InstrFX

/-- The FX function of a declaration in a module instance. -/
def FXDecl.func (d : FXDecl) (inst : ModuleInst) : FuncFX :=
  { module := inst, nparams := d.type.params.length, nresults := d.type.results.length,
    locals := d.locals, body := d.body }

/-- An FX module: a Core 3.0 module and FX function declarations. -/
structure ModuleFX where
  core : Module
  fxs : List FXDecl

/-- An FX module instance: the Core module instance and the named FX function exports. -/
structure InstFX where
  core : ModuleInst
  fx : List (String × ExternAddr)

/-- Allocate the FX functions of a module instance. -/
def allocFX {H : Type} (inst : ModuleInst) :
    Store (FXCode H) → List FXDecl → Store (FXCode H) × List (String × ExternAddr)
  | s, [] => (s, [])
  | s, d :: ds =>
    let p := SingleThreaded.allocHost s d.type (.fx (d.func inst))
    let q := allocFX inst p.1 ds
    (q.1, (d.name, .func p.2) :: q.2)

/-- Instantiation of an FX module: the Core module (`core3P`'s `prepareE?`), then its FX
functions. -/
def prepareFX? {H : Type} (s : Store (FXCode H)) (m : ModuleFX) (xas : List ExternAddr) :
    Option (Store (FXCode H) × InstFX × Option Nat) :=
  match Silmaril.Wasm.Component.Engine.Core3.prepareE? s m.core xas with
  | some (s₁, i, st) =>
    let q := allocFX i s₁ m.fxs
    some (q.1, ⟨i, q.2⟩, st)
  | none => none

/-! ## Threads -/

/-- FX engine threads: Core threads, FX threads, and FX threads parked at a host call. -/
inductive ThreadFX (H : Type) where
  | core (t : SingleThreaded.Thread)
  | fx (K : List (Option ContFX)) (f : Frame) (code : List AdminFX)
  | parked (K : List (Option ContFX)) (f : Frame) (E : Silmaril.Wasm.Models.FX.Ctx)
      (Ec : SingleThreaded.Ctx) (h : H) (args : List Execution.Core.Val)

/-- **The internal step of the FX engine.** -/
def InternalFX (P : Profile) {H : Type} (x y : Store (FXCode H) × ThreadFX H) : Prop :=
  match x.2 with
  | .core t =>
    (∃ t', y.2 = .core t' ∧ Silmaril.Wasm.Game.InternalP P (x.1, t) (y.1, t')) ∨
      ((∃ F args, Silmaril.Wasm.Game.statusP P x.1 t = .callout (.fx F) args) ∧
        ∃ K f code, y.2 = .fx K f code ∧
          StepFX P (noHostFX H) fxOf (ofCore (t.config x.1)) ⟨y.1, K, f, code⟩)
  | .fx K f code =>
    (∃ K' f' code', y.2 = .fx K' f' code' ∧
        StepFX P (noHostFX H) fxOf ⟨x.1, K, f, code⟩ ⟨y.1, K', f', code'⟩) ∨
      (y.1 = x.1 ∧ ∃ (E : Silmaril.Wasm.Models.FX.Ctx) (cs : List Admin) (Ec : SingleThreaded.Ctx)
        (a : Nat) (h : H) (args : List Execution.Core.Val), code = E.plug (cs.map .core) ∧
        SingleThreaded.decompose? x.1 cs = some (Ec, a, FXCode.host h, args) ∧
        y.2 = .parked K f E Ec h args)
  | .parked .. => False

/-- Rename the host code of an engine status from `FXCode H` to `H` (a callout of an FX
function, which the FX engine never reports, becomes `stuck`). -/
def mapHostS {H : Type} : Status (FXCode H) → Status H
  | .running => .running
  | .returned r => .returned r
  | .callout (.host h) args => .callout h args
  | .callout (.fx _) _ => .stuck
  | .stuck => .stuck

/-- The status of a Core thread in the FX engine: its flat Core status, with a call of an FX
function `running`. -/
def liftR {H : Type} : SingleThreaded.Status (FXCode H) → Status H
  | .callout (.fx _) _ => .running
  | st => mapHostS (flatStatus st)

open Classical in
/-- The final status of FX code that takes no step. -/
noncomputable def fxResult {H : Type} (code : List AdminFX) : Status H :=
  if h : ∃ vs, code = cvals vs then
    match h.choose.mapM SingleThreaded.toFlat? with
    | some fvs => .returned (.values fvs)
    | none => .stuck
  else if code = [.core .trap] then .returned .trap
  else if ∃ a, code = cthrowing a then .returned .trap
  else .stuck

open Classical in
/-- **The status of an FX engine thread.** -/
noncomputable def statusFX (P : Profile) {H : Type} (s : Store (FXCode H)) :
    ThreadFX H → Status H
  | .core t => liftR (Silmaril.Wasm.Game.statusP P s t)
  | .fx K f code => if ∃ y, InternalFX P (s, .fx K f code) y then .running else fxResult code
  | .parked _ _ _ _ h args =>
    match args.mapM SingleThreaded.toFlat? with
    | some fargs => .callout h fargs
    | none => .stuck

/-- **Resumption** of a parked thread with a host result. -/
def resumeFX {H : Type} (s : Store (FXCode H)) : ThreadFX H → CallResult → ThreadFX H
  | .core t, r => .core (SingleThreaded.resume s t (Silmaril.Wasm.Component.Engine.Core3.toCR r))
  | .parked K f E Ec _ _, r =>
    .fx K f (E.plug ((Ec.fill (Silmaril.Wasm.Component.Engine.Core3.toCR r).toAdmin).map .core))
  | t, _ => t

/-! ## The engine -/

/-- **The WasmFX engine** at profile `P`. -/
noncomputable def fxE (P : Profile) : Engine where
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
  prepare? s m xas := prepareFX? s m xas
  allocHost s ft h := (core3P P).allocHost s ft (.host h)
  funcType? s a := (core3P P).funcType? s a
  memAddrType? s m := (core3P P).memAddrType? s m
  memSize? s m := (core3P P).memSize? s m
  memRead? s m st len := (core3P P).memRead? s m st len
  memWrite? s m st bs := (core3P P).memWrite? s m st bs
  tableAddrType? s t := (core3P P).tableAddrType? s t
  tableFunc? s t i := (core3P P).tableFunc? s t i
  Thread H := ThreadFX H
  invoke a args := .core (SingleThreaded.Thread.invokeFlat a args)
  status s t := statusFX P s t
  Internal x y := InternalFX P x y
  resume s t r := resumeFX s t r

/-- Import matching of the FX engine is that of Core 3.0, hence decidable. -/
instance fxE_decExternSub (P : Profile) (a b : (fxE P).ExternType) :
    Decidable ((fxE P).ExternSub a b) :=
  core3P_decExternSub P a b

/-! ## IR modules -/

/-- A numeric IR module as an FX module with no FX functions. -/
def ofNum (m : NumModule) : ModuleFX := ⟨m.mod, []⟩

/-- IR modules over the FX engine: an FX module with the flat types of its exports (Core
exports and FX functions alike, by name). -/
structure FXNumModule where
  mod : ModuleFX
  exports : CoreIface

instance : CoreModule FXNumModule := ⟨fun _ => [], FXNumModule.exports⟩

end Silmaril.Wasm.Component.FXEngine
