module

public import Silmaril.Wasm.Execution.InstantiateTrap.Defs
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitTrap
public import Silmaril.Wasm.Execution.Core.Exec.PrepareDirect
public import Silmaril.Wasm.Execution.MemRep.Sim.Defs
import Silmaril.Proofs.Wasm.Execution.InstantiateTrap

/-!
# Instantiation that reports a segment trap with the residual store: theorems

Agreement with the success-only functions (any memory representation):

* `initSegmentsR?_ok_iff`: `initSegmentsR? ev s f m = .ok (s', f') ↔ initSegments? ev s f m =
  some (s', f')`;
* `instantiateT?_ok_iff`: `instantiateT? s m xas = .ok s' f st ↔ prepareDirect? evalConst? s m xas
  = some (s', f, st)`;
* `instantiateOnceT?_ok_iff`: `instantiateOnceT? s m xas = .ok s' f st ↔ instantiateOnce? s m xas
  = some (s', f, st)`;
* `instantiateOnceT?_of_nil`: on a module without globals, `instantiateOnceT? = instantiateT?`.

Memory representations (`Execution.MemRep`, lawful): `instantiateT?_toBytes`,
`instantiateOnceT?_toBytes`: run on `KMem` stores and read through `Store.toBytes`, the outcome is
the outcome on `ByteArray` stores.

The specification (`ByteArray` stores, any profile `P` and host):

* `initSegmentsR?_trap`: a trap of `initSegmentsR?` is a trap of `initSegmentsT?`
  (`Exec/SegmentInitTrap`), with the same store;
* `instantiateT?_trap_sound`: for a valid module and imports of the import types, `instantiateT?
  s m xas = .trap s'` gives the configuration `c₀` of `$instantiate` (`Instantiate P host s m xas
  c₀`, from `prepare?`) and a run `Steps P host c₀ ⟨s', c₀.frame, [trap]⟩`: the **residual store
  `s'` is the store of the trapping configuration**, reached by the specification's reduction of
  the segment code. It holds the allocation of the module and every write of the segments before
  the trapping one; nothing is rolled back, and the start function is not called.
* `instantiateT?_ok_sound`: `.ok s' f st` gives `Instantiate P host s m xas c₀` and `Steps P host
  c₀ ⟨s', f, startCode st⟩`.
* `instantiateT?_eq_fail_iff`: `.fail` is exactly a failure of `prepare?` or an `initSegmentsT?`
  failure; for valid modules in typed stores neither happens when an `Instantiate` derivation
  exists (`Silmaril.Wasm.Game.InstantiateTrap.Thms`).
* `instantiateOnceT?_trap_steps`: a trap of single allocation is a run of the global-free
  residue's segment code to `trap`, with the hypotheses of `Game.spec_trap_seg` (the
  specification's instantiation, globals allocated twice, plays as the thread stopped at that
  trap).

The configuration form `instantiateCfg?` (the scripts against the typed `spectest` host):
`instantiateCfg?_eq_none_iff` (it fails exactly when `instantiateT?` does),
`instantiateCfg?_toBytes`, and `instantiateCfg?_sound`: its configuration is reached by the
specification's reduction from the `Instantiate` configuration, whose frame names its module
instance.

Proofs: `Silmaril.Proofs.Wasm.Execution.InstantiateTrap`.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)

section Generic

variable {H R : Type} [MemRep R]

theorem initSegmentsR?_ok_iff {ev : Store H R → Frame → Expr → Option (Store H R × Val)}
    {s s' : Store H R} {f f' : Frame} {m : Module} :
    initSegmentsR? ev s f m = .ok (s', f') ↔ initSegments? ev s f m = some (s', f') :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.initSegmentsR?_ok_iff

theorem instantiateT?_ok_iff {s s' : Store H R} {m : Module} {xas : List ExternAddr} {f : Frame}
    {st : Option FuncIdx} :
    instantiateT? s m xas = .ok s' f st ↔ prepareDirect? evalConst? s m xas = some (s', f, st) :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateT?_ok_iff

theorem instantiateOnceT?_ok_iff {s s' : Store H R} {m : Module} {xas : List ExternAddr}
    {f : Frame} {st : Option FuncIdx} :
    instantiateOnceT? s m xas = .ok s' f st ↔ instantiateOnce? s m xas = some (s', f, st) :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateOnceT?_ok_iff

/-- On a module without globals, single allocation is the specification's. -/
theorem instantiateOnceT?_of_nil {s : Store H R} {m : Module} {xas : List ExternAddr}
    (h : m.globals = []) : instantiateOnceT? s m xas = instantiateT? s m xas :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateOnceT?_of_nil h

/-- `instantiateCfg?` fails exactly when `instantiateT?` does. -/
theorem instantiateCfg?_eq_none_iff {s : Store H R} {m : Module} {xas : List ExternAddr} :
    instantiateCfg? s m xas = none ↔ instantiateT? s m xas = .fail :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateCfg?_eq_none_iff

variable [LawfulMemRep R]

theorem instantiateT?_toBytes (s : Store H R) (m : Module) (xas : List ExternAddr) :
    instantiateT? s.toBytes m xas = (instantiateT? s m xas).map Store.toBytes :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateT?_toBytes s m xas

theorem instantiateOnceT?_toBytes (s : Store H R) (m : Module) (xas : List ExternAddr) :
    instantiateOnceT? s.toBytes m xas = (instantiateOnceT? s m xas).map Store.toBytes :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateOnceT?_toBytes s m xas

theorem instantiateCfg?_toBytes (s : Store H R) (m : Module)
    (xas : List ExternAddr) :
    instantiateCfg? s.toBytes m xas = (instantiateCfg? s m xas).map fun p => (p.1.toBytes, p.2) :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateCfg?_toBytes s m xas

end Generic

section Spec

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem initSegmentsR?_trap {ev : Store H → Frame → Expr → Option (Store H × Val)}
    {s s' : Store H} {f : Frame} {m : Module} (h : initSegmentsR? ev s f m = .trap s') :
    initSegmentsT? ev s f m = .trap s' :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.initSegmentsR?_trap h

/-- **A segment trap of `instantiateT?` is the specification's instantiation run to `trap`**,
with the residual store `s'` as the store of the trapping configuration. -/
theorem instantiateT?_trap_sound {s s' : Store H} {m : Module} {xas : List ExternAddr}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : instantiateT? s m xas = .trap s') :
    ∃ c st, prepare? evalConst? s m xas = some (c, st) ∧
      initSegmentsT? evalConst? c.store c.frame m = .trap s' ∧
      Instantiate P host s m xas (c.withStart st) ∧
      Steps P host (c.withStart st) ⟨s', c.frame, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateT?_trap_sound hvalid h

/-- **Success of `instantiateT?` is the specification's instantiation run to the start code.** -/
theorem instantiateT?_ok_sound {s s' : Store H} {m : Module} {xas : List ExternAddr} {f : Frame}
    {st : Option FuncIdx}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : instantiateT? s m xas = .ok s' f st) :
    ∃ c, prepare? evalConst? s m xas = some (c, st) ∧ st = m.start ∧
      Instantiate P host s m xas (c.withStart st) ∧
      Steps P host (c.withStart st) ⟨s', f, startCode st⟩ :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateT?_ok_sound hvalid h

/-- `instantiateT?` fails exactly when `prepare?` fails or the segment initialisation ends in
`.fail` (neither a result nor a trap). -/
theorem instantiateT?_eq_fail_iff {s : Store H} {m : Module} {xas : List ExternAddr} :
    instantiateT? s m xas = .fail ↔ prepare? evalConst? s m xas = none ∨
      ∃ c st, prepare? evalConst? s m xas = some (c, st) ∧
        initSegmentsT? evalConst? c.store c.frame m = .fail :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateT?_eq_fail_iff

/-- **A segment trap of single allocation** is a run of the global-free residue's segment code to
`trap` in the residual store `s'`. -/
theorem instantiateOnceT?_trap_steps {s s' : Store H} {m : Module} {xas : List ExternAddr}
    (h : instantiateOnceT? s m xas = .trap s') :
    ∃ s₁ f₁ vs c st, evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩
        (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, vs) ∧
      prepare? evalConst? s₁ m.globalResidue
        (xas ++ globalAddrs s.globals.length m.globals.length) = some (c, st) ∧
      initSegmentsT? evalConst? c.store c.frame m.globalResidue = .trap s' ∧
      Steps P host (c.withStart st) ⟨s', c.frame, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateOnceT?_trap_steps h

/-- **The configuration of `instantiateCfg?` is reached from the specification's instantiation**
(globals allocated as `$instantiate` allocates them): the `Instantiate` configuration `c₀` runs
to it, and `c₀`'s frame names the returned module instance. -/
theorem instantiateCfg?_sound {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H}
    {mi : ModuleInst}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : instantiateCfg? s m xas = some (c, mi)) :
    ∃ c₀, Instantiate P host s m xas c₀ ∧ c₀.frame.module = mi ∧ Steps P host c₀ c :=
  Silmaril.Proofs.Wasm.Execution.InstantiateTrap.instantiateCfg?_sound hvalid h

end Spec

end Silmaril.Wasm.Execution.Core

end
