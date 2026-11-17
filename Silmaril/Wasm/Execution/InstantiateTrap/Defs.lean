module

public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce

/-!
# Instantiation that reports a segment trap with the residual store

Wasm 3.0 §4.4 "Instantiation" (`$instantiate`, `4.4-execution.modules.spectec` at
WebAssembly/spec `608711107b`) allocates the module instance into the store (`$allocmodule`) and
returns the configuration `s''''; {MODULE moduleinst}; instr_E* instr_D* instr_S?`: the code of
the element segments (`$runelem_`), then of the data segments (`$rundata_`), then the start call.
An active segment's code is its offset, `i32.const 0`, `i32.const n`, `table.init`/`memory.init`
and `elem.drop`/`data.drop`; a declarative element segment's code is `elem.drop`; a passive
segment has none. A `table.init`/`memory.init` out of bounds traps
(`Step_read/table.init-oob`, `Step_read/memory.init-oob`), and the trap absorbs the rest of the
code (`Step_pure/trap-instrs`). The allocation and the writes of the segments before the trapping
one stay in the store: the store is threaded through the reduction and nothing restores it.

`instantiateOnce?` and `instantiate?`-based checks report only success. This header adds the
outcome with the store:

* `InitOutcome`: `ok a`, `trap s` (`s` the store at the trapping instruction) or `fail`.
* `initSegmentsR?`: the element segments, then the data segments, applied to the store directly
  (as `initSegments?`), at any memory representation `R`; a segment whose initial bounds check
  fails ends in `trap s₁`, with `s₁` the store after the earlier segments and the segment's
  offset. On `ByteArray` stores it is `initSegmentsT?` of `Exec/SegmentInitTrap`.
* `InstOutcome`: `ok s f start`, `trap s` or `fail` (allocation, initialiser evaluation or
  bounds-unrelated failure; never a trap).
* `instantiateT?`: `prepare?` (the specification's `$instantiate` up to its code, every global
  allocated twice, as `$evalglobals` and `$allocmodule` do), then `initSegmentsR?`.
* `instantiateOnceT?`: `$evalglobals`, then `prepare?` of the global-free residue
  (`Module.globalResidue`), then `initSegmentsR?`: the trap-aware `instantiateOnce?` (every global
  allocated once). On a module without globals it is `instantiateT?`
  (`instantiateOnceT?_of_nil`, `….Thms`).

Neither runs the start function: on `ok` the caller runs `startCode st` (a start function that
traps is a trap of that run, with its own store).

* `instantiateCfg?`: `instantiateT?` as the configuration to continue from, with the module
  instance that `$allocmodule` allocated: on success the start code in the store after the
  segments, on a segment trap `trap` in the residual store, both in the frame of the
  specification's configuration. It is the specification's `Instantiate` configuration run
  through its segment code (`instantiateCfg?_sound`, `….Thms`); the WAST scripts against the
  typed `spectest` host continue from it.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution (MemRep)

/-- The outcome of a trap-aware initialisation: a result, a trap with the store at the trapping
instruction, or a failure that is not a trap. -/
inductive InitOutcome (S α : Type) where
  | ok (a : α)
  | trap (s : S)
  | fail

/-- The outcome of a trap-aware instantiation: the store, frame and start function after
allocation and segment initialisation; a trap in the segment initialisation, with the store at
the trapping instruction; or a failure that is not a trap. -/
inductive InstOutcome (S : Type) where
  | ok (s : S) (f : Frame) (start : Option FuncIdx)
  | trap (s : S)
  | fail

/-- Map the stores of an outcome. -/
def InstOutcome.map {S S' : Type} (g : S → S') : InstOutcome S → InstOutcome S'
  | .ok s f st => .ok (g s) f st
  | .trap s => .trap (g s)
  | .fail => .fail

variable {H R : Type} [MemRep R]

/-- The initial bounds check of `table.init x y` fails (after both lookups succeed). -/
def tableInitOobR? (s : Store H R) (f : Frame) (x : TableIdx) (y : ElemIdx) (a : AddrType)
    (i : BitVec a.intType.width) (j n : BitVec 32) : Bool :=
  match s.table? f x, s.elem? f y with
  | some (_, ti), some (_, ei) =>
    decide (ti.refs.length < i.toNat + n.toNat ∨ ei.refs.length < j.toNat + n.toNat)
  | _, _ => false

/-- The initial bounds check of `memory.init x y` fails (after both lookups succeed). -/
def memoryInitOobR? (s : Store H R) (f : Frame) (x : MemIdx) (y : DataIdx) (a : AddrType)
    (i : BitVec a.intType.width) (j n : BitVec 32) : Bool :=
  match s.mem? f x, s.data? f y with
  | some (_, mi), some (_, di) =>
    decide (MemRep.size mi.bytes < i.toNat + n.toNat ∨ di.bytes.size < j.toNat + n.toNat)
  | _, _ => false

section
variable (ev : Store H R → Frame → Expr → Option (Store H R × Val))

/-- The store at which `$runelem_(k, e)` traps, if it does: the store after the offset. -/
def elemSegTrapR? (s : Store H R) (f : Frame) (k : Nat) (e : Elem) : Option (Store H R) :=
  match e.mode with
  | .active y off =>
    match ev s f off with
    | some (s₁, v) =>
      match v.addr? with
      | some ⟨a, i⟩ =>
        if tableInitOobR? s₁ f y ⟨Fin.ofNat _ k⟩ a i 0 (BitVec.ofNat 32 e.init.length) then
          some s₁ else none
      | none => none
    | none => none
  | _ => none

/-- The store at which `$rundata_(k, d)` traps, if it does: the store after the offset. -/
def dataSegTrapR? (s : Store H R) (f : Frame) (k : Nat) (d : Data) : Option (Store H R) :=
  match d.mode with
  | .active y off =>
    match ev s f off with
    | some (s₁, v) =>
      match v.addr? with
      | some ⟨a, i⟩ =>
        if memoryInitOobR? s₁ f y ⟨Fin.ofNat _ k⟩ a i 0 (BitVec.ofNat 32 d.bytes.size) then
          some s₁ else none
      | none => none
    | none => none
  | _ => none

/-- Trap-aware `$runelem_(k, e)`. -/
def initElemSegR? (s : Store H R) (f : Frame) (k : Nat) (e : Elem) :
    InitOutcome (Store H R) (Store H R) :=
  match initElemSeg? ev s f k e with
  | some s' => .ok s'
  | none =>
    match elemSegTrapR? ev s f k e with
    | some s₁ => .trap s₁
    | none => .fail

/-- Trap-aware `$rundata_(k, d)`. -/
def initDataSegR? (s : Store H R) (f : Frame) (k : Nat) (d : Data) :
    InitOutcome (Store H R) (Store H R) :=
  match initDataSeg? ev s f k d with
  | some s' => .ok s'
  | none =>
    match dataSegTrapR? ev s f k d with
    | some s₁ => .trap s₁
    | none => .fail

/-- Trap-aware element segments, in order. -/
def initElemListR? : Store H R → Frame → List (Nat × Elem) → InitOutcome (Store H R) (Store H R)
  | s, _, [] => .ok s
  | s, f, (k, e) :: es =>
    match initElemSegR? ev s f k e with
    | .ok s₁ => initElemListR? s₁ f es
    | .trap s₁ => .trap s₁
    | .fail => .fail

/-- Trap-aware data segments, in order. -/
def initDataListR? : Store H R → Frame → List (Nat × Data) → InitOutcome (Store H R) (Store H R)
  | s, _, [] => .ok s
  | s, f, (k, d) :: ds =>
    match initDataSegR? ev s f k d with
    | .ok s₁ => initDataListR? s₁ f ds
    | .trap s₁ => .trap s₁
    | .fail => .fail

/-- **Trap-aware segment initialisation** (`instr_E* instr_D*` of `$instantiate`): the element
segments, then the data segments. -/
def initSegmentsR? (s : Store H R) (f : Frame) (m : Module) :
    InitOutcome (Store H R) (Store H R × Frame) :=
  match initElemListR? ev s f ((List.range m.elems.length).zip m.elems) with
  | .ok s₁ =>
    match initDataListR? ev s₁ f ((List.range m.data.length).zip m.data) with
    | .ok s₂ => .ok (s₂, f)
    | .trap t => .trap t
    | .fail => .fail
  | .trap t => .trap t
  | .fail => .fail

end

/-- **Trap-aware `$instantiate`**, every global allocated twice as in the specification:
`prepare?`, then the trap-aware segment initialisation. -/
def instantiateT? (s : Store H R) (m : Module) (xas : List ExternAddr) : InstOutcome (Store H R) :=
  match prepare? evalConst? s m xas with
  | none => .fail
  | some (c, st) =>
    match initSegmentsR? evalConst? c.store c.frame m with
    | .ok (s', f') => .ok s' f' st
    | .trap s' => .trap s'
    | .fail => .fail

/-- **Trap-aware single-allocation instantiation** (the trap-aware `instantiateOnce?`):
`$evalglobals`, `prepare?` of the global-free residue, then the trap-aware segment
initialisation. -/
def instantiateOnceT? (s : Store H R) (m : Module) (xas : List ExternAddr) :
    InstOutcome (Store H R) :=
  match evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) with
  | none => .fail
  | some (s₁, _, _) =>
    match prepare? evalConst? s₁ m.globalResidue
        (xas ++ globalAddrs s.globals.length m.globals.length) with
    | none => .fail
    | some (c, st) =>
      match initSegmentsR? evalConst? c.store c.frame m.globalResidue with
      | .ok (s', f') => .ok s' f' st
      | .trap s' => .trap s'
      | .fail => .fail

/-- **The specification's instantiation run through its segment code**: `prepare?` (Wasm 3.0
`$instantiate` up to its code: `$evalglobals`, then `$allocmodule`, every global allocated as the
specification allocates it), then the trap-aware segment initialisation. The configuration to
continue from (the start code in the store after the segments, or `trap` in the residual store,
in the frame of the module instance) and the module instance. -/
def instantiateCfg? (s : Store H R) (m : Module) (xas : List ExternAddr) :
    Option (Config H R × ModuleInst) :=
  match prepare? evalConst? s m xas with
  | none => none
  | some (c, st) =>
    match initSegmentsR? evalConst? c.store c.frame m with
    | .ok (s', f') => some (⟨s', f', startCode st⟩, c.frame.module)
    | .trap s' => some (⟨s', c.frame, [.trap]⟩, c.frame.module)
    | .fail => none

end Silmaril.Wasm.Execution.Core

end
