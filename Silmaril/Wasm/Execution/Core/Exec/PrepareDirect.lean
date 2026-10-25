module

public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInit
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit

@[expose] public section

/-! # Computable preparation with segments applied directly

`prepareDirect?` runs `prepare?` (allocation) and then applies the element/data
segment initialisation directly to the store via `initSegments?`, returning the
final store, frame and the start function index (if any). This is the entry
point used by the component engine. `instantiateDirect?` specialises it to the
concrete constant evaluator `evalConst?`.

`prepare?_code`, `Steps.withStart` and `evalConst?_evalSound` are reused from
`Exec/InstantiateInit.lean`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- The code that remains after direct preparation: `call x` for a start
function, nothing otherwise. -/
def startCode : Option FuncIdx → List Admin
  | some x => [.plain (.call x)]
  | none => []

section
variable (ev : Store H → Frame → Expr → Option (Store H × Val))

/-- Allocation followed by direct segment initialisation. -/
def prepareDirect? (s : Store H) (m : Module) (xas : List ExternAddr) :
    Option (Store H × Frame × Option FuncIdx) :=
  match prepare? ev s m xas with
  | none => none
  | some (c, st) =>
    match initSegments? ev c.store c.frame m with
    | none => none
    | some (s', f') => some (s', f', st)

end

variable {ev : Store H → Frame → Expr → Option (Store H × Val)}

theorem prepareDirect?_start {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {f' : Frame} {st : Option FuncIdx} (h : prepareDirect? ev s m xas = some (s', f', st)) :
    st = m.start := by
  unfold prepareDirect? at h
  split at h
  · cases h
  · rename_i c st₀ hp
    split at h
    · cases h
    · cases h
      exact prepare?_start hp

variable {P : Profile} {host : HostSemantics H}

theorem prepareDirect?_steps (hev : EvalSound P host ev) {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (h : prepareDirect? ev s m xas = some (s', f', st)) :
    ∃ c, prepare? ev s m xas = some (c, st) ∧ Steps P host c ⟨s', f', []⟩ := by
  unfold prepareDirect? at h
  split at h
  · cases h
  · rename_i c st₀ hp
    split at h
    · cases h
    · rename_i s₁ f₁ hi
      cases h
      refine ⟨c, hp, ?_⟩
      have hs := initSegments?_steps (P := P) (host := host) hev hi
      rw [← prepare?_code hp] at hs
      exact hs

/-- The frame returned by `prepareDirect?` is the frame of the prepared config. -/
theorem prepareDirect?_frame {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (h : prepareDirect? ev s m xas = some (s', f', st)) :
    ∃ c, prepare? ev s m xas = some (c, st) ∧ f' = c.frame := by
  unfold prepareDirect? at h
  split at h
  · cases h
  · rename_i c st₀ hp
    split at h
    · cases h
    · rename_i s₁ f₁ hi
      cases h
      exact ⟨c, hp, initSegments?_frame hi⟩

theorem Config.withStart_nil (s' : Store H) (f' : Frame) (st : Option FuncIdx) :
    (⟨s', f', []⟩ : Config H).withStart st = ⟨s', f', startCode st⟩ := by
  cases st <;> rfl

theorem prepareDirect?_sound (hev : EvalSound P host ev) {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (h : prepareDirect? ev s m xas = some (s', f', st))
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    ∃ c, prepare? ev s m xas = some (c, st) ∧ st = m.start ∧
      Instantiate P host s m xas (c.withStart st) ∧
      Steps P host (c.withStart st) ⟨s', f', startCode st⟩ := by
  obtain ⟨c, hp, hs⟩ := prepareDirect?_steps hev h
  obtain ⟨hst, hi⟩ := prepare?_sound hev hp hvalid
  refine ⟨c, hp, hst, hi, ?_⟩
  rw [← Config.withStart_nil]
  exact Steps.withStart hs

/-- Concrete direct instantiation, driven by `evalConst?`. -/
def instantiateDirect? (s : Store H) (m : Module) (xas : List ExternAddr) :
    Option (Store H × Frame × Option FuncIdx) :=
  prepareDirect? evalConst? s m xas

theorem instantiateDirect?_start {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {f' : Frame} {st : Option FuncIdx} (h : instantiateDirect? s m xas = some (s', f', st)) :
    st = m.start :=
  prepareDirect?_start h

theorem instantiateDirect?_sound {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (h : instantiateDirect? s m xas = some (s', f', st))
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    ∃ c, prepare? evalConst? s m xas = some (c, st) ∧ st = m.start ∧
      Instantiate P host s m xas (c.withStart st) ∧
      Steps P host (c.withStart st) ⟨s', f', startCode st⟩ :=
  prepareDirect?_sound evalConst?_evalSound h hvalid

end Silmaril.Wasm.Execution.Core
