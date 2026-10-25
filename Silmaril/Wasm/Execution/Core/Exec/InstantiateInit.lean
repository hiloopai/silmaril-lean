module

public import Silmaril.Wasm.Execution.Core.Exec.ConstEval
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInit

@[expose] public section

/-! # Concrete end-to-end instantiation for Core 3.0

`instantiateInit?` composes `prepare?` (allocation) and `initSegments?` (direct
element/data segment initialisation), both driven by the concrete constant
evaluator `evalConst?`, and leaves only the start call (if any) to run.

`instantiateInit?_sound`: the result is reachable by `Steps` from a configuration
produced by `Instantiate`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

theorem evalConst?_evalSound {P : Profile} {host : HostSemantics H} :
    EvalSound P host (evalConst? (H := H)) :=
  fun _ _ _ _ _ h => evalConst?_sound h

/-- Concrete instantiation: allocate, initialise segments directly, and return the
configuration that still has to run the start function (if any). -/
def instantiateInit? (s : Store H) (m : Module) (xas : List ExternAddr) : Option (Config H) :=
  match prepare? evalConst? s m xas with
  | none => none
  | some (c, st) =>
    match initSegments? evalConst? c.store c.frame m with
    | none => none
    | some (s', f') => some ((⟨s', f', []⟩ : Config H).withStart st)

variable {ev : Store H → Frame → Expr → Option (Store H × Val)}

theorem prepare?_code {s : Store H} {m : Module} {xas : List ExternAddr}
    {c : Config H} {st : Option FuncIdx} (h : prepare? ev s m xas = some (c, st)) :
    c.code =
      expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
      expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d) := by
  unfold prepare? at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · cases h; rfl
  · cases h

variable {P : Profile} {host : HostSemantics H}

theorem Steps.append_suffix {s s' : Store H} {f f' : Frame} {is r : List Admin}
    (h : Steps P host ⟨s, f, is⟩ ⟨s', f', []⟩) :
    Steps P host ⟨s, f, is ++ r⟩ ⟨s', f', r⟩ := by
  have := Steps.ctxtInstrs (vs := []) (rest := r) h
  simpa only [vals, List.map_nil, List.nil_append] using this

theorem Steps.withStart {c : Config H} {s' : Store H} {f' : Frame} {st : Option FuncIdx}
    (h : Steps P host c ⟨s', f', []⟩) :
    Steps P host (c.withStart st) ((⟨s', f', []⟩ : Config H).withStart st) := by
  rcases c with ⟨s, f, is⟩
  cases st with
  | none => exact h
  | some x => simpa [Config.withStart] using Steps.append_suffix (r := [.plain (.call x)]) h

theorem instantiateInit?_sound {s : Store H} {m : Module} {xas : List ExternAddr}
    {c' : Config H}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : instantiateInit? s m xas = some c') :
    ∃ c₀, Instantiate P host s m xas c₀ ∧ Steps P host c₀ c' := by
  unfold instantiateInit? at h
  split at h
  · cases h
  · rename_i c st hp
    split at h
    · cases h
    · rename_i s' f' hi
      cases h
      refine ⟨c.withStart st, (prepare?_sound evalConst?_evalSound hp hvalid).2, ?_⟩
      have hs := initSegments?_steps (P := P) (host := host) evalConst?_evalSound hi
      rw [← prepare?_code hp] at hs
      exact Steps.withStart hs

/-! ## Examples -/

section Examples

/-- One immutable i32 global initialised to 42; no segments. -/
def oneGlobalModule : Module :=
  { globals := [⟨⟨.const, .num (.int .i32)⟩, [.intConst .i32 42]⟩] }

example : (instantiateInit? ({} : Store Empty) oneGlobalModule []).isSome = true := by
  decide

example : (instantiateInit? ({} : Store Empty) ({} : Module) []).isSome = true := by
  decide

end Examples

end Silmaril.Wasm.Execution.Core
