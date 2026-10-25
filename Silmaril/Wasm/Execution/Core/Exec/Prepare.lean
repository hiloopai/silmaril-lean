module

public import Silmaril.Wasm.Execution.Core.Exec.Instantiate

@[expose] public section

/-! # Computable preparation (instantiation without running start) for Core 3.0

`prepare?` performs allocation and builds the element/data segment-initialisation
code, returning the start function index separately instead of appending
`call start`. This is what the component engine needs. It is parametrised over a
constant-expression evaluator `ev`, exactly like `instantiate?`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Append `call x` for a start function, if any. -/
def Config.withStart (c : Config H) : Option FuncIdx → Config H
  | some x => { c with code := c.code ++ [.plain (.call x)] }
  | none => c

section
variable (ev : Store H → Frame → Expr → Option (Store H × Val))

/-- Computable preparation: allocation plus segment initialisation code, with the
start function returned rather than appended. -/
def prepare? (s : Store H) (m : Module) (xas : List ExternAddr) :
    Option (Config H × Option FuncIdx) :=
  if m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32) then
    match evalGlobals? ev s ⟨[], ModuleInst.initial s m xas⟩
        (m.globals.map fun g => ⟨g.type.mutability,
          (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩)
        (m.globals.map Global.init) with
    | none => none
    | some (s₁, f₁, valsG) =>
      match evalExprs? ev s₁ f₁ (m.tables.map Table.init) with
      | none => none
      | some (s₂, f₂, refsT) =>
        match evalExprss? ev s₂ f₂ (m.elems.map Elem.init) with
        | none => none
        | some (s₃, _, refsE) =>
          match allocModule? s₃ m xas valsG refsT refsE with
          | none => none
          | some (s₄, mi) =>
            some (⟨s₄, { module := mi },
              expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
              expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d)⟩,
              m.start)
  else none

end

variable {ev : Store H → Frame → Expr → Option (Store H × Val)}

theorem prepare?_start {s : Store H} {m : Module} {xas : List ExternAddr}
    {c : Config H} {st : Option FuncIdx} (h : prepare? ev s m xas = some (c, st)) :
    st = m.start := by
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

theorem prepare?_instantiate? (s : Store H) (m : Module) (xas : List ExternAddr) :
    instantiate? ev s m xas = (prepare? ev s m xas).map fun p => p.1.withStart p.2 := by
  unfold instantiate? prepare?
  split
  · rcases hG : evalGlobals? ev s _ _ _ with _ | ⟨s₁, f₁, valsG⟩
    · rfl
    · simp only []
      rcases hT : evalExprs? ev s₁ f₁ _ with _ | ⟨s₂, f₂, refsT⟩
      · rfl
      · simp only []
        rcases hE : evalExprss? ev s₂ f₂ _ with _ | ⟨s₃, f₃, refsE⟩
        · rfl
        · simp only []
          rcases hM : allocModule? s₃ m xas valsG refsT refsE with _ | ⟨s₄, mi⟩
          · rfl
          · simp only [Option.map]
            cases m.start <;> simp [Config.withStart]
  · rfl

theorem prepare?_sound {P : Profile} {host : HostSemantics H} (hev : EvalSound P host ev)
    {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H} {st : Option FuncIdx}
    (h : prepare? ev s m xas = some (c, st))
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    st = m.start ∧ Instantiate P host s m xas (c.withStart st) := by
  refine ⟨prepare?_start h, instantiate?_sound hev ?_ hvalid⟩
  rw [prepare?_instantiate?, h]; rfl

end Silmaril.Wasm.Execution.Core
