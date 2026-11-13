module

public import Silmaril.Wasm.Component.FXRes.Example.Defs

/-!
# Continuations as Component Model resources: the example run (proofs)

`example_run`: the four steps of the example (`cont.new`, `new`, `take`, `resume`) as a joint
run, with its table and store histories.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.Example

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Resource Silmaril.Wasm.Component.FXRes
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

theorem step_contNew {s : Store H} {f : Frame} {a : ℕ} {fi : FuncInst H} {ct : TypeIdx}
    (hf : s.funcs[a]? = some fi) :
    JStep P host fx (start s f a ct) [] [.alloc 0]
      ⟨Table.empty, ⟨s, [some (contOf a fi)], f, [.contRef 0, .fx (.resume ct [])]⟩⟩ :=
  .fx (StepFX'.seq (vs := []) (rest := [.fx (.resume ct [])])
      (es := [.core (.ref (.func a)), .fx (.contNew ct)]) (.contNew hf)
      (.inr (List.cons_ne_nil _ _)))
    (.alloc [] (contOf a fi))

theorem step_new {s : Store H} {f : Frame} {a : ℕ} {fi : FuncInst H} {ct : TypeIdx} :
    JStep P host fx
      ⟨Table.empty, ⟨s, [some (contOf a fi)], f, [.contRef 0, .fx (.resume ct [])]⟩⟩
      [.added 1 (contOf a fi)] [.free 0]
      ⟨tab₁ (contOf a fi), ⟨s, [none], f, [handleVal 1, .fx (.resume ct [])]⟩⟩ :=
  .op (RStep.new (k := 0) rfl rfl)

theorem step_take {s : Store H} {f : Frame} {a : ℕ} {fi : FuncInst H} {ct : TypeIdx} :
    JStep P host fx
      ⟨tab₁ (contOf a fi), ⟨s, [none], f, [handleVal 1, .fx (.resume ct [])]⟩⟩
      [.removed 1 (contOf a fi)] [.alloc 1]
      ⟨tab₂, ⟨s, [none, some (contOf a fi)], f, [.contRef 1, .fx (.resume ct [])]⟩⟩ :=
  .op (RStep.take (b := BitVec.ofNat 32 1) rfl)

theorem step_resume {s : Store H} {f : Frame} {a : ℕ} {fi : FuncInst H} {ct : TypeIdx} :
    JStep P host fx
      ⟨tab₂, ⟨s, [none, some (contOf a fi)], f, [.contRef 1, .fx (.resume ct [])]⟩⟩
      [] [.free 1] (finish s f a fi) :=
  .fx (StepFX'.resume (P := P) (host := host) (fx := fx) (s := s)
      (K := [none, some (contOf a fi)]) (f := f) (vs := []) (k := 1) (C := contOf a fi) (ct := ct)
      (hs := []) (hs' := []) rfl rfl)
    (.consume (k := 1) rfl)

/-- **The example run.** -/
theorem example_run {s : Store H} {f : Frame} {a : ℕ} {fi : FuncInst H} {ct : TypeIdx}
    (hf : s.funcs[a]? = some fi) :
    JSteps P host fx (start s f a ct) [.added 1 (contOf a fi), .removed 1 (contOf a fi)]
      [.alloc 0, .free 0, .alloc 1, .free 1] (finish s f a fi) :=
  .cons (step_contNew hf) (.cons step_new (.cons step_take (.cons step_resume (.refl _))))

end Silmaril.Wasm.Component.FXRes.Example
