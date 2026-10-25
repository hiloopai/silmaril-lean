module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Family

@[expose] public section

/-! # Memory-step transport between frames with unchanged memory/data addresses -/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- Memory steps inspect the module's memory and data addresses, never its
function/global addresses or local values. -/
theorem memoryStep_frame {S : Store H} {f f' : Frame} {l : List Admin} {c : Config H}
    (hm : f.module.mems = f'.module.mems) (hd : f.module.datas = f'.module.datas)
    (h : MemoryStep P ⟨S, f, l⟩ c) :
    MemoryStep P ⟨S, f', l⟩ ⟨c.store, f', c.code⟩ := by
  cases h <;> constructor <;>
    first | assumption | (simp_all only [Store.mem?, Store.data?] <;> rfl)

/-- Each memory reduction emits only memory instructions, constants and traps,
which are identical on both sides of the function/global renaming. -/
theorem memoryStep_code {X : SimCtx} {m : Mode} {c c' : Config H}
    (h : MemoryStep P c c') (hl : ∀ a ∈ c.code, flatF X.n0 a) : CodeR X m c'.code c'.code := by
  cases m <;> cases h <;>
    simp only [aconst, constI32, load8u, store8] <;>
    repeat' first
    | apply CodeR.cons
    | exact CodeR.nil
    | exact ARel.plainS
    | exact ARel.plainO (.simple rfl)
    | exact ARel.trap
    | exact ARel.val ((flatF_toAdmin _ _).mp (hl _ (by simp)))

/-- Related frames retain the same memory addresses. -/
theorem FrameRel.mems {X : SimCtx} (hX : X.WF) {m : Mode} {f f' : Frame}
    (h : FrameRel X m f f') : f.module.mems = f'.module.mems := by
  cases m
  · rw [h.1]
  · rw [h.1, h.2.1]; exact hX.mems

/-- Related frames retain the same data addresses. -/
theorem FrameRel.datas {X : SimCtx} (hX : X.WF) {m : Mode} {f f' : Frame}
    (h : FrameRel X m f f') : f.module.datas = f'.module.datas := by
  cases m
  · rw [h.1]
  · rw [h.1, h.2.1]; exact hX.datas

end Silmaril.Wasm.Binaryen.RUMESim
