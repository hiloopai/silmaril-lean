module

public import Silmaril.Wasm.JcoTool.Helpers.Defs
public import Silmaril.Wasm.JcoTool.ToolI.Thms
public import Silmaril.Wasm.JcoTool.LimeFull.Thms
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Perf.CoreDecode.Thms

/-!
# The helper modules of `wasm-jco new` are what they should be

* `helperOk_spec`: a helper that passes the check **encodes**, in silmaril's Core binary
  grammar (`Encodes`, unambiguous: `Silmaril.Wasm.Binary.Core.functional`), a module that is a
  shim (`isShim`) or a fixup (`isFixup`) as specified in `Helpers.Defs`.
* **`newFullV_correct`**: the output of `wasm-jco new` (thin wrapper, every world) is that of
  `newFull`, so `ToolI.newFull_correct` applies, and every helper core module of it (the core
  modules after the input) encodes a shim or a fixup. `newLimeFullV_correct`: the same for
  `--lime`, with `newLimeFull_correct`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Helpers

theorem helperOk_spec {b : ByteArray} (h : helperOk b = true) :
    ∃ m, Silmaril.Wasm.Binary.Core.decode? b = some m ∧
      Silmaril.Wasm.Binary.Core.Encodes b.data.toList m ∧ (isShim m = true ∨ isFixup m = true) := by
  unfold helperOk at h
  rw [Silmaril.Wasm.Perf.CoreDecode.decodeF_eq] at h
  split at h
  · rename_i m hm
    exact ⟨m, hm, Silmaril.Wasm.Binary.Core.decode?_sound hm, by simpa using h⟩
  · cases h

theorem helpersOk_spec {o : Tool.Out} (h : helpersOk o = true) :
    ∀ b ∈ o.cores.drop 1, ∃ m, Silmaril.Wasm.Binary.Core.decode? b = some m ∧
      Silmaril.Wasm.Binary.Core.Encodes b.data.toList m ∧ (isShim m = true ∨ isFixup m = true) :=
  fun b hb => helperOk_spec (List.all_eq_true.mp h b hb)

end Silmaril.Wasm.JcoTool.Helpers

namespace Silmaril.Wasm.JcoTool.ToolV

open Silmaril.Wasm.Wit.Binary (WorldFull)
open New (bind_ok require_ok)
open Helpers

/-- What the checked entry points add to an output of the unchecked ones. -/
def Checked (o o' : Tool.Out) : Prop :=
  o.bytes = o'.bytes ∧ o.ast = o'.ast ∧ o.ir = o'.ir ∧ o.cores = o'.cores ∧
    ∀ b ∈ o.cores.drop 1, ∃ m, Silmaril.Wasm.Binary.Core.decode? b = some m ∧
      Silmaril.Wasm.Binary.Core.Encodes b.data.toList m ∧ (isShim m = true ∨ isFixup m = true)

/-- **The correctness theorem of `wasm-jco new`** with the helper modules checked. -/
theorem newFullV_correct {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : newFullV core wf = .ok o) :
    ∃ o', ToolI.newFull core wf = .ok o' ∧ Checked o o' ∧
      ((ToolI.inOld wf.world = true ∧ Tool.newWith core wf.world = .ok o') ∨
        (ToolI.inOld wf.world = false ∧ ToolI.NewIOk core wf o')) := by
  obtain ⟨o', ho, h₁⟩ := bind_ok h
  obtain ⟨_, hq, h₂⟩ := bind_ok h₁
  cases h₂
  exact ⟨o', ho, ⟨rfl, rfl, rfl, rfl, helpersOk_spec (require_ok hq)⟩, ToolI.newFull_correct ho⟩

/-- **`wasm-jco new --lime`** with the helper modules checked. -/
theorem newLimeFullV_correct {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : newLimeFullV core wf = .ok o) :
    ∃ o', ToolI.newLimeFull core wf = .ok o' ∧ Checked o o' := by
  obtain ⟨o', ho, h₁⟩ := bind_ok h
  obtain ⟨_, hq, h₂⟩ := bind_ok h₁
  cases h₂
  exact ⟨o', ho, rfl, rfl, rfl, rfl, helpersOk_spec (require_ok hq)⟩

end Silmaril.Wasm.JcoTool.ToolV
