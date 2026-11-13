module

public import Silmaril.Wasm.LimeCompile.DataDrop.Defs

/-!
# The container with `data.drop`: the compiled module

What the rewrite does to `memory.init 0 y` and `data.drop y`, that it keeps sequence lengths,
and how many functions the output has.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.DataDrop

open Silmaril.Wasm Silmaril.Wasm.LimeCompile.DataDrop
open Silmaril.Wasm.LimeCompile.PassiveData (idx)

theorem rwI_memoryInit (m : Module) (y : DataIdx) :
    rwI m (.memoryInit (idx 0) y) = .call (idx (wrapIdx m y.toNat)) := by
  rw [rwI]
  rfl

theorem rwI_dataDrop (m : Module) (y : DataIdx) :
    rwI m (.dataDrop y) = .call (idx (dropIdx m y.toNat)) := by
  rw [rwI]

theorem rwL_length (m : Module) : ∀ l : List Instr, (rwL m l).length = l.length
  | [] => by rw [rwL]
  | _ :: l => by rw [rwL, List.length_cons, List.length_cons, rwL_length m l]

theorem segs_length (m : Module) : (segs m).length = m.data.length := by
  simp [segs]

theorem emuModule_funcs_length (m : Module) :
    (emuModule m).funcs.length = m.funcs.length + 4 * m.data.length := by
  simp only [emuModule, List.length_append, List.length_map, segs_length]
  omega

end Silmaril.Proofs.Wasm.LimeCompile.DataDrop
