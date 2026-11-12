module

public import Silmaril.Wasm.Jco.Resource.Example.Thms
public import Silmaril.Wasm.Jco.Resource.Handle.Thms

/-!
# The litmus world with a resource, handle-passing

For the litmus instance `exRInst` and world `exMdR` of `Silmaril.Wasm.Jco.Resource.Example`:

* `exR_recognizeThinR`: the thin-wrapper recognizer accepts the world (no world function is
  named `cabi_realloc`);
* `exR_thinR_fuseR`: the thin wrapper of the fused handle-passing module `fuseR exRInst exMdR`
  is `wrapR exMdR`, for every table implementation;
* `exR_thinR`: hence it simulates the rep-passing convention from the empty canonical table,
  with no remaining hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res.Example

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Component.Runtime (Table)

theorem exR_names : exMdR.world.all (·.name != fuseReallocName) = true := by decide

theorem exR_recognizeThinR : recognizeThinR exMdR = some (thinR exMdR fuseReallocName) := by
  simp only [recognizeThinR, exR_names, ↓reduceIte]

theorem exR_thinR_fuseR (H : HTab) :
    (thinR exMdR fuseReallocName).callExportH (fuseR exRInst exMdR) H =
      (wrapR exMdR).callExport exRInst H :=
  thinR_fuseR exRInst H exMdR exR_names

/-- The fused module's thin wrapper for the litmus world, from the empty canonical table. -/
theorem exR_thinR (name : String) (vs : List RVal) :
    Sim ((thinR exMdR fuseReallocName).callExportH (fuseR exRInst exMdR) refTab name vs)
      (exMdR.spec exRInst name vs) Silmaril.Wasm.Component.Runtime.Table.empty fun a b t' => a = b ∧ refTab.Same Silmaril.Wasm.Component.Runtime.Table.empty t' :=
  thinR_fuseR_correct exRInst refTab refTab_lawful exMdR exR_names exR_conforms name vs empty_inv
    (exR_room name)

end Silmaril.Wasm.Jco.Res.Example
