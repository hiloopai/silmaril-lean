module

public import Silmaril.Project.WasmComponents.Kernel.Framing.Defs
public import Silmaril.Raw.Project.WasmComponents.Kernel.Framing

/-!
# Kernel decoders: the list framing is the framing

**PROVED** (the case analyses of the cursor parsers are in
`Silmaril.Raw.Project.WasmComponents.Kernel.Framing`):

* `uAux_of_uAuxL`: a successful `uAuxL` on the window `bs[i:s]` is the run of `uAux` there;
* `coreSectionsFrom_of_framesL`, hence `coreSections_eq_fast`;
* `name_of_nameL`, hence `name_eq_fast`;
* `extract_eq_sliceOf`: `ByteArray.extract` is the list slice `sliceOf`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Parse.ByteParse (Parser Res)
open Silmaril.Wasm.Wit.Binary

/-- **`coreSections` is its list form.** -/
theorem coreSections_eq_fast (b : ByteArray) : coreSections b = coreSectionsFast b := by
  unfold coreSectionsFast
  split
  · rename_i hc
    split
    · rename_i t ht
      unfold coreSections
      have : ((b.extract 0 8).data.toList == coreHeader) = true := by
        rw [extract_eq_sliceOf]
        simp only [sliceOf, List.drop_zero, Nat.sub_zero, hc.2, beq_self_eq_true]
      rw [ite_eq_left this]
      exact coreSectionsFrom_of_framesL hc.1 ht
    · rfl
  · rfl

/-- **`name` is its list form.** -/
theorem name_eq_fast (b : ByteArray) (s i : Nat) :
    Silmaril.Parse.ByteParse.name b s i = nameFast b s i := by
  unfold nameFast
  split
  · rename_i hc
    split
    · rename_i str k hk
      exact name_of_nameL hc.1 hc.2 hk
    · rfl
  · rfl

end Silmaril.Project.WasmComponents.Kernel

end
