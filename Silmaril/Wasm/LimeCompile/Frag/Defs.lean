module

public import Silmaril.Wasm.LimeCompile.Direct.Defs
public import Silmaril.Wasm.Lime1.Validation.Modules
public import Silmaril.Wasm.Validation.Modules

/-!
# The 3.0 → Lime compiler, a fragment without a Lime1 validity hypothesis

an earlier container fragment `Container.Frag m` asks for a valid source *and* a valid Lime1
module `L` with `L.toCore = selM m`. The second half is a validity-transfer hypothesis: it is
not checked by the compiler, and nothing derived it from the source's validity. This topic
replaces it by a syntactic condition on the source:

* **`NumFrag m`**: `m` is a valid Core module, and its direct lowering
  (`Direct.lowerModule`: typed `select`s at number types become the untyped `select`) is the
  Core image of a Lime1 module `L`. Every typed `select` of `m` is then at number types, so the
  lowering keeps validity (`Direct.lowerModule_valid`) and erases every annotation;
* `Task.lime1ValidOfCore` (**open, frozen**): Lime1 validation reflects Core validation of the
  image, `ModuleOk L.toCore mt → Lime1.Validation.ModuleValid L`. Only the converse
  (`Lime1.Validation.ModuleValid.toCore`) is proved in silmaril-lean; results that need this
  direction (`NumFrag ⊆ Container.Frag`) are stated conditionally in `Thms`. It is not
  verified that the statement holds at every edge (limits, alignment, segment modes).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Frag

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.Direct (lowerModule)

/-- **The pass-2 fragment**: valid Core modules whose numeric-`select` lowering is a Lime1
image. No Lime1 validity is assumed. -/
def NumFrag (m : Module) : Prop :=
  (∃ mt, ModuleOk m mt) ∧ ∃ L : Lime1.Module, L.toCore = lowerModule m

/-- **Open target (frozen)**: Lime1 validation reflects Core validation of the Core image. -/
def Task.lime1ValidOfCore : Prop :=
  ∀ L : Lime1.Module, (∃ mt, ModuleOk L.toCore mt) → Lime1.Validation.ModuleValid L

end Silmaril.Wasm.LimeCompile.Frag
