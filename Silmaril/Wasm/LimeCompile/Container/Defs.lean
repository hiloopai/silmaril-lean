module

public import Silmaril.Wasm.LimeCompile.Select.Defs
public import Silmaril.Wasm.Lime1.ToCore
public import Silmaril.Wasm.Lime1.Validation.Modules

/-!
# The 3.0 → Lime container compiler: definitions

The **container** approach compiles a Wasm 3.0 module `M` (silmaril-lean Core syntax) to a Lime1
module `C(M)` that hosts `M` behind the same export API. In this first pass the fragment is the
smallest one with a 3.0 feature Lime1 lacks: **Lime1 plus the typed `select`** (`select (t)`,
from 2.0's reference-types proposal; Lime1 has multi-value, so "Lime + multi-value" is Lime
itself). The host needed for that feature is empty: the typed `select` is compiled to the untyped
one, and the result is read back as Lime1 syntax.

* `compile M := Lime1.Module.ofCore? (selM M)`: erase the `select` annotations of the function
  bodies (`Select.selM`), then take silmaril-lean's retraction of the canonical Lime1 image
  (`Lime1.Module.ofCore?`, which rejects everything outside Lime1 syntax);
* `Frag M`: the documented fragment: `M` is a valid Core module, and erasing its `select`
  annotations gives the Core image (`Lime1.Module.toCore`, the module map of `lime1Emb`) of a
  valid Lime1 module;
* `resultsOf rt`: the results of a recursive group made of one function type (used to state
  which APIs the fragment cannot have).

The fragment is stated as an image, not by a syntactic check: membership amounts to
`compile M = some L` together with `L.toCore = selM M` (`Thms`), and the second conjunct is the
one that rules out non-canonical spellings, e.g. a `(ref func)` element segment, which
`ofCore?` reads back but `toCore` respells as `funcref`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Container

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.Select (selM)

/-- **The container compiler** (Lime1 plus the typed `select`). -/
def compile (m : Module) : Option Lime1.Module := Lime1.Module.ofCore? (selM m)

/-- **The fragment** : valid Core modules that are, up to `select` annotations, the
Core image of a valid Lime1 module. -/
def Frag (m : Module) : Prop :=
  (∃ mt, ModuleOk m mt) ∧ ∃ L : Lime1.Module, Lime1.Validation.ModuleValid L ∧ L.toCore = selM m

/-- The results of a recursive group made of one function type. -/
def resultsOf (rt : RecType) : Option (List ValType) :=
  match rt.types with
  | [⟨_, _, .func ft⟩] => some ft.results
  | _ => none

end Silmaril.Wasm.LimeCompile.Container
