module

public import Silmaril.Wasm.Wac.Lower.Defs
public import Silmaril.Wasm.Wac.Bridge.Encode.Defs

/-!
# WAC: embedding the packages of a composition (`wac compose` without `--import-dependencies`)

`Bridge.encode` writes a composition the way `wac compose --import-dependencies` does: every
package it instantiates is an import `unlocked-dep=<ns:name>` of a component (`depName`). The
default of `wac compose` (`define_components = true`) instead *defines* each package in the
composition, as a nested `(component …)` holding the package's own component, so the result
runs on its own.

`embed ps c` does this on the component `c`: an import section `(import "n" (component …))`
whose name `n` is in the table `ps` (import name ↦ the package's component) becomes the
section `(component d)`. Both allocate exactly one component index and nothing else, so every
index space of `c` is unchanged (`Silmaril.Wasm.Wac.Embed.Thms`: `allocs_embed`), the result is
still in the composition profile (`isProfile_embed`) and it lowers to the same composition
graph (`graph_embed`). The type that typed the import stays, unused.

Differences from wac (tested, see `docs/projects/wasm-components.md`): wac does not write the type of
an embedded package and places the `(component …)` where the import was; the composition
therefore has a few more type definitions than wac's, which are never referred to.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Embed

open Silmaril.Wasm.Component.Binary

/-- The table of a composition's packages: the import name of the package (`Bridge.depName`)
and its component. -/
abbrev PkgTable := List (String × Ast)

/-- The table of packages by key (`ns:name` or `ns:name@version`). -/
def table (ps : List (String × Ast)) : PkgTable := ps.map fun p => (Bridge.depName p.1, p.2)

/-- One section: an import of a package in the table becomes its definition. -/
def embedSec (ps : PkgTable) : Section → Section
  | .imports [⟨n, .component t⟩] =>
    match ps.lookup n.name with
    | some d => .component d
    | none => .imports [⟨n, .component t⟩]
  | s => s

/-- **Embed the packages of a composition.** -/
def embed (ps : PkgTable) (c : Ast) : Ast := .mk (c.sections.map (embedSec ps))

/-- The index spaces a section allocates in: the sorts of its items, in order. -/
def secAllocs : Section → List ItemSort
  | .component _ => [.component]
  | .imports xs => xs.map fun i => match i.desc with
    | .coreModule _ => .core .module
    | .func _ => .func
    | .value _ => .value
    | .type _ => .type
    | .instance _ => .instance
    | .component _ => .component
  | .instances xs => xs.map fun _ => .instance
  | .aliases xs => xs.map (·.sort)
  | .exports xs => xs.map (·.item.sort)
  | .types xs => xs.map fun _ => .type
  | _ => []

/-- The index spaces a component allocates in, in order. -/
def allocs (c : Ast) : List ItemSort := c.sections.flatMap secAllocs

/-- The package imports of a component that the table does not define. -/
def unembedded (ps : PkgTable) (c : Ast) : List String :=
  c.sections.filterMap fun
    | .imports [⟨n, .component _⟩] => if (ps.lookup n.name).isNone then some n.name else none
    | _ => none

end Silmaril.Wasm.Wac.Embed
