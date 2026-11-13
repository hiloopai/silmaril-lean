module

public import Silmaril.Wasi.Versions.WitImport.Defs

@[expose] public section

/-!
# Selecting the interfaces of a package

`importPkg` (`Silmaril.Wasi.Versions.WitImport`) elaborates every item of the listed files. A
world file such as `http/worlds.wit` of WASI 0.3.2 also holds the worlds `service` and
`middleware`, which `include` `wasi:clocks/imports` and `wasi:random/imports` and import
`wasi:cli` interfaces: elaborating them needs all of WASI 0.3. The interfaces `client` and
`handler` of the same file only `use` `wasi:http/types`.

`importIfaces fs` is `importPkg fs` with the worlds dropped from every package before the front
end elaborates (`dropWorlds`): only the interfaces (and top-level `use`s) are elaborated. This
selection is part of the unverified glue (as `mergeDocs`): it is a filter on the parsed
`Package.items`; the verified parser and elaborator run unchanged on the rest.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- An item that is not a world. -/
def notWorld : PackageItem → Bool
  | .world _ => false
  | _ => true

/-- The package without its worlds. -/
def dropWorlds (p : Package) : Package := { p with items := p.items.filter notWorld }

/-- **The importer on interfaces only**: as `importPkg`, with the worlds of every listed
package dropped before elaboration. -/
def importIfaces (fs : List Src) : Except String Binary.Package := do
  let ds ← fs.mapM parseSrc
  let U := (mergeDocs ds).map dropWorlds
  let P ← U.head?.elim (.error "no package") pure
  let (B, _) ← Elab.elaborate U P.name []
  pure B

end Silmaril.Wasi.Versions.WitImport
