module

public import Silmaril.Wasm.Wac.Splice.Defs
public import Silmaril.Wasm.Component.BinaryAsync.Defs

/-!
# WAC: embedding packages with the async built-ins

`Splice.splice raw c` copies each package's bytes into the composition `c` unchanged
(`wasm-wac compose --wasm`, `Emit.composeWasmRaw`). `Splice.parse_splice` reads the result back
only when every package is a component of the *base* binary AST, so not for stream components,
whose core functions come from the async built-ins (`stream.read`, `task.return`, …).

This module states embedding over the extended AST of `Silmaril.Wasm.Component.BinaryAsync`
(`AstX`, with every `canon` built-in of `Binary.md` that wasm-tools 1.262.0 reads):

* `embedSecX tbl s`, `embedX tbl c`: the base composition `c` as an extended component, with
  each package import `unlocked-dep=<pkg>` whose package is in `tbl` replaced by the section
  `(component d)` of its extended AST `d`;
* `AgreesX tbl raw`: the table of extended ASTs and the table of bytes have the same names, and
  each AST encodes (`EncodeX.ast`) to its bytes;
* `canonTable raw`: the check the tool runs: parse each package's bytes with `parseX` and
  re-encode; it succeeds exactly when every package's bytes are the canonical encoding of what
  they parse to, and then `AgreesX` holds for the table it returns (`canonTable_agrees`);
* `pkgSrcs c`, `pkgsOf a`: the components of a composition in index order (the variables of
  its composition graph, `Lower.graph`): a package import by name, a definition, or an alias.

Theorems in `Silmaril.Wasm.Wac.SpliceX.Thms`: `splice_eq_embedX`, `parseX_splice` (the spliced
bytes parse back to `embedX tbl c` with `parseX`), `erase_embedX` (erasing the built-ins gives
`Embed.embed` of the erased packages), `graph_embedX` (it lowers to the graph of `c`),
`pkgsOf_embedX` (the `k`-th component of the result is the package of the `k`-th package
import of `c`, looked up in `tbl`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.SpliceX

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.BinaryAsync

/-- The packages of a composition as extended ASTs, by import name. -/
abbrev PkgTableX := List (String × AstX)

/-- One section: an import of a package in the table becomes its definition; every other
section is the same base section. -/
def embedSecX (ps : PkgTableX) : Section → SectionX
  | .imports [⟨n, .component t⟩] =>
    match ps.lookup n.name with
    | some d => .component d
    | none => SectionX.ofSection (.imports [⟨n, .component t⟩])
  | s => SectionX.ofSection s

/-- **Embed packages with the async built-ins** into a composition. -/
def embedX (ps : PkgTableX) (c : Ast) : AstX := .mk (c.sections.map (embedSecX ps))

/-- The table of extended ASTs agrees with the table of bytes. -/
def AgreesX (tbl : PkgTableX) (raw : Splice.RawTable) : Prop :=
  ∀ n, (tbl.lookup n).bind EncodeX.ast = (raw.lookup n).map (·.data.toList) ∧
    ((tbl.lookup n).isSome ↔ (raw.lookup n).isSome)

/-- One package: its bytes parse (`parseX`) to an AST that re-encodes to the same bytes. -/
def canonPkg (p : String × ByteArray) : Option (String × AstX) :=
  match parseX p.2 with
  | .ok a => if EncodeX.ast a = some p.2.data.toList then some (p.1, a) else none
  | .error _ => none

/-- **The canonicity check**: every package's bytes are the canonical encoding of an extended
AST; the table of those ASTs. -/
def canonTable (raw : Splice.RawTable) : Option PkgTableX := raw.mapM canonPkg

/-! ## The components of a composition, in index order -/

/-- Where a component index of a composition comes from. -/
inductive PkgSrc where
  /-- An imported component (a package of the composition when its name is in the table). -/
  | named (n : String)
  /-- A component defined in the composition. -/
  | inline (d : Ast)
  /-- A component alias, or an imported component in a section `embed` does not rewrite (an
  import section with several items). -/
  | other
  deriving Inhabited

/-- The component indices a base section allocates, in order, other than a package import. -/
def otherSrcs : Section → List PkgSrc
  | .component d => [.inline d]
  | .imports xs => xs.filterMap fun i => match i.desc with
    | .component _ => some .other
    | _ => none
  | .aliases xs => xs.filterMap fun a => if a.sort = .component then some .other else none
  | _ => []

/-- The component indices a base section allocates, in order: a package import (an import
section of one component, as `Bridge.encode` writes it) is named. -/
def secSrcs : Section → List PkgSrc
  | .imports [⟨n, .component _⟩] => [.named n.name]
  | s => otherSrcs s

/-- The component indices of a composition, in order. -/
def pkgSrcs (c : Ast) : List PkgSrc := c.sections.flatMap secSrcs

/-- The components of an extended section, in index order (`none`: imported or aliased). -/
def secPkgsX : SectionX → List (Option AstX)
  | .component d => [some d]
  | .imports xs => xs.filterMap fun i => match i.desc with
    | .component _ => some none
    | _ => none
  | .aliases xs => xs.filterMap fun a => if a.sort = .component then some none else none
  | _ => []

/-- **The components of an extended composition**, in index order: `some d` for a component
defined in it (an embedded package), `none` for an imported or aliased one. -/
def pkgsOf (a : AstX) : List (Option AstX) := a.sections.flatMap secPkgsX

/-- What a component index of `c` becomes after embedding the table. -/
def PkgSrc.resolve (tbl : PkgTableX) : PkgSrc → Option AstX
  | .named n => tbl.lookup n
  | .inline d => some (AstX.ofAst d)
  | .other => none

end Silmaril.Wasm.Wac.SpliceX
