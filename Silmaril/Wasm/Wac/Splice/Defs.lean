module

public import Silmaril.Wasm.Wac.Embed.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs

/-!
# WAC: embedding packages at the byte level

`Embed.embed` defines each package inside the composition as a component *AST*, so the package
must be one the component binary AST of `Silmaril.Wasm.Component.Binary` can hold. Packages that
use what that AST lacks (the async canonical built-ins `task.return`, `stream.*`,
`waitable-set.*`, …) cannot be parsed into it. `splice raw c` embeds them anyway: it encodes
`c` section by section, as `Encode.ast`, but writes an import of a package whose bytes `r` are
in `raw` as the component section `0x04 size r`, copying the package's bytes unchanged.

`Silmaril.Wasm.Wac.Splice.Thms` (`splice_eq_embed`): when every package's bytes are the encoding of
an AST of the table (the canonical encodings, which `Encode.ast` writes), `splice raw c` is
`Encode.ast (Embed.embed tbl c)`, so it parses back to the embedded composition
(`parse_splice`). Without that hypothesis the bytes are still the frame
`preamble ++ section₁ ++ …` with each package import replaced by the package's own bytes, by
definition.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Splice

open Silmaril.Wasm.Component.Binary
open Silmaril.Parse.ByteParse (Bytes)

/-- The packages' bytes, by import name. -/
abbrev RawTable := List (String × ByteArray)

/-- The bytes of packages by key, by import name (`Bridge.depName`). -/
def table (ps : List (String × ByteArray)) : RawTable := ps.map fun p => (Bridge.depName p.1, p.2)

/-- One section: a package import with bytes in the table is the component section of the
bytes; any other section is encoded. -/
def rawSec (raw : RawTable) : Section → Option Bytes
  | .imports [⟨n, .component t⟩] =>
    match raw.lookup n.name with
    | some r => do
      let s ← Silmaril.Parse.ByteParse.Enc.sized r.data.toList
      pure (0x04 :: s)
    | none => Encode.section_ (.imports [⟨n, .component t⟩])
  | s => Encode.section_ s

/-- The sections. -/
def rawSecs (raw : RawTable) : List Section → Option Bytes
  | [] => some []
  | s :: ss => do
    let a ← rawSec raw s
    let b ← rawSecs raw ss
    pure (a ++ b)

/-- **A composition with its packages' bytes embedded.** -/
def splice (raw : RawTable) (c : Ast) : Option ByteArray :=
  (rawSecs raw c.sections).map fun b => ⟨(preambleBytes ++ b).toArray⟩

/-- The table of ASTs agrees with the table of bytes: the same names, and each AST encodes to
its bytes. -/
def Agrees (tbl : Embed.PkgTable) (raw : RawTable) : Prop :=
  ∀ n, (tbl.lookup n).bind Encode.ast = (raw.lookup n).map (·.data.toList) ∧
    ((tbl.lookup n).isSome ↔ (raw.lookup n).isSome)

end Silmaril.Wasm.Wac.Splice
