module

public import Silmaril.Project.Defs
public import Silmaril.Project.Formats.Wasm.Defs
public import Silmaril.Wasm.Wit.Project.Ext.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Wit.Tool.Source.Defs

/-!
# The Wasm components pilot: problems about registered binaries

Problems over Wasm modules and components registered by `mor project components add`
(`docs/projects/wasm-wasi.md`).

| problem | statement |
|---|---|
| `silmaril.wasm_components.same_world` | `SameWorld X Y`: `X` and `Y` decode and project to one world |
| `silmaril.wasm_components.same_code` | `SameCode X Y`: the files have the same non-custom sections |
| `silmaril.wasm_components.reencodes_to` | `ReencodesTo X Y`: `wasm-wit encode` of `X` is the file of `Y` |
| `silmaril.wasm_components.distinct` | `Distinct X Y`: the files differ (different digests) |

These are the pilot's problems that no standard shape covers: statements about files (bytes)
and the evidence behind a behavioural equality. Validity, worlds and behaviour are rows of the
standard shapes `silmaril.shapes.component.*` (`Silmaril.Project.WasmComponents.Thms`).

`worldBytes?` is the world file `wasm-wit project … -o OUT.wasm` writes:
`Wit.Tool.projectBytesX` (the verified parser, then the projection), encoded as
`Wit.Tool.worldAst`.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents

open Silmaril.Project (Value)

/-- The world file of a component, as `wasm-wit project IN.wasm -o OUT.wasm` writes it. -/
def worldBytes? (b : ByteArray) : Option ByteArray :=
  match Silmaril.Wasm.Wit.Tool.projectBytesX b with
  | .ok w => Silmaril.Wasm.Component.Binary.encode (Silmaril.Wasm.Wit.Tool.worldAst w)
  | .error _ => none

/-- An unsigned LEB128 (at most `fuel + 1` bytes) and the rest of the input. -/
def leb (fuel : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs) else
    match fuel with
    | 0 => none
    | f + 1 => (leb f bs).map fun (n, r) => (b.toNat % 128 + 128 * n, r)

/-- The sections `(id, contents)` of the bytes after a preamble; `none` if the framing is
broken. `fuel` bounds the number of sections. -/
def sections : Nat → List UInt8 → Option (List (UInt8 × List UInt8))
  | _, [] => some []
  | 0, _ :: _ => none
  | f + 1, id :: bs => do
    let (n, r) ← leb 4 bs
    if r.length < n then none else
    let rest ← sections f (r.drop n)
    some ((id, r.take n) :: rest)

/-- The sections of a module or component other than custom sections (id 0). -/
def codeSections (b : ByteArray) : Option (List (UInt8 × List UInt8)) :=
  (sections b.size (b.data.toList.drop 8)).map (·.filter (·.1 != 0))

/-- **`X` and `Y` have one world**: both decode to components whose WIT projection
(`wasm-wit project`, `Wit.Project.projectX`) is defined and the same. -/
@[problem "silmaril.wasm_components.same_world"
  (title := "Two registered components have the same world")]
def SameWorld (X Y : Value Silmaril.Wasm.Component.Binary.Ast) : Prop :=
  X.Satisfies fun a => Y.Satisfies fun b => (Silmaril.Wasm.Wit.Project.projectX a).isSome ∧
    Silmaril.Wasm.Wit.Project.projectX a = Silmaril.Wasm.Wit.Project.projectX b

/-- **The files of `X` and `Y` differ only in custom sections**: their framing parses and their
other sections are equal, in order (bytes only; under any format). -/
@[problem "silmaril.wasm_components.same_code"
  (title := "Two registered binaries differ only in custom sections")]
def SameCode {V W : Type} (X : Value V) (Y : Value W) : Prop :=
  (codeSections X.bytes.data).isSome ∧ codeSections X.bytes.data = codeSections Y.bytes.data

/-- **`wasm-wit encode` of `X` gives `Y`** (`Wit.Tool.reencode`: decode the WIT package, then
wit-component's encoding; `reencode_sound`). -/
@[problem "silmaril.wasm_components.reencodes_to"
  (title := "wasm-wit re-encodes one registered package to another")]
def ReencodesTo {V W : Type} (X : Value V) (Y : Value W) : Prop :=
  Silmaril.Wasm.Wit.Tool.reencode X.bytes.data = .ok Y.bytes.data

/-- **Different digests**: the two files differ. -/
@[problem "silmaril.wasm_components.distinct"
  (title := "Two registered binaries are different files")]
def Distinct {V W : Type} (X : Value V) (Y : Value W) : Prop := X.bytes ≠ Y.bytes

end Silmaril.Project.WasmComponents

end
