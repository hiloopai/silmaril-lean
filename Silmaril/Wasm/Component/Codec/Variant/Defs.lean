module

public import Silmaril.Wasm.Component.Codec.Defs
public import Silmaril.Wasm.Component.BinaryAsync.Defs
public import Silmaril.Wasm.Component.BinaryGC.Defs

/-!
# The variants of the component binary codec

`Codec.Variant` names the component binary decoders of the repository besides the facade's
`Codec.decode` (`Silmaril.Wasm.Component.Codec.Defs`), and `Variant.accepts v b` says whether
variant `v` reads `b`. `dropAsyncBytes` and `resourceF32Bytes` are the binaries that separate
`async` from `lax` and `lax` from `gc` (`Codec.not_async_sub_lax`, `Codec.not_lax_sub_gc` in
`Silmaril.Wasm.Component.Codec.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Codec

/-- The component binary decoders of the repository. -/
inductive Variant where
  /-- `Binary.parse`: `Binary.md` at `8505ba7`, no async built-ins. -/
  | mvp
  /-- `BinaryAsync.parseX`: `mvp` and the built-ins `wasm-jco` writes. -/
  | async
  /-- `Codec.decodeLax`: `Binary.md` at `d095e2f`. -/
  | lax
  /-- `Codec.decode`: `lax` and the rules `BinaryP3.StrictOk`. -/
  | strict
  /-- `BinaryGC.parse`: WebAssembly 3.0 core types and the GC canonical options. -/
  | gc
  deriving DecidableEq, Repr

/-- Whether an `Except` is a success. -/
def ok {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- Whether variant `v` reads the binary `b`. -/
def Variant.accepts : Variant → ByteArray → Bool
  | .mvp, b => ok (Binary.parse b)
  | .async, b => ok (BinaryAsync.parseX b)
  | .lax, b => ok (decodeLax b)
  | .strict, b => ok (decode b)
  | .gc, b => ok (BinaryGC.parse b)

/-! ## Binaries that separate the variants -/

/-- A component whose one section is a canon section holding `resource.drop async 0` (tag
`0x07`), a built-in `wasm-jco` writes and `Binary.md` at `d095e2f` dropped. -/
def dropAsyncBytes : ByteArray :=
  ⟨(Binary.preambleBytes ++ [0x08, 0x03, 0x01, 0x07, 0x00]).toArray⟩

/-- A component whose one section is a type section holding a resource type represented as
`f32` (`0x3f 0x7d`, no destructor): the grammar reads any core value type there, the reference
syntax only `i32` and `i64`. -/
def resourceF32Bytes : ByteArray :=
  ⟨(Binary.preambleBytes ++ [0x07, 0x04, 0x01, 0x3f, 0x7d, 0x00]).toArray⟩

end Silmaril.Wasm.Component.Codec
