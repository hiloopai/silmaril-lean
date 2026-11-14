module

public import Silmaril.Wasm.Component.BinaryP3.Strict.Thms
public import Silmaril.Project.WasmP3Rust.HelloP3.Thms
public import Silmaril.Project.WasmP3Rust.Hello.P3.Thms
public import Silmaril.Project.WasmP3Rust.Hello.Core0.Decode.Thms
public import Silmaril.Project.WasmP3Rust.Hello.Core1.Decode.Thms
public import Silmaril.Project.WasmP3Rust.Hello.Core2.Decode.Thms
public import Silmaril.Project.WasmP3Rust.Cat.P3.Thms
public import Silmaril.Project.WasmP3Rust.Cat.Core0.Decode.Thms
public import Silmaril.Project.WasmP3Rust.Cat.Core1.Decode.Thms
public import Silmaril.Project.WasmP3Rust.Cat.Core2.Decode.Thms
public import Silmaril.Project.WasmP3Rust.Echo.P3.Thms
public import Silmaril.Project.WasmP3Rust.Echo.Core0.Decode.Thms
public import Silmaril.Project.WasmP3Rust.Echo.Core1.Decode.Thms
public import Silmaril.Project.WasmP3Rust.Echo.Core2.Decode.Thms
public import Silmaril.Project.WasmP3Rust.CatDebug.P3.Thms
public import Silmaril.Project.WasmP3Rust.CatDebug.Core0.Decode.Thms
public import Silmaril.Project.WasmP3Rust.CatDebug.Core1.Decode.Thms
public import Silmaril.Project.WasmP3Rust.CatDebug.Core2.Decode.Thms

/-!
# `parseStrict` on the four WASI 0.3 examples

**PROVED** (kernel): `BinaryP3.parseStrict` (`parse`, then the core-module, outer-alias-sort and
attribute rules) reads each of `hello.wasm`, `cat.wasm`, `echo.wasm` and `cat-debug.wasm` as the
AST `X.P3.ast` of `Parses3` (`<x>_parseStrict`), and `hello.wasm` as `HelloP3.ast`
(`helloP3_parseStrict`). The core-module rule is silmaril's `decode?` itself, on modules of
up to 3.1 MB (`cat-debug.wasm`'s main module), from the generated certificates
`X.CoreI.Decode.Thms` (`Silmaril.Wasm.Component.ChunkedDecode`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.Strict

open Silmaril.Wasm.Component.BinaryP3 Silmaril.Wasm.Component.Chunked

/-- The core modules of `hello.wasm`. -/
theorem hello_modules : (Hello.P3.ast).collect.modules = [arr (slice Hello.File.bytes 279 39729), arr (slice Hello.File.bytes 39732 39921), arr (slice Hello.File.bytes 39924 40053)] := by
  rfl

/-- **`hello.wasm` satisfies the strict rules**: its three core modules decode
(`decode_eq`, kernel), its aliases and names pass the checks (kernel). -/
theorem hello_strictOk : StrictOk Hello.P3.ast := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hello_modules]
    simp only [List.all_cons, List.all_nil, moduleOk, Hello.Core0.decode_eq, Hello.Core1.decode_eq, Hello.Core2.decode_eq, Option.isSome_some, Bool.and_true]
  · decide +kernel
  · decide +kernel

/-- The core modules of `hello.wasm` (the AST `HelloP3.ast`). -/
theorem helloP3_modules : (HelloP3.ast).collect.modules = [arr (slice Hello.File.bytes 279 39729), arr (slice Hello.File.bytes 39732 39921), arr (slice Hello.File.bytes 39924 40053)] := by
  rfl

/-- **`hello.wasm` satisfies the strict rules**: its three core modules decode
(`decode_eq`, kernel), its aliases and names pass the checks (kernel). -/
theorem helloP3_strictOk : StrictOk HelloP3.ast := by
  refine ⟨?_, ?_, ?_⟩
  · rw [helloP3_modules]
    simp only [List.all_cons, List.all_nil, moduleOk, Hello.Core0.decode_eq, Hello.Core1.decode_eq, Hello.Core2.decode_eq, Option.isSome_some, Bool.and_true]
  · decide +kernel
  · decide +kernel

/-- **`parseStrict` reads `hello.wasm` as `Hello.P3.ast`.** -/
theorem hello_parseStrict : parseStrict (arr Hello.File.bytes) = .ok Hello.P3.ast :=
  parseStrict_ok_iff.2 ⟨Hello.P3.parse_eq, hello_strictOk⟩

/-- The core modules of `cat.wasm`. -/
theorem cat_modules : (Cat.P3.ast).collect.modules = [arr (slice Cat.File.bytes 322 44549), arr (slice Cat.File.bytes 44552 44760), arr (slice Cat.File.bytes 44763 44902)] := by
  rfl

/-- **`cat.wasm` satisfies the strict rules**: its three core modules decode
(`decode_eq`, kernel), its aliases and names pass the checks (kernel). -/
theorem cat_strictOk : StrictOk Cat.P3.ast := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cat_modules]
    simp only [List.all_cons, List.all_nil, moduleOk, Cat.Core0.decode_eq, Cat.Core1.decode_eq, Cat.Core2.decode_eq, Option.isSome_some, Bool.and_true]
  · decide +kernel
  · decide +kernel

/-- **`parseStrict` reads `cat.wasm` as `Cat.P3.ast`.** -/
theorem cat_parseStrict : parseStrict (arr Cat.File.bytes) = .ok Cat.P3.ast :=
  parseStrict_ok_iff.2 ⟨Cat.P3.parse_eq, cat_strictOk⟩

/-- The core modules of `echo.wasm`. -/
theorem echo_modules : (Echo.P3.ast).collect.modules = [arr (slice Echo.File.bytes 343 42367), arr (slice Echo.File.bytes 42370 42578), arr (slice Echo.File.bytes 42581 42720)] := by
  rfl

/-- **`echo.wasm` satisfies the strict rules**: its three core modules decode
(`decode_eq`, kernel), its aliases and names pass the checks (kernel). -/
theorem echo_strictOk : StrictOk Echo.P3.ast := by
  refine ⟨?_, ?_, ?_⟩
  · rw [echo_modules]
    simp only [List.all_cons, List.all_nil, moduleOk, Echo.Core0.decode_eq, Echo.Core1.decode_eq, Echo.Core2.decode_eq, Option.isSome_some, Bool.and_true]
  · decide +kernel
  · decide +kernel

/-- **`parseStrict` reads `echo.wasm` as `Echo.P3.ast`.** -/
theorem echo_parseStrict : parseStrict (arr Echo.File.bytes) = .ok Echo.P3.ast :=
  parseStrict_ok_iff.2 ⟨Echo.P3.parse_eq, echo_strictOk⟩

/-- The core modules of `cat-debug.wasm`. -/
theorem catDebug_modules : (CatDebug.P3.ast).collect.modules = [arr (slice CatDebug.File.bytes 323 3136781), arr (slice CatDebug.File.bytes 3136784 3136992), arr (slice CatDebug.File.bytes 3136995 3137134)] := by
  rfl

/-- **`cat-debug.wasm` satisfies the strict rules**: its three core modules decode
(`decode_eq`, kernel), its aliases and names pass the checks (kernel). -/
theorem catDebug_strictOk : StrictOk CatDebug.P3.ast := by
  refine ⟨?_, ?_, ?_⟩
  · rw [catDebug_modules]
    simp only [List.all_cons, List.all_nil, moduleOk, CatDebug.Core0.decode_eq, CatDebug.Core1.decode_eq, CatDebug.Core2.decode_eq, Option.isSome_some, Bool.and_true]
  · decide +kernel
  · decide +kernel

/-- **`parseStrict` reads `cat-debug.wasm` as `CatDebug.P3.ast`.** -/
theorem catDebug_parseStrict : parseStrict (arr CatDebug.File.bytes) = .ok CatDebug.P3.ast :=
  parseStrict_ok_iff.2 ⟨CatDebug.P3.parse_eq, catDebug_strictOk⟩

/-- **`parseStrict` reads `hello.wasm` as `HelloP3.ast`** (the AST of `HelloDen`). -/
theorem helloP3_parseStrict :
    parseStrict (Silmaril.Project.WasmP3Rust.arrOf Hello.File.bytes) = .ok HelloP3.ast :=
  parseStrict_ok_iff.2 ⟨HelloP3.parse_eq, helloP3_strictOk⟩

end Silmaril.Project.WasmP3Rust.Strict

end
