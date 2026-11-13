module

public import Silmaril.Project.WasmP3Rust.Hello.Thms
public import Silmaril.Project.WasmP3Rust.Echo.Thms
public import Silmaril.Project.WasmP3Rust.Cat.Thms
public import Silmaril.Project.WasmP3Rust.CatDebug.Thms
public import Silmaril.Project.WasmP3Rust.Tasks.Defs

/-!
# The WASI 0.3 Rust examples: what is decoded in the kernel

**PROVED**, for each of `hello.wasm` (42914 bytes), `echo.wasm` (45906), `cat.wasm` (47930) and
the debug build `cat-debug.wasm` (3140228) of `examples/wasip3-rust/dist`:

* `framing_eq`: the file is the component preamble followed by its framed sections (`frames`:
  id and body, every body a slice of the file), so the whole file is accounted for, including
  the `canon` sections with async built-ins that Silmaril's component grammar does not cover yet;
* `cores_encode`: each of its three core modules (the Rust program, and the two shims
  wasm-component-ld adds) encodes its `CoreN.module` under silmaril's Core 3.0 binary grammar
  (`Encodes`, sound by `decode?_sound` and unique by `Binary.Core.functional`);
* `secN_eq`: every component section other than the core modules and the `canon` sections
  with async built-ins is an AST of Silmaril's component grammar, checked with its encoder;
* `world_names`: its top-level import and export sections import `wasi:cli/{types,stdin,stdout}@0.3.0` (and `wasi:cli/environment@0.3.0` for
  `echo`) and export `wasi:cli/run@0.3.0`.

The certificates are per section, per custom section and per group of code entries
(`Silmaril.Wasm.Component.Chunked`), each checked in its own module from windows of the file's
chunk literals; for the 3 MB file the largest module takes about 12 s. The behavioural targets
are frozen in `Silmaril.Project.WasmP3Rust.Tasks.Defs`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust

/-- **`cat.wasm` and its 3 MB debug build decode**: framing and core modules. -/
theorem cat_decodes :
    Silmaril.Wasm.Component.Chunked.framing Cat.frames = some Cat.File.bytes ∧
      Silmaril.Wasm.Component.Chunked.framing CatDebug.frames = some CatDebug.File.bytes :=
  ⟨Cat.framing_eq, CatDebug.framing_eq⟩

end Silmaril.Project.WasmP3Rust

end
