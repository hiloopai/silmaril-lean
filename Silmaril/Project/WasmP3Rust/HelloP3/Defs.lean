module

public import Silmaril.Project.WasmP3Rust.Hello.Component.Defs
public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Component.Chunked.Defs

/-!
# `hello.wasm` as an AST of the async-aware grammar

`ast` is `hello.wasm` under `BinaryP3` (component-model `d095e2f`): the 33 sections of the old
grammar (`Silmaril.Project.WasmP3Rust.Hello.secN`, embedded with `Section.ofV0`), the three core
modules (bytes of the file), and the 8 `canon` sections with async built-ins, written from the
compiled parser's output (`BinaryP3.parse`); `Silmaril.Project.WasmP3Rust.HelloP3.Thms` proves in
the kernel that the parser returns exactly this AST.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.HelloP3

open Silmaril.Wasm.Component.BinaryP3 (Section Ast Canon)
open Silmaril.Wasm.Component.Chunked (slice arr)

/-- The `canon` section at 40059. -/
def c40059 : Section :=
  .canons [.contextGet .i32 0, .contextSet .i32 0, .waitableSetDrop, .waitableSetNew, .waitableJoin]

/-- The `canon` section at 40204. -/
def c40204 : Section :=
  .canons [.taskCancel]

/-- The `canon` section at 40235. -/
def c40235 : Section :=
  .canons [.streamNew 5]

/-- The `canon` section at 40279. -/
def c40279 : Section :=
  .canons [.futureCancelWrite 8 false, .futureCancelRead 8 false, .futureDropWritable 8,
    .futureDropReadable 8, .futureNew 8]

/-- The `canon` section at 40309. -/
def c40309 : Section :=
  .canons [.streamCancelWrite 5 false, .streamCancelRead 5 false, .streamDropWritable 5,
    .streamDropReadable 5]

/-- The `canon` section at 40968. -/
def c40968 : Section :=
  .canons [.taskReturn (some (.idx 9)) []]

/-- The `canon` section at 41129. -/
def c41129 : Section :=
  .canons [.waitableSetPoll 0]

/-- The `canon` section at 41155. -/
def c41155 : Section :=
  .canons [.futureWrite 8 [.memory 0, .async], .futureRead 8 [.memory 0, .async],
    .streamWrite 5 [.memory 0, .async], .streamRead 5 [.memory 0, .async]]

/-- The sections of `hello.wasm`, in order. -/
noncomputable def sections : List Section :=
  [Section.ofV0 Hello.sec8,
   Section.ofV0 Hello.sec62,
   Section.ofV0 Hello.sec89,
   Section.ofV0 Hello.sec106,
   Section.ofV0 Hello.sec132,
   Section.ofV0 Hello.sec159,
   Section.ofV0 Hello.sec176,
   Section.ofV0 Hello.sec247,
   .coreModule (arr (slice Hello.File.bytes 279 39729)),
   .coreModule (arr (slice Hello.File.bytes 39732 39921)),
   .coreModule (arr (slice Hello.File.bytes 39924 40053)),
   Section.ofV0 Hello.sec40053,
   c40059,
   Section.ofV0 Hello.sec40071,
   Section.ofV0 Hello.sec40080,
   c40204,
   Section.ofV0 Hello.sec40208,
   Section.ofV0 Hello.sec40229,
   c40235,
   Section.ofV0 Hello.sec40240,
   Section.ofV0 Hello.sec40269,
   c40279,
   Section.ofV0 Hello.sec40294,
   c40309,
   Section.ofV0 Hello.sec40322,
   Section.ofV0 Hello.sec40908,
   Section.ofV0 Hello.sec40931,
   Section.ofV0 Hello.sec40938,
   Section.ofV0 Hello.sec40962,
   c40968,
   Section.ofV0 Hello.sec40975,
   Section.ofV0 Hello.sec41102,
   c41129,
   Section.ofV0 Hello.sec41135,
   c41155,
   Section.ofV0 Hello.sec41182,
   Section.ofV0 Hello.sec41224,
   Section.ofV0 Hello.sec41231,
   Section.ofV0 Hello.sec41322,
   Section.ofV0 Hello.sec41333,
   Section.ofV0 Hello.sec41398,
   Section.ofV0 Hello.sec41422,
   Section.ofV0 Hello.sec41448,
   Section.ofV0 Hello.sec42865]

/-- **`hello.wasm` as an AST.** -/
noncomputable def ast : Ast := .mk sections

end Silmaril.Project.WasmP3Rust.HelloP3

end
