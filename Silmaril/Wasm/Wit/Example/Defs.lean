module

public import Silmaril.Wasm.Wit.Valid.Thms

/-!
# WIT: examples

`wasiIo`: the AST of a fragment of `wasi:io@0.2.0` (the `error`, `poll` and `streams`
interfaces with their resources, a `use` chain and an `imports` world), as a WIT text
parser would produce it:

```wit
/// WASI I/O.
package wasi:io@0.2.0;

interface error {
  resource error { to-debug-string: func() -> string; }
}
interface poll {
  resource pollable { ready: func() -> bool; block: func(); }
  poll: func(in: list<borrow<pollable>>) -> list<u32>;
}
interface streams {
  use error.{error};
  use poll.{pollable};
  variant stream-error { last-operation-failed(error), closed }
  resource input-stream {
    read: func(len: u64) -> result<list<u8>, stream-error>;
    subscribe: func() -> pollable;
  }
}
@since(version = 0.2.0)
world imports { import streams; import poll; import error; }
```

It is valid (`wasiIo_valid`); the negative examples each break one rule.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Example

def v020 : Version := ⟨0, 2, 0, [], []⟩

def io : PackageName := ⟨"wasi", "io", some v020⟩

def errorIface : Interface :=
  { name := "error"
    items := [.type { name := "error", kind := .resource [
      { kind := .method "to-debug-string", func := { result := some .string } }] }] }

def pollIface : Interface :=
  { name := "poll"
    items := [
      .type { name := "pollable", kind := .resource [
        { kind := .method "ready", func := { result := some .bool } },
         { kind := .method "block", func := {} }] },
      .func { name := "poll", func :=
        { params := [("in", .list (.borrow "pollable"))], result := some (.list .u32) } }] }

def streamsIface : Interface :=
  { name := "streams"
    items := [
      .use { path := .local "error", names := [{ name := "error" }] },
      .use { path := .local "poll", names := [{ name := "pollable" }] },
      .type { name := "stream-error", kind := .variant [
        { name := "last-operation-failed", ty := some (.named "error") }, { name := "closed" }] },
      .type { name := "input-stream", kind := .resource [
        { kind := .method "read", func :=
            { params := [("len", .u64)],
              result := some (.result (some (.list .u8)) (some (.named "stream-error"))) } },
         { kind := .method "subscribe", func := { result := some (.named "pollable") } }] }] }

def importsWorld : World :=
  { name := "imports"
    gates := [.since v020]
    items := [.import { ext := .path (.local "streams") }, .import { ext := .path (.local "poll") },
      .import { ext := .path (.local "error") }] }

def wasiIo : Package :=
  { name := io, docs := ⟨some "WASI I/O."⟩
    items := [.iface errorIface, .iface pollIface, .iface streamsIface, .world importsWorld] }

/-- A consumer package using `wasi:io` by its foreign path. -/
def consumer : Package :=
  { name := ⟨"local", "app", none⟩
    items := [
      .iface { name := "api", items := [
        .use { path := .foreign io "streams", names := [{ name := "input-stream", as := some "in" }] },
        .func { name := "run", func := { params := [("s", .own "in")] } }] },
      .world { name := "app", items := [
        .import { ext := .path (.foreign io "streams") },
        .export { ext := .path (.local "api") }] }] }

/-! ## Negative examples -/

/-- `own<t>` where `t` is a record, not a resource. -/
def ownRecord : Package :=
  { name := ⟨"x", "y", none⟩
    items := [.iface { name := "i", items := [
      .type { name := "t", kind := .record [{ name := "a", ty := .u8 }] },
      .func { name := "f", func := { params := [("x", .own "t")] } }] }] }

/-- `type a = b; type b = a;` -/
def typeCycle : Package :=
  { name := ⟨"x", "y", none⟩
    items := [.iface { name := "i", items := [
      .type { name := "a", kind := .alias (.named "b") },
      .type { name := "b", kind := .alias (.named "a") }] }] }

/-- Two interfaces using each other. -/
def useCycle : Package :=
  { name := ⟨"x", "y", none⟩
    items := [
      .iface { name := "i", items := [.use { path := .local "j", names := [{ name := "b" }] },
        .type { name := "a", kind := .alias .u8 }] },
      .iface { name := "j", items := [.use { path := .local "i", names := [{ name := "a" }] },
        .type { name := "b", kind := .alias .u8 }] }] }

/-- A name used but not defined. -/
def undefinedName : Package :=
  { name := ⟨"x", "y", none⟩
    items := [.iface { name := "i", items := [
      .func { name := "f", func := { result := some (.named "nope") } }] }] }

/-- A function returning a `borrow`. -/
def borrowResult : Package :=
  { name := ⟨"x", "y", none⟩
    items := [.iface { name := "i", items := [
      .type { name := "r", kind := .resource [] },
      .func { name := "f", func := { result := some (.borrow "r") } }] }] }

/-- A duplicate name and a non-kebab identifier. -/
def badNames : Package :=
  { name := ⟨"x", "y", none⟩
    items := [.iface { name := "i", items := [
      .type { name := "a", kind := .alias .u8 }, .func { name := "a", func := {} },
      .type { name := "Bad", kind := .alias .u8 }] }] }

end Silmaril.Wasm.Wit.Example
