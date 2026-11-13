module

public import Silmaril.Wasm.Wac.Elab.Defs

/-!
# WAC elaboration: the examples of `LANGUAGE.md`

Package registries and documents for the examples of wac's `LANGUAGE.md` (wac
`5a7480c`), as ASTs. The expected results are in `Silmaril.Wasm.Wac.ElabExample.Thms`.

* `implicitDoc`: implicit imports of two components, merged (`LANGUAGE.md`,
  "Implicit Imports");
* `inferDoc`: the four inferred-argument rules, a named argument by path tail
  (`input-stream: …`) and an access by path tail (`i.outgoing-stream`), an export
  named by an access;
* `spreadDoc`: a spread argument matching a semver-compatible export;
* `exportSpreadDoc`: an export spread skipping a name exported before
  (`LANGUAGE.md`, "Export Statements");
* errors: `...` not last, a duplicate argument, a missing argument, an argument of the
  wrong type, an implicit import named like an explicit one, two implicit imports
  that do not merge, an export without a name;
* `targetsDoc`: a composition checked against a world.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.ElabExample

open Silmaril.Wasm.Wac Silmaril.Wasm.Wac.Syntax

/-- `func()`. -/
def fUnit : Kind := .func ⟨false, [], none⟩
/-- `func() -> string`. -/
def fStr : Kind := .func ⟨false, [], some (.prim .string)⟩

/-! ## Implicit imports -/

def implicitEnv : PkgEnv := [
  ("example:my-component", { imports := [("i", .inst none [("f", fUnit)])] }),
  ("example:my-other-component", { imports := [("i", .inst none [("g", fStr)])] })]

/-- `let my-instance = new example:my-component { ... };`
`let my-other-instance = new example:my-other-component { ... };` -/
def implicitDoc : Document := { pkg := ⟨"example:composition", none⟩, stmts := [
  .let "my-instance" (.new ⟨"example:my-component", none⟩ [.fill]),
  .let "my-other-instance" (.new ⟨"example:my-other-component", none⟩ [.fill])] }

/-! ## Name inference -/

/-- The interface `foo:bar/baz`. -/
def bazI : Kind := .inst (some "foo:bar/baz") [("hello", fUnit)]
/-- The interface `wasi:io/input-stream`. -/
def inI : Kind := .inst (some "wasi:io/input-stream") [("read", fStr)]
/-- The interface `wasi:io/outgoing-stream`. -/
def outI : Kind := .inst (some "wasi:io/outgoing-stream") [("write", fUnit)]

def inferEnv : PkgEnv := [
  ("foo:bar", { defs := [("baz", .type bazI)] }),
  ("my:stream", { exports := [("wasi:io/input-stream", inI), ("wasi:io/outgoing-stream", outI)] }),
  ("a:b",
    { imports := [("foo:bar/baz", bazI), ("c", fUnit), ("wasi:io/input-stream", inI), ("d", fStr)]
      exports := [("run", fUnit)] })]

/-- ```
import baz: foo:bar/baz;               // rule 1: the interface path foo:bar/baz
import c-fn as "c": func();             // rule 2: the import name c
let s = new my:stream {};
let input-stream = s.input-stream;      // access by path tail: wasi:io/input-stream
import d: func() -> string;             // rule 4: the local name d
let i = new a:b { baz, c-fn, input-stream, d };
let run = i.run;
export run;                             // named by the access: run
``` -/
def inferDoc : Document := { pkg := ⟨"my:comp", none⟩, stmts := [
  .import { id := "baz", ty := .path ⟨"foo:bar", ["baz"], none⟩ },
  .import { id := "c-fn", as := some "c", ty := .func {} },
  .let "s" (.new ⟨"my:stream", none⟩ []),
  .let "input-stream" (.access (.ident "s") "input-stream"),
  .import { id := "d", ty := .func { result := some .string } },
  .let "i" (.new ⟨"a:b", none⟩ [.inferred "baz", .inferred "c-fn", .inferred "input-stream",
    .inferred "d"]),
  .let "run" (.access (.ident "i") "run"),
  .export (.ident "run") .none] }

/-- The same instantiation with a named argument by path tail:
`new a:b { baz, c: c-fn, input-stream: s.input-stream, d }`. -/
def namedDoc : Document := { pkg := ⟨"my:comp", none⟩, stmts := [
  .import { id := "baz", ty := .path ⟨"foo:bar", ["baz"], none⟩ },
  .import { id := "c-fn", as := some "c", ty := .func {} },
  .let "s" (.new ⟨"my:stream", none⟩ []),
  .import { id := "d", ty := .func { result := some .string } },
  .let "i" (.new ⟨"a:b", none⟩ [.inferred "baz", .named (.str "c") (.ident "c-fn"),
    .named (.ident "input-stream") (.access (.ident "s") "input-stream"), .inferred "d"])] }

/-! ## Spread arguments and spread exports -/

def spreadEnv : PkgEnv := [
  ("x:src", { exports := [("wasi:io/streams@0.2.3", .inst none [("read", fStr)]), ("other", fUnit)] }),
  ("x:dst",
    { imports := [("wasi:io/streams@0.2.0", .inst none [("read", fStr)])]
      exports := [("run", fUnit), ("setup", fUnit)] }),
  ("b:c", { exports := [("run", fUnit)] })]

/-- `let src = new x:src {}; let dst = new x:dst { ...src };` -/
def spreadDoc : Document := { pkg := ⟨"my:comp", none⟩, stmts := [
  .let "src" (.new ⟨"x:src", none⟩ []),
  .let "dst" (.new ⟨"x:dst", none⟩ [.spread "src"])] }

/-- ```
let my-instance = new x:dst { ... };
let run = new b:c { }.run;
export run;
export my-instance...;
``` -/
def exportSpreadDoc : Document := { pkg := ⟨"my:comp", none⟩, stmts := [
  .let "my-instance" (.new ⟨"x:dst", none⟩ [.fill]),
  .let "run" (.access (.new ⟨"b:c", none⟩ []) "run"),
  .export (.ident "run") .none,
  .export (.ident "my-instance") .spread] }

/-! ## Errors -/

def fillNotLastDoc : Document := { pkg := ⟨"my:comp", none⟩, stmts := [
  .import { id := "d", ty := .func { result := some .string } },
  .let "i" (.new ⟨"a:b", none⟩ [.fill, .inferred "d"])] }

def duplicateArgDoc : Document := { pkg := ⟨"my:comp", none⟩, stmts := [
  .import { id := "d", ty := .func { result := some .string } },
  .let "i" (.new ⟨"a:b", none⟩ [.inferred "d", .named (.str "d") (.ident "d"), .fill])] }

def missingArgDoc : Document := { pkg := ⟨"my:comp", none⟩, stmts := [
  .import { id := "d", ty := .func { result := some .string } },
  .let "i" (.new ⟨"a:b", none⟩ [.inferred "d"])] }

def mismatchDoc : Document := { pkg := ⟨"my:comp", none⟩, stmts := [
  .import { id := "d", ty := .func {} },
  .let "i" (.new ⟨"a:b", none⟩ [.inferred "d", .fill])] }

def conflictDoc : Document := { pkg := ⟨"example:composition", none⟩, stmts := [
  .import { id := "i", ty := .func {} },
  .let "my-instance" (.new ⟨"example:my-component", none⟩ [.fill])] }

def mergeEnv : PkgEnv := [
  ("p:one", { imports := [("f", fUnit)] }),
  ("p:two", { imports := [("f", fStr)] })]

def mergeConflictDoc : Document := { pkg := ⟨"my:comp", none⟩, stmts := [
  .let "a" (.new ⟨"p:one", none⟩ [.fill]),
  .let "b" (.new ⟨"p:two", none⟩ [.fill])] }

def exportRequiresAsDoc : Document := { pkg := ⟨"my:comp", none⟩, stmts := [
  .export (.new ⟨"b:c", none⟩ []) .none] }

/-! ## Targets -/

def targetsEnv : PkgEnv := spreadEnv ++ [
  ("wasi:cli", { defs := [("command", .type (.comp (some "wasi:cli/command")
      [("wasi:io/streams@0.2.0", .inst none [("read", fStr)])] [("run", fUnit)]))] })]

/-- `package my:comp targets wasi:cli/command; let i = new x:dst { ... }; export i.run;` -/
def targetsDoc : Document :=
  { pkg := ⟨"my:comp", none⟩
    targets := some ⟨"wasi:cli", ["command"], none⟩
    stmts := [.let "i" (.new ⟨"x:dst", none⟩ [.fill]), .export (.access (.ident "i") "run") .none] }

/-- The same without the export: the world's export `run` is missing. -/
def targetsMissingDoc : Document := { targetsDoc with stmts := [.let "i" (.new ⟨"x:dst", none⟩ [.fill])] }

end Silmaril.Wasm.Wac.ElabExample
