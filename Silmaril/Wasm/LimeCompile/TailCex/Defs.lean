module

public import Silmaril.Wasm.LimeCompile.Tail.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation

/-!
# Tail calls under `try_table`: the counterexample module

`cexM` has a tag `$e : [] → []` and two functions of type `[] → [i32]`:

```wat
(func $f (export "f") (result i32)
  (block (try_table (catch_all 0) (return_call $g)))
  (i32.const 7))
(func $g (result i32) (throw $e))
```

In Core 3.0, `return_call $g` leaves the `try_table`'s handler (and `$f`'s frame) before `$g`
runs, so `$g`'s exception escapes: invoking `f` throws. The naive rewrite (`naiveModule`, which
also rewrites inside `try_table`) replaces it by `call $g; return`, which runs `$g` *inside* the
handler: `catch_all` catches the exception, branches out of the block, and `f` returns `7`.

* `cexM`, `bodyF`, `bodyFN`, `bodyG`: the module and the bodies (`bodyFN` the naive rewrite of
  `bodyF`);
* `dts`, `miC`, `storeC`, `storeN`: the closed types, the module instance and the stores that
  `allocModule?` builds for `cexM` and for `naiveModule cexM` in the empty store (no imports),
  written out (the equations are in `TailCex.Thms`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.TailCex

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- Label / index `0`. -/
abbrev l0 : LabelIdx := ⟨⟨0, by decide⟩⟩

/-- The body of `$f`. -/
def bodyF : Expr :=
  [.block .empty [.tryTable .empty [.catchAll l0] [.returnCall ⟨1⟩]], .intConst .i32 7]

/-- The naive rewrite of `bodyF`: `call $g; return` inside the `try_table`. -/
def bodyFN : Expr :=
  [.block .empty [.tryTable .empty [.catchAll l0] [.call ⟨1⟩, .return_]], .intConst .i32 7]

/-- The body of `$g`. -/
def bodyG : Expr := [.throw ⟨0⟩]

/-- `(func (result i32))` and `(func)`, as two recursion groups. -/
def cexTypes : List RecType :=
  [⟨[⟨true, [], .func ⟨[], [.num (.int .i32)]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]

/-- **The counterexample module.** -/
def cexM : Module where
  types := cexTypes
  tags := [⟨1⟩]
  funcs := [⟨⟨0⟩, [], bodyF⟩, ⟨⟨0⟩, [], bodyG⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- `(func (result i32))`, closed (a one-type recursion group). -/
def dtF : DefType := .defn (.group (.cons (.sub true .nil (.func .nil (.cons .i32 .nil))) .nil)) 0

/-- `(func)`, closed. -/
def dtE : DefType := .defn (.group (.cons (.sub true .nil (.func .nil .nil)) .nil)) 0

/-- The closed types of `cexM`. -/
def dts : List DefType := [dtF, dtE]

/-- The module instance of `cexM` (and of its naive rewrite). -/
def miC : ModuleInst where
  types := dts
  tags := [0]
  funcs := [0, 1]
  exports := [⟨"f", .func 0⟩]

variable {H : Type}

/-- The store after allocating `cexM` in the empty store. -/
def storeC : Store H where
  tags := [⟨dtE⟩]
  funcs := [⟨dtF, miC, .wasm ⟨⟨0⟩, [], bodyF⟩⟩, ⟨dtF, miC, .wasm ⟨⟨0⟩, [], bodyG⟩⟩]

/-- The store after allocating `naiveModule cexM` in the empty store. -/
def storeN : Store H where
  tags := [⟨dtE⟩]
  funcs := [⟨dtF, miC, .wasm ⟨⟨0⟩, [], bodyFN⟩⟩, ⟨dtF, miC, .wasm ⟨⟨0⟩, [], bodyG⟩⟩]

end Silmaril.Wasm.LimeCompile.TailCex
