module

public import Silmaril.Project.WasmP3Rust.HelloDen.Defs
public import Silmaril.Project.WasmP3Rust.HelloP3.Thms
public import Silmaril.Proofs.Project.WasmP3Rust.HelloDen.Main

/-!
# `hello` under `den`

Proofs in `Silmaril.Proofs.Project.WasmP3Rust.HelloDen.{Obs,Run,Resume,Write,Wait,Steps,Main}`.

**PROVED**

* `wiring`: the index spaces of `hello.wasm` (`HelloP3.ast`, the kernel-checked parse of the
  file) give the async callback lift of `run` (core functions 29 and 30) and the built-ins
  `helloK` calls (`HelloWiring`), by evaluation in the kernel;
* `hello_sat`: for **any** component whose index spaces have that wiring, `den` with the core
  layer `helloK` meets `helloG1` over every host of the wait discipline `waitTh3`: in a trace
  with at most one call of `run`, stdout accepted a prefix of `Hello, WASI 0.3!\n`, and all of
  it if `run` returned `ok`. Partial writes (`COMPLETED k`), `BLOCKED` writes completed through
  `waitable-set.wait` (the callback driver), a future that blocks, dropped or cancelled copies,
  answers of the wrong shape (traps) are all covered;
* `hello_prints_model`: **`Task.helloPrintsP3` for `den` instantiated with `helloK`**: the file
  parses (`HelloP3.parse_eq`) and its denotation meets `helloG1` over every host of
  `stdoutTh3w`;
* `hello_prints_of_core`: `Task.helloPrintsP3 (den Ks)` for any core semantics `Ks` under which
  the denotation of `hello.wasm` refines that of the model (`Task.helloCore Ks`).

**OPEN** (frozen): `Task.helloCore Ks` for `Ks` a core Wasm interpreter (silmaril's Core 3.0
machine) run on the three core modules of `hello.wasm`: that the Rust program, `wit-bindgen`'s
async runtime and `wasi-libc`-free `p3rt` glue behave as `helloK` at the canonical ABI boundary.
Note that the real code also calls `context.get/set` (supported by `den`) and may call
`waitable-set.poll`, `waitable-set.drop` and `future.drop-readable`; `den` traps on `poll` (it is
outside `p3World`), so if the code polls, `Task.helloCore` fails for it and `den` must first be
extended.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.HelloDen

open Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Project.WasmP3Rust.Den
open Silmaril.Wasm.Component.BinaryP3 (Ast)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Project.Shapes.Component (WasiSat)

/-- **The wiring of `hello.wasm`.** -/
theorem wiring : HelloWiring (spaces HelloP3.ast) where
  run := by decide +kernel
  streamNew := by decide +kernel
  wvs := by decide +kernel
  wsNew := by decide +kernel
  write := by decide +kernel
  join := by decide +kernel
  dropW := by decide +kernel
  fread := by decide +kernel
  taskReturn := by decide +kernel

/-- **`hello`'s model meets its guarantee over every host of the wait discipline.** -/
theorem hello_sat {c : Ast} (hw : HelloWiring (spaces c)) :
    WasiSat (den (fun _ => helloK) c) waitTh3 helloG1 :=
  Silmaril.Proofs.Project.WasmP3Rust.HelloDen.hello_sat hw

/-- A stronger theory gives a weaker assumption. -/
theorem wasiSat_stdoutTh3w {σ : p3World.Model} (h : WasiSat σ waitTh3 helloG1) :
    WasiSat σ stdoutTh3w helloG1 := fun s hs hT =>
  h s hs ((Protocol.accepts_prod_iff _ _ _).1 hT).2

/-- **`Task.helloPrintsP3` with the core layer `helloK`.** -/
theorem hello_prints_model : Task.helloPrintsP3 (den fun _ => helloK) :=
  ⟨HelloP3.ast, HelloP3.parse_eq, wasiSat_stdoutTh3w (hello_sat wiring)⟩

/-- Open: **the core modules of `hello.wasm` behave as `helloK`** under the core layer semantics
`Ks`: every play of the denotation of the file is a play of the model's. -/
def Task.helloCore (Ks : Ast → CoreExec) : Prop :=
  den Ks HelloP3.ast ≤ den (fun _ => helloK) HelloP3.ast

/-- **`hello` prints its line under any core semantics that refines the model.** -/
theorem hello_prints_of_core {Ks : Ast → CoreExec} (h : Task.helloCore Ks) :
    Task.helloPrintsP3 (den Ks) :=
  ⟨HelloP3.ast, HelloP3.parse_eq, fun s hs hT =>
    wasiSat_stdoutTh3w (hello_sat wiring) s (h hs) hT⟩

end Silmaril.Project.WasmP3Rust.HelloDen

end
