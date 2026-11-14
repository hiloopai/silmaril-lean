module

public import Silmaril.Project.WasmP3Rust.StdioK.Defs
public import Silmaril.Project.WasmP3Rust.TasksX.Defs
public import Silmaril.Project.WasmP3Rust.TasksP3.Thms
public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Main
public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Echo

/-!
# `cat`, its debug build and `echo` under `DenX.den`, with core models

Proofs in `Silmaril.Raw.Project.WasmP3Rust.StdioK.{Obs,Inv,Args,Resume,Loop,Rw,Wait,WaitRes,
Steps,Main}`.

**PROVED**

* `catWiring`, `catDebugWiring`, `echoWiring`: the index spaces of the three files (their
  kernel-checked parses `<N>.P3.ast`) give the async callback lift of `run` (core functions 31
  and 32) and the built-ins of `catPlan`, `catDebugPlan`, `echoPlan` (kernel evaluation). The
  release and debug builds of `cat` call the same built-ins at different core indices.
* `stdio_sat`: for **any** component whose index spaces have a plan's wiring, `DenX.den` with
  the core layer `stdioK P` meets `GP P` over every host of the wait discipline `waitTh3x`
  (reads, writes, futures that block and complete through `waitable-set.wait`, partial copies,
  dropped and cancelled copies, answers of the wrong shape).
* **`cat_copies_model : Task.catCopiesX (DenX.den fun _ => stdioK catPlan)`**: stdout accepted
  a prefix of what stdin delivered, all of it once `run` returned `ok`, over every host of
  `stdoutTh3x`.
* **`catDebug_copies_model : Task.catDebugCopiesX (DenX.den fun _ => stdioK catDebugPlan)`**.
* **`echo_prints_model args : Task.echoPrintsX (DenX.den fun _ => stdioK echoPlan) args`**: in
  `p3xWorld`, over every host of `echoTh args` (`get-arguments` answers `args`), stdout accepted
  a prefix of `" ".intercalate (args.drop 1) ++ "\n"` (UTF-8), all of it once `run` returned
  `ok`. The line is read back from memory as the Canonical ABI laid out the `list<string>`
  (`lowerArgs_spec`).
* `<n>_of_core`: each statement for any core semantics under which the denotation of the file
  refines that of the model (`Task.catCore`, `Task.catDebugCore`, `Task.echoCore`, open).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.StdioK

open Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX
open Silmaril.Project.WasmP3Rust.Den (spaces)
open Silmaril.Wasm.Component.BinaryP3 (Ast)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Project.Shapes.Component (WasiSat)
open Silmaril.Raw.Project.WasmP3Rust.StdioK (GP stdio_sat goodB obsOf argsSeen echo_sat)

/-! ## Wiring -/

/-- **The wiring of `cat.wasm`.** -/
theorem catWiring : Wiring catPlan (spaces Cat.P3.ast) where
  run := by decide +kernel
  src := by decide +kernel
  streamNew := by decide +kernel
  wvs := by decide +kernel
  wsNew := by decide +kernel
  read := by decide +kernel
  write := by decide +kernel
  join := by decide +kernel
  dropW := by decide +kernel
  fread := by decide +kernel
  taskReturn := by decide +kernel

/-- **The wiring of `cat-debug.wasm`.** -/
theorem catDebugWiring : Wiring catDebugPlan (spaces CatDebug.P3.ast) where
  run := by decide +kernel
  src := by decide +kernel
  streamNew := by decide +kernel
  wvs := by decide +kernel
  wsNew := by decide +kernel
  read := by decide +kernel
  write := by decide +kernel
  join := by decide +kernel
  dropW := by decide +kernel
  fread := by decide +kernel
  taskReturn := by decide +kernel

/-- **The wiring of `echo.wasm`.** -/
theorem echoWiring : Wiring echoPlan (spaces Echo.P3.ast) where
  run := by decide +kernel
  src := by decide +kernel
  streamNew := by decide +kernel
  wvs := by decide +kernel
  wsNew := by decide +kernel
  read := by decide +kernel
  write := by decide +kernel
  join := by decide +kernel
  dropW := by decide +kernel
  fread := by decide +kernel
  taskReturn := by decide +kernel

/-! ## `cat` -/

/-- A stronger theory gives a weaker assumption. -/
theorem wasiSat_stdoutTh3x {σ : p3xWorld.Model} {S' : Type} {G : Protocol S' WEv}
    (h : WasiSat σ waitTh3x G) : WasiSat σ stdoutTh3x G := fun s hs hT =>
  h s hs ((Protocol.accepts_prod_iff _ _ _).1 hT).2

/-- `cat`'s guarantee is the plan's. -/
theorem catGX_eq {P : Plan} (hk : P.kind = .cat) : GP P = catGX := by
  unfold GP catGX
  congr
  funext t
  simp only [goodB, Silmaril.Raw.Project.WasmP3Rust.StdioK.tgt, hk]
  rfl

/-- **`cat` copies stdin to stdout, with the core model `stdioK catPlan`.** -/
theorem cat_copies_model : Task.catCopiesX (DenX.den fun _ => stdioK catPlan) :=
  ⟨Cat.P3.ast, Cat.P3.parse_eq, catGX_eq (P := catPlan) rfl ▸
    wasiSat_stdoutTh3x (stdio_sat catWiring)⟩

/-- **The debug build of `cat` copies stdin to stdout, with the core model `stdioK
catDebugPlan`.** -/
theorem catDebug_copies_model : Task.catDebugCopiesX (DenX.den fun _ => stdioK catDebugPlan) :=
  ⟨CatDebug.P3.ast, CatDebug.P3.parse_eq, catGX_eq (P := catDebugPlan) rfl ▸
    wasiSat_stdoutTh3x (stdio_sat catDebugWiring)⟩

/-! ## `echo` -/

/-- **`echo` prints its arguments, with the core model `stdioK echoPlan`**, in `p3xWorld`, over
every host of `echoTh args`. -/
theorem echo_prints_model (args : List String) :
    Task.echoPrintsX (DenX.den fun _ => stdioK echoPlan) args :=
  ⟨Echo.P3.ast, Echo.P3.parse_eq, echo_sat (stdio_sat echoWiring)⟩

/-! ## The real core code: open -/

/-- Open: **the core modules of `cat.wasm` behave as `stdioK catPlan`** under the core layer
semantics `Ks`: every play of the denotation of the file is a play of the model's. -/
def Task.catCore (Ks : Ast → CoreExecX) : Prop :=
  DenX.den Ks Cat.P3.ast ≤ DenX.den (fun _ => stdioK catPlan) Cat.P3.ast

/-- Open: the same for `cat-debug.wasm`. -/
def Task.catDebugCore (Ks : Ast → CoreExecX) : Prop :=
  DenX.den Ks CatDebug.P3.ast ≤ DenX.den (fun _ => stdioK catDebugPlan) CatDebug.P3.ast

/-- Open: the same for `echo.wasm`. -/
def Task.echoCore (Ks : Ast → CoreExecX) : Prop :=
  DenX.den Ks Echo.P3.ast ≤ DenX.den (fun _ => stdioK echoPlan) Echo.P3.ast

/-- **`cat` copies stdin to stdout under any core semantics that refines the model.** -/
theorem cat_copies_of_core {Ks : Ast → CoreExecX} (h : Task.catCore Ks) :
    Task.catCopiesX (DenX.den Ks) :=
  ⟨Cat.P3.ast, Cat.P3.parse_eq, fun s hs hT =>
    (catGX_eq (P := catPlan) rfl ▸ wasiSat_stdoutTh3x (stdio_sat catWiring)) s (h hs) hT⟩

/-- **The debug build, under any core semantics that refines its model.** -/
theorem catDebug_copies_of_core {Ks : Ast → CoreExecX} (h : Task.catDebugCore Ks) :
    Task.catDebugCopiesX (DenX.den Ks) :=
  ⟨CatDebug.P3.ast, CatDebug.P3.parse_eq, fun s hs hT =>
    (catGX_eq (P := catDebugPlan) rfl ▸ wasiSat_stdoutTh3x (stdio_sat catDebugWiring)) s (h hs) hT⟩

/-- **`echo` prints its arguments under any core semantics that refines its model.** -/
theorem echo_prints_of_core {Ks : Ast → CoreExecX} (h : Task.echoCore Ks) (args : List String) :
    Task.echoPrintsX (DenX.den Ks) args :=
  ⟨Echo.P3.ast, Echo.P3.parse_eq, fun s hs hT => echo_sat (stdio_sat echoWiring) s (h hs) hT⟩

end Silmaril.Project.WasmP3Rust.StdioK

end
