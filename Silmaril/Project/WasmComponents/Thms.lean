module

public import Silmaril.Project.WasmComponents.Defs
public import Silmaril.Project.WasmComponents.Code.Thms
public import Silmaril.Project.WasmComponents.Refresh.Defs
public import Silmaril.Project.Formats.Component.Thms
public import Silmaril.Project.Formats.Wit.Defs
public import Silmaril.Project.Shapes.Wasm.Thms
public import Silmaril.Project.Shapes.Component.Example.Thms
public import Silmaril.Wasm.Component.Binary.Example.Defs
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# The Wasm components pilot: values, rows, answers and the verdict group

The binaries are registered in `silmaril/artifacts.toml` by `sil project components add`
(`docs/projects/wasm-wasi.md`, provenance and licenses in `examples/wasm-components/README.md`),
each read under the format of what it is:

* `adapter.{reactor,command}`: the `wasi_snapshot_preview1` adapters of wasmtime v50.0.1, core
  modules (`wasm.module.core3`), and the worlds they embed (`….world`, `wasm.module.world`);
* `wasi.io.v0_2_12.{oci,fixture}`: `wasi:io@0.2.12` as published (OCI, fetched by digest) and
  as encoded by wasm-tools 1.263.0 (`tests/wat`), as components (`wasm.component.binary`) and
  as WIT packages (`….package`, `wit.binary`);
* `gen.producer` (`wasm.module.core3`) and the components `gen.{comp_b,linked,run}` with the
  worlds `gen.{comp_b,linked}.world`, which Silmaril generates; the components and worlds are
  **certificates** (`@[value]`): their `….is` problem says the file parses to the given AST.

The rows are of the standard shapes (`silmaril.shapes.component.{valid,has_world,
digest_behaviour_eq}`, `silmaril.shapes.wasm.returns`) and, for statements about files, of the
pilot's problems (`Silmaril.Project.WasmComponents.Defs`). Solved here, in the kernel:

* the five certificates (`Binary.encode` of the AST is the file, then `Binary.parse_encode`),
  hence their `parses`; `producer` parses and its function 0 returns 42;
* `valid` and `has_world` of `comp_b`, `linked` and `run`; `comp_b` and `run` are different
  files (different digests) with **one behaviour**: the same IR lowering, so the same WASI
  model under every core semantics (`compB_run_behaviourEq`, the row at `topSem`);
* the two `wasi:io@0.2.12` files are different files with the same framed non-custom sections
  (`io_same_code`, `io_distinct`).

Conditional (`Silmaril.Project.WasmComponents.Code.Thms`): once both `wasi:io` files parse,
`Task.parse_codeSections` (open) turns `io_same_code` into one world (`io_same_world_of`) and
one behaviour (`io_behaviourEq_of`). Open: the `parses` of every value of the `wasi_io` and
`adapter` groups (a kernel parse of the 15 KB fixture takes about 4 minutes, of a 51 KB adapter
more), and `wasi:io` `same_world`, `behaviour_eq` and `reencodes`.
-/

open Silmaril.Project (Value)

-- `sil project components add` writes the registry after a cached `Silmaril.Project.Defs`
silmaril_artifacts_refresh "silmaril/artifacts.toml"
silmaril load "silmaril/wasm-components/values.toml"

@[expose] public section

namespace Silmaril.Project.WasmComponents

open Silmaril.Wasm.Component.Binary (Ast)
open Silmaril.Project.Shapes.Component

/-! ## Transfer lemmas -/

/-- Files of different sizes are different files. -/
theorem Distinct.of_size {V W : Type} {X : Value V} {Y : Value W}
    (h : X.bytes.data.size ≠ Y.bytes.data.size) : Distinct X Y :=
  fun e => h (by rw [e])

/-- A component certificate from the encoder: if `Binary.encode c` is the file, the file
parses to `c`. -/
theorem is_of_encode {X : Value Ast} (hf : X.format = Silmaril.Project.Formats.wasmComponent) {c : Ast}
    (h : Silmaril.Wasm.Component.Binary.encode c = some X.bytes.data) : X.Is c := by
  show X.format.parse X.bytes = some c
  rw [hf]
  exact Silmaril.Project.Formats.wasmComponent_parse_eq.mpr (Silmaril.Wasm.Component.Binary.parse_encode h)

/-- A certificate of a component value is a parse of its file. -/
theorem parse_of_is {X : Value Ast} (hf : X.format = Silmaril.Project.Formats.wasmComponent) {c : Ast}
    (h : X.Is c) : Silmaril.Wasm.Component.Binary.parse X.bytes.data = .ok c := by
  have h' : X.format.parse X.bytes = some c := h
  rw [hf] at h'
  exact Silmaril.Project.Formats.wasmComponent_parse_eq.mp h'

/-! ## The Silmaril-generated components (certificates) -/

/-- `Binary.Example.compB` with its export ascribed `(func (type 0))`
(`examples/project-formats/component-run.wasm`, `gen-components.lean`). -/
def runAst : Ast :=
  match Silmaril.Wasm.Component.Binary.Example.compB with
  | .mk ss => .mk (ss.dropLast ++ [.exports [⟨↑"run", ⟨.func, 1⟩, some (.func 0)⟩]])

/-- The world of `Binary.Example.linked`: the type `func() -> u32` and the export `run`. -/
def linkedWorld : Silmaril.Wasm.Wit.Project.WorldType :=
  [.inst (.type Silmaril.Wasm.Component.Binary.Example.getTy), .inst (.export ↑"run" (.func 0))]

end Silmaril.Project.WasmComponents

end

/-- The component `comp-b.wasm`: `Binary.Example.compB`. -/
@[expose, value "silmaril.wasm_components.gen.comp_b" (format := wasm.component.binary)
  (source := silmaril.wasm_components.gen.comp_b.blob)
  (doc := "A component importing get and exporting run = get + 1 (Binary.Example.compB)")]
public def Silmaril.Project.WasmComponents.compBCert : Silmaril.Wasm.Component.Binary.Ast :=
  Silmaril.Wasm.Component.Binary.Example.compB

/-- The component `linked.wasm`: `Binary.Example.linked`. -/
@[expose, value "silmaril.wasm_components.gen.linked" (format := wasm.component.binary)
  (source := silmaril.wasm_components.gen.linked.blob)
  (doc := "Producer and consumer linked in one component (Binary.Example.linked)")]
public def Silmaril.Project.WasmComponents.linkedCert : Silmaril.Wasm.Component.Binary.Ast :=
  Silmaril.Wasm.Component.Binary.Example.linked

/-- The component `component-run.wasm`: `compB` with its export ascribed. -/
@[expose, value "silmaril.wasm_components.gen.run" (format := wasm.component.binary)
  (source := silmaril.wasm_components.gen.run.blob)
  (doc := "Binary.Example.compB with its export ascribed (func (type 0))")]
public def Silmaril.Project.WasmComponents.runCert : Silmaril.Wasm.Component.Binary.Ast :=
  Silmaril.Project.WasmComponents.runAst

/-- The world file of `comp-b.wasm` (`wasm-wit project`): the component type of
`compBWorld`. -/
@[expose, value "silmaril.wasm_components.gen.comp_b.world" (format := wasm.component.binary)
  (source := silmaril.wasm_components.gen.comp_b.world.blob)
  (doc := "The world of silmaril.wasm_components.gen.comp_b (wasm-wit project)")]
public def Silmaril.Project.WasmComponents.compBWorldCert : Silmaril.Wasm.Component.Binary.Ast :=
  Silmaril.Wasm.Wit.Tool.worldAst Silmaril.Project.Shapes.Component.Example.compBWorld

/-- The world file of `linked.wasm` (`wasm-wit project`): the component type of
`linkedWorld`. -/
@[expose, value "silmaril.wasm_components.gen.linked.world" (format := wasm.component.binary)
  (source := silmaril.wasm_components.gen.linked.world.blob)
  (doc := "The world of silmaril.wasm_components.gen.linked (wasm-wit project)")]
public def Silmaril.Project.WasmComponents.linkedWorldCert : Silmaril.Wasm.Component.Binary.Ast :=
  Silmaril.Wasm.Wit.Tool.worldAst Silmaril.Project.WasmComponents.linkedWorld

@[expose] public section

namespace Silmaril.Project.WasmComponents

/-- The denotation the generated rows compare: the IR model under the loosest core semantics,
with the names `get` and `run`. -/
def getRunDen : Silmaril.Wasm.Component.Binary.Ast → getRunLayout.world.Model := irDen topSem getRunLayout

/-- The layout with no functions (the `wasi:io` packages define types only). -/
def typesLayout : Silmaril.Wasi.Layout := ⟨[], []⟩

/-- The denotation the `wasi:io` row compares: the IR model under the loosest core semantics,
with no functions. -/
def typesDen : Silmaril.Wasm.Component.Binary.Ast → typesLayout.world.Model := irDen topSem typesLayout

end Silmaril.Project.WasmComponents

end

-- the rows
silmaril load "silmaril/wasm-components/instances.toml"
-- `wasm.returns`: function address 0 of the producer module returns 42
silmaril instance silmaril.wasm_components.gen.producer.returns_42 (expect := "THM") :=
  silmaril.shapes.wasm.returns
  (m := silmaril.wasm_components.gen.producer) (a := 0) (args := []) (res := [.i32 42])

@[expose] public section

namespace Silmaril.Project.WasmComponents

open Silmaril.Wasm.Component.Binary (Ast)
open Silmaril.Project.Shapes.Component

/-! ## Certificates -/

@[solves "silmaril.wasm_components.gen.comp_b.is"]
theorem compB_is : silmaril.wasm_components.gen.comp_b.is :=
  is_of_encode rfl (by decide +kernel)

@[solves "silmaril.wasm_components.gen.linked.is"]
theorem linked_is : silmaril.wasm_components.gen.linked.is :=
  is_of_encode rfl (by decide +kernel)

@[solves "silmaril.wasm_components.gen.run.is"]
theorem run_is : silmaril.wasm_components.gen.run.is :=
  is_of_encode rfl (by decide +kernel)

@[solves "silmaril.wasm_components.gen.comp_b.world.is"]
theorem compB_world_is : silmaril.wasm_components.gen.comp_b.world.is :=
  is_of_encode rfl (by decide +kernel)

@[solves "silmaril.wasm_components.gen.linked.world.is"]
theorem linked_world_is : silmaril.wasm_components.gen.linked.world.is :=
  is_of_encode rfl (by decide +kernel)

@[solves "silmaril.wasm_components.gen.producer.parses"]
theorem producer_parses : silmaril.wasm_components.gen.producer.parses := by silmaril_decide

/-! ## Valid, has world -/

@[answers "silmaril.wasm_components.gen.comp_b.valid" thm]
theorem compB_valid : silmaril.wasm_components.gen.comp_b.valid := by
  show CompValid compBCert
  unfold CompValid
  decide +kernel

@[answers "silmaril.wasm_components.gen.linked.valid" thm]
theorem linked_valid : silmaril.wasm_components.gen.linked.valid := by
  show CompValid linkedCert
  unfold CompValid
  decide +kernel

@[answers "silmaril.wasm_components.gen.run.valid" thm]
theorem run_valid : silmaril.wasm_components.gen.run.valid := by
  show CompValid runCert
  unfold CompValid
  decide +kernel

@[answers "silmaril.wasm_components.gen.comp_b.has_world" thm]
theorem compB_hasWorld : silmaril.wasm_components.gen.comp_b.has_world :=
  ⟨_, rfl, rfl⟩

@[answers "silmaril.wasm_components.gen.linked.has_world" thm]
theorem linked_hasWorld : silmaril.wasm_components.gen.linked.has_world :=
  ⟨_, rfl, rfl⟩

@[answers "silmaril.wasm_components.gen.run.has_world" thm]
theorem run_hasWorld : silmaril.wasm_components.gen.run.has_world :=
  ⟨_, rfl, rfl⟩

@[answers "silmaril.wasm_components.gen.producer.returns_42" thm]
theorem producer_returns : silmaril.wasm_components.gen.producer.returns_42 :=
  Silmaril.Project.Shapes.Returns.of_value_kernel 100 (by decide +kernel)

/-! ## Two digests, one behaviour: `comp_b` and `run` -/

/-- The ascription of `run`'s export does not change the IR lowering. -/
theorem lower_run : Silmaril.Wasm.Component.Binary.lower runCert =
    Silmaril.Wasm.Component.Binary.lower compBCert := rfl

/-- **`comp_b` and `run` behave the same under every core semantics and names.** -/
theorem compB_run_behaviourEq (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (L : Silmaril.Wasi.Layout) :
    DigestBehaviourEq (irDen C L) silmaril.wasm_components.gen.comp_b silmaril.wasm_components.gen.run :=
  ⟨_, _, compB_is, run_is, by simp only [irDen, lower_run]⟩

@[answers "silmaril.wasm_components.gen.comp_b_run.behaviour_eq" thm]
theorem compB_run_behaviourEq_row : silmaril.wasm_components.gen.comp_b_run.behaviour_eq :=
  compB_run_behaviourEq topSem getRunLayout

@[answers "silmaril.wasm_components.gen.comp_b_run.distinct" thm]
theorem compB_run_distinct : silmaril.wasm_components.gen.comp_b_run.distinct :=
  Distinct.of_size (by decide +kernel)

/-! ## One release, two digests: `wasi:io@0.2.12` -/

@[answers "silmaril.wasm_components.wasi.io.v0_2_12.same_code" thm]
theorem io_same_code : silmaril.wasm_components.wasi.io.v0_2_12.same_code := by
  show SameCode silmaril.wasm_components.wasi.io.v0_2_12.oci silmaril.wasm_components.wasi.io.v0_2_12.fixture
  unfold SameCode
  decide +kernel

@[answers "silmaril.wasm_components.wasi.io.v0_2_12.distinct" thm]
theorem io_distinct : silmaril.wasm_components.wasi.io.v0_2_12.distinct :=
  Distinct.of_size (by decide +kernel)

/-- The code of the two `wasi:io@0.2.12` files is one, once they parse (under the open
`Task.parse_codeSections`). -/
theorem io_codeEq_of (hT : Task.parse_codeSections) {a b : Ast}
    (ha : silmaril.wasm_components.wasi.io.v0_2_12.oci.Is a)
    (hb : silmaril.wasm_components.wasi.io.v0_2_12.fixture.Is b) : CodeEq a b :=
  hT silmaril.wasm_components.wasi.io.v0_2_12.oci.bytes.data
    silmaril.wasm_components.wasi.io.v0_2_12.fixture.bytes.data a b
    (parse_of_is rfl ha) (parse_of_is rfl hb) io_same_code.2

/-- **One world** for the two `wasi:io@0.2.12` files, once they parse and one of them
projects (under `Task.parse_codeSections`). -/
theorem io_same_world_of (hT : Task.parse_codeSections) {a b : Ast}
    (ha : silmaril.wasm_components.wasi.io.v0_2_12.oci.Is a)
    (hb : silmaril.wasm_components.wasi.io.v0_2_12.fixture.Is b)
    (hw : (Silmaril.Wasm.Wit.Project.projectX a).isSome) :
    silmaril.wasm_components.wasi.io.v0_2_12.same_world :=
  ⟨a, ha, b, hb, hw, projectX_eq_of_codeEq (io_codeEq_of hT ha hb)⟩

/-- **One behaviour** for the two `wasi:io@0.2.12` files under every core semantics and names,
once they parse (under `Task.parse_codeSections`). -/
theorem io_behaviourEq_of (hT : Task.parse_codeSections) {a b : Ast}
    (ha : silmaril.wasm_components.wasi.io.v0_2_12.oci.Is a)
    (hb : silmaril.wasm_components.wasi.io.v0_2_12.fixture.Is b)
    (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod) (L : Silmaril.Wasi.Layout) :
    DigestBehaviourEq (irDen C L) silmaril.wasm_components.wasi.io.v0_2_12.oci
      silmaril.wasm_components.wasi.io.v0_2_12.fixture :=
  digestBehaviourEq_of_codeEq (irDen_stripCustom C L) ha hb (io_codeEq_of hT ha hb)

end Silmaril.Project.WasmComponents

end

silmaril load "silmaril/wasm-components/dag.toml"
