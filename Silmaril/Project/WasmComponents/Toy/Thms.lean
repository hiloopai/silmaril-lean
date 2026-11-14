module

public import Silmaril.Project.WasmComponents.Toy.Defs
public import Silmaril.Project.WasmComponents.Ref.Thms
public import Silmaril.Project.WasmComponents.Thms
public import Silmaril.Wasm.Resource.CompToy.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Wit.Tool.Defs

/-!
# The Wasm components pilot: the resource-provider toy

Two releases of the toy component defining a resource (`Silmaril.Wasm.Resource.CompToy`), written
by `examples/wasm-components/gen/Toy.lean` and registered by `sil project components add`:

* `gen.toy` (`lean/toy.wasm`, 295 B): `Toy.toyAst`, a certificate under
  `wasm.component.binary`; its world `gen.toy.world` (`lean/toy.world.wasm`, written by
  `wasm-wit project`), the certificate `Wit.Tool.worldAst Toy.toyWorld`;
* `gen.toy_split` (`lean/toy-split.wasm`, 319 B): `Toy.toySplitAst`, the same items one per
  section. `wasm-wit project` writes the same world file for it (byte for byte, so one
  artifact: `sil project lock` refuses a second name for one digest).

Proved here, in the kernel or from proved theorems:

* the certificates (`Binary.encode` of the ASTs is the files), hence their `parses`;
* `valid` and `has_world` (`toyWorld`: the resource `r` exported as `(sub resource)` and the
  functions `make`, `get`, `drop` over `own<r>` and `borrow<r>`) of both releases;
* both releases read as the reference component `CompToy.toyComp` (`toRef_toy`,
  `toRef_toySplit`: `Ref.toRef?`, decoding the core module, by kernel evaluation);
* **`toy_wasiSat`**, **`toy_wasiEveryHost`**: at every profile `P` and choice profile `prof`, the
  reference denotation of `gen.toy` satisfies the provider guarantee `toyGuar` (`make` never
  returns a live handle) under every WASI theory, and over every host of every theory. Both
  come from `CompToy.toy_compProvider` (the toy is a correct provider over `refMultiSem`) by
  `Ref.wasiSat_refDen`;
* **`toySplit_upgrades`**: `gen.toy_split` is an upgrade-compatible successor of `gen.toy` at
  their (one) world: its denotation is the same model (`toyDen_split`), at every `P` and
  `prof`; `toy_split_behaviourEq`: the two releases, at different digests, behave the same.

The rows are at the specification profile and nondeterministic choices (`toyDenSpec`), under the
trivial theory `topP` (the toy has no imports; the theorems hold for every theory).

What the denotation sees, and what it does not: the WASI view `Ref.wval` keeps scalars and
handles and replaces other values by a placeholder; `refMultiSem` observes resolved calls one
after the other on one instance (`Silmaril.Wasm.Spec.Component.RefMulti`). That the model has a
play with a `make` return is not proved at `core3P P`: the executable session of the toy
(`CompToy.toySession_trace`) runs on the engine `core3 neverFail`.
-/

open Silmaril.Project (Value)

silmaril_artifacts_refresh "silmaril/artifacts.toml"

/-- The component `lean/toy.wasm`: `Toy.toyAst`. -/
@[expose, value "silmaril.wasm_components.gen.toy" (format := wasm.component.binary)
  (source := silmaril.wasm_components.gen.toy.blob)
  (doc := "The resource provider toy (Silmaril.Wasm.Resource.CompToy) as a binary component")]
public def Silmaril.Project.WasmComponents.Toy.toyCert : Silmaril.Wasm.Component.Binary.Ast :=
  Silmaril.Project.WasmComponents.Toy.toyAst

/-- The component `lean/toy-split.wasm`: `Toy.toySplitAst`. -/
@[expose, value "silmaril.wasm_components.gen.toy_split" (format := wasm.component.binary)
  (source := silmaril.wasm_components.gen.toy_split.blob)
  (doc := "The resource provider toy with one item per section (a second release)")]
public def Silmaril.Project.WasmComponents.Toy.toySplitCert : Silmaril.Wasm.Component.Binary.Ast :=
  Silmaril.Project.WasmComponents.Toy.toySplitAst

/-- The world file of both releases (`wasm-wit project`): the component type `toyWorld`. -/
@[expose, value "silmaril.wasm_components.gen.toy.world" (format := wasm.component.binary)
  (source := silmaril.wasm_components.gen.toy.world.blob)
  (doc := "The world of silmaril.wasm_components.gen.toy and gen.toy_split (wasm-wit project)")]
public def Silmaril.Project.WasmComponents.Toy.toyWorldCert : Silmaril.Wasm.Component.Binary.Ast :=
  Silmaril.Wasm.Wit.Tool.worldAst Silmaril.Project.WasmComponents.Toy.toyWorld

-- the rows
silmaril instance silmaril.wasm_components.gen.toy.valid (expect := "THM") :=
  silmaril.shapes.component.valid (c := Silmaril.Project.WasmComponents.Toy.toyCert)
silmaril instance silmaril.wasm_components.gen.toy_split.valid (expect := "THM") :=
  silmaril.shapes.component.valid (c := Silmaril.Project.WasmComponents.Toy.toySplitCert)
silmaril instance silmaril.wasm_components.gen.toy.has_world (expect := "THM") :=
  silmaril.shapes.component.has_world (c := Silmaril.Project.WasmComponents.Toy.toyCert)
  (W := Silmaril.Project.WasmComponents.Toy.toyWorld)
silmaril instance silmaril.wasm_components.gen.toy_split.has_world (expect := "THM") :=
  silmaril.shapes.component.has_world (c := Silmaril.Project.WasmComponents.Toy.toySplitCert)
  (W := Silmaril.Project.WasmComponents.Toy.toyWorld)
silmaril instance silmaril.wasm_components.gen.toy.provider (expect := "THM") :=
  silmaril.shapes.component.wasi_sat
  (σ := Silmaril.Project.WasmComponents.Toy.toyDenSpec Silmaril.Project.WasmComponents.Toy.toyCert)
  (T := Silmaril.Wasi.topP) (G := Silmaril.Project.WasmComponents.Toy.toyGuar)
silmaril instance silmaril.wasm_components.gen.toy.provider_every_host (expect := "THM") :=
  silmaril.shapes.component.wasi_every_host
  (σ := Silmaril.Project.WasmComponents.Toy.toyDenSpec Silmaril.Project.WasmComponents.Toy.toyCert)
  (T := Silmaril.Wasi.topP) (G := Silmaril.Project.WasmComponents.Toy.toyGuar)
silmaril instance silmaril.wasm_components.gen.toy_split.upgrade (expect := "THM") :=
  silmaril.shapes.component.upgrade_compatible (f := Silmaril.Project.WasmComponents.Toy.toyUpgrade)
  (v₂ := Silmaril.Project.WasmComponents.Toy.toyDenSpec Silmaril.Project.WasmComponents.Toy.toySplitCert)
  (v₁ := Silmaril.Project.WasmComponents.Toy.toyDenSpec Silmaril.Project.WasmComponents.Toy.toyCert)
silmaril instance silmaril.wasm_components.gen.toy_split.behaviour_eq (expect := "THM") :=
  silmaril.shapes.component.digest_behaviour_eq (den := Silmaril.Project.WasmComponents.Toy.toyDenSpec)
  (X := silmaril.wasm_components.gen.toy) (Y := silmaril.wasm_components.gen.toy_split)
silmaril instance silmaril.wasm_components.gen.toy_split.distinct (expect := "THM") :=
  silmaril.wasm_components.distinct (X := silmaril.wasm_components.gen.toy)
  (Y := silmaril.wasm_components.gen.toy_split)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Toy

open Silmaril.Wasm.Component.Binary (Ast)
open Silmaril.Project.Shapes.Component
open Silmaril.Wasm.Resource.CompToy (toyComp toyProgP toy_compProvider)

/-! ## Certificates -/

@[solves "silmaril.wasm_components.gen.toy.is"]
theorem toy_is : silmaril.wasm_components.gen.toy.is :=
  is_of_encode rfl (by kernel_rfl)

@[solves "silmaril.wasm_components.gen.toy_split.is"]
theorem toySplit_is : silmaril.wasm_components.gen.toy_split.is :=
  is_of_encode rfl (by kernel_rfl)

@[solves "silmaril.wasm_components.gen.toy.world.is"]
theorem toyWorld_is : silmaril.wasm_components.gen.toy.world.is :=
  is_of_encode rfl (by decide +kernel)

@[solves "silmaril.wasm_components.gen.toy.parses"]
theorem toy_parses : silmaril.wasm_components.gen.toy.parses := Silmaril.Project.Value.parses_of_is toy_is

@[solves "silmaril.wasm_components.gen.toy_split.parses"]
theorem toySplit_parses : silmaril.wasm_components.gen.toy_split.parses :=
  Silmaril.Project.Value.parses_of_is toySplit_is

@[solves "silmaril.wasm_components.gen.toy.world.parses"]
theorem toyWorld_parses : silmaril.wasm_components.gen.toy.world.parses :=
  Silmaril.Project.Value.parses_of_is toyWorld_is

/-! ## Valid, has world -/

@[answers "silmaril.wasm_components.gen.toy.valid" thm]
theorem row_toy_valid : silmaril.wasm_components.gen.toy.valid := by
  show CompValid toyCert
  unfold CompValid
  decide +kernel

@[answers "silmaril.wasm_components.gen.toy_split.valid" thm]
theorem row_toySplit_valid : silmaril.wasm_components.gen.toy_split.valid := by
  show CompValid toySplitCert
  unfold CompValid
  decide +kernel

/-- The projection of the toy is `toyWorld`. -/
theorem projectX_toy : Silmaril.Wasm.Wit.Project.projectX toyCert = some toyWorld := by
  kernel_rfl

/-- … and so is the projection of the second release. -/
theorem projectX_toySplit : Silmaril.Wasm.Wit.Project.projectX toySplitCert = some toyWorld := by
  kernel_rfl

@[answers "silmaril.wasm_components.gen.toy.has_world" thm]
theorem row_toy_hasWorld : silmaril.wasm_components.gen.toy.has_world :=
  ⟨_, projectX_toy, rfl⟩

@[answers "silmaril.wasm_components.gen.toy_split.has_world" thm]
theorem row_toySplit_hasWorld : silmaril.wasm_components.gen.toy_split.has_world :=
  ⟨_, projectX_toySplit, rfl⟩

/-! ## The reference reading -/

/-- **The binary toy reads as the reference toy** (the core module decoded in the kernel). -/
theorem toRef_toy : Ref.toRef? toyCert = some toyComp := by kernel_rfl

/-- **So does the second release.** -/
theorem toRef_toySplit : Ref.toRef? toySplitCert = some toyComp := by kernel_rfl

/-- The WASI names of the toy's exports are distinct. -/
theorem toyFnE_injective : Function.Injective toyFnE := by decide

/-- The two releases have one denotation, at every profile and choice profile. -/
theorem toyDen_split (P : Silmaril.Wasm.Numerics.Profile) (prof : Silmaril.Wasm.Component.ProfileKind) :
    toyDen P prof toySplitCert = toyDen P prof toyCert := by
  unfold toyDen
  rw [Ref.refDen_of_toRef toRef_toySplit, Ref.refDen_of_toRef toRef_toy]

/-! ## A correct provider, as a WASI component -/

/-- **The toy satisfies the provider guarantee under every WASI theory**, at every profile and
choice profile (from `toy_compProvider`). -/
theorem toy_wasiSat (P : Silmaril.Wasm.Numerics.Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    {S : Type} (T : Silmaril.Wasm.Resource.Protocol S Silmaril.Wasi.WEv) :
    WasiSat (toyDen P prof toyCert) T toyGuar :=
  Ref.wasiSat_refDen toyFnE_injective toRef_toy (toy_compProvider P prof) T

/-- **… and over every host of every theory.** -/
theorem toy_wasiEveryHost (P : Silmaril.Wasm.Numerics.Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) {S : Type}
    (T : Silmaril.Wasm.Resource.Protocol S Silmaril.Wasi.WEv) :
    WasiEveryHost (toyDen P prof toyCert) T toyGuar :=
  Ref.wasiEveryHost_refDen toyFnE_injective toRef_toy (toy_compProvider P prof) T

@[answers "silmaril.wasm_components.gen.toy.provider" thm]
theorem row_toy_provider : silmaril.wasm_components.gen.toy.provider :=
  toy_wasiSat _ _ _

@[answers "silmaril.wasm_components.gen.toy.provider_every_host" thm]
theorem row_toy_provider_every_host : silmaril.wasm_components.gen.toy.provider_every_host :=
  toy_wasiEveryHost _ _ _

/-! ## Two releases -/

/-- **The second release is an upgrade-compatible successor of the first**, at every profile
and choice profile. -/
theorem toySplit_upgrades (P : Silmaril.Wasm.Numerics.Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) :
    UpgradeCompatible toyUpgrade (toyDen P prof toySplitCert) (toyDen P prof toyCert) :=
  UpgradeCompatible.of_refines (le_of_eq (toyDen_split P prof))

@[answers "silmaril.wasm_components.gen.toy_split.upgrade" thm]
theorem row_toySplit_upgrade : silmaril.wasm_components.gen.toy_split.upgrade :=
  toySplit_upgrades _ _

/-- **Two digests, one behaviour**, at every profile and choice profile. -/
theorem toy_split_behaviourEq (P : Silmaril.Wasm.Numerics.Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) :
    DigestBehaviourEq (toyDen P prof) silmaril.wasm_components.gen.toy
      silmaril.wasm_components.gen.toy_split :=
  ⟨_, _, toy_is, toySplit_is, (toyDen_split P prof).symm⟩

@[answers "silmaril.wasm_components.gen.toy_split.behaviour_eq" thm]
theorem row_toySplit_behaviourEq : silmaril.wasm_components.gen.toy_split.behaviour_eq :=
  toy_split_behaviourEq _ _

@[answers "silmaril.wasm_components.gen.toy_split.distinct" thm]
theorem row_toySplit_distinct : silmaril.wasm_components.gen.toy_split.distinct :=
  Distinct.of_size (by decide +kernel)

end Silmaril.Project.WasmComponents.Toy

end

silmaril load "silmaril/wasm-components/toy-dag.toml"
