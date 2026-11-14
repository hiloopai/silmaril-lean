module

public import Silmaril.Project.WasmComponents.Registry.Defs
public import Silmaril.Project.WasmComponents.Thms
public import Silmaril.Project.Components.Thms

/-!
# The Wasm components pilot: studying by hash

* **Two digests, one behaviour** (`compB_run_twoDigests`): `gen.comp_b` and `gen.run` are pinned
  by their releases (`Release.Pins`, SHA-256 in the kernel, about 1 s each), the digests
  differ, so the files differ (`Release.bytes_ne_of_digest_ne`, no assumption), and they
  behave the same under every core semantics (`compB_run_behaviourEq`).
* **One release, two digests** (`io_oneReleaseTwoDigests`): the published `wasi:io@0.2.12` and
  Silmaril's fixture name one release with different digests. That the files are the ones these
  digests pin is rule P1 of `sil project check` (SHA-256 of 15 KB is over the kernel budget);
  given it, the files differ (`io_bytes_ne_of_pins`), which `io_distinct` also shows from the
  sizes.
* **Not a reproducibility finding** (`io_not_finding`): whatever source the published file was
  built from, it and the fixture are no finding, as their toolchains differ; the recorded builds
  (`ioFixtureBuild`, `ioReencodeBuild`) are reproducible (`io_builds_reproducible`: no two
  share a recipe). The two digests are explained by the toolchain and the custom sections the
  publisher adds, not by a non-deterministic build.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents

open Silmaril.Project.Components
open Silmaril.Project.Shapes.Component

/-! ## Two digests, one behaviour -/

theorem compB_pins : compBRelease.Pins silmaril.wasm_components.gen.comp_b.bytes := by
  decide +kernel

theorem run_pins : runRelease.Pins silmaril.wasm_components.gen.run.bytes := by
  decide +kernel

theorem compB_run_digest_ne : compBRelease.digest ≠ runRelease.digest := by
  decide +kernel

/-- **Two digests, one behaviour**: the releases `silmaril:comp-b@0.1.0` and `silmaril:run@0.1.0`
pin different files, which behave the same under every core semantics and names. -/
theorem compB_run_twoDigests
    (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod) (L : Silmaril.Wasi.Layout) :
    silmaril.wasm_components.gen.comp_b.bytes ≠ silmaril.wasm_components.gen.run.bytes ∧
      DigestBehaviourEq (irDen C L) silmaril.wasm_components.gen.comp_b silmaril.wasm_components.gen.run :=
  ⟨Release.bytes_ne_of_digest_ne compB_pins run_pins compB_run_digest_ne,
    compB_run_behaviourEq C L⟩

/-! ## One release, two digests -/

theorem io_oneReleaseTwoDigests :
    ioOciRelease.pkg = ioFixtureRelease.pkg ∧ ioOciRelease.digest ≠ ioFixtureRelease.digest :=
  ⟨rfl, by decide +kernel⟩

theorem io_ref : ioOciRelease.ref = "wasi:io@0.2.12" := by decide +kernel

/-- Given the digests (rule P1 of `sil project check`), the two files differ. -/
theorem io_bytes_ne_of_pins (h₁ : ioOciRelease.Pins silmaril.wasm_components.wasi.io.v0_2_12.oci.bytes)
    (h₂ : ioFixtureRelease.Pins silmaril.wasm_components.wasi.io.v0_2_12.fixture.bytes) :
    silmaril.wasm_components.wasi.io.v0_2_12.oci.bytes ≠
      silmaril.wasm_components.wasi.io.v0_2_12.fixture.bytes :=
  Release.bytes_ne_of_digest_ne h₁ h₂ io_oneReleaseTwoDigests.2

/-! ## Reproducibility -/

/-- **Not a reproducibility finding**, whatever the published file's source. -/
theorem io_not_finding (s : Digest) : ¬ ReproducibilityFinding (ioOciBuild s) ioFixtureBuild := by
  rintro ⟨h, -⟩
  have h' := congrArg (fun r => r.2.1) h
  simp [Build.recipe, ioOciBuild, ioFixtureBuild] at h'

theorem io_builds_findings : findings [ioFixtureBuild, ioReencodeBuild] = [] := by decide +kernel

/-- The recorded builds of the fixture's digest are reproducible. -/
theorem io_builds_reproducible : Reproducible [ioFixtureBuild, ioReencodeBuild] :=
  findings_eq_nil_iff.mp io_builds_findings

end Silmaril.Project.WasmComponents

end
