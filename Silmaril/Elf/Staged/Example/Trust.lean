module

public import Silmaril.Data.IncludeBytes
public import Silmaril.Elf.Staged.Example.Thms
public import Silmaril.Elf.Staged.Leaf.Registry
public import Silmaril.Prelude.Trust.Policy.Defs
-- Native runs interpret the leaf checkers, the certificates and the included bytes.
meta import Silmaril.Elf.Staged.Leaf.Thms
meta import Silmaril.Elf.Staged.Example.Defs
meta import Silmaril.Data.IncludeBytes.Types

/-! # The staged `hello-gcc` checks under the trust policy

The propositions of `Silmaril.Elf.Staged.Example` (layout, loader, a section body, the symbol
indexes, and `main`'s seven x86 tiles), each proved by `sil_check` with both runs of its leaf.
In the default profile only `elf.layout` (in the `default` trust set) runs natively; the others
use their kernel runs. Under `local`, every leaf runs natively. The audits at the end show which
proofs carry a native axiom, and that each axiom is bound to its leaf.

The native runs read a computable copy of the file (`helloC`). It is the same `include_bytes`
term as `PinBytes.helloGcc`, so `blobOf helloC` is `F` by unfolding (`helloC_eq`).
-/

@[expose] public section

-- These tests check each profile's behaviour, so they fix the profile they start from.
set_option silmaril.trust.profile "default"

namespace Silmaril.Elf.Staged.Example.Trust

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Example

/-- The pinned file, computable, for native runs. -/
def helloC : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../examples/dyn/pinned/hello-gcc"⟩

theorem helloC_eq : helloC = Silmaril.Elf.Link.Dyn.PinBytes.helloGcc := rfl

/-- `elf.layout`: native in the default profile. -/
theorem layout' : LayoutIs F L := by
  sil_check elf.layout (native := Leaf.of_native Leaf.layout (b := helloC) (c := L))
    (kernel := Leaf.of_kernel Leaf.layout hc (c := L))

/-- `elf.loader`: the kernel run in the default profile. -/
theorem loader' : LoaderIs F L ld := by
  sil_check elf.loader (native := Leaf.of_native Leaf.loader (b := helloC) (c := (L, ld)))
    (kernel := Leaf.of_kernel Leaf.loader hc (c := (L, ld)))

-- `elf.loader` natively, under `local`.
set_option silmaril.trust.profile "local" in
theorem loaderNative : LoaderIs F L ld := by
  sil_check elf.loader (native := Leaf.of_native Leaf.loader (b := helloC) (c := (L, ld)))
    (kernel := Leaf.of_kernel Leaf.loader hc (c := (L, ld)))

-- `elf.symbols.byName` natively, under `local`.
set_option silmaril.trust.profile "local" in
theorem byNameNative : byName.sorted = true ∧ byName.Sound F := by
  sil_check elf.symbols.byName (native := Leaf.of_native Leaf.byName (b := helloC) (c := byName))
    (kernel := Leaf.of_kernel Leaf.byName hc (c := byName))

-- `main`'s seven tiles are x86 instructions (`elf.tiles.x86`), natively under `local`.
set_option silmaril.trust.profile "local" in
theorem mainTilesNative : TilesAt F x86Ok 4192 mainTiles := by
  sil_check elf.tiles.x86
    (native := Leaf.of_native Leaf.tilesX86 (b := helloC) (c := (4192, mainTiles)))
    (kernel := Leaf.of_kernel Leaf.tilesX86 hc (c := (4192, mainTiles)))

-- The registry entry is bound to its leaf: `elf.layout` does not accept a run of `elf.loader`.
/--
error: sil_check elf.layout: the kernel check is not bound to Silmaril.Elf.Staged.Leaf.layout
  Leaf.loader.kernel pg (L, ld)
-/
#guard_msgs in
example : LoaderIs F L ld := by
  sil_check elf.layout (kernel := Leaf.of_kernel Leaf.loader hc (c := (L, ld)))

set_option silmaril.trust.profile "local" in
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Trust.layout'","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Trust","native_axioms":["_private.Silmaril.Elf.Staged.Example.Trust.0.Silmaril.Elf.Staged.Example.Trust.layout'._native.edge.elf.layout.ax_1_1"],"own_native":["elf.layout"],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Trust.loader'","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Trust","native_axioms":[],"own_native":[],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Trust.loaderNative","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Trust","native_axioms":["_private.Silmaril.Elf.Staged.Example.Trust.0.Silmaril.Elf.Staged.Example.Trust.loaderNative._native.edge.elf.loader.ax_1_1"],"own_native":["elf.loader"],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Trust.byNameNative","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Trust","native_axioms":["_private.Silmaril.Elf.Staged.Example.Trust.0.Silmaril.Elf.Staged.Example.Trust.byNameNative._native.edge.elf.symbols.byName.ax_1_1"],"own_native":["elf.symbols.byName"],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Trust.mainTilesNative","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Trust","native_axioms":["_private.Silmaril.Elf.Staged.Example.Trust.0.Silmaril.Elf.Staged.Example.Trust.mainTilesNative._native.edge.elf.tiles.x86.ax_1_1"],"own_native":["elf.tiles.x86"],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
-/
#guard_msgs in
trust_audit layout' loader' loaderNative byNameNative mainTilesNative

end Silmaril.Elf.Staged.Example.Trust
