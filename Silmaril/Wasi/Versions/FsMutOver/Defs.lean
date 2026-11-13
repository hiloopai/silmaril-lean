module

public import Silmaril.Wasi.Versions.FsMut.Defs
public import Silmaril.Wasi.Versions.FsOver.Defs

@[expose] public section

/-!
# Filesystem mutations 0.3 over 0.2

A forwarder (`Silmaril.Wasi.Versions.FwdT`) from the 0.3 functions of the mutation theory
`FsMut.mutThV` (`get-directories`, `open-at`, `stat-at`, `set-times-at`, `create-directory-at`,
`remove-directory-at`, `unlink-file-at`, `rename-at`, `link-at`, `symlink-at`, `readlink-at`)
to the 0.2 functions of the same name. `mutThV` constrains only `ok` answers, which have the same
shape in both versions, so the forwarder passes them unchanged and translates error codes
(`FsOver.openTr`: `fsE2to3`). `FsMutOver.Thms.mut3Over2_model`: over every host of `mutTh2 T`
it is a model of `mutTh3 T`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.FsMutOver

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions (fwdT)
open Silmaril.Wasi.Versions.FsMore
open Silmaril.Wasi.Versions.FsMut

/-- The method names of the slice. -/
def mutMethods : List String :=
  ["[method]descriptor.open-at", "[method]descriptor.stat-at", "[method]descriptor.set-times-at",
   "[method]descriptor.create-directory-at", "[method]descriptor.remove-directory-at",
   "[method]descriptor.unlink-file-at", "[method]descriptor.rename-at",
   "[method]descriptor.link-at", "[method]descriptor.symlink-at",
   "[method]descriptor.readlink-at"]

/-- The 0.3 functions exported. -/
def mutX3 : Set FnName := {f | f = v3.getDirs ∨ (f.iface = v3.types ∧ f.fn ∈ mutMethods)}

/-- The 0.2 functions imported. -/
def mutI2 : Set FnName := {f | f = v2.getDirs ∨ (f.iface = v2.types ∧ f.fn ∈ mutMethods)}

/-- The 0.2 function of a 0.3 one: the same name in the 0.2 interface. -/
def mto (f : FnName) : FnName := if f = v3.getDirs then v2.getDirs else ⟨v2.types, f.fn⟩

theorem mto_mem : ∀ f ∈ mutX3, mto f ∈ mutI2 := by
  intro f hf
  rcases hf with h | ⟨_, hm⟩
  · left; simp [mto, h]
  · by_cases h : f = v3.getDirs
    · left; simp [mto, h]
    · right; simp [mto, h, hm]

/-- **Filesystem mutations 0.3 over 0.2.** -/
def mut3Over2 := fwdT mutX3 mutI2 mto mto_mem fun _ r => FsOver.openTr r

end Silmaril.Wasi.Versions.FsMutOver
