module

public import Silmaril.Elf.Staged.Example.Thms
-- Native runs interpret the objects, the bytes and the checkers while elaborating.
public meta import Silmaril.Elf.Staged.Example.Thms
public meta import Silmaril.Prelude.Trust.Elab.Defs

/-! # ELF leaves under each trust profile

The same propositions as `Silmaril.Elf.Staged.Example.Thms`, proved under each profile, with
their audits:

* **default**: `elf.layout` is in the `default` set, so it runs natively on the `ByteArray`;
  `elf.loader` is not, so the kernel checks it on the kernel bytes;
* **local** (every procedure in the scope's `max`): the leaves run natively;
* **paranoid**: every leaf is checked by the kernel, no native axiom;
* a **kernel-only** leaf (no `native :=`) is checked by the kernel even under `local`;
* an **unsupported** leaf (`elf.dwarf.line`, not registered) is an error;
* a **false** native check is an error under `local`: it does not fall back to the kernel.
-/

@[expose] public section

-- These tests check each profile's behaviour, so they fix the profile they start from.
set_option silmaril.trust.profile "default"

namespace Silmaril.Elf.Staged.Example.Profiles

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Example

-- Kernel bytes for this module's kernel runs (a `kbytes_def` body is not exported yet).
kbytes_def kb of_include helloRaw

/-- Default profile, in the `default` set: native. -/
theorem layout_default : LayoutIs F L := by
  elf_leaf elf.layout (native := Native.layout_sound)
    (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq)

/-- Default profile, not in the `default` set: kernel. -/
theorem loader_default : LoaderIs F L ld := by
  elf_leaf elf.loader (native := Native.loader_sound (c := (L, ld)))
    (kernel := Kernel.loader_sound kb.wf kb.toByteArray_eq (c := (L, ld)))

set_option silmaril.trust.profile "local" in
/-- Local profile: native. -/
theorem loader_local : LoaderIs F L ld := by
  elf_leaf elf.loader (native := Native.loader_sound (c := (L, ld)))
    (kernel := Kernel.loader_sound kb.wf kb.toByteArray_eq (c := (L, ld)))

set_option silmaril.trust.profile "local" in
/-- Local profile: the code of `main`, natively decoded. -/
theorem main_local : TilesAt F x86Ok 4192 mainTiles := by
  elf_leaf elf.tiles.x86 (native := Native.tilesX86_sound (c := (4192, mainTiles)))
    (kernel := Kernel.tilesX86_sound kb.wf kb.toByteArray_eq (c := (4192, mainTiles)))

set_option silmaril.trust.profile "paranoid" in
/-- Paranoid profile: the kernel, even for `elf.layout`. -/
theorem layout_paranoid : LayoutIs F L := by
  elf_leaf elf.layout (native := Native.layout_sound)
    (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq)

set_option silmaril.trust.profile "local" in
/-- Kernel-only: no native checker is given, so the kernel checks it under `local` too. -/
theorem layout_kernelOnly : LayoutIs F L := by
  elf_leaf elf.layout (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq)

/-- A layout with a wrong entry point. -/
def badL : Layout := { L with header := { L.header with entry := 0 } }

/-- error: elf_leaf: elf.dwarf.line is not a registered ELF procedure (unsupported leaf) -/
#guard_msgs in
example : LayoutIs F L := by
  elf_leaf elf.dwarf.line (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq)

-- A false native check fails under `local`; it is not retried in the kernel.
/-- error: edge_decide: elf.layout evaluated to false -/
#guard_msgs (substring := true) in
set_option silmaril.trust.profile "local" in
example : LayoutIs F badL := by
  elf_leaf elf.layout (native := Native.layout_sound)
    (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq)

-- The same false claim fails in the kernel under `paranoid`.
/-- error: elf_leaf: the kernel did not check elf.layout -/
#guard_msgs (substring := true) in
set_option silmaril.trust.profile "paranoid" in
example : LayoutIs F badL := by
  elf_leaf elf.layout (native := Native.layout_sound)
    (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq)

/-! ## Audits and recorded uses -/

-- The default-profile layout ran natively: its own native procedure and axiom.
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.layout_default","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":["_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.layout_default._native.edge.elf.layout.ax_1_1"],"own_native":["elf.layout"]}
-/
#guard_msgs in
trust_audit layout_default

set_option silmaril.trust.profile "local" in
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.loader_local","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":["_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.loader_local._native.edge.elf.loader.ax_1_1"],"own_native":["elf.loader"]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.main_local","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":["_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.main_local._native.edge.elf.tiles.x86.ax_1_1"],"own_native":["elf.tiles.x86"]}
-/
#guard_msgs in
trust_audit loader_local main_local

/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.loader_default","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":[],"own_native":[]}
-/
#guard_msgs in
trust_audit loader_default

set_option silmaril.trust.profile "paranoid" in
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.layout_paranoid","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":[],"own_native":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.layout_kernelOnly","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":[],"own_native":[]}
-/
#guard_msgs in
trust_audit layout_paranoid layout_kernelOnly

/-- The recorded uses of this module: one per leaf proof, with its mode. -/
meta def usesHere : Lean.CoreM (List String) := do
  let env ← Lean.getEnv
  let us := Silmaril.Trust.allEntries Silmaril.Trust.useExt env
  return (us.filter (·.module == env.mainModule)).toList.map fun u =>
    s!"{u.decl.componentsRev.head!} {u.proc} {match u.mode with | .native => "native" | .kernel => "kernel"} {u.profile} {u.ax.isSome}"

/--
info: layout_default elf.layout native default true
loader_default elf.loader kernel default false
loader_local elf.loader native local true
main_local elf.tiles.x86 native local true
layout_paranoid elf.layout kernel paranoid false
layout_kernelOnly elf.layout kernel local false
-/
#guard_msgs in
run_meta do Lean.logInfo ("\n".intercalate (← usesHere))

end Silmaril.Elf.Staged.Example.Profiles
