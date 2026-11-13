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
* when the profile allows the **kernel side's** procedure but not the native side's, the kernel
  side is still checked by the kernel (`edge_pair` never runs it natively);
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
  edge_pair (native := Native.layout_sound (raw := helloRaw) (L := L))
    (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq (L := L))

/-- Default profile, not in the `default` set: kernel. -/
theorem loader_default : LoaderIs F L ld := by
  edge_pair (native := Native.loader_sound (raw := helloRaw) (c := (L, ld)))
    (kernel := Kernel.loader_sound kb.wf kb.toByteArray_eq (c := (L, ld)))

set_option silmaril.trust.profile "local" in
/-- Local profile: native. -/
theorem loader_local : LoaderIs F L ld := by
  edge_pair (native := Native.loader_sound (raw := helloRaw) (c := (L, ld)))
    (kernel := Kernel.loader_sound kb.wf kb.toByteArray_eq (c := (L, ld)))

set_option silmaril.trust.profile "local" in
/-- Local profile: the code of `main`, natively decoded. -/
theorem main_local : TilesAt F x86Ok 4192 mainTiles := by
  edge_pair (native := Native.tilesX86_sound (raw := helloRaw) (c := (4192, mainTiles)))
    (kernel := Kernel.tilesX86_sound kb.wf kb.toByteArray_eq (c := (4192, mainTiles)))

set_option silmaril.trust.profile "paranoid" in
/-- Paranoid profile: the kernel, even for `elf.layout`. -/
theorem layout_paranoid : LayoutIs F L := by
  edge_pair (native := Native.layout_sound (raw := helloRaw) (L := L))
    (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq (L := L))

/-- A profile that allows only the kernel side's procedure natively. -/
trust_set elfKernelSide := {elf.layout.kernel}

set_option silmaril.trust.profile "elfKernelSide" in
/-- The native side is denied and the kernel side's procedure is allowed: the kernel side is
still checked by the kernel, never run natively. -/
theorem layout_kernelSide : LayoutIs F L := by
  edge_pair (native := Native.layout_sound (raw := helloRaw) (L := L))
    (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq (L := L))

/-- A layout with a wrong entry point. -/
def badL : Layout := { L with header := { L.header with entry := 0 } }

-- An unsupported leaf has no registered procedure.
/-- error: edge_decide: unknown native procedure elf.dwarf.line -/
#guard_msgs in
example : Kernel.layout kb L = true := by edge_decide elf.dwarf.line

-- A false native check fails under `local`; it is not retried in the kernel.
/-- error: edge_decide: elf.layout evaluated to false -/
#guard_msgs (substring := true) in
set_option silmaril.trust.profile "local" in
example : LayoutIs F badL := by
  edge_pair (native := Native.layout_sound (raw := helloRaw) (L := badL))
    (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq (L := badL))

-- The same false claim fails in the kernel under `paranoid`.
/-- error: edge_decide: the kernel did not check elf.layout.kernel -/
#guard_msgs (substring := true) in
set_option silmaril.trust.profile "paranoid" in
example : LayoutIs F badL := by
  edge_pair (native := Native.layout_sound (raw := helloRaw) (L := badL))
    (kernel := Kernel.layout_sound kb.wf kb.toByteArray_eq (L := badL))

/-! ## Audits and recorded uses -/

-- The default-profile layout ran natively: its own native procedure and axiom.
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.layout_default","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":["_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.layout_default._native.edge.elf.layout.ax_1_1"],"own_native":["elf.layout"],"profile":"default","schema":"silmaril.trust.v1"}
-/
#guard_msgs in
trust_audit layout_default

set_option silmaril.trust.profile "local" in
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.loader_local","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":["_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.loader_local._native.edge.elf.loader.ax_1_1"],"own_native":["elf.loader"],"profile":"local","schema":"silmaril.trust.v1"}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.main_local","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":["_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.main_local._native.edge.elf.tiles.x86.ax_1_1"],"own_native":["elf.tiles.x86"],"profile":"local","schema":"silmaril.trust.v1"}
-/
#guard_msgs in
trust_audit loader_local main_local

/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.loader_default","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1"}
-/
#guard_msgs in
trust_audit loader_default

set_option silmaril.trust.profile "paranoid" in
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.layout_paranoid","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":[],"own_native":[],"profile":"paranoid","schema":"silmaril.trust.v1"}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.layout_kernelSide","dep_native":[],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":[],"own_native":[],"profile":"paranoid","schema":"silmaril.trust.v1"}
-/
#guard_msgs in
trust_audit layout_paranoid layout_kernelSide

/-- The recorded uses of this module: one per leaf proof, with its mode. -/
meta def usesHere : Lean.CoreM (List String) := do
  let env ← Lean.getEnv
  let us := Silmaril.Trust.allEntries Silmaril.Trust.useExt env
  return (us.filter (·.module == env.mainModule)).toList.map fun u =>
    s!"{u.decl.componentsRev.head!} {u.proc} {match u.mode with | .native => "native" | .kernel => "kernel"} {u.profile} {u.ax.isSome}"

/--
info: layout_default elf.layout native default true
loader_default elf.loader.kernel kernel default false
loader_local elf.loader native local true
main_local elf.tiles.x86 native local true
layout_paranoid elf.layout.kernel kernel paranoid false
layout_kernelSide elf.layout.kernel kernel elfKernelSide false
-/
#guard_msgs in
run_meta do Lean.logInfo ("\n".intercalate (← usesHere))

end Silmaril.Elf.Staged.Example.Profiles
