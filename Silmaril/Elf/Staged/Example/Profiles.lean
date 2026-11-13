module

public import Silmaril.Elf.Staged.Example.Thms
-- Native runs interpret the objects, the bytes and the checkers while elaborating.
public meta import Silmaril.Elf.Staged.Example.Thms
public meta import Silmaril.Prelude.Trust.Elab.Defs

/-! # ELF leaves under each trust profile

The same propositions as `Silmaril.Elf.Staged.Example.Thms`, proved under each profile, with
their audits:

* **default**: `elf.layout` is in the `default` set (core's policy), so it runs natively on the `ByteArray`;
  `elf.loader` is not, so the kernel checks it on the kernel bytes;
* **local** (every procedure in the scope's `max`): the leaves run natively;
* **paranoid**: every leaf is checked by the kernel, no native axiom;
* a **kernel-only** check (no native backend given) is checked by the kernel even under
  `local`;
* an **unsupported** leaf (`elf.dwarf.line`, not registered) is an error;
* a **false** native check is an error under `local`: it does not fall back to the kernel.
-/

@[expose] public section

-- These tests check each profile's behaviour, so they fix the profile they start from.
set_option silmaril.trust.profile "default"

namespace Silmaril.Elf.Staged.Example.Profiles

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Example

/-- Default profile, in the `default` set: native. -/
theorem layout_default : LayoutIs F L := by
  sil_check elf.layout (native := Native.layout_sound (raw := helloRaw) (L := L))
    (kernel := Kernel.layout_sound hello.wf_true hello.toByteArray_eq (L := L))

/-- Default profile, not in the `default` set: kernel. -/
theorem loader_default : LoaderIs F L ld := by
  sil_check elf.loader (native := Native.loader_sound (raw := helloRaw) (c := (L, ld)))
    (kernel := Kernel.loader_sound hello.wf_true hello.toByteArray_eq (c := (L, ld)))

set_option silmaril.trust.profile "local" in
/-- Local profile: native. -/
theorem loader_local : LoaderIs F L ld := by
  sil_check elf.loader (native := Native.loader_sound (raw := helloRaw) (c := (L, ld)))
    (kernel := Kernel.loader_sound hello.wf_true hello.toByteArray_eq (c := (L, ld)))

set_option silmaril.trust.profile "local" in
/-- Local profile: the code of `main`, natively decoded. -/
theorem main_local : TilesAt F x86Ok 4192 mainTiles := by
  sil_check elf.tiles.x86 (native := Native.tilesX86_sound (raw := helloRaw) (c := (4192, mainTiles)))
    (kernel := Kernel.tilesX86_sound hello.wf_true hello.toByteArray_eq (c := (4192, mainTiles)))

set_option silmaril.trust.profile "paranoid" in
/-- Paranoid profile: the kernel, even for `elf.layout`. -/
theorem layout_paranoid : LayoutIs F L := by
  sil_check elf.layout (native := Native.layout_sound (raw := helloRaw) (L := L))
    (kernel := Kernel.layout_sound hello.wf_true hello.toByteArray_eq (L := L))

set_option silmaril.trust.profile "local" in
/-- Kernel-only: only the kernel backend is given, so the kernel checks it even under `local`,
where `elf.layout` may run natively. -/
theorem layout_kernelOnly : LayoutIs F L := by
  sil_check elf.layout (kernel := Kernel.layout_sound hello.wf_true hello.toByteArray_eq (L := L))

/-- A layout with a wrong entry point. -/
def badL : Layout := { L with header := { L.header with entry := 0 } }

-- An unsupported leaf has no declared procedure.
/-- error: sil_check: no procedure elf.dwarf.line (declare `Silmaril.Procedures.elf.dwarf.line : ProcDecl`) -/
#guard_msgs in
example : LayoutIs F L := by
  sil_check elf.dwarf.line (kernel := Kernel.layout_sound hello.wf_true hello.toByteArray_eq (L := L))

-- A false native check fails under `local`; it is not retried in the kernel.
/-- error: sil_check elf.layout: the native check returned false -/
#guard_msgs (substring := true) in
set_option silmaril.trust.profile "local" in
example : LayoutIs F badL := by
  sil_check elf.layout (native := Native.layout_sound (raw := helloRaw) (L := badL))
    (kernel := Kernel.layout_sound hello.wf_true hello.toByteArray_eq (L := badL))

-- The same false claim fails in the kernel under `paranoid`.
/-- error: sil_check elf.layout: the kernel did not check it -/
#guard_msgs (substring := true) in
set_option silmaril.trust.profile "paranoid" in
example : LayoutIs F badL := by
  sil_check elf.layout (native := Native.layout_sound (raw := helloRaw) (L := badL))
    (kernel := Kernel.layout_sound hello.wf_true hello.toByteArray_eq (L := badL))

/-! ## Audits and recorded uses -/

-- The default-profile layout ran natively: its own native procedure and axiom.
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.layout_default","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":["_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.layout_default._native.edge.elf.layout.ax_1_1"],"own_native":["elf.layout"],"profile":"default","schema":"silmaril.trust.v1","violations":[]}
-/
#guard_msgs in
trust_audit layout_default

set_option silmaril.trust.profile "local" in
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.loader_local","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":["_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.loader_local._native.edge.elf.loader.ax_1_1"],"own_native":["elf.loader"],"profile":"local","schema":"silmaril.trust.v1","violations":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.main_local","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":["_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.main_local._native.edge.elf.tiles.x86.ax_1_1"],"own_native":["elf.tiles.x86"],"profile":"local","schema":"silmaril.trust.v1","violations":[]}
-/
#guard_msgs in
trust_audit loader_local main_local

/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.loader_default","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","violations":[]}
-/
#guard_msgs in
trust_audit loader_default

set_option silmaril.trust.profile "paranoid" in
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.layout_paranoid","dep_native":[],"elaborated_profiles":["paranoid"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":[],"own_native":[],"profile":"paranoid","schema":"silmaril.trust.v1","violations":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Elf.Staged.Example.Profiles.layout_kernelOnly","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Elf.Staged.Example.Profiles","native_axioms":[],"own_native":[],"profile":"paranoid","schema":"silmaril.trust.v1","violations":[]}
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
