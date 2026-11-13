module

public import Silmaril.Prelude.Bytes.Elab.Defs
public import Silmaril.Prelude.Bytes.Native.Defs
public import Silmaril.Prelude.Trust.Policy.Defs

/-! # Kernel bytes and native edges: examples

`hello` is the pinned `hello-gcc` (15,960 bytes; SHA-256
`6964f3f23e27cfd2b6c26bd469cb210ff000dd359fc9988138cadc96683065c7`), written out as the
canonical tree by `kbytes_def`.

* **Reads** are proved by `decide +kernel`: they are kernel-only.
* The **staged ELF facts** read the header (stage 1), then the program header table it
  locates (stage 2), then the `PT_INTERP` string that table points at (stage 3), each with one
  wide read. They are examples of the byte interface, not an ELF parser (`Silmaril.Elf` owns
  that).
* **Ropes** (slices and appends) are compared with `edge_decide`. That runs natively in the
  default profile and in the kernel in the paranoid profile, for the same statement.
* `bytes.eqByteArray` has no kernel fallback, so it fails closed in the paranoid profile.
-/

@[expose] public section

-- These tests check each profile's behaviour, so they fix the profile they start from.
set_option silmaril.trust.profile "default"

namespace Silmaril.KBytes.Examples

open Silmaril.KBytes

kbytes_def hello from_file "../../../examples/dyn/pinned/hello-gcc" computable

example : hello.len = 15960 := hello.len_eq

/-! ## Stage 1: the ELF header -/

theorem magic : hello.readLE 0 4 = some 0x464c457f := by decide +kernel
theorem elfClass64 : hello.readLE 4 1 = some 2 := by decide +kernel
theorem typeDyn : hello.readLE 16 2 = some 3 := by decide +kernel
theorem machineX86_64 : hello.readLE 18 2 = some 62 := by decide +kernel
theorem phoff : hello.readLE 32 8 = some 64 := by decide +kernel
theorem shoff : hello.readLE 40 8 = some 13976 := by decide +kernel
theorem phentsize_phnum : hello.readLE 54 4 = some (56 + 13 * 65536) := by decide +kernel

/-! ## Stage 2: the program header table, as a slice -/

/-- The 13 program headers, sharing the file's leaves. -/
noncomputable def phdrs : KBytes := hello.slice 64 (13 * 56)

/-- The second program header is `PT_INTERP` (type 3) at file offset 792, 28 bytes long. -/
theorem interpHeader :
    phdrs.readLE 56 4 = some 3 ∧ phdrs.readLE (56 + 8) 8 = some 792 ∧
      phdrs.readLE (56 + 32) 8 = some 28 := by
  decide +kernel

/-- The slice reads what the file reads at the same place. -/
theorem phdrs_toList : phdrs.toList = (hello.toList.drop 64).take (13 * 56) :=
  toList_slice hello 64 _ hello.wf (by rw [hello.len_eq]; decide)

/-! ## Stage 3: the interpreter path, as one wide read -/

theorem interp :
    hello.readLE 792 28 = some (leVal "/lib64/ld-linux-x86-64.so.2\x00".toUTF8.data.toList) := by
  decide +kernel

/-! ## Ropes and canonical forms -/

/-- Cut at an unaligned offset and glued back: a rope with the file's bytes. -/
def rope : KBytes := hello.slice 0 5000 ++ hello.slice 5000 (15960 - 5000)

/-- Default profile: `bytes.sameBytes` runs natively (one `_native.edge.bytes.sameBytes` axiom). -/
theorem rope_same_native : rope.sameBytes 65536 hello = true := by edge_decide

-- Paranoid profile: the same statement, checked by the kernel; no native axiom.
set_option silmaril.trust.profile "paranoid" in
theorem rope_same_kernel : rope.sameBytes 65536 hello = true := by edge_decide

theorem rope_toList : rope.toList = hello.toList :=
  toList_eq_of_sameBytes 65536 rope hello
    (wf_append (wf_slice _ _ _ hello.wf (by rw [hello.len_eq]; decide))
      (wf_slice _ _ _ hello.wf (by rw [hello.len_eq]; decide)))
    hello.wf rope_same_kernel

/-- A canonicalised rope is the canonical tree itself: the kernel checks it by evaluation and
one structural comparison. -/
theorem canon_rope : (rope.canon 4096).beq hello = true := by decide +kernel

/-! ## Fail closed -/

-- `bytes.eqByteArray` has no kernel fallback, so the paranoid profile refuses it.
/--
error: edge_decide: bytes.eqByteArray may not run natively in Silmaril.Prelude.Bytes.Examples under profile paranoid, and it has no kernel fallback
-/
#guard_msgs in
set_option silmaril.trust.profile "paranoid" in
example : hello.eqByteArray hello.toByteArray = true := by edge_decide

/-- In the default profile it runs natively. -/
example : hello.eqByteArray hello.toByteArray = true := by edge_decide

/-! ## Audit -/

/-- The native comparison, used through a soundness theorem: the native axiom is inherited. -/
theorem rope_toList_native : rope.toList = hello.toList :=
  toList_eq_of_sameBytes 65536 rope hello
    (wf_append (wf_slice _ _ _ hello.wf (by rw [hello.len_eq]; decide))
      (wf_slice _ _ _ hello.wf (by rw [hello.len_eq]; decide)))
    hello.wf rope_same_native

/--
info: {"axioms":[],"decl":"Silmaril.KBytes.Examples.rope_same_native","dep_native":[],"kind":"audit","module":"Silmaril.Prelude.Bytes.Examples","native_axioms":["_private.Silmaril.Prelude.Bytes.Examples.0.Silmaril.KBytes.Examples.rope_same_native._native.edge.bytes.sameBytes.ax_1_1"],"own_native":["bytes.sameBytes"]}
{"axioms":[],"decl":"Silmaril.KBytes.Examples.rope_same_kernel","dep_native":[],"kind":"audit","module":"Silmaril.Prelude.Bytes.Examples","native_axioms":[],"own_native":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.KBytes.Examples.rope_toList_native","dep_native":["bytes.sameBytes"],"kind":"audit","module":"Silmaril.Prelude.Bytes.Examples","native_axioms":["_private.Silmaril.Prelude.Bytes.Examples.0.Silmaril.KBytes.Examples.rope_same_native._native.edge.bytes.sameBytes.ax_1_1"],"own_native":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.KBytes.Examples.rope_toList","dep_native":[],"kind":"audit","module":"Silmaril.Prelude.Bytes.Examples","native_axioms":[],"own_native":[]}
{"axioms":[],"decl":"Silmaril.KBytes.Examples.magic","dep_native":[],"kind":"audit","module":"Silmaril.Prelude.Bytes.Examples","native_axioms":[],"own_native":[]}
-/
#guard_msgs in
trust_audit rope_same_native rope_same_kernel rope_toList_native rope_toList magic

end Silmaril.KBytes.Examples
