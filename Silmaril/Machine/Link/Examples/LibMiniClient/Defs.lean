module

public import Silmaril.Machine.Link.FnSpec.Defs
public import Silmaril.Machine.X86.Stencils.ByteLoop.Defs
public import Silmaril.Machine.Link.Fixtures.LibMiniClientBfd

/-! # Ladder rung 12: a client of libmini, composed under the `FnSpec` link logic

The program (`examples/elf-ladder/12-libmini-client`) has four translation units, linked
by GNU ld.bfd with `--gc-sections` and validated by `Silmaril.Machine.Link.Fixtures.LibMiniClientBfd`:

* `start.o`: `_start` calls `cmain` and exits (not verified: `unverified` spec);
* `main.o`: `cmain` calls `memset`, `memcpy` and `len1` (not verified);
* `client.o`: `len1(s) = strlen(s) + 1`, compiled to
  `sub $8,%rsp; call strlen; add $8,%rsp; add $1,%rax; ret` with `R_X86_64_PLT32 strlen-4`;
* `libmini.o`: `memcpy`, `memset`, `strlen` with the separation-logic layer's specs `copySpec`, `fillSpec`,
  `scanSpec`; `memmove` and `memcmp` are present but not verified (and discarded by
  `--gc-sections`).

**Specs.** `plusOneSpec S` is the spec of "call a function meeting `S`, add one to its
result": the same arguments and precondition, a stack budget sixteen bytes larger (the
alignment slot and the return address of the inner call), and `rax = w + 1` where `S`
returns `w`. `len1Spec := plusOneSpec scanSpec`: for `s ↦ cstr bs`, `len1` returns
`|bs| + 1` and returns the string unchanged.

**Objects.** `prepared` is exactly what the validator links: the input blobs read by the
kernel-fast reader and rewritten by `prepare` with the witness's discarded sections.
`units` attaches the interfaces; `Thms` proves `units.map TU.object = prepared` by kernel
evaluation, so the composed theorem is about the validated link, not about a transcription.
-/

@[expose] public section

namespace Silmaril.Machine.Link.Examples.LibMiniClient

open Silmaril.X86 (Word Byte Insn)
open Silmaril.Formats.ELF
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Stencils.ByteLoop
open Silmaril.Machine.Link.Unit
open Silmaril.Machine.Link.FnSpec
open Silmaril.Machine.Link.Fixtures.LibMiniClientBfd
open Silmaril.Machine.Link (Blob)

/-- **"Call `S`, then add one."** -/
def plusOneSpec (S : FnSpec) : FnSpec where
  Arg := S.Arg
  args := S.args
  stack := S.stack + 16
  pre := S.pre
  post x v := sexists fun w => ⌜v = w + 1#64⌝ ∗ S.post x w

/-- `len1`'s spec: libmini's `scanSpec` plus one. -/
def len1Spec : FnSpec := plusOneSpec scanSpec

/-- `sub $8,%rsp; call rel; add $8,%rsp; add $1,%rax; ret`. -/
def plusOneCode (rel : BitVec 32) : List Byte :=
  [0x48, 0x83, 0xec, 0x08] ++ Insn.encode (.call rel) ++ [0x48, 0x83, 0xc4, 0x08] ++
    [0x48, 0x83, 0xc0, 0x01] ++ Insn.encode .ret

/-! ## Names -/

def nStart : NameBytes := [0x5f, 0x73, 0x74, 0x61, 0x72, 0x74]
def nCmain : NameBytes := [0x63, 0x6d, 0x61, 0x69, 0x6e]
def nLen1 : NameBytes := [0x6c, 0x65, 0x6e, 0x31]
def nStrlen : NameBytes := [0x73, 0x74, 0x72, 0x6c, 0x65, 0x6e]
def nMemcpy : NameBytes := [0x6d, 0x65, 0x6d, 0x63, 0x70, 0x79]
def nMemset : NameBytes := [0x6d, 0x65, 0x6d, 0x73, 0x65, 0x74]
def nMemmove : NameBytes := [0x6d, 0x65, 0x6d, 0x6d, 0x6f, 0x76, 0x65]
def nMemcmp : NameBytes := [0x6d, 0x65, 0x6d, 0x63, 0x6d, 0x70]

/-! ## The prepared objects and the units -/

/-- The input objects as the validator reads them. -/
def parsed : List ObjectFile := (objects.mapM fun b => Blob.readObjectN b.n b.len).getD []

/-- The objects the validator links (`prepare`: weak resolution, discarded sections). -/
def prepared : List ObjectFile := Silmaril.Machine.Link.Validate.prepare parsed witness.dropped

def startTU (o : ObjectFile) : TU Abi.Conv FnSpec where
  object := o
  exports := [⟨nStart, .sysv64, unverified⟩]
  imports := [⟨nCmain, .sysv64, unverified⟩]

def mainTU (o : ObjectFile) : TU Abi.Conv FnSpec where
  object := o
  exports := [⟨nCmain, .sysv64, unverified⟩]
  imports := [⟨nMemset, .sysv64, fillSpec⟩, ⟨nMemcpy, .sysv64, copySpec⟩,
    ⟨nLen1, .sysv64, len1Spec⟩]

def clientTU (o : ObjectFile) : TU Abi.Conv FnSpec where
  object := o
  exports := [⟨nLen1, .sysv64, len1Spec⟩]
  imports := [⟨nStrlen, .sysv64, scanSpec⟩]

def libminiTU (o : ObjectFile) : TU Abi.Conv FnSpec where
  object := o
  exports := [⟨nMemcpy, .sysv64, copySpec⟩, ⟨nMemmove, .sysv64, unverified⟩,
    ⟨nMemset, .sysv64, fillSpec⟩, ⟨nMemcmp, .sysv64, unverified⟩, ⟨nStrlen, .sysv64, scanSpec⟩]

/-- A placeholder object (never used: `prepared` has four objects, `Thms.units_objects`). -/
def emptyObject : ObjectFile := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, [], [], []⟩

/-- The `i`-th prepared object. -/
def obj (i : Nat) : ObjectFile := prepared.getD i emptyObject

/-- The four units over the prepared objects, in link order. -/
def units : List (TU Abi.Conv FnSpec) :=
  [startTU (obj 0), mainTU (obj 1), clientTU (obj 2), libminiTU (obj 3)]

end Silmaril.Machine.Link.Examples.LibMiniClient
