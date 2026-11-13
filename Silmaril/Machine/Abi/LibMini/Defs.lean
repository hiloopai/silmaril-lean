module

public import Silmaril.Machine.Abi.OpenMachine.Defs
public import Silmaril.X86.Ladder.LibMini.Defs
/-! # libmini against the System V comorphism: prototypes, C contracts and rooms

The declared C header of libmini (`examples/elf-ladder/common/libmini.c`, with
`typedef unsigned long usize`), as prototypes of track C's INTEGER/pointer fragment:

```c
void *memcpy(void *restrict d, const void *restrict s, usize n);
void *memmove(void *d, const void *s, usize n);
void *memset(void *d, int c, usize n);
int   memcmp(const void *a, const void *b, usize n);
usize strlen(const char *s);
```

(`restrict`, `const` and the pointee types are not part of the fragment: pointers are
64-bit addresses.)

**C contracts.** Track C's sentences are *value-level*: a precondition on the argument
values and a postcondition on the returned value. Memory effects cannot be stated in them.
So:

* `strlenC k`: "returns `k`". It is used under `StrlenRoom entry k`, whose state part says
  that the argument points to a NUL-terminated string of length `k`. This gives a family of
  institution sentences over `k`.
* `memcpyC`: "returns its first argument". The copy itself is not a value-level fact. It is
  carried by the typed FFI certificate (`Thms.memcpy_ffiRealizesCall`, footprint
  `[d, d + n)`) and by the separation-logic `FnSpec` `copySpec`.

**Rooms.** A room is the state-level assumption of an institution sentence
(`Silmaril.Machine.Abi.within`). It consists of the state-level entry condition of the function's
stencil contract (code loaded at `entry`, `rip = entry`, buffers readable/writable and
apart) and the return address lying outside the code (first-return reading, `callModel`).
-/

@[expose] public section
namespace Silmaril.Machine.Abi.LibMini

open Silmaril.X86 (Word)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi (Ffi.State Ffi.Call)
open Silmaril.Machine.Abi.SystemV (Proto vocab)
open Silmaril.Machine.Abi.OpenMachine (RetOutside)
open Silmaril.X86.Stencils.ByteLoop
open Silmaril.X86.Ladder.LibMini

/-- `usize strlen(const char *s)`. -/
def strlenProto : Proto := ⟨⟨[.pointer], some .uint64⟩, by decide⟩

/-- `void *memcpy(void *d, const void *s, usize n)` (also `memmove`). -/
def memcpyProto : Proto := ⟨⟨[.pointer, .pointer, .uint64], some .pointer⟩, by decide⟩

/-- `void *memset(void *d, int c, usize n)`. -/
def memsetProto : Proto := ⟨⟨[.pointer, .int32, .uint64], some .pointer⟩, by decide⟩

/-- `int memcmp(const void *a, const void *b, usize n)`. -/
def memcmpProto : Proto := ⟨⟨[.pointer, .pointer, .uint64], some .int32⟩, by decide⟩

/-- The value-level C contract of `strlen` on a string of length `k`: it returns `k`. -/
def strlenC (k : Nat) :
    Contracts.Contract (vocab.Args strlenProto) (Option (vocab.Ret strlenProto)) where
  pre _ := True
  post _ r := r = some (BitVec.ofNat 64 k)

/-- The value-level C contract of `memcpy`: it returns its first argument. -/
def memcpyC : Contracts.Contract (vocab.Args memcpyProto) (Option (vocab.Ret memcpyProto)) where
  pre _ := True
  post a r := match a with | .cons d _ => r = some d

/-- The room of `strlen` at `entry` on a string of length `k`. -/
def StrlenRoom (entry : Word) (k : Nat) (s : Ffi.State) : Prop :=
  (scanContract strlenCode entry).entry s.machine ∧ RetOutside entry strlenCode.length s.machine ∧
    CStr s.machine.memory (arg0 s.machine) k

/-- The room of `memcpy` at `entry`. -/
def MemcpyRoom (entry : Word) (s : Ffi.State) : Prop :=
  (copyContract memcpyCode entry).entry s.machine ∧ RetOutside entry memcpyCode.length s.machine

/-- The domain of the typed FFI certificate of `strlen` at `entry` on a string of length `k`
(beyond the ABI model's `Ffi.Entry`): the code loaded, the call entering at `entry`, the string. -/
def strlenDomain (entry : Word) (k : Nat) {α : Type} (_ : α) (call : Ffi.Call) : Prop :=
  Silmaril.X86.Ext.Loaded call.initial.machine.memory entry strlenCode ∧ call.entry = entry ∧
    CStr call.initial.machine.memory (arg0 call.initial.machine) k

/-- The domain of the typed FFI certificate of `memcpy` at `entry`: the state-level entry
condition of `copyContract` with the call entering at `entry`. -/
def memcpyDomain (entry : Word) {α : Type} (_ : α) (call : Ffi.Call) : Prop :=
  call.entry = entry ∧ (copyContract memcpyCode entry).entry call.initial.machine

end Silmaril.Machine.Abi.LibMini
