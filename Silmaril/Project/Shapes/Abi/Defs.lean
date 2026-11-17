module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.Project.Shapes.X86.Defs

/-!
# Standard problem shapes: ABI conformance

**ABI conformance** of machine code, as a standard problem. The code, called as a versioned ABI
requires for the prototype a C header declares, returns as the ABI requires. Its result is one
the ABI reads back and a C spec allows. It writes only what it may, and it never reaches a state
the machine cannot step (`Silmaril.Machine.Abi.Conformance`, guide
`docs/projects/abi-conformance.md`).

**The machine is part of the statement.** A row is about a *restricted x86-64 machine model*
`M` (the standard instances: `Mach.ofInt` of `Open.isa` and `Open9.isa`), not about real x86.
Code using instructions outside `M` (SSE, x87, `std`, `ldmxcsr`, `bsr` on `Open`, …) is stuck
on `M`, so it has no row: neither mode admits stuck code. Reading a row about real x86 is `Conforms.onRef`, under the
assumption `Faithful R M` for a reference machine `R`.

| name | statement |
| --- | --- |
| `silmaril.shapes.abi.conforms` | `Conforms A M mode hdr f p code frame S` |
| `silmaril.shapes.abi.conforms.sysv_int_open` | the same for the System V AMD64 INTEGER fragment (`sysvInt`) on the open machine model (`Mach.ofInt Open.isa`) |
| `silmaril.shapes.abi.conforms.sysv_int_open9` | … on `Mach.ofInt Open9.isa` |
| `silmaril.shapes.abi.header_sat_partial` | `HeaderSatPartial A M hdr cov impl`: at least one function claimed, each conforming; the others excluded with checked reasons; says nothing about the excluded ones |
| `silmaril.shapes.abi.header_sat_available` | `HeaderSatAvailable`: partial, with no `unclaimed` declaration and every claimed function total; `absent` declarations (version gaps) allowed and listed |
| `silmaril.shapes.abi.header_sat_complete` | `HeaderSatComplete`: available, with nothing absent: every declaration claimed or refused by the ABI |

A partial or available row is never whole-header satisfaction; only `header_sat_complete` is.

The ELF-bound forms (the code is the file's, at its symbol's address and size, at every load
base) are `silmaril.shapes.elf.abi_conforms`, `abi_header_sat_partial`, `abi_header_sat_available` and `abi_header_sat_complete`
(`Silmaril.Elf.Abi`).

These are distinct from the shapes that state less:

* **symbol presence** (`silmaril.shapes.elf.lookup`, `binds`): an ELF symbol has a value and a
  size; it carries no C signature;
* **layout** (`Silmaril.Data.Layout`): sizes and offsets of C types under a data model;
* **a function contract** (`silmaril.shapes.x86.abi_function`, `elf.fn_contract`): a
  System V *entry* and *return* discipline (`AbiEntry`/`AbiReturn`) around a hand-written spec,
  with no prototype, argument placement or result read-back;
* **translation validation** (`silmaril.shapes.sysv.implements`, `c.compiles_to`): the code
  against a source meaning, on INTEGER scalars, for leaf functions writing only their frame.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Abi

open Silmaril.Machine.Abi.Conformance

/-- **The code conforms to the ABI `A` on the machine model `M`** as the function `f` of the
header `hdr` (`Silmaril.Machine.Abi.Conformance.Conforms`). -/
@[problem "silmaril.shapes.abi.conforms"
  (title := "Machine code conforms to a versioned ABI on a restricted x86-64 machine model, as its C header declares it (which FP, vector and control state the model computes and which it carries depends on the machine: Mach.models)")]
def AbiConforms (A : AbiDef) (M : Mach) (mode : Mode) (hdr : HeaderSrc) (f : String)
    (p : A.V.Proto) (c : Code) (frame : Nat) (S : CallSpec A.V p) : Prop :=
  Conforms A M mode hdr f p c frame S

/-- **A binary satisfies a claimed part of a header** (`HeaderSatPartial`). -/
@[problem "silmaril.shapes.abi.header_sat_partial"
  (title := "PARTIAL: a binary satisfies the claimed part of a C header under a versioned ABI, on a restricted x86-64 machine model")]
def AbiHeaderSatPartial (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage)
    (impl : String → Option (Impl A)) : Prop :=
  HeaderSatPartial A M hdr cov impl

/-- **A binary satisfies every function of a header it provides** (`HeaderSatAvailable`). -/
@[problem "silmaril.shapes.abi.header_sat_available"
  (title := "A binary satisfies every function of a C header it provides (absent functions allowed as version gaps), total, under a versioned ABI, on a restricted x86-64 machine model")]
def AbiHeaderSatAvailable (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage)
    (impl : String → Option (Impl A)) : Prop :=
  HeaderSatAvailable A M hdr cov impl

/-- **A binary satisfies a whole header** (`HeaderSatComplete`). -/
@[problem "silmaril.shapes.abi.header_sat_complete"
  (title := "A binary satisfies a whole C header (every declaration the ABI lowers, total) under a versioned ABI, on a restricted x86-64 machine model")]
def AbiHeaderSatComplete (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage)
    (impl : String → Option (Impl A)) : Prop :=
  HeaderSatComplete A M hdr cov impl

end Silmaril.Project.Shapes.Abi

end

silmaril instance silmaril.shapes.abi.conforms.sysv_int_open
    (title := "conforms, System V AMD64 INTEGER fragment, on the open machine model (Open)") :=
  silmaril.shapes.abi.conforms (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.abi.conforms.sysv_int_open9
    (title := "conforms, System V AMD64 INTEGER fragment, on the open machine model (Open9)") :=
  silmaril.shapes.abi.conforms (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa)
