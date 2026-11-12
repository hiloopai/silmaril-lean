module

public import Silmaril.Libc.X86Alloc.Spec.Defs
public import Silmaril.Project.Shapes.X86.Defs

/-!
# Standard problem shapes: allocators in x86-64 executables

An **allocator row** names an executable (a registered value `exe`), the loader `L`, the x86-64
model `M`, and the allocator's `Layout`: its code region (holding `malloc` and `free`), their
entry addresses, and its static state as the loader puts it in a `rw` segment. Three strengths:

| name | statement |
|---|---|
| `silmaril.shapes.alloc.safe` | `Safe L M exe lay align stack`: some `Iface` `A` with this alignment and stack budget, established by the loaded static state (`lay.Init ⊢ A.mm`), whose loose `mallocSpec`/`freeSpec` the code meets: **safety** (failure always allowed) |
| `silmaril.shapes.alloc.live` | `Live L M exe lay C s0 align stack`: the same for `mallocSpecL`/`freeSpecL` of the capacity model `C`, from the initial abstract state `s0`: **liveness** (malloc fails only when `¬ C.avail s n`; the state is threaded) |
| `silmaril.shapes.alloc.functional` | `Functional L M exe lay R s0 align stack`: the same for `mallocSpecF`/`freeSpecF` of the reference model `R`: **functional correctness** (the returned block is `R.malloc s n`) |
| `silmaril.shapes.alloc.functional_rel` | `FunctionalRel L M exe lay R s0 align stack`: as `functional` for `malloc` (`mallocSpecR`), with a *relational* `free` (`freeSpecR`): some state `R.dealloc` admits; the form that fits header-sized blocks without ghost state |
| `….safe.x86_open`, `….live.x86_open`, `….functional.x86_open`, `….functional_rel.x86_open` | `L := Loader.x86`, `M := Open.isa` |

Each shape includes `LoadsLayout L exe lay`: the loader puts `lay.code` at `lay.codeAddr` in an
`rx` segment and `lay.data` at `lay.dataAddr` in an `rw` segment, and both entries lie in the
code. The witness interface is existential, so a row fixes only what a client may rely on (the
alignment, the stack budget, and for the stronger shapes the model and its initial state); a
model with nothing available, or a vacuous `mm`, is excluded because the loaded bytes must
establish the state.

`Silmaril.Libc.Shapes.Alloc.Thms`: `Functional.live` (along a simulation of a capacity model),
`Functional.live_self`, `Live.safe`, and the client theorems `Safe.client` (a client proved for
every `Iface` runs against this allocator from the loaded image) and `Live.serves` (an available
request returns a fresh block: the success branch is not vacuous).

**Functional strength and tokens (a finding).** A row of `functional` needs `free(p)` to move the
model to `R.dealloc s p n`, a function of the state, the pointer and the *requested* size. For an
allocator whose blocks carry their real size in a header (first-fit, coalescing, glibc), that
size must reach the model. Recording it in the model (`allocated : addr → size`, set by `alloc`)
does not suffice without ghost state. `freeSpecL` must hold for *every* fragment satisfying
`mmS s ∗ tok p n ∗ blockAny p n`:

* if the token owns the header, `mmS s` cannot constrain its value, and a precondition whose
  header disagrees with `s.allocated p` is satisfiable, so the pushed block disagrees with the
  model;
* if `mmS s` owns the header, the token must still own something that ties `(p, n)` to a live
  block; for `n` below the recorded request the payload bytes in between are owned by nobody in
  the precondition, so the postcondition (the whole block back on the list) is unprovable on a
  satisfiable precondition.

**How weak rung 05's `live` row is.** Its capacity model `ffCap` has `dealloc s _ _ = s`: a freed
block is never promised reusable, so the row only guarantees that blocks in the *initial* (and
split-off) free set serve requests. That is why `functional_rel` (exact free list, first-fit address,
`free` pushes the block) is the meaningful strength for first-fit.

Two ways out: ghost state linking tokens to the allocator state (an authoritative map, as in
Iris, or VST's `malloc_token`/`mem_mgr` with ghost), or a *relational* `dealloc` that admits the
size the header actually holds (then `malloc`'s returned address stays determined by the
resulting state). VST's verified malloc stops at the resource-vector (`live`) strength for the
same reason. Rung 05 is proved at `live` and `safe`; its `functional` row stays open for this
reason. The `RefModel` signature itself is not the obstruction.

**The same gap at `safe` (rung 08t).** An allocator whose `free` reads the tags of an
*allocated* neighbour (textbook boundary tags; glibc's chunk headers with `PREV_INUSE`) cannot
meet even the loose interface: if `mm` owns allocated blocks' tags, tokens are forgeable (a
pointer into another block's payload satisfies `tok`); if tokens own them, `free` reads memory
outside its precondition. Ghost state or fractional permissions on the tags would express it.
Rung 08 (side tables marking free blocks) avoids the reads and is the provable variant; rung
08t keeps the textbook design with an open row.

**Trusted**: the LPS ELF loading rules (`Loader.x86`), the x86-64 model `M`, and that the program
does not touch `lay.data` except through `malloc`/`free` (the client's frame does not own it).
Not covered here: `calloc`/`realloc` (the specs exist in `Silmaril.X86.Sep.Alloc`), symbol
tables (the row gives addresses), threads.
-/

@[expose] public section

namespace Silmaril.Libc.Shapes.Alloc

open Silmaril.X86 (Word Byte MState)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Project.Shapes (Loader Model Loads)
open Silmaril.Libc.X86Alloc

/-- The executable loads the allocator's code and static state where the layout says. -/
def LoadsLayout (L : Loader) {V : Type} (exe : Silmaril.Project.Value V) (lay : Layout) : Prop :=
  Loads L exe "rx" lay.codeAddr lay.code ∧ Loads L exe "rw" lay.dataAddr lay.data ∧
    lay.codeAddr ≤ lay.malloc ∧ lay.malloc < lay.codeAddr + lay.code.length ∧
    lay.codeAddr ≤ lay.free ∧ lay.free < lay.codeAddr + lay.code.length

/-- **Safety**: the allocator meets the loose interface. -/
@[problem "silmaril.shapes.alloc.safe"
  (title := "An executable's malloc/free meet the loose allocator interface")]
def Safe (L : Loader) (M : Model) {V : Type} (exe : Silmaril.Project.Value V) (lay : Layout)
    (align stack : Nat) : Prop :=
  LoadsLayout L exe lay ∧ ∃ A : Iface, A.align = align ∧ A.stack = stack ∧ (lay.Init ⊢ₛ A.mm) ∧
    (mallocSpec A).Sat M lay.C lay.mallocAt ∧ (freeSpec A).Sat M lay.C lay.freeAt

/-- **Liveness**: the allocator meets the capacity model `C` from the state `s0`. -/
@[problem "silmaril.shapes.alloc.live"
  (title := "An executable's malloc succeeds whenever its capacity model has room")]
def Live (L : Loader) (M : Model) {V : Type} (exe : Silmaril.Project.Value V) (lay : Layout)
    (C : CapModel) (s0 : C.St) (align stack : Nat) : Prop :=
  LoadsLayout L exe lay ∧ ∃ B : IfaceL C, B.align = align ∧ B.stack = stack ∧
    (lay.Init ⊢ₛ B.mmS s0) ∧
    (mallocSpecL B).Sat M lay.C lay.mallocAt ∧ (freeSpecL B).Sat M lay.C lay.freeAt

/-- **Functional correctness**: the allocator refines the reference model `R` from `s0`. -/
@[problem "silmaril.shapes.alloc.functional"
  (title := "An executable's malloc/free refine a reference allocator")]
def Functional (L : Loader) (M : Model) {V : Type} (exe : Silmaril.Project.Value V)
    (lay : Layout) (R : RefModel) (s0 : R.St) (align stack : Nat) : Prop :=
  LoadsLayout L exe lay ∧ ∃ B : IfaceL R.toCap, B.align = align ∧ B.stack = stack ∧
    (lay.Init ⊢ₛ B.mmS s0) ∧
    (mallocSpecF B).Sat M lay.C lay.mallocAt ∧ (freeSpecF B).Sat M lay.C lay.freeAt

end Silmaril.Libc.Shapes.Alloc

end

silmaril instance silmaril.shapes.alloc.safe.x86_open
    (title := "safe, with the x86-64 loader and the open machine (Open)") :=
  silmaril.shapes.alloc.safe (L := Silmaril.Project.Shapes.Loader.x86) (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.alloc.live.x86_open
    (title := "live, with the x86-64 loader and the open machine (Open)") :=
  silmaril.shapes.alloc.live (L := Silmaril.Project.Shapes.Loader.x86) (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.alloc.functional.x86_open
    (title := "functional, with the x86-64 loader and the open machine (Open)") :=
  silmaril.shapes.alloc.functional (L := Silmaril.Project.Shapes.Loader.x86)
    (M := Silmaril.X86.Open.isa)

@[expose] public section

namespace Silmaril.Libc.Shapes.Alloc

open Silmaril.X86.Sep
open Silmaril.Project.Shapes (Loader Model)
open Silmaril.Libc.X86Alloc

/-- **Functional correctness with a relational `free`**: `malloc` refines the deterministic part
of `R`; `free` moves to some state `R.dealloc` admits (for header-sized blocks: the block pushed
with the size its header holds). -/
@[problem "silmaril.shapes.alloc.functional_rel"
  (title := "An executable's malloc is a function of a reference state; free is relational")]
def FunctionalRel (L : Loader) (M : Model) {V : Type} (exe : Silmaril.Project.Value V)
    (lay : Layout) (R : RelModel) (s0 : R.St) (align stack : Nat) : Prop :=
  LoadsLayout L exe lay ∧ ∃ B : IfaceL R.toCap, B.align = align ∧ B.stack = stack ∧
    (lay.Init ⊢ₛ B.mmS s0) ∧
    (mallocSpecR B).Sat M lay.C lay.mallocAt ∧ (freeSpecR B).Sat M lay.C lay.freeAt

end Silmaril.Libc.Shapes.Alloc

end

silmaril instance silmaril.shapes.alloc.functional_rel.x86_open
    (title := "functional_rel, with the x86-64 loader and the open machine (Open)") :=
  silmaril.shapes.alloc.functional_rel (L := Silmaril.Project.Shapes.Loader.x86)
    (M := Silmaril.X86.Open.isa)

@[expose] public section

namespace Silmaril.Libc.Shapes.Alloc

open Silmaril.X86.Sep
open Silmaril.Project.Shapes (Loader Model)
open Silmaril.Libc.X86Alloc

/-- **Correctness against an explicit heap model**: there is a heap model whose initial heap
(no live payloads) the loaded image represents, and `malloc`/`free` meet `mallocSpecH` and
`freeSpecH`. The live set is authoritative, so `free` may require a live pointer and the
allocator may read the tags of allocated blocks (textbook boundary tags, glibc's chunk
headers), which the loose interface cannot express without ghost state. The client's
side is the precondition `(p, u) ∈ live H` instead of a token. -/
@[problem "silmaril.shapes.alloc.model"
  (title := "An executable's malloc/free against an explicit heap model (authoritative live set)")]
def HeapModelShape (L : Loader) (M : Model) {V : Type} (exe : Silmaril.Project.Value V)
    (lay : Layout) (align stack : Nat) : Prop :=
  LoadsLayout L exe lay ∧ ∃ (HM : HeapModel) (H0 : HM.Heap), HM.live H0 = [] ∧
    (lay.Init ⊢ₛ HM.rep H0) ∧
    (mallocSpecH HM align stack).Sat M lay.C lay.mallocAt ∧
    (freeSpecH HM stack).Sat M lay.C lay.freeAt

end Silmaril.Libc.Shapes.Alloc

end

silmaril instance silmaril.shapes.alloc.model.x86_open
    (title := "model, with the x86-64 loader and the open machine (Open)") :=
  silmaril.shapes.alloc.model (L := Silmaril.Project.Shapes.Loader.x86)
    (M := Silmaril.X86.Open.isa)
