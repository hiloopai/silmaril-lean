module

public import Silmaril.Libc.AllocSig.Defs
public import Silmaril.Elf.Link.ElfBind.Defs
public import Silmaril.X86.RelIsa.Defs

/-!
# Allocator correctness over an ELF file: POSIX-safe with invariant

The machine-level half of the allocator rows (`silmaril.shapes.alloc.elf.posix_safe`): **an ELF file `F` (its bytes), whose exports are found by ld.so's
lookup, is a POSIX-safe allocator at the signature level `s`**, in a loading model `LM`.

## The statement (`Contract T LM s F S`, `PosixSafe := Contract loose`)

There are entry offsets `v op`, with **(0) binding**: `F`'s `.dynsym` binds each function of `s`
(the name `S.pre ++ cname`, version `S.ver op`, `ElfBind.Bound` with `Sel.dyn`: ld.so's
`do_lookup_x`) to a non-IFUNC definition at `v op`; and there is a **witness** `W`: a ghost
abstract state `W.St` with its live blocks `W.heap` (block start ↦ requested size), the
**owned regions** `W.own b S` (the bytes the allocator owns with the library loaded at `b` in
abstract state `S`: its `.data`/`.bss`, metadata, arenas, freed chunks) and the **invariant**
`W.Inv b S x` over machine states, such that

* **(i) setup** (`Setup`): every state the loading model calls *started* (`LM.Started F b x`:
  `F` loaded at `b` by the loader, its constructors run or not, before the first allocator
  call) satisfies `Inv b S` for some `S` with no live block. Lazy initialisation on the first
  call is the case of an invariant that accepts an uninitialised image.
* **(ii) calls** (`CallOk`): from every System V entry at `b + v op` in the invariant whose
  call is **valid POSIX use** (`AllocSig.Valid` on the ghost heap: no double free, no free of
  a non-block; and for `posix_memalign` a writable result slot outside the allocator's memory)
  with the stack budget free (`StackOk`), **every run** of the loading model's machine
  terminates without stopping (`RelIsa.Must`: total correctness, demonically) in a System V
  return, the thread pointer kept, in the invariant at some `S'`, where
  - the abstract step is one `T` allows (`T (heap S) call (heap S') ret blk`; for `loose`,
    **`NULL`/`ENOMEM` is always allowed**, `AllocSig.loose`): **correctness only**;
  - a returned block of `n` bytes is readable and writable, neither owned nor foreign; zero for
    `calloc`; for `realloc`, it holds the old block's first `min old n` bytes; for
    `posix_memalign`, the result slot holds it;
  - **(iv) frame** (`Frame`): every other byte keeps its value, unless it is owned before or
    after the call, in the call's own stack (`Scratch`: the `budget` bytes below the entry
    `rsp`, the red zone included), in the released or the returned block, or (`posix_memalign`)
    the result slot; permissions change only in owned memory and the two blocks.
* **(iii) after UB, nothing is promised**: an invalid call has no obligation, and nothing is
  said of states outside the invariant.
* **ownership discipline** (`Disc`): owned memory is disjoint from the live blocks and from the
  rest of the process's memory (`LM.foreign`), live blocks are readable, writable and not
  foreign, and the invariant is **stable** under every client step (`LM.Client`) that leaves the
  owned memory alone. So a witness cannot own the client's memory, and the client may write its
  blocks, its stack and its data between calls (writes within the requested sizes: client steps
  that touch owned memory, a use after free of a block the allocator took back, are not client
  steps).

Since the invariant, the ghost state and the owned regions are existential, the statement
fixes only the ELF bytes, the symbol names, the signature and the loading model. A file that
binds the symbols and never allocates meets the contract (the bottom allocator,
`AllocSig.bottom_safe`, at the abstract level): `loose` is the base strength. **Stronger
strengths** are stronger relations `T ≤ loose` (`Thms.mono`): a functional relation, liveness
(fail only when a capacity model has no room), robustness to invalid frees (a relation that
also constrains the invalid calls, with `Valid` weakened) are optional extensions.

## The loading model (`LoadModel`)

The trusted base of a row: a relational x86-64 machine (`Silmaril.X86.RelIsa`: one step of the
library's code, the loader's and the C runtime's code or atomic contracts, the kernel) with

* `Started F b x`: `x` is a process state in which the loader placed `F` at `b` (its scope,
  relocations, TLS, the C runtime started) before the first allocator call. Its ELF part is
  checked: it implies `ElfBind.Placement F b` and `ElfBind.RoLoaded F b` (`started_elf`);
* `foreign x a`: the byte `a` belongs to the rest of the process (the executable, the other
  libraries, the client's stack and its own mappings);
* `Client own x y`: what the client may do between calls: any step of its own that keeps the
  bytes and permissions of `own` and the thread pointer.

It is a parameter of the shape. A concrete instance is `Silmaril.Libc.AllocLoad.model`: the
library's segments loaded at a page-aligned base as the ELF says, its imports bound to functions
that satisfy named contracts (`AllocLoad`). The frame lets a call write its own stack and its
owned memory.
-/

@[expose] public section

namespace Silmaril.Libc.AllocElf

open Silmaril.Libc (Heap)
open Silmaril.Libc.AllocSig
open Silmaril.X86 (Word Byte State)
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.ElfBind (Placement RoLoaded Bound Sel leBytes)

/-! ## The loading model -/

/-- **A loading model** (module doc). -/
structure LoadModel : Type 1 where
  σ : Type
  mach : Silmaril.X86.RelIsa σ
  Started : Blob → Word → σ → Prop
  foreign : σ → Nat → Prop
  Client : (Nat → Prop) → σ → σ → Prop
  started_elf : ∀ F b x, Started F b x → Placement F b ∧ RoLoaded F b (mach.mem x)

namespace LoadModel

variable (LM : LoadModel)

/-- An argument or result register of a state, as a number. -/
def reg (x : LM.σ) (r : Silmaril.X86.Reg) : Nat := ((LM.mach.core x).read r).toNat

/-- The entry stack pointer. -/
def sp (x : LM.σ) : Nat := LM.reg x .rsp

end LoadModel

/-! ## Symbols -/

/-- **How the allocator's functions are named** in the file: the prefix of every name (`""`;
`"je_"` for a jemalloc built with `--with-jemalloc-prefix=je_`) and the version each reference
asks for (`none`: unversioned; glibc's `GLIBC_2.2.5`, `GLIBC_2.16`). -/
structure Syms where
  pre : String := ""
  ver : Op → Option Silmaril.Elf.Link.DynElf.Elf.Ver := fun _ => none

/-- The reference ld.so looks up for `op`. -/
def Syms.ref (S : Syms) (op : Op) : Silmaril.Elf.Link.DynElf.Elf.Ref :=
  ⟨Silmaril.Elf.Link.DynElf.nm S.pre ++ Silmaril.Elf.Link.DynElf.nm op.cname, false, S.ver op⟩

/-- The selector of `op`: ld.so's lookup in `.dynsym`. -/
def Syms.sel (S : Syms) (op : Op) : Sel := .dyn (S.ref op)

/-! ## Calls on the machine -/

/-- The stack a call may use below its entry `rsp` (the red zone included). -/
def budget : Nat := 0x10000

/-- `a` is in the scratch stack of a call entered with stack pointer `sp`. -/
def Scratch (sp a : Nat) : Prop := sp - budget ≤ a ∧ a < sp

variable {LM : LoadModel}

/-- The abstract call the argument registers make. -/
def callOf (LM : LoadModel) (op : Op) (x : LM.σ) : Call :=
  match op with
  | .malloc => .malloc (LM.reg x .rdi)
  | .free => .free (LM.reg x .rdi)
  | .calloc => .calloc (LM.reg x .rdi) (LM.reg x .rsi)
  | .realloc => .realloc (LM.reg x .rdi) (LM.reg x .rsi)
  | .alignedAlloc => .alignedAlloc (LM.reg x .rdi) (LM.reg x .rsi)
  | .posixMemalign => .posixMemalign (LM.reg x .rsi) (LM.reg x .rdx)
  | .usableSize => .usableSize (LM.reg x .rdi)

/-- The requested size of the block a call returns (`0` for `free`, `malloc_usable_size`). -/
def reqOf (LM : LoadModel) (op : Op) (x : LM.σ) : Nat :=
  match op with
  | .malloc => LM.reg x .rdi
  | .calloc => LM.reg x .rdi * LM.reg x .rsi
  | .realloc | .alignedAlloc => LM.reg x .rsi
  | .posixMemalign => LM.reg x .rdx
  | .free | .usableSize => 0

/-- The result of a call: `rax`, or `eax` for `posix_memalign` (an `int`). -/
def retOf (LM : LoadModel) (op : Op) (y : LM.σ) : Nat :=
  match op with
  | .posixMemalign => ((LM.mach.core y).read .rax).toNat % 2 ^ 32
  | _ => LM.reg y .rax

/-- `m` holds the 8-byte little-endian word `q` at `p`. -/
def WordAt (m : Memory) (p q : Nat) : Prop := m.readBytes p 8 = some (leBytes q 8)

/-- **The block a call hands out** (`0`: none): `rax` for `malloc`, `calloc`, `realloc`,
`aligned_alloc`; the word the result slot `*memptr` holds after a successful `posix_memalign`. -/
def BlkOf (LM : LoadModel) (op : Op) (x y : LM.σ) (q : Nat) : Prop :=
  match op with
  | .malloc | .calloc | .realloc | .alignedAlloc => q = LM.reg y .rax
  | .posixMemalign => (retOf LM op y = 0 ∧ WordAt (LM.mach.mem y) (LM.reg x .rdi) q) ∨
      (retOf LM op y ≠ 0 ∧ q = 0)
  | .free | .usableSize => q = 0

/-- `posix_memalign`'s result slot `[memptr, memptr + 8)`. -/
def Slot (LM : LoadModel) (op : Op) (x : LM.σ) (a : Nat) : Prop :=
  op = .posixMemalign ∧ LM.reg x .rdi ≤ a ∧ a < LM.reg x .rdi + 8

/-- The block a call releases: `free`'s and `realloc`'s argument, a live block of `h`. -/
def Released (LM : LoadModel) (h : Heap) (op : Op) (x : LM.σ) (a : Nat) : Prop :=
  (op = .free ∨ op = .realloc) ∧ ∃ n, h (LM.reg x .rdi) = some n ∧
    LM.reg x .rdi ≤ a ∧ a < LM.reg x .rdi + n

/-- The block `q` of `n` bytes. -/
def InBlk (q n a : Nat) : Prop := q ≠ 0 ∧ q ≤ a ∧ a < q + n

/-! ## The witness and the contract -/

/-- **A witness** (module doc): ghost abstract state, live blocks, owned regions, invariant. -/
structure Witness (LM : LoadModel) : Type 1 where
  St : Type
  heap : St → Heap
  own : Word → St → Nat → Prop
  Inv : Word → St → LM.σ → Prop

namespace Witness

variable (W : Witness LM)

/-- **(i) Setup**: every started state is in the invariant, with no live block. -/
def Setup (F : Blob) : Prop :=
  ∀ b x, LM.Started F b x → ∃ S, W.heap S = Heap.empty ∧ W.Inv b S x

/-- **The ownership discipline** (module doc). -/
structure Disc : Prop where
  disjoint : ∀ b S x a, W.Inv b S x → W.own b S a → ¬ (W.heap S).Owns a ∧ ¬ LM.foreign x a
  blocks : ∀ b S x a, W.Inv b S x → (W.heap S).Owns a →
    (LM.mach.mem x).permits .read a = true ∧ (LM.mach.mem x).permits .write a = true ∧
      ¬ LM.foreign x a
  stable : ∀ b S x y, W.Inv b S x → LM.Client (W.own b S) x y → W.Inv b S y

/-- **The stack budget is free**: `[sp - budget, sp + 8)` (the scratch stack and the return
address) is readable and writable, neither owned nor in a live block. -/
def StackOk (b : Word) (S : W.St) (x : LM.σ) : Prop :=
  budget ≤ LM.sp x ∧ LM.sp x + 8 < 2 ^ 64 ∧ ∀ a, LM.sp x - budget ≤ a → a < LM.sp x + 8 →
    (LM.mach.mem x).permits .read a = true ∧ (LM.mach.mem x).permits .write a = true ∧
      ¬ W.own b S a ∧ ¬ (W.heap S).Owns a

/-- **The entry**: System V, the stack budget free, a valid call; for `posix_memalign` a
writable result slot, neither owned nor in the scratch stack. -/
def Entry (op : Op) (b : Word) (S : W.St) (x : LM.σ) : Prop :=
  AbiEntry (LM.mach.core x) (LM.mach.mem x) ∧ W.StackOk b S x ∧
    Valid (W.heap S) (callOf LM op x) ∧
    (op = .posixMemalign → ∀ a, Slot LM op x a →
      (LM.mach.mem x).permits .write a = true ∧ ¬ W.own b S a ∧ a ≥ LM.sp x + 8)

/-- **(iv) The frame** of a call from `x` (state `S`) to `y` (state `S'`) that handed out `q`. -/
def Frame (op : Op) (b : Word) (S S' : W.St) (x y : LM.σ) (q : Nat) : Prop :=
  (∀ a, ¬ W.own b S a → ¬ W.own b S' a → ¬ Scratch (LM.sp x) a →
    ¬ Released LM (W.heap S) op x a → ¬ InBlk q (reqOf LM op x) a → ¬ Slot LM op x a →
    (LM.mach.mem y).bytes.get? a = (LM.mach.mem x).bytes.get? a) ∧
  (∀ a, ¬ W.own b S a → ¬ W.own b S' a →
    ¬ Released LM (W.heap S) op x a → ¬ InBlk q (reqOf LM op x) a →
    ∀ acc, (LM.mach.mem y).permits acc a = (LM.mach.mem x).permits acc a)

/-- **The returned block** `q ≠ 0` of the request's size: readable, writable, neither owned
nor foreign; zero for `calloc`; for `realloc`, the old block's first `min old n` bytes. -/
def BlockOk (op : Op) (b : Word) (S S' : W.St) (x y : LM.σ) (q : Nat) : Prop :=
  q ≠ 0 →
    (LM.mach.mem y).Permitted .read q (reqOf LM op x) ∧
    (LM.mach.mem y).Permitted .write q (reqOf LM op x) ∧
    (∀ a, q ≤ a → a < q + reqOf LM op x → ¬ W.own b S' a ∧ ¬ LM.foreign y a) ∧
    (op = .calloc → ∀ i < reqOf LM op x, (LM.mach.mem y).bytes.get? (q + i) = some 0#8) ∧
    (op = .realloc → ∀ old, W.heap S (LM.reg x .rdi) = some old → ∀ i < min old (reqOf LM op x),
      (LM.mach.mem y).bytes.get? (q + i) = (LM.mach.mem x).bytes.get? (LM.reg x .rdi + i))

/-- **What a return guarantees** at the relation `T` (module doc, (ii) and (iv)). -/
def Ret (T : Rel) (op : Op) (b : Word) (S : W.St) (x y : LM.σ) : Prop :=
  AbiReturn (LM.mach.core x) (LM.mach.mem x) (LM.mach.core y) ∧
    (LM.mach.core y).fsBase = (LM.mach.core x).fsBase ∧
    ∃ S' q, W.Inv b S' y ∧ BlkOf LM op x y q ∧
      T (W.heap S) (callOf LM op x) (W.heap S') (retOf LM op y) q ∧
      W.Frame op b S S' x y q ∧ W.BlockOk op b S S' x y q

/-- **(ii) A call of `op` at offset `v` meets the contract** at the relation `T`: from every
valid entry in the invariant (any placement), every run returns as `Ret` says. -/
def CallOk (T : Rel) (F : Blob) (op : Op) (v : Nat) : Prop :=
  ∀ b S x, Placement F b → W.Inv b S x → (LM.mach.core x).rip = b + BitVec.ofNat 64 v →
    W.Entry op b S x →
    Silmaril.X86.RelIsa.Must LM.mach (fun _ => True) (W.Ret T op b S x) x

end Witness

/-- **The allocator contract at relation `T` and signature `s`** (module doc). -/
def Contract (T : Rel) (LM : LoadModel) (s : Sig) (F : Blob) (S : Syms) : Prop :=
  ∃ v : Op → Nat, (∀ op ∈ s.ops, Bound F (S.sel op) (v op)) ∧
    ∃ W : Witness LM, W.Setup F ∧ W.Disc ∧ ∀ op ∈ s.ops, W.CallOk T F op (v op)

/-- **POSIX-safe with invariant** (the base strength). -/
def PosixSafe (LM : LoadModel) (s : Sig) (F : Blob) (S : Syms) : Prop := Contract loose LM s F S

/-- **The exports exist**: each function of `s` is bound (the binding part (0) alone, which a
row checks on the file's pages). -/
def Exports (s : Sig) (F : Blob) (S : Syms) : Prop :=
  ∀ op ∈ s.ops, ∃ v, Bound F (S.sel op) v

end Silmaril.Libc.AllocElf
